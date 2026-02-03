#!/usr/bin/env python3
"""Coordinate batch statement/proof formalization runs."""

from __future__ import annotations

import argparse
import json
import itertools
import subprocess
import sys
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Set, Tuple


DEFAULT_REGISTRY = Path("output/blueprint_to_proof/blueprint_nodes.json")
DEFAULT_LEAN_ROOT = Path("GhostConjectureLean")
DEFAULT_STATEMENT_RUNNER = Path("pipeline/blueprint_to_proof/statement_formalize_run.py")
DEFAULT_PROOF_RUNNER = Path("pipeline/blueprint_to_proof/proof_formalize_run.py")


def load_registry(path: Path) -> Dict[str, object]:
    if not path.exists():
        raise FileNotFoundError(f"Registry not found: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def is_formalized(node: dict, field: str) -> bool:
    status = node.get("status", {}) if isinstance(node, dict) else {}
    return status.get(field) == "formalized"


def statement_dependencies_formalized(nodes: dict, label: str) -> bool:
    node = nodes[label]
    deps = node.get("dependencies", {}).get("statement", [])
    for dep in deps:
        if dep not in nodes or not is_formalized(nodes[dep], "statement"):
            return False
    return True


def proof_dependencies_formalized(nodes: dict, label: str) -> bool:
    node = nodes[label]
    deps = node.get("dependencies", {}).get("proof", [])
    for dep in deps:
        if dep not in nodes or not is_formalized(nodes[dep], "statement"):
            return False
    return True


def select_statement_candidates(nodes: dict) -> List[str]:
    labels: List[str] = []
    for label, node in nodes.items():
        if is_formalized(node, "statement"):
            continue
        if statement_dependencies_formalized(nodes, label):
            labels.append(label)
    return sorted(labels)


def build_proof_dependency_edges(nodes: dict, candidates: List[str]) -> Dict[str, Set[str]]:
    edges: Dict[str, Set[str]] = {label: set() for label in candidates}
    candidate_set = set(candidates)
    for label in candidates:
        deps = nodes[label].get("dependencies", {}).get("proof", [])
        for dep in deps:
            if dep in candidate_set:
                edges[label].add(dep)
    return edges


def select_independent_proof_candidates(nodes: dict, max_proof_failures: int) -> List[str]:
    candidates: List[str] = []
    for label, node in nodes.items():
        if not node.get("has_proof", False):
            continue
        if is_formalized(node, "proof"):
            continue
        lean_obj = node.get("lean", {})
        if not isinstance(lean_obj, dict) or not lean_obj.get("name"):
            continue
        if not proof_dependencies_formalized(nodes, label):
            continue
        failures = 0
        if isinstance(node, dict):
            failures = int(node.get("proof_failures", 0))
        if failures > max_proof_failures:
            continue
        candidates.append(label)

    candidates = sorted(candidates)
    edges = build_proof_dependency_edges(nodes, candidates)

    selected: List[str] = []
    selected_set: Set[str] = set()
    for label in candidates:
        if any((label in edges.get(sel, set()) or sel in edges.get(label, set())) for sel in selected_set):
            continue
        selected.append(label)
        selected_set.add(label)
    return selected


def run_tasks(
    labels: List[str],
    runner: Path,
    lean_root: Path,
    max_concurrency: int,
    dry_run: bool,
) -> List[Tuple[str, int]]:
    if not labels:
        return []

    def _run(label: str) -> Tuple[str, int]:
        with in_progress_lock:
            in_progress.add(label)
        print(f"Starting {label}...", flush=True)
        cmd = ["python", str(runner), "--label", label, "--lean-root", str(lean_root)]
        result = subprocess.run(cmd, check=False)
        sys.stdout.write("\n")
        sys.stdout.flush()
        print(f"Finished {label} (exit {result.returncode})", flush=True)
        with in_progress_lock:
            in_progress.discard(label)
        return label, result.returncode

    if dry_run:
        for label in labels:
            print(f"[dry-run] Would run {label}", flush=True)
        return [(label, 0) for label in labels]

    results: List[Tuple[str, int]] = []
    in_progress: Set[str] = set()
    in_progress_lock = threading.Lock()
    stop_event = threading.Event()

    def _status_reporter() -> None:
        spinner = itertools.cycle(["-", "/", "|", "\\"])
        while not stop_event.wait(0.25):
            with in_progress_lock:
                running = ", ".join(sorted(in_progress)) if in_progress else "(none)"
            sys.stdout.write(f"\r[status] {next(spinner)} Running: {running}")
            sys.stdout.flush()

    with ThreadPoolExecutor(max_workers=max_concurrency) as executor:
        reporter = threading.Thread(target=_status_reporter, daemon=True)
        reporter.start()
        futures = {executor.submit(_run, label): label for label in labels}
        for future in as_completed(futures):
            label, code = future.result()
            results.append((label, code))
        stop_event.set()
        reporter.join(timeout=1)
        sys.stdout.write("\r")
        sys.stdout.flush()
        print("", flush=True)
    return results


def summarize_results(results: List[Tuple[str, int]]) -> Dict[str, List[str]]:
    summary = {"success": [], "failed": []}
    for label, code in results:
        if code == 0:
            summary["success"].append(label)
        else:
            summary["failed"].append(label)
    return summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Coordinate batch formalization runs.")
    parser.add_argument(
        "--registry",
        default=str(DEFAULT_REGISTRY),
        help="Path to blueprint registry JSON",
    )
    parser.add_argument(
        "--lean-root",
        default=str(DEFAULT_LEAN_ROOT),
        help="Lean project root",
    )
    parser.add_argument(
        "--statement-runner",
        default=str(DEFAULT_STATEMENT_RUNNER),
        help="Path to statement formalization runner",
    )
    parser.add_argument(
        "--proof-runner",
        default=str(DEFAULT_PROOF_RUNNER),
        help="Path to proof formalization runner",
    )
    parser.add_argument(
        "--max-concurrency",
        type=int,
        default=2,
        help="Maximum concurrent tasks",
    )
    parser.add_argument(
        "--max-count",
        type=int,
        default=None,
        help="Maximum number of tasks total across statement+proof",
    )
    parser.add_argument(
        "--mode",
        choices=("auto", "statement", "proof"),
        default="auto",
        help="Which phase to run (default: auto)",
    )
    parser.add_argument(
        "--max-proof-failures",
        type=int,
        default=0,
        help="Skip proofs with failures greater than this count",
    )
    parser.add_argument(
        "--loop-proofs",
        action="store_true",
        help="Repeat proof runs until all remaining proofs exceed max failures",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Only list tasks and skip running codex",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    registry = load_registry(Path(args.registry))
    nodes = registry.get("nodes") if isinstance(registry, dict) else None
    if not isinstance(nodes, dict):
        raise ValueError("Invalid registry format: missing nodes")

    statement_labels = select_statement_candidates(nodes)
    proof_labels = select_independent_proof_candidates(nodes, args.max_proof_failures)

    if args.mode == "auto":
        mode = "statement" if statement_labels else "proof"
    else:
        mode = args.mode
    if mode == "statement":
        proof_labels = []
    else:
        statement_labels = []

    if args.max_count is not None:
        if mode == "statement":
            statement_labels = statement_labels[: args.max_count]
        else:
            proof_labels = proof_labels[: args.max_count]

    print(f"Mode: {mode}")
    print("Statements to process:")
    for label in statement_labels:
        print(f"- {label}")
    print("Proofs to process:")
    for label in proof_labels:
        print(f"- {label}")
    print(f"Max concurrency: {args.max_concurrency}", flush=True)

    statement_results: List[Tuple[str, int]] = []
    proof_results: List[Tuple[str, int]] = []

    statement_results = run_tasks(
        statement_labels,
        Path(args.statement_runner),
        Path(args.lean_root),
        args.max_concurrency,
        args.dry_run,
    )

    if mode == "proof" and args.loop_proofs and not args.dry_run:
        loop_round = 1
        while True:
            registry = load_registry(Path(args.registry))
            nodes = registry.get("nodes") if isinstance(registry, dict) else None
            if not isinstance(nodes, dict):
                break
            proof_labels = select_independent_proof_candidates(nodes, args.max_proof_failures)
            if args.max_count is not None:
                proof_labels = proof_labels[: args.max_count]
            if not proof_labels:
                break
            print(f"\nProof loop round {loop_round}", flush=True)
            proof_results.extend(
                run_tasks(
                    proof_labels,
                    Path(args.proof_runner),
                    Path(args.lean_root),
                    args.max_concurrency,
                    args.dry_run,
                )
            )
            loop_round += 1
    else:
        proof_results = run_tasks(
            proof_labels,
            Path(args.proof_runner),
            Path(args.lean_root),
            args.max_concurrency,
            args.dry_run,
        )

    statement_summary = summarize_results(statement_results)
    proof_summary = summarize_results(proof_results)

    print("\nStatement formalization results:")
    print("  success:", ", ".join(statement_summary["success"]) or "(none)")
    print("  failed:", ", ".join(statement_summary["failed"]) or "(none)")

    print("\nProof formalization results:")
    print("  success:", ", ".join(proof_summary["success"]) or "(none)")
    print("  failed:", ", ".join(proof_summary["failed"]) or "(none)")


if __name__ == "__main__":
    main()
