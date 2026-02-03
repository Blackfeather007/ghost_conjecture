#!/usr/bin/env python3
"""Run codex exec to formalize a proof using the blueprint registry."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import List


DEFAULT_REGISTRY = Path("output/blueprint_to_proof/blueprint_nodes.json")
DEFAULT_TEMPLATE = Path("pipeline/blueprint_to_proof/proof_formalize_prompt.md")
DEFAULT_LEAN_ROOT = Path("GhostConjectureLean")
DEFAULT_LOG_DIR = Path("output/blueprint_to_proof/proof_formalization_log")
DEFAULT_CODEX_CMD = ["codex", "exec", "--full-auto", "--json"]


def safe_filename(label: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", label)


def load_registry(path: Path) -> dict:
    if not path.exists():
        raise FileNotFoundError(f"Registry not found: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def read_file_or_note(path: Path) -> str:
    if not path.exists():
        return f"(missing file: {path})"
    return path.read_text(encoding="utf-8")


def format_dependency(label: str, node: dict | None, lean_root: Path) -> str:
    if node is None:
        return (
            f"- label: {label}\n"
            f"  - latex: (missing from registry)\n"
            f"  - lean file: (unknown)\n"
            f"  - lean content: (unknown)\n"
        )

    latex = ""
    latex_obj = node.get("latex", {}) if isinstance(node, dict) else {}
    if isinstance(latex_obj, dict):
        latex = latex_obj.get("statement", "")
    lean_obj = node.get("lean", {}) if isinstance(node, dict) else {}
    lean_file = None
    if isinstance(lean_obj, dict):
        lean_file = lean_obj.get("file")

    lean_content = "(not recorded)"
    if lean_file:
        lean_path = lean_root / lean_file
        lean_content = read_file_or_note(lean_path)

    return (
        f"- label: {label}\n"
        f"  - latex:\n```tex\n{latex}\n```\n"
        f"  - lean file: {lean_file or '(not recorded)'}\n"
        f"  - lean content:\n```lean\n{lean_content}\n```\n"
    )


def build_dependencies_block(deps: List[str], nodes: dict, lean_root: Path) -> str:
    if not deps:
        return "(none)"

    parts: List[str] = []
    for dep in deps:
        node = nodes.get(dep) if isinstance(nodes, dict) else None
        parts.append(format_dependency(dep, node, lean_root))
    return "\n".join(parts).rstrip()


def render_prompt(
    template: str,
    theorem_content: str,
    proof_content: str,
    lean_file_path: str,
    lean_decl_name: str,
    deps_block: str,
) -> str:
    return (
        template.replace("{theorem_content}", theorem_content)
        .replace("{proof_content}", proof_content)
        .replace("{lean_file_path}", lean_file_path)
        .replace("{lean_decl_name}", lean_decl_name)
        .replace("{list_of_latex_with_lean_file}", deps_block)
    )


def build_prompt(
    label: str,
    registry_path: Path,
    template_path: Path,
    lean_root: Path,
) -> str:
    registry = load_registry(registry_path)
    nodes = registry.get("nodes") if isinstance(registry, dict) else None
    if not isinstance(nodes, dict) or label not in nodes:
        raise ValueError(f"Label {label} not found in registry {registry_path}")

    node = nodes[label]
    latex_obj = node.get("latex", {}) if isinstance(node, dict) else {}
    theorem_content = latex_obj.get("statement", "") if isinstance(latex_obj, dict) else ""
    proof_content = latex_obj.get("proof", "") if isinstance(latex_obj, dict) else ""

    lean_obj = node.get("lean", {}) if isinstance(node, dict) else {}
    lean_file = lean_obj.get("file") if isinstance(lean_obj, dict) else None
    lean_name = lean_obj.get("name") if isinstance(lean_obj, dict) else None

    if not lean_file or not lean_name:
        raise ValueError(
            f"Label {label} is missing lean.file or lean.name in registry; update first."
        )

    deps_obj = node.get("dependencies", {}) if isinstance(node, dict) else {}
    deps = deps_obj.get("proof", []) if isinstance(deps_obj, dict) else []
    deps_block = build_dependencies_block(deps, nodes, lean_root)

    template = template_path.read_text(encoding="utf-8")
    return render_prompt(
        template,
        theorem_content,
        proof_content,
        lean_file,
        lean_name,
        deps_block,
    )


def run_codex(prompt: str, cmd: List[str], workspace_dir: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        list(cmd),
        input=prompt,
        text=True,
        capture_output=True,
        cwd=workspace_dir,
        check=False,
    )


def write_log(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run codex exec to formalize a proof and log the session."
    )
    parser.add_argument("--label", required=True, help="Blueprint label to formalize")
    parser.add_argument(
        "--registry",
        default=str(DEFAULT_REGISTRY),
        help="Path to blueprint registry JSON",
    )
    parser.add_argument(
        "--template",
        default=str(DEFAULT_TEMPLATE),
        help="Prompt template file",
    )
    parser.add_argument(
        "--lean-root",
        default=str(DEFAULT_LEAN_ROOT),
        help="Lean project root",
    )
    parser.add_argument(
        "--log-dir",
        default=str(DEFAULT_LOG_DIR),
        help="Directory to store formalization logs",
    )
    parser.add_argument(
        "--codex-cmd",
        nargs="+",
        default=DEFAULT_CODEX_CMD,
        help="Command list to run Codex (default: codex exec --full-auto --json)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print the prompt and exit without running codex",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    registry_path = Path(args.registry)
    template_path = Path(args.template)
    lean_root = Path(args.lean_root)
    log_dir = Path(args.log_dir)

    prompt = build_prompt(args.label, registry_path, template_path, lean_root)

    if args.dry_run:
        print(prompt)
        return

    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    log_name = f"{safe_filename(args.label)}_{timestamp}.log"
    log_path = log_dir / log_name

    result = run_codex(prompt, args.codex_cmd, lean_root)

    stdout = result.stdout or ""
    stderr = result.stderr or ""
    log_content = (
        f"# label: {args.label}\n"
        f"# timestamp: {timestamp}\n"
        f"# codex cmd: {args.codex_cmd}\n\n"
        f"## Prompt\n{prompt}\n\n"
        f"## Codex stdout\n{stdout}\n\n"
        f"## Codex stderr\n{stderr}\n"
    )

    if result.returncode != 0:
        write_log(log_path, log_content)
        raise RuntimeError(f"codex exec failed (code {result.returncode}); see log {log_path}")

    write_log(log_path, log_content)


if __name__ == "__main__":
    main()
