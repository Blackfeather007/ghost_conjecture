#!/usr/bin/env python3
"""Run codex exec to formalize a statement and update the registry."""

from __future__ import annotations

import argparse
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Tuple

import json

DEFAULT_REGISTRY = Path("output/blueprint_to_proof/blueprint_nodes.json")
DEFAULT_TEMPLATE = Path("pipeline/blueprint_to_proof/statement_formalize_prompt.md")
DEFAULT_LEAN_ROOT = Path("GhostConjectureLean")
DEFAULT_LOG_DIR = Path("output/blueprint_to_proof/statement_formalization_log")
DEFAULT_CODEX_CMD = ["codex", "exec", "--full-auto", "--json"]
DEFAULT_UPDATE_SCRIPT = Path("pipeline/blueprint_to_proof/blueprint_registry.py")


def safe_filename(label: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", label)


def parse_agent_output(output: str) -> Tuple[str, str]:
    raw = extract_text_from_codex_output(output)
    file_matches = re.findall(r"^\s*LEAN_FILE:\s*(.+)$", raw, flags=re.MULTILINE)
    name_matches = re.findall(r"^\s*LEAN_NAME:\s*(.+)$", raw, flags=re.MULTILINE)
    if not file_matches or not name_matches:
        raise ValueError("Agent output missing LEAN_FILE or LEAN_NAME lines.")
    return file_matches[-1].strip(), name_matches[-1].strip()


def extract_text_from_json(payload: object) -> str:
    if isinstance(payload, str):
        return payload
    if isinstance(payload, list):
        return "\n".join(extract_text_from_json(item) for item in payload)
    if isinstance(payload, dict):
        for key in ("message", "output", "content", "text", "stdout"):
            if key in payload:
                return extract_text_from_json(payload[key])
        return "\n".join(extract_text_from_json(v) for v in payload.values())
    return str(payload)


def extract_text_from_codex_output(output: str) -> str:
    """Parse codex --json stream and extract the final agent message text."""
    lines = [line for line in output.splitlines() if line.strip()]
    if not lines:
        return output

    messages: List[str] = []
    for line in lines:
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(event, dict):
            continue
        item = event.get("item")
        if isinstance(item, dict) and item.get("type") == "agent_message":
            text = item.get("text")
            if isinstance(text, str):
                messages.append(text)

    if messages:
        return messages[-1]

    try:
        parsed = json.loads(output)
        return extract_text_from_json(parsed)
    except json.JSONDecodeError:
        return output


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


def render_prompt(template: str, latex_snippet: str, deps_block: str) -> str:
    return (
        template.replace("{latex_snippet_of_decl}", latex_snippet).replace(
            "{list_of_latex_with_lean_file}", deps_block
        )
    )


def write_log(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


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
    latex_snippet = latex_obj.get("statement", "") if isinstance(latex_obj, dict) else ""

    deps_obj = node.get("dependencies", {}) if isinstance(node, dict) else {}
    deps = deps_obj.get("statement", []) if isinstance(deps_obj, dict) else []
    deps_block = build_dependencies_block(deps, nodes, lean_root)

    template = template_path.read_text(encoding="utf-8")
    return render_prompt(template, latex_snippet, deps_block)


def run_codex(prompt: str, cmd: List[str], workspace_dir: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        list(cmd),
        input=prompt,
        text=True,
        capture_output=True,
        cwd=workspace_dir,
        check=False,
    )


def run_update(
    update_script: Path,
    label: str,
    lean_file: str,
    lean_name: str,
    lean_root: Path,
) -> None:
    cmd = [
        "python",
        str(update_script),
        "update",
        "--label",
        label,
        "--lean-file",
        lean_file,
        "--lean-name",
        lean_name,
        "--lean-root",
        str(lean_root),
    ]
    subprocess.run(cmd, check=True)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run codex exec to formalize a statement and update the registry."
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
        "--update-script",
        default=str(DEFAULT_UPDATE_SCRIPT),
        help="Path to registry update script",
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
    update_script = Path(args.update_script)

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

    try:
        lean_file, lean_name = parse_agent_output(stdout)
    except ValueError:
        write_log(log_path, log_content)
        raise

    log_content += f"\n## Parsed Output\nLEAN_FILE: {lean_file}\nLEAN_NAME: {lean_name}\n"
    write_log(log_path, log_content)
    run_update(update_script, args.label, lean_file, lean_name, lean_root)


if __name__ == "__main__":
    main()
