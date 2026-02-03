#!/usr/bin/env python3
"""Initialize and maintain a JSON registry for blueprint declarations."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
import re
from typing import Dict, List, Optional, Tuple


DEFAULT_BLUEPRINT_DIR = Path("GhostConjectureLean/blueprint/src/chapters")
DEFAULT_OUTPUT_PATH = Path("output/blueprint_to_proof/blueprint_nodes.json")
DEFAULT_LEAN_ROOT = Path("GhostConjectureLean")

PROOF_REQUIRED_ENVS = {
    "lemma",
    "theorem",
    "proposition",
    "corollary",
    "claim",
    "conjecture",
}

DEFAULT_STATUS = {"statement": "todo", "proof": "todo"}
FORMALIZED_STATUS = "formalized"


@dataclass
class EnvBlock:
    env: str
    start: int
    end: int
    content: str
    start_line: int


BEGIN_END_RE = re.compile(r"\\(begin|end)\{([^}]+)\}")
USES_RE = re.compile(r"\\uses\{([^}]*)\}", re.DOTALL)
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
BEGIN_TITLE_RE = re.compile(r"\\begin\{([^}]+)\}(?:\[([^]]+)\])?")


def find_unescaped_percent(line: str) -> int:
    escaped = False
    for idx, ch in enumerate(line):
        if ch == "\\" and not escaped:
            escaped = True
            continue
        if ch == "%" and not escaped:
            return idx
        escaped = False
    return -1


def find_top_level_blocks(text: str) -> List[EnvBlock]:
    stack: List[Tuple[str, int, int]] = []  # env, start_pos, start_line
    blocks: List[EnvBlock] = []
    pos = 0
    line_no = 1

    lines = text.splitlines(keepends=True)
    for line in lines:
        scan_line = line
        comment_idx = find_unescaped_percent(line)
        if comment_idx != -1:
            scan_line = line[:comment_idx]
        for match in BEGIN_END_RE.finditer(scan_line):
            kind = match.group(1)
            env = match.group(2)
            token_pos = pos + match.start()
            if kind == "begin":
                stack.append((env, token_pos, line_no))
            else:
                if not stack:
                    raise ValueError(f"Unmatched \\end{{{env}}} at line {line_no}")
                last_env, start_pos, start_line = stack.pop()
                if last_env != env:
                    raise ValueError(
                        f"Mismatched environment: expected \\end{{{last_env}}} "
                        f"but found \\end{{{env}}} at line {line_no}"
                    )
                if not stack:
                    content = text[start_pos : token_pos + len(match.group(0))]
                    blocks.append(
                        EnvBlock(
                            env=env,
                            start=start_pos,
                            end=token_pos + len(match.group(0)),
                            content=content,
                            start_line=start_line,
                        )
                    )
        pos += len(line)
        line_no += 1

    if stack:
        env, _, start_line = stack[-1]
        raise ValueError(f"Unclosed \\begin{{{env}}} starting at line {start_line}")

    blocks.sort(key=lambda b: b.start)
    return blocks


def extract_uses(block_text: str) -> List[str]:
    deps: List[str] = []
    for raw in USES_RE.findall(block_text):
        normalized = raw.replace("\n", " ").strip()
        if not normalized:
            continue
        for item in normalized.split(","):
            label = item.strip()
            if label and label not in deps:
                deps.append(label)
    return deps


def extract_label(block_text: str) -> Optional[str]:
    match = LABEL_RE.search(block_text)
    if not match:
        return None
    return match.group(1).strip()


def extract_title(block_text: str) -> Optional[str]:
    match = BEGIN_TITLE_RE.search(block_text)
    if not match:
        return None
    title = match.group(2)
    return title.strip() if title else None


def parse_blueprint_file(path: Path) -> List[Dict[str, object]]:
    text = path.read_text(encoding="utf-8")
    if "\\proves" in text:
        raise AssertionError(f"\\proves found in {path}. Proofs must follow statements directly.")

    blocks = find_top_level_blocks(text)
    nodes: List[Dict[str, object]] = []

    i = 0
    while i < len(blocks):
        block = blocks[i]
        if block.env == "proof":
            print(
                f"WARN: proof block at {path}:{block.start_line} has no preceding statement",
                file=sys.stderr,
            )
            i += 1
            continue

        label = extract_label(block.content)
        if not label:
            i += 1
            continue

        statement_uses = extract_uses(block.content)
        title = extract_title(block.content)
        proof_block: Optional[EnvBlock] = None
        proof_uses: List[str] = []
        proof_latex = ""

        if i + 1 < len(blocks) and blocks[i + 1].env == "proof":
            proof_block = blocks[i + 1]
            proof_uses = extract_uses(proof_block.content)
            proof_latex = proof_block.content
            i += 1  # skip proof block
        else:
            if block.env.lower() in PROOF_REQUIRED_ENVS:
                print(
                    f"WARN: missing proof for {label} ({block.env}) in {path}:{block.start_line}",
                    file=sys.stderr,
                )

        nodes.append(
            {
                "label": label,
                "env": block.env,
                "title": title,
                "dependencies": {
                    "statement": statement_uses,
                    "proof": proof_uses,
                },
                "latex": {
                    "statement": block.content,
                    "proof": proof_latex,
                },
                "lean": {"file": None, "name": None},
                "has_proof": proof_block is not None,
                "source": {
                    "file": str(path),
                    "line": block.start_line,
                },
            }
        )
        i += 1

    return nodes


def load_existing(path: Path) -> Dict[str, object]:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"Invalid JSON at {path}: {exc}")


def merge_nodes(
    existing: Dict[str, object],
    new_nodes: Dict[str, Dict[str, object]],
) -> Dict[str, Dict[str, object]]:
    existing_nodes = existing.get("nodes", {}) if isinstance(existing, dict) else {}
    merged: Dict[str, Dict[str, object]] = {}

    for label, node in new_nodes.items():
        prior = existing_nodes.get(label, {}) if isinstance(existing_nodes, dict) else {}
        merged_node = dict(node)
        merged_node["status"] = prior.get("status", DEFAULT_STATUS)
        prior_lean = prior.get("lean") if isinstance(prior, dict) else None
        if prior_lean and merged_node.get("lean") == {"file": None, "name": None}:
            merged_node["lean"] = prior_lean
        merged[label] = merged_node

    return merged


def build_registry(blueprint_dir: Path, output_path: Path, verbose: bool) -> None:
    tex_files = sorted(blueprint_dir.rglob("*.tex"))
    if not tex_files:
        raise FileNotFoundError(f"No .tex files found in {blueprint_dir}")

    nodes_by_label: Dict[str, Dict[str, object]] = {}
    for tex_file in tex_files:
        if verbose:
            print(f"Parsing {tex_file}")
        for node in parse_blueprint_file(tex_file):
            label = node["label"]
            if label in nodes_by_label:
                raise ValueError(f"Duplicate label {label} found in {tex_file}")
            nodes_by_label[label] = node

    existing = load_existing(output_path)
    merged_nodes = merge_nodes(existing, nodes_by_label)
    existing_metadata = existing.get("metadata", {}) if isinstance(existing, dict) else {}

    metadata = {
        "blueprint_dir": str(blueprint_dir),
        "files": [str(p) for p in tex_files],
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "script": "pipeline/blueprint_to_proof/blueprint_to_proof.py",
    }
    if "updated_at" in existing_metadata:
        metadata["updated_at"] = existing_metadata["updated_at"]

    output = {
        "metadata": metadata,
        "nodes": merged_nodes,
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def resolve_lean_file(lean_root: Path, lean_file: Path) -> str:
    lean_root_abs = lean_root.resolve()
    lean_file_path = lean_file if lean_file.is_absolute() else lean_root / lean_file
    lean_file_abs = lean_file_path.resolve()
    try:
        rel = lean_file_abs.relative_to(lean_root_abs)
    except ValueError as exc:
        raise ValueError(f"Lean file {lean_file_abs} is not under {lean_root_abs}") from exc
    return rel.as_posix()


def update_block_with_lean(block_text: str, lean_name: str, label: str) -> str:
    lines = block_text.splitlines()
    lean_pattern = re.compile(r"\\\\lean\\{[^}]*\\}")

    idx_lean = None
    idx_leanok = None
    for idx, line in enumerate(lines):
        if idx_lean is None and "\\lean{" in line:
            idx_lean = idx
        if idx_leanok is None and "\\leanok" in line:
            idx_leanok = idx

    if idx_lean is not None:
        lines[idx_lean] = lean_pattern.sub(f"\\\\lean{{{lean_name}}}", lines[idx_lean])

    def leading_ws(line: str) -> str:
        return line[: len(line) - len(line.lstrip())]

    def insert_line(at: int, content: str) -> None:
        lines.insert(at, content)

    if idx_lean is not None and idx_leanok is None:
        insert_line(idx_lean + 1, f"{leading_ws(lines[idx_lean])}\\leanok")
    elif idx_leanok is not None and idx_lean is None:
        insert_line(idx_leanok, f"{leading_ws(lines[idx_leanok])}\\lean{{{lean_name}}}")
    elif idx_lean is None and idx_leanok is None:
        insert_after = None
        for idx, line in enumerate(lines):
            if "\\uses{" in line:
                insert_after = idx
        if insert_after is None:
            for idx, line in enumerate(lines):
                if "\\label{" in line:
                    insert_after = idx
                    break
        if insert_after is None:
            insert_after = 0
        indent = leading_ws(lines[insert_after]) if lines else "  "
        insert_line(insert_after + 1, f"{indent}\\lean{{{lean_name}}}")
        insert_line(insert_after + 2, f"{indent}\\leanok")

    updated = "\n".join(lines)
    if f"\\label{{{label}}}" not in updated:
        raise ValueError(f"Label {label} disappeared while updating block.")
    return updated


def locate_label_in_file(path: Path, label: str) -> EnvBlock:
    text = path.read_text(encoding="utf-8")
    blocks = find_top_level_blocks(text)
    for block in blocks:
        if block.env == "proof":
            continue
        if extract_label(block.content) == label:
            return block
    raise ValueError(f"Label {label} not found in {path}")


def update_blueprint_label(blueprint_dir: Path, label: str, lean_name: str, verbose: bool) -> Path:
    tex_files = sorted(blueprint_dir.rglob("*.tex"))
    if not tex_files:
        raise FileNotFoundError(f"No .tex files found in {blueprint_dir}")

    matches: List[Tuple[Path, EnvBlock]] = []
    for tex_file in tex_files:
        text = tex_file.read_text(encoding="utf-8")
        if "\\proves" in text:
            raise AssertionError(f"\\proves found in {tex_file}. Proofs must follow statements directly.")
        blocks = find_top_level_blocks(text)
        for block in blocks:
            if block.env == "proof":
                continue
            if extract_label(block.content) == label:
                matches.append((tex_file, block))

    if not matches:
        raise ValueError(f"Label {label} not found in {blueprint_dir}")
    if len(matches) > 1:
        paths = ", ".join(str(p) for p, _ in matches)
        raise ValueError(f"Label {label} found in multiple files: {paths}")

    tex_file, block = matches[0]
    text = tex_file.read_text(encoding="utf-8")
    new_block = update_block_with_lean(block.content, lean_name, label)
    new_text = text[: block.start] + new_block + text[block.end :]
    tex_file.write_text(new_text, encoding="utf-8")
    if verbose:
        print(f"Updated {label} in {tex_file}")
    return tex_file


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Initialize and maintain blueprint-to-proof JSON registry."
    )
    subparsers = parser.add_subparsers(dest="mode", required=True)

    init_parser = subparsers.add_parser("init", help="Initialize or refresh the registry.")
    init_parser.add_argument(
        "--blueprint-dir",
        default=str(DEFAULT_BLUEPRINT_DIR),
        help="Directory containing blueprint .tex files",
    )
    init_parser.add_argument(
        "--output",
        default=str(DEFAULT_OUTPUT_PATH),
        help="Output JSON path",
    )
    init_parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print parsing progress",
    )

    update_parser = subparsers.add_parser("update", help="Mark a statement as formalized.")
    update_parser.add_argument(
        "--label",
        required=True,
        help="Blueprint label to update",
    )
    update_parser.add_argument(
        "--lean-file",
        required=True,
        help="Path to the Lean file (absolute or relative to --lean-root)",
    )
    update_parser.add_argument(
        "--lean-name",
        required=True,
        help="Fully qualified Lean name",
    )
    update_parser.add_argument(
        "--lean-root",
        default=str(DEFAULT_LEAN_ROOT),
        help="Lean project root for relative path computation",
    )
    update_parser.add_argument(
        "--blueprint-dir",
        default=str(DEFAULT_BLUEPRINT_DIR),
        help="Directory containing blueprint .tex files",
    )
    update_parser.add_argument(
        "--output",
        default=str(DEFAULT_OUTPUT_PATH),
        help="Output JSON path",
    )
    update_parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print update progress",
    )

    return parser.parse_args()


def main() -> None:
    args = parse_args()

    if args.mode == "init":
        blueprint_dir = Path(args.blueprint_dir)
        output_path = Path(args.output)

        if not blueprint_dir.exists():
            raise FileNotFoundError(f"Blueprint directory not found: {blueprint_dir}")

        build_registry(blueprint_dir, output_path, args.verbose)
        return

    if args.mode == "update":
        blueprint_dir = Path(args.blueprint_dir)
        output_path = Path(args.output)
        lean_root = Path(args.lean_root)
        lean_file = Path(args.lean_file)
        lean_name = args.lean_name

        if not blueprint_dir.exists():
            raise FileNotFoundError(f"Blueprint directory not found: {blueprint_dir}")
        if not lean_root.exists():
            raise FileNotFoundError(f"Lean root not found: {lean_root}")

        data = load_existing(output_path)
        if not data:
            raise FileNotFoundError(f"Registry not found at {output_path}; run init first.")
        nodes = data.get("nodes")
        if not isinstance(nodes, dict) or args.label not in nodes:
            raise ValueError(f"Label {args.label} not found in registry. Run init to refresh.")

        tex_file = update_blueprint_label(blueprint_dir, args.label, lean_name, args.verbose)
        updated_block = locate_label_in_file(tex_file, args.label)

        rel_path = resolve_lean_file(lean_root, lean_file)
        node = nodes[args.label]
        status = node.get("status", dict(DEFAULT_STATUS))
        status["statement"] = FORMALIZED_STATUS
        node["status"] = status
        node["lean"] = {"file": rel_path, "name": lean_name}
        node["source"] = {"file": str(tex_file), "line": updated_block.start_line}
        nodes[args.label] = node
        data["nodes"] = nodes
        metadata = data.get("metadata", {})
        metadata["updated_at"] = datetime.now(timezone.utc).isoformat()
        data["metadata"] = metadata
        output_path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        build_registry(blueprint_dir, output_path, args.verbose)
        return

    raise ValueError(f"Unknown mode {args.mode}")


if __name__ == "__main__":
    main()
