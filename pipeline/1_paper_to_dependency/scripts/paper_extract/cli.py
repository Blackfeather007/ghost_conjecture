from __future__ import annotations

import argparse
from pathlib import Path
from typing import Optional

from .checker import check
from .extractor import extract


def default_out_json(root_tex: Path) -> Path:
    stage_dir = Path(__file__).resolve().parent.parent
    return stage_dir / "output" / f"{root_tex.stem}.json"


def default_aux(root_tex: Path) -> Optional[Path]:
    cand = root_tex.with_suffix(".aux")
    return cand if cand.exists() else None


def main(argv: Optional[list[str]] = None) -> None:
    parser = argparse.ArgumentParser(description="Extract theorem/proof/equation blocks from LaTeX sources.")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_extract = sub.add_parser("extract", help="Extract blocks and write a JSON file.")
    p_extract.add_argument("--root-tex", required=True, type=Path, help="Path to the root .tex file.")
    p_extract.add_argument("--out-json", type=Path, default=None, help="Output JSON path.")
    p_extract.add_argument(
        "--aux",
        type=Path,
        default=None,
        help="Optional .aux file path for PDF-accurate numbering (defaults to <root>.aux if it exists).",
    )

    p_check = sub.add_parser("check", help="Validate that all referenced labels exist as extracted blocks.")
    p_check.add_argument("--in-json", required=True, type=Path, help="Input JSON path produced by 'extract'.")
    p_check.add_argument("--out-diagnostics", type=Path, default=None, help="Optional path to write diagnostics JSON.")
    p_check.add_argument(
        "--strict",
        action="store_true",
        help="Fail on any missing label (default: only fail on missing theorem/equation labels).",
    )

    args = parser.parse_args(argv)

    if args.cmd == "extract":
        root_tex: Path = args.root_tex
        out_json: Path = args.out_json or default_out_json(root_tex)
        aux: Optional[Path] = args.aux or default_aux(root_tex)
        extract(root_tex=root_tex, out_json=out_json, aux=aux)
        print(f"Wrote: {out_json}")
        return

    if args.cmd == "check":
        diag = check(in_json=args.in_json, out_diagnostics=args.out_diagnostics)
        if args.out_diagnostics:
            print(f"Wrote: {args.out_diagnostics}")
        if diag["ok"]:
            print("OK")
            return

        missing = diag.get("missing_labels") or []
        fatal = []
        if args.strict:
            fatal = missing
        else:
            for item in missing:
                kind = item.get("declared_kind")
                if kind == "equation":
                    fatal.append(item)
                elif kind and kind not in ("section", "other", "proof"):
                    fatal.append(item)

        if fatal:
            raise SystemExit(2)
        print("OK (non-strict): only non-extractable/external labels are missing")
        return

