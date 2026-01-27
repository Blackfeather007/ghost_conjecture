from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, Optional

from .util import read_text


def check(*, in_json: Path, out_diagnostics: Optional[Path]) -> Dict[str, Any]:
    data = json.loads(read_text(in_json))
    blocks = data.get("blocks", [])
    declared_labels = data.get("declared_labels") or {}

    by_label: Dict[str, str] = {}
    for b in blocks:
        lab = b.get("label")
        if lab:
            by_label.setdefault(lab, b.get("id"))

    missing: Dict[str, list[str]] = {}
    for b in blocks:
        deps = (b.get("dependencies") or {}).get("labels") or []
        for lab in deps:
            if lab not in by_label:
                missing.setdefault(lab, []).append(b.get("id", ""))

    missing_classified = []
    for lab, ids in sorted(missing.items()):
        decl = declared_labels.get(lab)
        missing_classified.append(
            {
                "label": lab,
                "referenced_by": ids,
                "declared": bool(decl),
                "declared_kind": (decl.get("kind") if isinstance(decl, dict) else None),
            }
        )

    diagnostics = {
        "schema_version": "paper-extract-check/v1",
        "input": str(in_json),
        "missing_labels": missing_classified,
        "counts": {
            "blocks": len(blocks),
            "unique_labels": len(by_label),
            "missing_labels": len(missing),
        },
        "ok": len(missing) == 0,
    }

    if out_diagnostics:
        out_diagnostics.parent.mkdir(parents=True, exist_ok=True)
        out_diagnostics.write_text(json.dumps(diagnostics, ensure_ascii=False, indent=2), encoding="utf-8")
    return diagnostics

