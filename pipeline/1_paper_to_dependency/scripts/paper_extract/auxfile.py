from __future__ import annotations

import re
from pathlib import Path

from .types import AuxLabel


_RE_NEWLABEL = re.compile(r"\\newlabel\{([^}]+)\}\{\{([^}]*)\}\{([^}]*)\}.*\}")


def parse_aux(path: Path | None) -> dict[str, AuxLabel]:
    """Parse a LaTeX .aux file to map label -> displayed number (best-effort)."""
    mapping: dict[str, AuxLabel] = {}
    if not path or not path.exists():
        return mapping

    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = _RE_NEWLABEL.search(raw)
        if not m:
            continue
        label = m.group(1).strip()
        number = m.group(2).strip()
        page = m.group(3).strip() if m.group(3).strip() else None
        mapping[label] = AuxLabel(number=number, page=page)
    return mapping

