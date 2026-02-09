#!/usr/bin/env python3
from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import sys
from typing import Dict, List, Optional, Sequence, Tuple

import re

@dataclass(frozen=True)
class MacroDef:
    name: str
    nargs: int
    opt_default: Optional[str]
    replacement: str
    span_start: int
    span_end: int
    kind: str


class TexScanError(RuntimeError):
    pass


class Scanner:
    def __init__(self, text: str, *, start: int = 0, end: Optional[int] = None):
        self.text = text
        self.i = start
        self.end = len(text) if end is None else end

    def eof(self) -> bool:
        return self.i >= self.end

    def peek(self) -> str:
        if self.eof():
            return ""
        return self.text[self.i]

    def get(self) -> str:
        if self.eof():
            return ""
        ch = self.text[self.i]
        self.i += 1
        return ch

    def startswith(self, s: str) -> bool:
        return self.text.startswith(s, self.i, self.end)

    def skip_whitespace(self) -> None:
        while not self.eof() and self.peek() in " \t\r\n":
            self.i += 1

    def skip_comment_keep_newline(self) -> str:
        # Assumes current char is '%'
        start = self.i
        while not self.eof() and self.peek() != "\n":
            self.i += 1
        if not self.eof() and self.peek() == "\n":
            self.i += 1
        return self.text[start : self.i]

    def skip_comment_strip_newline(self) -> None:
        # Assumes current char is '%'
        while not self.eof() and self.peek() != "\n":
            self.i += 1
        if not self.eof() and self.peek() == "\n":
            self.i += 1

    def skip_spaces_and_comments_strip_newline(self) -> None:
        while True:
            self.skip_whitespace()
            if self.peek() == "%":
                self.skip_comment_strip_newline()
                continue
            return

    def read_control_sequence(self) -> Tuple[str, str, bool]:
        """
        Returns (name, token_text, is_control_word).
        - control word: letters/@ sequence (e.g. \\newcommand, \\rmP)
        - control symbol: single non-letter (e.g. \\%, \\{, \\_)
        """
        if self.peek() != "\\":
            raise TexScanError(f"expected backslash at {self.i}")
        start = self.i
        self.i += 1
        if self.eof():
            return "", self.text[start : self.i], False
        c = self.peek()
        if c.isalpha() or c == "@":
            j = self.i
            while not self.eof():
                d = self.peek()
                if d.isalpha() or d == "@":
                    self.i += 1
                else:
                    break
            name = self.text[j : self.i]
            return name, self.text[start : self.i], True
        self.i += 1
        return c, self.text[start : self.i], False

    def _read_balanced(
        self,
        open_ch: str,
        close_ch: str,
        *,
        strip_comments: bool,
        include_outer: bool,
    ) -> str:
        if self.peek() != open_ch:
            raise TexScanError(f"expected {open_ch!r} at {self.i}")
        out: List[str] = []
        if include_outer:
            out.append(self.get())
        else:
            self.i += 1
        depth = 1
        while not self.eof() and depth > 0:
            ch = self.peek()
            if ch == "\\":
                _, tok, _ = self.read_control_sequence()
                out.append(tok)
                continue
            if ch == "%" and strip_comments:
                self.skip_comment_strip_newline()
                continue
            if ch == open_ch:
                depth += 1
                out.append(self.get())
                continue
            if ch == close_ch:
                depth -= 1
                if depth == 0:
                    if include_outer:
                        out.append(self.get())
                    else:
                        self.i += 1
                    break
                out.append(self.get())
                continue
            out.append(self.get())
        if depth != 0:
            raise TexScanError(f"unbalanced {open_ch}{close_ch} starting near {self.i}")
        return "".join(out)

    def read_braced_group(self, *, strip_comments: bool, include_outer: bool = False) -> str:
        return self._read_balanced("{", "}", strip_comments=strip_comments, include_outer=include_outer)

    def read_bracket_group(self, *, strip_comments: bool, include_outer: bool = False) -> str:
        return self._read_balanced("[", "]", strip_comments=strip_comments, include_outer=include_outer)

    def read_argument(self) -> str:
        # Reads one TeX undelimited argument: {balanced} or a single token.
        if self.eof():
            raise TexScanError("unexpected EOF while reading argument")
        ch = self.peek()
        if ch == "{":
            return self.read_braced_group(strip_comments=False, include_outer=False)
        if ch == "\\":
            _, tok, _ = self.read_control_sequence()
            return tok
        return self.get()


def _parse_cs_name_from_group(group_content: str) -> str:
    s = group_content.strip()
    if not s.startswith("\\"):
        raise TexScanError(f"expected control sequence in group, got: {s!r}")
    sc = Scanner(s)
    name, _, _ = sc.read_control_sequence()
    if not name:
        raise TexScanError(f"empty control sequence in group: {s!r}")
    sc.skip_whitespace()
    if not sc.eof():
        raise TexScanError(f"unexpected trailing tokens in macro name group: {s!r}")
    return name


def _consume_optional_star(scanner: Scanner) -> bool:
    scanner.skip_spaces_and_comments_strip_newline()
    if scanner.peek() == "*":
        scanner.i += 1
        return True
    return False


def _consume_trailing_to_eol(scanner: Scanner) -> None:
    # Expand span to include trailing spaces and a single newline, if present.
    while not scanner.eof() and scanner.peek() in " \t\r":
        scanner.i += 1
    if not scanner.eof() and scanner.peek() == "\n":
        scanner.i += 1


def find_begin_document_index(text: str) -> int:
    s = Scanner(text)
    while not s.eof():
        ch = s.peek()
        if ch == "%":
            s.skip_comment_strip_newline()
            continue
        if ch != "\\":
            s.i += 1
            continue
        start = s.i
        name, _, _ = s.read_control_sequence()
        if name != "begin":
            continue
        saved = s.i
        s.skip_whitespace()
        if s.peek() == "{":
            grp = s.read_braced_group(strip_comments=True, include_outer=False)
            if grp.strip() == "document":
                return start
        s.i = saved
    raise TexScanError("could not find \\begin{document} outside comments")


def parse_preamble_macros(text: str, *, end_index: int) -> Dict[str, MacroDef]:
    s = Scanner(text, start=0, end=end_index)
    macros: Dict[str, MacroDef] = {}
    while not s.eof():
        ch = s.peek()
        if ch == "%":
            s.skip_comment_strip_newline()
            continue
        if ch != "\\":
            s.i += 1
            continue
        start = s.i
        name, _, _ = s.read_control_sequence()
        if name == "def":
            s.skip_spaces_and_comments_strip_newline()
            if s.peek() != "\\":
                raise TexScanError(f"expected macro name after \\def at {s.i}")
            macro_name, _, _ = s.read_control_sequence()

            # Read pure #1#2... parameter list (no delimiters supported)
            param_digits: List[int] = []
            while True:
                s.skip_spaces_and_comments_strip_newline()
                if s.peek() == "{":
                    break
                if s.peek() == "#":
                    s.i += 1
                    if s.eof() or not s.peek().isdigit():
                        raise TexScanError(f"expected digit after # in \\def for {macro_name} near {s.i}")
                    param_digits.append(int(s.get()))
                    continue
                if s.peek() in " \t\r\n":
                    s.i += 1
                    continue
                raise TexScanError(
                    f"unsupported delimited parameter text in \\def\\{macro_name} near {s.i}"
                )

            nargs = max(param_digits) if param_digits else 0
            if param_digits and param_digits != list(range(1, nargs + 1)):
                raise TexScanError(f"non-sequential parameters in \\def\\{macro_name}: {param_digits}")
            replacement = s.read_braced_group(strip_comments=True, include_outer=False)
            span_end_pos = s.i
            _consume_trailing_to_eol(s)
            md = MacroDef(
                name=macro_name,
                nargs=nargs,
                opt_default=None,
                replacement=replacement,
                span_start=start,
                span_end=s.i if s.i > span_end_pos else span_end_pos,
                kind="def",
            )
            macros[macro_name] = md
            continue

        if name in {"newcommand", "DeclareMathOperator"}:
            is_decl = name == "DeclareMathOperator"
            star = _consume_optional_star(s)
            s.skip_spaces_and_comments_strip_newline()

            # Macro name: either {\\Foo} or \\Foo
            if s.peek() == "{":
                grp = s.read_braced_group(strip_comments=True, include_outer=False)
                macro_name = _parse_cs_name_from_group(grp)
            elif s.peek() == "\\":
                macro_name, _, _ = s.read_control_sequence()
            else:
                raise TexScanError(f"expected macro name after \\{name} at {s.i}")

            if is_decl:
                s.skip_spaces_and_comments_strip_newline()
                if s.peek() != "{":
                    raise TexScanError(f"expected operator text group in \\DeclareMathOperator for {macro_name}")
                op_text = s.read_braced_group(strip_comments=True, include_outer=False)
                repl = f"\\operatorname{'*' if star else ''}{{{op_text}}}"
                span_end_pos = s.i
                _consume_trailing_to_eol(s)
                md = MacroDef(
                    name=macro_name,
                    nargs=0,
                    opt_default=None,
                    replacement=repl,
                    span_start=start,
                    span_end=s.i if s.i > span_end_pos else span_end_pos,
                    kind="DeclareMathOperator*"
                    if star
                    else "DeclareMathOperator",
                )
                macros[macro_name] = md
                continue

            # newcommand parsing
            nargs = 0
            opt_default: Optional[str] = None
            s.skip_spaces_and_comments_strip_newline()
            if s.peek() == "[":
                n_str = s.read_bracket_group(strip_comments=True, include_outer=False).strip()
                if not n_str.isdigit():
                    raise TexScanError(f"invalid argument count [{n_str!r}] in \\newcommand\\{macro_name}")
                nargs = int(n_str)
                s.skip_spaces_and_comments_strip_newline()
                if nargs > 0 and s.peek() == "[":
                    opt_default = s.read_bracket_group(strip_comments=True, include_outer=False)
            s.skip_spaces_and_comments_strip_newline()
            if s.peek() != "{":
                raise TexScanError(f"expected replacement group in \\newcommand\\{macro_name} at {s.i}")
            replacement = s.read_braced_group(strip_comments=True, include_outer=False)
            span_end_pos = s.i
            _consume_trailing_to_eol(s)
            md = MacroDef(
                name=macro_name,
                nargs=nargs,
                opt_default=opt_default,
                replacement=replacement,
                span_start=start,
                span_end=s.i if s.i > span_end_pos else span_end_pos,
                kind="newcommand*"
                if star
                else "newcommand",
            )
            macros[macro_name] = md
            continue

    return macros


def _substitute_params(replacement: str, args: Sequence[str]) -> str:
    out: List[str] = []
    i = 0
    n = len(replacement)
    while i < n:
        ch = replacement[i]
        if ch == "#":
            if i + 1 < n and replacement[i + 1] == "#":
                out.append("#")
                i += 2
                continue
            if i + 1 < n and replacement[i + 1].isdigit():
                k = int(replacement[i + 1])
                if k < 1 or k > len(args):
                    raise TexScanError(f"replacement refers to #{k} but only {len(args)} args provided")
                out.append(args[k - 1])
                i += 2
                continue
        out.append(ch)
        i += 1
    return "".join(out)


class MacroExpander:
    def __init__(self, macros: Dict[str, MacroDef], *, max_expansions: int):
        self.macros = macros
        self.max_expansions = max_expansions

    @dataclass
    class _Budget:
        remaining: int

        def consume(self) -> None:
            if self.remaining <= 0:
                raise TexScanError("expansion budget exhausted (possible recursion loop)")
            self.remaining -= 1

    def _expand_invocation(
        self, name: str, *, is_control_word: bool, scanner: Scanner, stack: List[str]
    ) -> str:
        budget = MacroExpander._Budget(self.max_expansions)
        return self._expand_invocation_with_budget(
            name, is_control_word=is_control_word, scanner=scanner, stack=stack, budget=budget
        )

    def _expand_invocation_with_budget(
        self,
        name: str,
        *,
        is_control_word: bool,
        scanner: Scanner,
        stack: List[str],
        budget: "MacroExpander._Budget",
    ) -> str:
        if name in stack:
            chain = " -> ".join(stack + [name])
            raise TexScanError(f"macro recursion detected: {chain}")
        md = self.macros[name]

        if is_control_word:
            # TeX ignores spaces following a control word.
            scanner.skip_whitespace()

        args: List[str] = []
        if md.opt_default is not None:
            scanner.skip_whitespace()
            if scanner.peek() == "[":
                arg0 = scanner.read_bracket_group(strip_comments=False, include_outer=False)
            else:
                arg0 = md.opt_default
            args.append(arg0)
            remaining = md.nargs - 1
        else:
            remaining = md.nargs

        for _ in range(remaining):
            scanner.skip_whitespace()
            args.append(scanner.read_argument())

        budget.consume()
        replaced = _substitute_params(md.replacement, args)
        stack.append(name)
        try:
            return self.expand_text(replaced, stack=stack, budget=budget)
        finally:
            stack.pop()

    def expand_text(
        self, text: str, *, stack: Optional[List[str]] = None, budget: Optional["_Budget"] = None
    ) -> str:
        if stack is None:
            stack = []
        s = Scanner(text)
        out: List[str] = []
        pending_script = False  # after '^' or '_' until first non-space token
        while not s.eof():
            ch = s.peek()
            if ch == "%":
                out.append(s.skip_comment_keep_newline())
                continue
            if pending_script and ch in " \t\r\n":
                out.append(s.get())
                continue
            if ch in "^_":
                pending_script = True
                out.append(s.get())
                continue
            if pending_script and ch == "{":
                pending_script = False
                out.append(s.get())
                continue
            if ch != "\\":
                if pending_script and ch not in " \t\r\n":
                    pending_script = False
                out.append(s.get())
                continue
            name, tok, is_word = s.read_control_sequence()
            if name in self.macros:
                if budget is None:
                    expanded = self._expand_invocation(name, is_control_word=is_word, scanner=s, stack=stack)
                else:
                    expanded = self._expand_invocation_with_budget(
                        name, is_control_word=is_word, scanner=s, stack=stack, budget=budget
                    )
                if re.search(r"\\[A-Za-z]*@[A-Za-z]", expanded):
                    grouped = "{\\makeatletter " + expanded + "\\makeatother}"
                else:
                    grouped = "{" + expanded + "}"
                out.append(grouped)
                if pending_script:
                    pending_script = False
            else:
                if pending_script:
                    pending_script = False
                out.append(tok)
        return "".join(out)


def _comment_block(block: str) -> str:
    lines = block.splitlines(True)
    return "".join(("%" + line) if line else "%" for line in lines)


def expand_file(
    text: str,
    macros: Dict[str, MacroDef],
    *,
    drop_defs: bool,
    comment_defs: bool,
    max_expansions: int,
) -> str:
    spans = sorted({(md.span_start, md.span_end) for md in macros.values()})
    expander = MacroExpander(macros, max_expansions=max_expansions)

    pieces: List[str] = []
    last = 0
    for start, end in spans:
        pieces.append(text[last:start])
        block = text[start:end]
        if comment_defs:
            pieces.append(_comment_block(block))
        elif not drop_defs:
            pieces.append(block)
        last = end
    pieces.append(text[last:])
    without_defs = "".join(pieces)
    return expander.expand_text(without_defs)


def _line_col_from_index(text: str, idx: int) -> Tuple[int, int]:
    # 1-based
    line = text.count("\n", 0, idx) + 1
    last_nl = text.rfind("\n", 0, idx)
    col = idx - last_nl
    return line, col


def find_remaining_macros(text: str, macro_names: Sequence[str]) -> Dict[str, List[Tuple[int, int]]]:
    names = set(macro_names)
    s = Scanner(text)
    found: Dict[str, List[Tuple[int, int]]] = {}
    while not s.eof():
        ch = s.peek()
        if ch == "%":
            s.skip_comment_strip_newline()
            continue
        if ch != "\\":
            s.i += 1
            continue
        start = s.i
        name, _, _ = s.read_control_sequence()
        if name in names:
            found.setdefault(name, []).append(_line_col_from_index(text, start))
    return found


def main(argv: Optional[Sequence[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Inline-expand \\def/\\newcommand/\\DeclareMathOperator macros in a TeX file.")
    p.add_argument("input", type=Path)
    p.add_argument("-o", "--output", type=Path, default=None)
    g = p.add_mutually_exclusive_group()
    g.add_argument("--drop-defs", action="store_true", help="Delete macro definition blocks (default).")
    g.add_argument("--comment-defs", action="store_true", help="Comment out macro definition blocks.")
    p.add_argument("--check", action="store_true", help="Fail if any collected macros remain in output (outside comments).")
    p.add_argument("--max-expansions", type=int, default=50, help="Maximum recursive macro expansions.")
    args = p.parse_args(argv)

    drop_defs = True
    comment_defs = False
    if args.comment_defs:
        drop_defs = False
        comment_defs = True
    if args.drop_defs:
        drop_defs = True
        comment_defs = False

    inp = args.input
    if not inp.exists():
        print(f"error: not found: {inp}", file=sys.stderr)
        return 2
    text = inp.read_text(encoding="utf-8", errors="ignore")
    begin_doc = find_begin_document_index(text)
    macros = parse_preamble_macros(text, end_index=begin_doc)

    if args.output is None:
        args.output = inp.with_name(f"{inp.stem}.expanded{inp.suffix}")

    expanded = expand_file(
        text,
        macros,
        drop_defs=drop_defs,
        comment_defs=comment_defs,
        max_expansions=args.max_expansions,
    )
    args.output.write_text(expanded, encoding="utf-8")

    if args.check:
        remaining = find_remaining_macros(expanded, sorted(macros.keys()))
        if remaining:
            print("error: some macros remain in output (outside comments):", file=sys.stderr)
            for name in sorted(remaining.keys()):
                locs = remaining[name][:10]
                loc_str = ", ".join(f"{ln}:{col}" for ln, col in locs)
                more = "" if len(remaining[name]) <= 10 else f" (+{len(remaining[name]) - 10} more)"
                print(f"  \\{name}: {loc_str}{more}", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
