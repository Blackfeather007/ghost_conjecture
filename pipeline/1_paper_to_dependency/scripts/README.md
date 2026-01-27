# `pipeline/1_paper_to_dependency/scripts`

This directory contains the LaTeX extraction tool used in stage “paper → dependency”.

## `extract_math_content.py` (v2)

Extracts three kinds of blocks from a LaTeX paper:

1. **Theorem-like environments** discovered from the root `.tex` preamble via `\newtheorem`
2. **Immediately following proofs** (`proof` environments) attached to theorem-like blocks
3. **Labeled equation blocks** (e.g. `equation`, `align`, `gather`, …) extracted as separate nodes and annotated with their parent context (statement vs proof)

It produces a single JSON file that your UI/agents can consume as a dependency graph substrate.

### Code layout

The CLI entrypoint is:

- `pipeline/1_paper_to_dependency/scripts/extract_math_content.py`

The implementation is split into small modules under:

- `pipeline/1_paper_to_dependency/scripts/paper_extract/`
  - `paper_extract/cli.py`: argument parsing + subcommands
  - `paper_extract/extractor.py`: extraction pipeline and JSON assembly
  - `paper_extract/preamble.py`: preamble scanning (`\\newtheorem`, packages/macros) and render context
  - `paper_extract/auxfile.py`: `.aux` parsing for numbering
  - `paper_extract/checker.py`: dependency-closure checking logic
  - `paper_extract/sections.py`: section/subsection state tracking
  - `paper_extract/util.py`: small helpers (comment stripping, stable ids, file reads)
  - `paper_extract/types.py`: small dataclasses (`TheoremEnv`, `AuxLabel`)

### Why v2 (what changed vs the old script)

- No hardcoded list of environments: theorem-like environments are discovered from `\newtheorem{...}` in the root file preamble.
- PDF-accurate numbering is supported by parsing a `.aux` file (default behavior if `<root>.aux` exists).
- Labeled equations are extracted as separate blocks and linked back to their containing theorem/proof.
- Per-block provenance is explicit (`location` and `origin` fields) even without resolving `\input`.
- A built-in checker validates that all referenced labels are present among extracted blocks.

## Usage

### Extract

```bash
python extract_math_content.py extract --root-tex data/arXiv-2206.15372v2.tex
```

By default this writes to:

- `pipeline/1_paper_to_dependency/output/<root_stem>.json`

and it will also use `data/arXiv-2206.15372v2.aux` if it exists (for numbering).

Override output path:

```bash
python extract_math_content.py extract \
  --root-tex data/arXiv-2206.15372v2.tex \
  --out-json output/arXiv-2206.15372v2.json
```

Override `.aux` path (or disable by passing a non-existent path):

```bash
python extract_math_content.py extract \
  --root-tex data/arXiv-2206.15372v2.tex \
  --aux data/arXiv-2206.15372v2.aux
```

### Check dependency closure

```bash
python extract_math_content.py check --in-json pipeline/1_paper_to_dependency/output/arXiv-2206.15372v2.json
```

By default, this only fails (exit code `2`) if **missing labels look like they should have been extracted**
(theorem-like or equation labels). Missing section/figure/etc labels are reported in diagnostics but are not fatal.

To fail on *any* missing label, use `--strict`:

```bash
python extract_math_content.py check \
  --in-json pipeline/1_paper_to_dependency/output/arXiv-2206.15372v2.json \
  --strict
```

To write a diagnostics JSON:

```bash
python extract_math_content.py check \
  --in-json pipeline/1_paper_to_dependency/output/arXiv-2206.15372v2.json \
  --out-diagnostics pipeline/1_paper_to_dependency/output/arXiv-2206.15372v2.diagnostics.json
```

## Implemented logic (high level)

### 1) Theorem-like environment discovery

- Reads the root `.tex` file preamble (up to `\begin{document}`).
- Scans for `\newtheorem{env}[shared]{Printed}[within]` and records:
  - `env` (environment name)
  - `printed_name` (human-facing name like “Lemma”, “Theorem”, …)
- The extractor then treats every `\begin{env}...\end{env}` as a statement block.

### 2) Proof attachment

After a theorem-like block ends, the extractor looks ahead to the next non-empty, non-comment line:

- If it is `\begin{proof}`, it extracts that proof environment and attaches it to the theorem block.
- Otherwise, no proof is attached.

### 3) Labeled equation extraction with parent context

Equation-like environments currently supported:

- `equation`, `align`, `alignat`, `gather`, `multline`, `flalign` (and `*` variants)

Extraction behavior:

- Any equation environment with at least one `\label{...}` is extracted as an `equation` block.
- If the equation occurs inside a theorem statement, it gets `parent.role = "statement"`.
- If it occurs inside an attached proof, it gets `parent.role = "proof"`.

### 4) Dependency extraction

Dependencies are extracted from each block’s LaTeX text by scanning ref-like commands:

- `\ref{...}`, `\eqref{...}`, `\cref{...}`, `\Cref{...}`, `\autoref{...}`

For `\cref`/`\Cref`, comma-separated lists inside the braces are supported.

### 5) Numbering (prefer `.aux`)

If a `.aux` file is provided (or `<root>.aux` exists), the extractor parses `\newlabel{...}` entries to populate:

- `block.display.number`
- `block.display.caption` (e.g. `Lemma 1.2.3`, `Equation (3.7)`)
- `block.display.number_source = "aux"`

If no `.aux` is available, numbering remains unset (`number_source = "none"`).

### 6) Provenance: `location` and `origin`

- `location`: where the block was extracted from (file + line span).
- `origin`: which logical source file “owns” the block going forward.
  - In v2 extraction, `origin.source_kind` starts as `"paper"` and `origin.source_tex` is the root `.tex`.
  - This is designed so later pipeline steps can move blocks into new `.tex` files (e.g. assumptions) without losing the original `location`.

### 7) Synthesized labels

If a theorem-like environment has no `\label{...}`, the extractor synthesizes one:

- `auto:<env>:<paper_id>:<filename>:<start_line>`

This enables stable UI linking even when the paper doesn’t label a result.

## Output JSON structure (summary)

Top level:

- `schema_version`, `paper_id`
- `source.root_tex`, `source.aux_file`
- `render.*` (preamble lines, packages, macro lines)
- `theorem_envs` (discovered theorem-like env metadata)
- `declared_labels` (all `\label{...}` seen in the root file, best-effort classified)
- `blocks[]` (all extracted nodes)
- `index.by_label`, `index.by_kind`

Each block contains:

- `id`, `kind`, `env`, `label`
- `display.*` (printed name + numbering if available)
- `location.*` and `origin.*`
- `dependencies.labels` and `dependencies.refs`
- `formalization.status` initialized to `"unformalized"`

## Current limitations / planned extensions

- Only scans the root `.tex` file (no `\input`/`\include` resolution yet).
- `.aux` parsing is best-effort; if a paper’s `.aux` uses a different `\newlabel` shape, the numbering may be missing.
- The “immediately following proof” policy is strict (it does not skip over intervening environments).
