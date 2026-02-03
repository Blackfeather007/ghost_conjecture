# Blueprint to Proof Registry

This folder contains a CLI script that scans the LaTeX blueprint, extracts each declaration block, and maintains a JSON registry of declaration metadata. It also supports an update workflow that records formalized Lean statements and annotates the blueprint with `\lean{...}` and `\leanok`.

## What the script does

### 1) Parse blueprint `.tex` files
- Default blueprint directory: `GhostConjectureLean/blueprint/src/chapters` (configurable).
- Recursively scans for `.tex` files.
- Asserts that `\proves{...}` does not appear anywhere in the blueprint (proofs must follow statements directly).
- Parses **top‑level** LaTeX environments using a stack of `\begin{...}` / `\end{...}` tokens (comments are ignored).
- Treats any top‑level environment *other than* `proof` as a “statement block”.

### 2) Extract metadata from statement/proof blocks
For each statement block with a `\label{...}`:
- **Label**: extracted from the first `\label{...}` in the statement block.
- **Title**: extracted from `\begin{env}[Title]` if present.
- **Dependencies**:
  - `statement`: labels in `\uses{...}` found in the statement block.
  - `proof`: labels in `\uses{...}` found in the proof block.
- **LaTeX snippets**: raw LaTeX for the statement and its immediately following proof (if any).
- **Proof association**: if the next top‑level block is a `proof`, it is attached to the statement; otherwise, for theorem‑like envs the script warns about missing proofs.

### 3) Maintain a JSON registry
- Output JSON default: `output/blueprint_to_proof/blueprint_nodes.json` (configurable).
- If the JSON already exists, **fixed** fields (`dependencies`, `latex`, `env`, `title`, etc.) are refreshed from the blueprint while **mutable** fields (`status`, `lean`) are preserved.
- New nodes are added with default status values.

### 4) Update workflow for formalized statements
The script supports an **update** mode that:
- Marks `status.statement` as `formalized` in the JSON.
- Records:
  - `lean.file`: path to the Lean file **relative to the Lean root** (configurable).
  - `lean.name`: the fully qualified Lean name.
- Inserts or updates `\lean{...}` and `\leanok` inside the corresponding statement block in the blueprint file.
  - If either is missing, it is inserted just after `\uses{...}` (or `\label{...}` if no `\uses` line exists).

## JSON structure
Top level:
- `metadata`: `blueprint_dir`, `files`, `generated_at`, `script`, and `updated_at` (on update).
- `nodes`: map `label -> node`.

Each `node` contains:
- `label`, `env`, `title`
- `dependencies`: `{ statement: [...], proof: [...] }`
- `latex`: `{ statement: "...", proof: "..." }`
- `lean`: `{ file: <relative path or null>, name: <fq name or null> }`
- `status`: `{ statement: "todo"|"formalized", proof: "todo" }`
- `has_proof`
- `source`: `{ file: <tex path>, line: <line number> }`

## How to use

### Run Codex and update the registry
```bash
python pipeline/blueprint_to_proof/statement_formalize_run.py \
  --label def:fps_ring \
  --lean-root GhostConjectureLean
```

### Generate a statement formalization prompt (dry run)
```bash
python pipeline/blueprint_to_proof/statement_formalize_run.py \
  --label def:fps_ring \
  --lean-root GhostConjectureLean \
  --dry-run
```

Logs are written to `output/blueprint_to_proof/statement_formalization_log` with a filename based on the label and a timestamp.
The script feeds the populated prompt to `codex exec` via stdin. Override with `--codex-cmd` if needed; it expects a command list (e.g. `--codex-cmd codex exec --full-auto --json -C GhostConjectureLean`).
The command list is used exactly as provided.
The agent must return the final two lines in the exact `LEAN_FILE:` / `LEAN_NAME:` format specified in the prompt.

### Initialize or refresh the registry
```bash
python pipeline/blueprint_to_proof/blueprint_registry.py init \
  --blueprint-dir GhostConjectureLean/blueprint/src/chapters \
  --output output/blueprint_to_proof/blueprint_nodes.json
```

### Update a formalized statement
```bash
python pipeline/blueprint_to_proof/blueprint_registry.py update \
  --label def:fps_ring \
  --lean-file GhostConjectureLean/GhostConjecture/Basic.lean \
  --lean-name GhostConjecture.Basic.fpsRing \
  --lean-root GhostConjectureLean
```

Notes:
- `--lean-file` can be absolute or relative to `--lean-root`.
- The update will fail if the label is not present in the JSON; run `init` first.
- Proofs are assumed to be in the same Lean file as the statement, so only statement formalization is recorded.

## TODO
- `update` currently runs a full registry refresh after modifying the blueprint and JSON. This is intentional (not performance-critical), but we should document/optimize if needed.

## Warnings & errors
- If a theorem‑like statement is missing a proof block, the script prints a warning to stderr.
- A standalone `proof` block (no preceding statement) also triggers a warning.
- Any usage of `\proves{...}` causes a hard error.
