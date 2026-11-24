# Contributing to `Osgood001/riemann-hypothesis`

Welcome! This fork is an open community collaboration hub for simplifying, refactoring, porting, and auditing the Lean 4 formalization of the Riemann Hypothesis & GRH (`149,097` active `v4.36.0` `.lean` files under `src/`, derived from Levent Alpöge's `175,187`-file / `980.4M`-character release).

> **Important:** Always open PRs against **`Osgood001/riemann-hypothesis`** (not upstream `leanprover-community/riemann-hypothesis` unless you are specifically targeting upstream).

---

## Two Ways to Contribute

### Track A — Direct GitHub Pull Requests (Recommended for `src/` & the 98%+ Uncovered Engine)

The 13 modular Playground Core Pillars (`Core 1–13`) currently cover **`1,938` deduplicated files (`1.11%` of files / `1.69%` of characters)**. Over **98.3% of the proof engine** is open for direct simplification, dead-code pruning, Mathlib reuse, and new modular pillar extractions!

High-impact uncovered module families in `src/` (by file count on `main`):

| Module Family in `src/` | Active `.lean` Files | Current Pillar Coverage |
|---|---:|---|
| `src/Development/AbelianVarietyTheory/` | ~81,500 | Uncovered (Phase 3 target) |
| `src/Development/AutomorphicArithmetic/` | 17,522 | Uncovered (Phase 3 target) |
| `src/Development/AutomorphicSpectrum/` | 13,629 | Partial (`Core 8`) |
| `src/Development/WeilBound/` | 6,797 | Partial (`Core 8`) |
| `src/Formalism/LocalToGlobal/` | 4,895 | Partial (`Core 6`, `Core 9`) |
| `src/GroundTheory/HeightsAndTheta/` | 4,878 | Partial (`Core 7`, `Core 11`) |
| `src/Formalism/PeriodIntegrals/` | 3,369 | Partial (`Core 3`, `Core 9`) |
| `src/Formalism/SharpRestriction/` | 2,757 | Partial (`Core 12`) |
| `src/ReciprocityTheory/ReductiveGroups/` | 2,660 | Partial (`Core 6`, `Core 7`) |
| `src/Formalism/HermitianCurvature/` | 1,796 | Partial (`Core 13`) |
| `src/Development/EtaleCohomology/` | 1,307 | Uncovered |
| `src/CompanionTheory/SpectralGeometry/` | 1,237 | Uncovered |

You can contribute directly on GitHub by:
1. **Simplifying or deleting unused/redundant modules in `src/`** while keeping `Main` & `Challenge` signatures invariant.
2. **Porting a staged Playground breakthrough** from Draft PRs `#2–#14` (`community/core<N>-attempt-<id>/`, standalone Lean `v4.34.1`) into `src/` (Lean `v4.36.0` `module` / `public import` / `@[expose] public section` / `autoImplicit = false`).
3. **Proposing a new self-contained sub-theorem / Phase 3 pillar extraction** with clean Mathlib or minimal frozen interfaces.

### Track B — Agentic Science Playground CLI (Automated Lean 4 + Comparator Scoring)

Prefer instant automated scoring on `Core 1–13` or the full Grand Challenge without setting up a huge local Lean build?
```bash
curl -fsSL https://play.bohrium.com/install.sh | bash
```
- Browse all 14 live challenges in [`README.md`](README.md) or on the [Live Progress Board](https://riemann.verifytask.cn/).
- Top verified (`0 sorry`, standard axioms only) Playground breakthroughs are automatically mirrored here as attributed Draft PRs via our sync automation (`playground/core<N>-attempt-<id>`).

---

## Local Setup & Workflow

### 1. Fork & Clone (Sparse Checkout Recommended for Targeted Edits)

Full checkouts contain `149,097` `.lean` files. If you are working on a specific subtree (e.g., `src/Formalism/SharpRestriction/`), a blobless partial clone is much faster:

```bash
git clone --filter=blob:none https://github.com/<your-user>/riemann-hypothesis.git
cd riemann-hypothesis
git remote add fork-origin https://github.com/Osgood001/riemann-hypothesis.git
```

### 2. Fetch Prebuilt `.olean` Cache & Build Your Target

```bash
# Restore Mathlib + project cache from the public community cache
lake exe cache get

# Build only the module(s) you modified (avoid rebuilding all 149k files)
lake build Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement
```

> **Toolchain Note:**
> - `Osgood001/riemann-hypothesis:main` uses **`leanprover/lean4:v4.36.0`** (`module` system, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`).
> - Playground `Core 1–13` run **`leanprover/lean4:v4.34.1`** with standalone `import Mathlib`.
> - The Playground full-RH Grand Challenge baseline runs **`leanprover/lean4:v4.33.1`**.

### 3. Run Local Static & Strict Warning Checks Before Opening a PR

1. **Zero-compilation static check & `TOKEN_RE` delta** (same script run by GitHub CI):
   ```bash
   python3 scripts/pr_lightweight_checks.py --base origin/main --head HEAD
   ```
   This verifies:
   - `0 sorry`, `0 admit`, `0 sorryAx`, and `0` custom `axiom` declarations across all modified/added `.lean` files.
   - Exact Playground-compatible `TOKEN_RE` normalized token delta (comments and `import` lines stripped).
   - `lean-toolchain` and `lake-manifest.json` remain untouched (unless labeled `allow-toolchain-change`).

2. **Strict per-file warning check** (do **not** add `warningAsError = true` to `lakefile.toml`, as that invalidates the entire 149k-module build cache):
   ```bash
   lake env lean -j1 --tstack=400000 \
     -DautoImplicit=false -DrelaxedAutoImplicit=false \
     -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true \
     -DmaxHeartbeats=4000000 -DwarningAsError=true \
     src/Path/To/ModifiedFile.lean
   ```

3. **Axiom audit** (only `propext`, `Classical.choice`, and `Quot.sound` are permitted):
   ```bash
   printf 'import Path.To.ModifiedFile\n#print axioms TargetTheorem\n' | lake env lean -j1 --stdin
   ```

---

## Pull Request Review & Verification Pipeline

1. **Automatic Lightweight CI (`.github/workflows/pr-lightweight-checks.yml`, ~12s on `ubuntu-latest`)**:
   - Runs automatically on every PR (`opened`, `synchronize`, `reopened`).
   - Checks `sorry`/`admit`/`sorryAx`/custom `axiom`, `lean-toolchain`/`lake-manifest.json` integrity, and posts a sticky `TOKEN_RE` compression summary comment.
2. **Maintainer-Gated Bohrium Sandbox Lean Verification (`.github/workflows/bohrium-verify.yml`)**:
   - For security against untrusted fork PRs and zero unwanted Actions billing, heavy Lean compilation / Comparator runs are **never** triggered automatically.
   - After inspecting a PR commit, a maintainer posts:
     ```text
     /verify <head_sha> [--profile=core-lean4341-c8m32|rh-lean4360-c8m32|rh-lean4360-c32m128] [--no-comparator]
     ```
   - The workflow pins the exact SHA (TOCTOU-proof), extracts validated `.lean` blobs from a bare git store, runs `lake build` + `-DwarningAsError=true` + `#print axioms` + optional Comparator inside an air-gapped zero-token Bohrium Sandbox, deletes the sandbox in `finally`, and posts the sanitized verdict back to the PR.
3. **Hard Requirements for Merge**:
   - `0 sorry`, `0 admit`, `0` custom axioms (`propext`, `Classical.choice`, `Quot.sound` only).
   - Do not modify `src/Challenge.lean`, `comparator.json`, `export-targets.txt`, `lean-toolchain`, or `lake-manifest.json` without maintainer approval.
   - For Playground-mirrored Draft PRs under `community/`: merging into `src/` requires explicit author confirmation, open-source licensing clearance, and `v4.36.0` interface porting.

---

## Community & Support

- **Live Progress & Proof Techniques Board:** <https://riemann.verifytask.cn/>
- **Discord Community:** <https://discord.gg/dUeUNEY5pc> (`#rh-proof-techniques`, `#playground-support`)
- **Updates on X:** <https://x.com/osgood001>
