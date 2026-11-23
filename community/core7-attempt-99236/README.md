# Core Pillar 7/13 — Connectedness of Zariski Basic Opens of Irreducible Complex Varieties (Playground Attempt #99236)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Andrew Pullin** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Andrew Pullin` |
| **Playground Challenge** | [Core 7/13 — Irreducible Complex Open Connected](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-7-connectedness-ec7f9c89) |
| **Module Family** | `GroundTheory/HeightsAndTheta + ReciprocityTheory/ReductiveGroups` |
| **Attempt ID** | `#99236` |
| **Playground Score** | `73.68` |
| **Normalized Tokens (`TOKEN_RE`)** | `12,156` vs baseline `765,918` (**-98.41%**, `63.01×` smaller) |
| **Characters / Lines / Files** | `40,346` chars vs `2,881,907` (**-98.60%**) · `725` lines · `1` `.lean` file(s) vs `584` baseline files |
| **Frozen Challenge Definitions** | 0 (pure 3-line Mathlib statement) |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `The Council` / `pi` |
| **Included Proof File(s)** | `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore7.irreducibleBasicOpenConnected :
    ∀ (σ : Type) [Fintype σ] (W : Ideal (MvPolynomial σ ℂ)) (g : MvPolynomial σ ℂ),
      W.IsPrime → g ∉ W →
      IsPreconnected (MvPolynomial.zeroLocus ℂ W \ {x : σ → ℂ | MvPolynomial.eval x g = 0})
```

### Proof Simplification Highlights
Refactors the core argument around Mathlib lemma(s) continuous_eval, single_le_sum; driven by `simp, linarith, nlinarith`.

## Corresponding Target Modules in `src/`

- `src/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PIrreducibleBasicOpenConnected.lean` (`GroundTheory.Heights₂.Heights.HilbertSamuel.IrreducibleBasicOpenConnected.proof`)

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core7-attempt-99236/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 7/13)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib` (+ challenge def imports if any), Playground namespace (`AlpogeRHCore7`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Zero frozen definitions — clean pure-Mathlib statement directly matching `PIrreducibleBasicOpenConnected.lean` (collapsing 584 transitive baseline files!).
- Replace `import Mathlib` with targeted `public import` headers under Lean `v4.36.0` `module` / `@[expose] public section` and `autoImplicit = false`.
- Check whether any downstream `GroundTheory/HeightsAndTheta/` or `ReciprocityTheory/ReductiveGroups/` modules import intermediate lemmas from the 584-file closure before pruning them.
