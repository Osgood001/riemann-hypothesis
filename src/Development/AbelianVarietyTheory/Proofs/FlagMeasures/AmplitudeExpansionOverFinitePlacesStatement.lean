module

public import Mathlib
public import Formalism.HermitianCurvature.DefectProducts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeExpansionOverFinitePlaces
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_expansion_over_finite_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ S1 : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S1 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ Q : Prop → Prop, G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = κ * ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty), ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ) else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
  exact @GlobalTheory.HL.DefectPhase.amp_sum_defect_sets

/-- The generic and nongeneric amplitudes are recovered from the all-good and total
products, with the same unit phase for every predicate on nongenericity. -/
theorem _root_.GlobalTheory.T.amplitude_products_over_finite_places :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k),
    4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) →
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S → ∃ κ : ℂ, ‖κ‖ = 1 ∧
    ∀ Q : Prop → Prop,
      let good := fun p => (G.S p).amp (d p) ((G.S p).BBzero (d p))
      let bad := fun p => (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ)
      G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = κ *
        ((if Q False then ∏ p ∈ S, good p else 0) +
         (if Q True then (∏ p ∈ S, (bad p + good p)) - ∏ p ∈ S, good p else 0)) := by
  intro F E _ _ _ _ _ sig A r k G hk d hd S hs
  obtain ⟨κ, hκ, h⟩ := GlobalTheory.T.amplitude_expansion_over_finite_places A r k G hk d hd S hs
  exact ⟨κ, hκ, fun Q => (h Q).trans (congrArg (κ * ·)
    (Formalism.HermitianLatticeCounting.DefectSum.filter_nonempty S _ _ Q))⟩
