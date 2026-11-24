import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeExpansionOverFinitePlacesStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace AlpogeRHCore35

theorem amplitudeExpansionOverFinitePlaces :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k),
      4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) →
      ∀ S1 : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S1 →
      ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ Q : Prop → Prop,
        G.amp d (fun Λ => Q (¬ G.Gen d Λ)) =
          κ * ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty),
            ∏ p ∈ S1,
              (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ)
               else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by exact GlobalTheory.T.amplitude_expansion_over_finite_places

end AlpogeRHCore35
