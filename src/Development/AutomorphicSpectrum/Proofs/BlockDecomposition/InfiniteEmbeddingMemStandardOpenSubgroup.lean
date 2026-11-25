module

public import Mathlib
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation

@[expose] public section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem infiniteEmbedding_mem_standardOpenSubgroup {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ standardOpenSubgroup F := by
  refine (mem_standardOpenSubgroup F).2 fun v ↦ ?_
  have h1 : ((infiniteEmbedding w a : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [coe_infiniteEmbedding]
    rfl
  have h2 : (((infiniteEmbedding w a)⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [← map_inv, coe_infiniteEmbedding]
    rfl
  rw [h1, h2]
  exact ⟨one_mem _, one_mem _⟩

theorem infiniteParams_eq_zero {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (hχ : standardOpenSubgroup F ≤ χ.toIdele.ker) (w : InfinitePlace F) :
    χ.infiniteParams w = (0, 0) := by
  refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
  have h : χ.toIdele (infiniteEmbedding w a) = 1 :=
    hχ (infiniteEmbedding_mem_standardOpenSubgroup w a)
  simp [HeckeCharacter.infiniteComponent_apply, h]

open NumberField.InfinitePlace

/-- The archimedean factor for ordinary ideal classes of any number field. -/
noncomputable def classGamma (F : Type*) [Field F] [NumberField F] (s : ℂ) : ℂ :=
  Complex.Gammaℝ s ^ nrRealPlaces F * Complex.Gammaℂ s ^ nrComplexPlaces F

variable {F : Type*} [Field F] [NumberField F]

theorem classGamma_eq (χ : HeckeCharacter F) (hχ : standardOpenSubgroup F ≤ χ.toIdele.ker)
    (s : ℂ) : χ.gammaFactor s = classGamma F s := by
  classical
  rw [HeckeCharacter.gammaFactor, InfinitePlace.prod_eq_prod_mul_prod]
  have h (w : InfinitePlace F) : χ.infiniteGamma w s =
      if w.IsReal then Complex.Gammaℝ s else Complex.Gammaℂ s := by
    simp [HeckeCharacter.infiniteGamma, HeckeCharacter.infiniteWeight, HeckeCharacter.infiniteTau,
      infiniteParams_eq_zero χ hχ w]
  simp_rw [h]
  have hr (w : {w : InfinitePlace F // w.IsReal}) :
      (if w.val.IsReal then Complex.Gammaℝ s else Complex.Gammaℂ s) = Complex.Gammaℝ s :=
    ite_eq_left w.property
  have hc (w : {w : InfinitePlace F // w.IsComplex}) :
      (if w.val.IsReal then Complex.Gammaℝ s else Complex.Gammaℂ s) = Complex.Gammaℂ s :=
    ite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr w.property)
  simp_rw [hr, hc]
  simp [classGamma, nrRealPlaces, nrComplexPlaces]

theorem classGamma_of_totallyReal [IsTotallyReal F] (s : ℂ) :
    classGamma F s = Complex.Gammaℝ s ^ Module.finrank ℚ F := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank F
  simpa [classGamma, IsTotallyReal.nrComplexPlaces_eq_zero] using
    congrArg (fun n : ℕ => Complex.Gammaℝ s ^ n) h

theorem classGamma_zero (F : Type*) [Field F] [NumberField F] : classGamma F 0 = 0 := by
  have hr : Complex.Gammaℝ 0 = 0 := Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by norm_num⟩
  have hc : Complex.Gammaℂ 0 = 0 := by simp [Complex.Gammaℂ]
  have h := InfinitePlace.card_add_two_mul_card_eq_rank F
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  by_cases hr0 : nrRealPlaces F = 0
  · have hc0 : nrComplexPlaces F ≠ 0 := by omega
    simp [classGamma, hr, hc, hr0, hc0]
  · simp [classGamma, hr, hr0]

theorem gammaFactor_eq_of_unramified : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (χ : HeckeCharacter F), standardOpenSubgroup F ≤ χ.toIdele.ker →
    ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F := by
  intro F _ _ _ χ hχ s
  rw [classGamma_eq χ hχ, classGamma_of_totallyReal]

end GlobalTheory.CompanionTheory.PartialZeta
