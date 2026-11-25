module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHeckeCharacterOfClassGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardOpenSubgroupLeKerInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConductorEqTopOfStandardOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteEmbeddingMemStandardOpenSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscrNormConductorEqDFOfUnramified
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootNumberEqDifferentCoeff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleSectionMemStandardOpenSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumAddCharOfMulMulOfMulInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationOfUnramified

@[expose] public section

noncomputable section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.CompanionTheory.PartialZeta
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {F : Type} [Field F] [NumberField F]

theorem coeff_inv_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (J : (Ideal (𝓞 F))⁰) :
    ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) = ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) := by
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have h1 := coeff_inv_mul_coeff F (classHecke ψ) (standardOpenSubgroup_le_ker ψ) J hJ
  rw [coeff_classHecke ψ J hJ] at h1
  have h2 : ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 J)) = 1 := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, inv_mul_cancel, ofMul_one, AddChar.map_zero_eq_one]
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)

def zetaOfClass (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).continuedLFunction s

def zetaOfClassInv (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).continuedLFunction s

theorem isPartialZeta_of_indicator {ι : Type} [Fintype ι] (χ : ι → HeckeCharacter F) (c : ι → ℂ)
    (C : ClassGroup (𝓞 F)) (hU : ∀ i, standardOpenSubgroup F ≤ (χ i).toIdele.ker)
    (horth : ∀ J : (Ideal (𝓞 F))⁰,
      (ClassGroup.mk0 J = C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 1) ∧
      (ClassGroup.mk0 J ≠ C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 0)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (fun s => ∑ i, c i * (χ i).continuedLFunction s) := by
  classical
  refine ⟨?_, fun s hs => ?_⟩
  · exact DifferentiableOn.fun_sum fun i _ => (differentiableOn_continuedLFunction F (χ i) (hU i)).const_mul (c i)
  · have h1 : HasSum (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)))
        (∑ i, c i * (χ i).continuedLFunction s) := by
      refine hasSum_sum fun i _ => ?_
      rw [(χ i).continuedLFunction_eq hs]
      exact ((χ i).hasSum_LFunction hs).mul_left (c i)
    have hfac : ∀ I : Ideal (𝓞 F),
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) =
          (∑ i, c i * (χ i).coeff I) * (Ideal.absNorm I : ℂ) ^ (-s) := fun I => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    let g : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} → Ideal (𝓞 F) :=
      fun J => (J.1 : Ideal (𝓞 F))
    have hg : Function.Injective g := fun a b hab =>
      Subtype.ext (Subtype.ext hab)
    have hsupp : ∀ I ∉ Set.range g,
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) = 0 := by
      intro I hI
      by_cases hbot : I = ⊥
      · subst hbot
        simp
      · let J : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hbot⟩
        have hJ : ClassGroup.mk0 J ≠ C := fun h => hI ⟨⟨J, h⟩, rfl⟩
        rw [hfac, show I = (J : Ideal (𝓞 F)) from rfl, (horth J).2 hJ, zero_mul]
    have h2 := (hg.hasSum_iff hsupp).2 h1
    have h3 : (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s))) ∘ g =
        fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
          ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s) := funext fun J => by
      simp only [Function.comp_apply]
      rw [hfac, show g J = (J.1 : Ideal (𝓞 F)) from rfl, (horth J.1).1 J.2, one_mul]
    rw [h3] at h2
    exact h2

theorem card_classGroup_ne_zero : (Fintype.card (ClassGroup (𝓞 F)) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem isPartialZeta_zetaOfClass (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClass C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => classHecke ψ) _ C (fun ψ => standardOpenSubgroup_le_ker ψ) fun J => ?_
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if ClassGroup.mk0 J = C then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_classHecke ψ J hJ]
    ring_nf
  rw [e]
  constructor
  · intro h
    rw [ite_eq_left h, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [ite_eq_right h, mul_zero]

theorem isPartialZeta_zetaOfClassInv (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClassInv C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => (classHecke ψ)⁻¹) _ C
    (fun ψ => standardOpenSubgroup_le_ker_inv F _ (standardOpenSubgroup_le_ker ψ)) fun J => ?_
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if C = ClassGroup.mk0 J then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_inv_classHecke ψ J, mul_assoc]
  rw [e]
  constructor
  · intro h
    rw [ite_eq_left h.symm, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [ite_eq_right (Ne.symm h), mul_zero]

theorem functionalEquation_classHecke [IsTotallyReal F] (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (D : (Ideal (𝓞 F))⁰) (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * (classHecke ψ).continuedLFunction s =
      ψ (Additive.ofMul (ClassGroup.mk0 D)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * ((classHecke ψ)⁻¹).continuedLFunction (1 - s)) := by
  have hU := standardOpenSubgroup_le_ker ψ
  have h := fe_of_parts F (classHecke ψ) (discrNormConductor_eq_dF_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ (standardOpenSubgroup_le_ker_inv F _ hU))
    (rootNumber_eq_coeff_different F _ hU) s h1 h2
  rw [← hD, coeff_classHecke ψ _ (nonZeroDivisors.coe_ne_zero D)] at h
  exact h

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

/-- The Tate-completed ideal-class partial zeta function, including the removable Gamma poles. -/
def completedZetaOfClass (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).completedLFunction s

private theorem classHecke_neg (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    classHecke (-ψ) = (classHecke ψ)⁻¹ := by
  ext x
  change (-ψ) _ = (((classCircle ψ (IdeleClassGroup.toClassGroup x))⁻¹ : Circle) : ℂ)
  rw [Circle.coe_inv, coe_classCircle, AddChar.neg_apply]
  exact AddChar.map_neg_eq_inv _ _

theorem completedZetaOfClass_eq (C : ClassGroup (𝓞 F)) {s : ℂ} (hs : classGamma F s ≠ 0) :
    completedZetaOfClass C s = (dF F : ℂ) ^ (s / 2) * classGamma F s * zetaOfClass C s := by
  rw [completedZetaOfClass, zetaOfClass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have hU := standardOpenSubgroup_le_ker ψ
  rw [(classHecke ψ).completedLFunction_eq_mul_continuedLFunction (by rwa [classGamma_eq _ hU]),
    classGamma_eq _ hU, discrNormConductor_eq_dF_of_unramified F _ hU]
  ring

private theorem classHecke_normPole (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) {τ : ℝ}
    (hτ : ∀ x : IdeleGroup F,
      ((classHecke ψ).toIdele x : ℂ) = ((ideleModule F x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)) :
    s ≠ -((τ : ℂ) * Complex.I) ∧ s ≠ 1 - (τ : ℂ) * Complex.I := by
  let w : InfinitePlace F := Classical.arbitrary _
  have hs : ∀ t : {x : ℝ // 0 < x}, (classHecke ψ).toIdele (moduleSection w t) = 1 :=
    fun t => MonoidHom.mem_ker.1 (standardOpenSubgroup_le_ker ψ (moduleSection_mem_standardOpenSubgroup w t))
  have h0 := archExponent_unique w (classHecke ψ) (τ := 0) (fun t => by simp [hs t])
  have hτ0 : τ = 0 := (archExponent_eq_of_forall hτ w).symm.trans h0
  simpa [hτ0] using And.intro hs0 hs1

theorem analyticAt_completedZetaOfClass (C : ClassGroup (𝓞 F)) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) : AnalyticAt ℂ (completedZetaOfClass C) s := by
  let U := {z : ℂ | z ≠ 0} ∩ {z : ℂ | z ≠ 1}
  have hU : IsOpen U := isOpen_ne.inter isOpen_ne
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds ⟨hs0, hs1⟩)
  apply DifferentiableOn.fun_sum
  intro ψ _
  apply DifferentiableOn.const_mul
  intro z hz
  by_cases h : ∃ τ : ℝ, ∀ x : IdeleGroup F,
      ((classHecke ψ).toIdele x : ℂ) = ((ideleModule F x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)
  · obtain ⟨τ, hτ⟩ := h
    obtain ⟨h0, h1⟩ := classHecke_normPole ψ hz.1 hz.2 hτ
    exact (HeckeCharacter.differentiableAt_completedLFunction_of_forall hτ h0 h1).differentiableWithinAt
  · exact ((classHecke ψ).differentiable_completedLFunction h).differentiableOn _ hz

theorem completedZetaOfClass_functionalEquation (C C' : ClassGroup (𝓞 F)) (D : (Ideal (𝓞 F))⁰)
    (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F)) (hC : C * C' = ClassGroup.mk0 D)
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedZetaOfClass C s = completedZetaOfClass C' (1 - s) := by
  classical
  unfold completedZetaOfClass
  refine Fintype.sum_equiv (Equiv.neg _) _ _ fun ψ => ?_
  have hU := standardOpenSubgroup_le_ker ψ
  have h := (classHecke ψ).completedLFunction_eq_rootNumber_mul (s := s)
    fun _ hτ => classHecke_normPole ψ hs0 hs1 hτ
  rw [rootNumber_eq_coeff_different F _ hU, ← hD, coeff_classHecke ψ _ (nonZeroDivisors.coe_ne_zero D)] at h
  have e : ψ (Additive.ofMul C⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 D)) = ψ (Additive.ofMul C') := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, ← hC, inv_mul_cancel_left]
  change _ = (_ * (-ψ) _) * (classHecke (-ψ)).completedLFunction (1 - s)
  rw [classHecke_neg, h]
  simp only [AddChar.neg_apply, ← ofMul_inv, inv_inv]
  rw [← e]
  ring

/-- The ideal-class functional equation with the archimedean factors of the actual signature. -/
theorem partialZetaFunctionalEquation_signature (C C' : ClassGroup (𝓞 F)) (D : (Ideal (𝓞 F))⁰)
    (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F)) (hC : C * C' = ClassGroup.mk0 D) :
    ∃ Z Z' : ℂ → ℂ, IsPartialZeta C Z ∧ IsPartialZeta C' Z' ∧
      ∀ s : ℂ, classGamma F s ≠ 0 → classGamma F (1 - s) ≠ 0 →
        (dF F : ℂ) ^ (s / 2) * classGamma F s * Z s =
          (dF F : ℂ) ^ ((1 - s) / 2) * classGamma F (1 - s) * Z' (1 - s) := by
  refine ⟨zetaOfClass C, zetaOfClass C', isPartialZeta_zetaOfClass C, isPartialZeta_zetaOfClass C',
    fun s hs ht => ?_⟩
  have h0 : s ≠ 0 := fun h => hs (h ▸ classGamma_zero F)
  have h1 : s ≠ 1 := by rintro rfl; simp [classGamma_zero] at ht
  rw [← completedZetaOfClass_eq C hs, ← completedZetaOfClass_eq C' ht]
  exact completedZetaOfClass_functionalEquation C C' D hD hC s h0 h1

theorem partialZetaFunctionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation := by
  intro F _ _ _ C C' D hD hC
  obtain ⟨Z, Z', hZ, hZ', h⟩ := partialZetaFunctionalEquation_signature C C' D hD hC
  refine ⟨Z, Z', hZ, hZ', fun s hs ht => ?_⟩
  have nz (t : ℂ) (h : ∀ n : ℕ, t ≠ -2 * n) : classGamma F t ≠ 0 := by
    rw [classGamma_of_totallyReal]
    apply pow_ne_zero
    intro h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
    exact h n (by simpa using hn)
  simpa only [classGamma_of_totallyReal] using h s (nz s hs) (nz (1 - s) ht)

end GlobalTheory.CompanionTheory.Hypotheses₂
