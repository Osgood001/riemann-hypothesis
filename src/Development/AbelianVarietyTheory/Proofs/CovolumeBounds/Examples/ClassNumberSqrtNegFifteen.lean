module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PrimitiveIdealEuler
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr

/-! In ℚ(√−15), the distinct kernel-reduced ideals of norm two represent a single
nontrivial class. The full Minkowski sum drops from three reduced ideals to two
represented classes. The collision is local: two principal ideals of norm six have
the same norm-three factor, so their norm-two factors have the same class. -/

@[expose] public section
noncomputable section

open NumberField Module Finset GlobalTheory
open scoped NumberField Real nonZeroDivisors

namespace NumberField.SqrtNegFifteen

/-- Removing the unique common norm-b factor from two distinct principal ideals of
coprime product norm gives distinct norm-a ideals representing the same class. -/
private theorem exists_distinct_norm_eq_same_class_of_principal_products {K : Type*} [Field K] [NumberField K]
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b)
    (hcount : {I : Ideal (𝓞 K) | I.absNorm = b}.ncard = 1) {A B : Ideal (𝓞 K)}
    (hA : A.absNorm = a * b) (hB : B.absNorm = a * b) (hne : A ≠ B)
    (hApr : A.IsPrincipal) (hBpr : B.IsPrincipal) :
    ∃ P Q : (Ideal (𝓞 K))⁰, P ≠ Q ∧ (P : Ideal (𝓞 K)).absNorm = a ∧
      (Q : Ideal (𝓞 K)).absNorm = a ∧ ClassGroup.mk0 P = ClassGroup.mk0 Q := by
  obtain ⟨R, hR⟩ := Set.ncard_eq_one.mp hcount
  have uniq (I : Ideal (𝓞 K)) : I.absNorm = b ↔ I = R := Set.ext_iff.mp hR I
  have nz {I : Ideal (𝓞 K)} {n : ℕ} (hn : n ≠ 0) (hI : I.absNorm = n) : I ∈ (Ideal (𝓞 K))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hn (by simpa [h] using hI.symm)
  let R' : (Ideal (𝓞 K))⁰ := ⟨R, nz hb ((uniq R).mpr rfl)⟩
  have split {L : Ideal (𝓞 K)} (hL : L.absNorm = a * b) :
      ∃ P : (Ideal (𝓞 K))⁰, (P : Ideal (𝓞 K)).absNorm = a ∧ (P : Ideal (𝓞 K)) * R = L := by
    obtain ⟨⟨P, T⟩, h⟩ := (scalarFreeFibreMulEquiv (K := K) ∅ (by simp) hab).surjective ⟨L, hL, by simp⟩
    have heq := congrArg Subtype.val h
    rw [scalarFreeFibreMulEquiv_apply, (uniq T).mp T.2.1] at heq
    exact ⟨⟨P, nz ha P.2.1⟩, P.2.1, heq⟩
  have prod {P : (Ideal (𝓞 K))⁰} {L : Ideal (𝓞 K)} (hd : (P : Ideal (𝓞 K)) * R = L)
      (hL : L.IsPrincipal) : ClassGroup.mk0 P * ClassGroup.mk0 R' = 1 := by
    rw [← map_mul, ClassGroup.mk0_eq_one_iff]
    change ((P : Ideal (𝓞 K)) * R).IsPrincipal
    rwa [hd]
  obtain ⟨P, hP, hp⟩ := split hA
  obtain ⟨Q, hQ, hq⟩ := split hB
  exact ⟨P, Q, fun h => hne (hp.symm.trans (h ▸ hq)), hP, hQ,
    mul_right_cancel ((prod hp hApr).trans (prod hq hBpr).symm)⟩

abbrev K := QuadraticAlgebra ℚ ((-4 : ℤ) : ℚ) ((1 : ℤ) : ℚ)
private abbrev O := QuadraticAlgebra ℤ (-4) 1

instance : Fact (¬ IsSquare (QuadraticAlgebra.discr ((-4 : ℤ) : ℚ) ((1 : ℤ) : ℚ))) := by
  refine ⟨fun ⟨z, hz⟩ => ?_⟩
  norm_num [QuadraticAlgebra.discr_def] at hz
  nlinarith [sq_nonneg z]

instance : NumberField K := NumberField.of_module_finite ℚ _

private theorem fundamental : Int.IsFundamentalDiscr (QuadraticAlgebra.discr (-4 : ℤ) 1) := by
  rw [Int.isFundamentalDiscr_iff_squarefree]
  norm_num [QuadraticAlgebra.discr_def, ← Int.squarefree_natAbs]
  exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 5)).mpr
    ⟨(by decide : Nat.Prime 3).squarefree, (by decide : Nat.Prime 5).squarefree⟩

private def model : O ≃ₐ[ℤ] 𝓞 K := QuadraticAlgebra.Int.algEquivIntegralClosure fundamental

private theorem discr_K : NumberField.discr K = -15 := by
  let B := QuadraticAlgebra.basis (-4 : ℤ) 1
  rw [← NumberField.discr_eq_discr _ (B.map model.toLinearEquiv)]
  change Algebra.discr ℤ (model ∘ B) = _
  rw [← Algebra.discr_eq_discr_of_algEquiv]
  exact (Algebra.discr_quadraticAlgebra (a := (-4 : ℤ)) (b := 1)).trans (by norm_num [QuadraticAlgebra.discr_def])

private theorem norm_form (x y : ℤ) : Algebra.norm ℤ (model ⟨x,y⟩) = x^2 + x*y + 4*y^2 := by
  rw [Algebra.norm_eq_of_algEquiv model, Algebra.norm_quadraticAlgebra_apply]
  change x*x + 1*x*y - (-4)*y*y = _
  ring

private theorem no_principal_norm_two {I : Ideal (𝓞 K)} (hI : I.absNorm = 2) : ¬I.IsPrincipal := by
  rintro ⟨v, hv⟩
  obtain ⟨⟨x,y⟩, rfl⟩ := model.surjective v
  rw [hv, Ideal.absNorm_span_singleton, norm_form] at hI
  have hpos : 0 ≤ x^2+x*y+4*y^2 := by nlinarith [sq_nonneg (2*x+y), sq_nonneg y]
  have h2 : x^2+x*y+4*y^2 = 2 := by have := Int.natAbs_of_nonneg hpos; omega
  have hmod : ∀ a b : ZMod 3, a^2+a*b+4*b^2 ≠ 2 := by decide
  exact hmod x y (by simpa using congrArg (Int.castRingHom (ZMod 3)) h2)

/-- The conjugate elements 2−ω and 1+ω both have norm six. Reduction modulo
(2,ω) kills the first but not the second, so they generate different ideals. -/
private theorem distinct_principal_norm_six :
    ∃ a b : 𝓞 K, (Ideal.span {a}).absNorm = 2 * 3 ∧
    (Ideal.span {b}).absNorm = 2 * 3 ∧ Ideal.span {a} ≠ Ideal.span {b} := by
  let a : 𝓞 K := model ⟨2,-1⟩
  let b : 𝓞 K := model ⟨1,1⟩
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rw [Ideal.absNorm_span_singleton, norm_form]
    decide
  · rw [Ideal.absNorm_span_singleton, norm_form]
    decide
  · let φ : O →ₐ[ℤ] ZMod 2 := QuadraticAlgebra.lift ⟨0, by decide⟩
    let ψ := φ.toRingHom.comp model.symm.toRingHom
    have ha : ψ a = 0 := by norm_num [ψ, φ, a, QuadraticAlgebra.lift]; decide
    have hb : ψ b = 1 := by norm_num [ψ, φ, b, QuadraticAlgebra.lift]
    intro h
    have hmem : b ∈ Ideal.span {a} := h ▸ Ideal.mem_span_singleton_self b
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
    have hh := congrArg ψ hc
    rw [map_mul, ha, hb, zero_mul] at hh
    exact one_ne_zero hh

open GlobalTheory.QuadraticZeta

private theorem norm_counts :
    {I : Ideal (𝓞 K) | I.absNorm = 2}.ncard = 2 ∧ {I : Ideal (𝓞 K) | I.absNorm = 3}.ncard = 1 := by
  have h1 : idealCount K 1 = 1 := by simp [idealCount, Ideal.absNorm_eq_one_iff]
  have hp (p : ℕ) (h : p.Prime) : (idealCount K p : ℤ) = 1 + kroneckerAt (-15) p := by
    have hc := idealCount_prime_mul (K := K) (QuadraticAlgebra.finrank_eq_two _ _) h 1
    rw [discr_K, h1] at hc
    simpa [h.not_dvd_one] using hc
  have h2 : kroneckerAt (-15) 2 = 1 := by norm_num [kroneckerAt]; decide +kernel
  have h3 : kroneckerAt (-15) 3 = 0 := by decide +kernel
  change idealCount K 2 = 2 ∧ idealCount K 3 = 1
  have := hp 2 Nat.prime_two
  have := hp 3 (by decide)
  omega

local notation "idClass" => MonoidHom.id (ClassGroup (𝓞 K))

private theorem reduced_of_norm_two {I : (Ideal (𝓞 K))⁰} (hI : (I : Ideal (𝓞 K)).absNorm = 2) :
    (I : Ideal (𝓞 K)) ∈ kernelReducedFibre idClass 2 := by
  refine ⟨hI, fun J hJ hd => ?_⟩
  have hirr := Ideal.irreducible_of_irreducible_absNorm (hI ▸ Nat.prime_two.prime.irreducible)
  rcases hirr.dvd_iff.mp hd with hu | ha
  · exact (Ideal.isUnit_iff.mp hu).trans Ideal.one_eq_top.symm
  · have heq : I = J := Subtype.ext (associated_iff_eq.mp ha)
    exact (no_principal_norm_two hI ((ClassGroup.mk0_eq_one_iff I.prop).mp (heq ▸ hJ))).elim

/-- At norm two both distinct reduced ideals represent the same nontrivial class. -/
theorem norm_two_collision :
    ∃ P Q : (Ideal (𝓞 K))⁰, (P : Ideal (𝓞 K)) ≠ Q ∧
      kernelReducedFibre idClass 2 = {(P : Ideal (𝓞 K)), (Q : Ideal (𝓞 K))} ∧
      ClassGroup.mk0 P = ClassGroup.mk0 Q ∧ ClassGroup.mk0 P ≠ 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := distinct_principal_norm_six
  obtain ⟨P, Q, hne, hp, hq, heq⟩ := exists_distinct_norm_eq_same_class_of_principal_products
    (by decide : 2 ≠ 0) (by decide : 3 ≠ 0) (by decide) norm_counts.2 ha hb hab ⟨a, rfl⟩ ⟨b, rfl⟩
  have hpq : (P : Ideal (𝓞 K)) ≠ Q := fun h => hne (Subtype.ext h)
  refine ⟨P, Q, hpq, ?_, heq, fun h => no_principal_norm_two hp ((ClassGroup.mk0_eq_one_iff P.prop).mp h)⟩
  have hfin := Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 K) 2
  have hsub : kernelReducedFibre idClass 2 ⊆ {I : Ideal (𝓞 K) | I.absNorm = 2} := fun _ h => h.1
  symm
  refine Set.eq_of_subset_of_ncard_le (Set.insert_subset (reduced_of_norm_two hp)
    (Set.singleton_subset_iff.mpr (reduced_of_norm_two hq))) ?_ (hfin.subset hsub)
  rw [Set.ncard_pair hpq]
  exact (Set.ncard_le_ncard hsub hfin).trans_eq norm_counts.1

private theorem reduced_one : kernelReducedFibre idClass 1 = {1} := by
  ext I
  constructor
  · intro h
    exact (Ideal.absNorm_eq_one_iff.mp h.1).trans Ideal.one_eq_top.symm
  · rintro rfl
    exact ⟨map_one _, fun J _ hJ => (Ideal.isUnit_iff.mp (isUnit_of_dvd_unit hJ isUnit_one)).trans Ideal.one_eq_top.symm⟩

private theorem minkowski_floor : ⌊minkowskiBound K⌋₊ = 2 := by
  have hK := QuadraticAlgebra.finrank_eq_two ((-4 : ℤ) : ℚ) ((1 : ℤ) : ℚ)
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by
    have h := NumberField.sign_discr K
    have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [discr_K] at h
    rw [hK] at hr
    by_contra! hn
    have hz : InfinitePlace.nrComplexPlaces K = 0 := by omega
    rw [hz] at h
    exact absurd h (by decide)
  apply (Nat.floor_eq_iff' (by decide : 2 ≠ 0)).mpr
  rw [minkowskiBound, hc, hK, discr_K]
  norm_num
  have hs : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have hu := Real.pi_lt_d2
  have hl := Real.pi_gt_three
  constructor <;> field_simp
  · nlinarith [Real.sqrt_nonneg 15, sq_nonneg (Real.sqrt 15 - 3.5)]
  · nlinarith [Real.sqrt_nonneg 15, sq_nonneg (Real.sqrt 15 - 4)]

/-- The original reduced-ideal sum is three. Counting their actual images gives two. -/
theorem exact_sieve_scores :
    (∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, (kernelReducedFibre idClass n).ncard) = 3 ∧
    (∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, (reducedClassImages idClass n).ncard) = 2 := by
  obtain ⟨P, Q, hne, hred, heq, _⟩ := norm_two_collision
  have hp : Subtype.val ⁻¹' kernelReducedFibre idClass 2 = ({P, Q} : Set (Ideal (𝓞 K))⁰) := by
    ext I
    simp only [Set.mem_preimage, hred, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
  have hone : Subtype.val ⁻¹' kernelReducedFibre idClass 1 = ({1} : Set (Ideal (𝓞 K))⁰) := by
    ext I
    simp only [Set.mem_preimage, reduced_one, Set.mem_singleton_iff, Subtype.ext_iff, OneMemClass.coe_one]
  rw [minkowski_floor, show Ioc 0 2 = {1,2} by decide]
  simp only [Finset.sum_insert (by decide : 1 ∉ ({2} : Finset ℕ)), Finset.sum_singleton]
  constructor
  · rw [reduced_one, hred, Set.ncard_singleton, Set.ncard_pair hne]
  · unfold reducedClassImages
    rw [hone, hp]
    simp [heq]

theorem class_number : classNumber K = 2 := by
  refine Nat.le_antisymm ((card_le_sum_reducedClassImages idClass Function.surjective_id).trans_eq exact_sieve_scores.2) ?_
  obtain ⟨P, _, _, _, _, hP⟩ := norm_two_collision
  have : Nontrivial (ClassGroup (𝓞 K)) := ⟨ClassGroup.mk0 P, 1, hP⟩
  exact Fintype.one_lt_card

end NumberField.SqrtNegFifteen
