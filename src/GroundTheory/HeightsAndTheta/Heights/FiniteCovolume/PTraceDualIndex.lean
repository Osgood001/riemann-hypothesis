module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StTraceHermNondegenerate
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordLatticeFullRank

@[expose] public section

open Module

namespace Submodule

variable {R V : Type*} [CommRing R] [IsDedekindDomain R] [AddCommGroup V]
    [Module R V] [Module.IsTorsionFree R V]

private theorem finrank_ideal_smul (I : Ideal R) (hI : I ≠ ⊥) (X : Submodule R V) :
    finrank R (I • X : Submodule R V) = finrank R X := by
  obtain ⟨r, hr, hr0⟩ := exists_mem_ne_zero_of_ne_bot hI
  apply congrArg Cardinal.toNat
  exact (rank_mono smul_le_right).antisymm (rank_le_of_isSMulRegular X (I • X)
    (.of_ne_zero hr0) fun _ hx => smul_mem_smul hr hx)

private theorem relIndex_prime_smul (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (X : Submodule R V) (hX : X.FG) :
    (p • X).toAddSubgroup.relIndex X.toAddSubgroup = p.absNorm ^ finrank R X := by
  have : Module.Finite R X := .of_fg hX
  let k : (R ⧸ p) ≃ₐ[R] p.ResidueField := AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField) p.bijective_algebraMap_quotient_residueField
  let q := quotEquivOfEq ((p • X).comap X.subtype) (p • (⊤ : Submodule R X))
    (map_injective_of_injective X.injective_subtype (by simp [smul_le_right]))
  let e : (X ⧸ (p • X).comap X.subtype) ≃ₗ[R] p.Fiber X :=
    (q.trans (TensorProduct.quotTensorEquivQuotSMul X p).symm).trans (k.toLinearEquiv.rTensor X)
  change Nat.card (X ⧸ (p • X).comap X.subtype) = _
  rw [Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := p.ResidueField),
    p.finrank_fiber_eq_finrank, ← Nat.card_congr k.toEquiv, Ideal.absNorm_of_ne_bot hp, cardQuot_apply]

/-- Twisting a finite torsion-free lattice by a nonzero ideal has relative index equal
    to the ideal norm to the lattice rank. No freeness or principal ideal is needed. -/
theorem relIndex_ideal_smul (I : Ideal R) (hI : I ≠ ⊥) (X : Submodule R V) (hX : X.FG) :
    (I • X).toAddSubgroup.relIndex X.toAddSubgroup = I.absNorm ^ finrank R X := by
  revert X
  revert hI
  refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
  · intro h
    exact absurd zero_eq_bot h
  · intro J hJ _ X _
    rw [Ideal.isUnit_iff.mp hJ, top_smul, Ideal.absNorm_top, one_pow, AddSubgroup.relIndex_self]
  · intro J p hJ hp ih _ X hX
    have : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    rw [mul_smul, ← AddSubgroup.relIndex_mul_relIndex (p • J • X).toAddSubgroup
      (J • X).toAddSubgroup X.toAddSubgroup smul_le_right smul_le_right,
      relIndex_prime_smul p hp.ne_zero (J • X) (FG.smul (IsNoetherian.noetherian J) hX),
      finrank_ideal_smul J hJ X, ih hJ X hX, _root_.map_mul, mul_pow]

end Submodule

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped nonZeroDivisors

noncomputable section

private def testModule {E Q I : Type*} [Field E] [NumberField E] [AddCommGroup Q]
    [Module E Q] [Module (𝓞 E) Q] [IsScalarTower (𝓞 E) E Q]
    (f : I → Q →ₗ[E] E) (J : Submodule (𝓞 E) E) : Submodule (𝓞 E) Q :=
  ⨅ i, J.comap ((f i).restrictScalars (𝓞 E))

private theorem mem_testModule {E Q I : Type*} [Field E] [NumberField E] [AddCommGroup Q]
    [Module E Q] [Module (𝓞 E) Q] [IsScalarTower (𝓞 E) E Q]
    (f : I → Q →ₗ[E] E) (J : Submodule (𝓞 E) E) (q : Q) :
    q ∈ testModule f J ↔ ∀ i, f i q ∈ J := by simp [testModule]

/-- Integral-valued tests are the different times codifferent-valued tests, even on
nonprincipal lattices: multiplication by the inverse fractional ideal cancels exactly. -/
private theorem different_smul_traceTests {E Q I : Type*} [Field E] [NumberField E]
    [AddCommGroup Q] [Module E Q] [Module (𝓞 E) Q] [IsScalarTower (𝓞 E) E Q]
    (f : I → Q →ₗ[E] E) :
    differentIdeal ℤ (𝓞 E) • testModule f (Submodule.traceDual ℤ ℚ 1) = testModule f 1 := by
  let D := differentIdeal ℤ (𝓞 E)
  let C := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)
  have eC : C.coeToSubmodule = Submodule.traceDual ℤ ℚ 1 :=
    FractionalIdeal.coeToSubmodule_dual_one _ _ _ _
  have eDC : IsLocalization.coeSubmodule E D * C.coeToSubmodule = 1 := by
    rw [← FractionalIdeal.coeToSubmodule_coeIdeal (S := (𝓞 E)⁰), ← FractionalIdeal.coeToSubmodule_mul]
    have e : (D : FractionalIdeal (𝓞 E)⁰ E) = C⁻¹ := coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
    rw [e, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero), FractionalIdeal.coeToSubmodule_one]
  have hmul (A J : Submodule (𝓞 E) E) : A • testModule f J ≤ testModule f (A * J) := by
    apply Submodule.smul_le.mpr
    intro r hr q hq
    apply (mem_testModule _ _ _).mpr
    intro i
    rw [map_smul, smul_eq_mul]
    exact Submodule.mul_mem_mul hr ((mem_testModule _ _ _).mp hq i)
  have scale (N : Submodule (𝓞 E) Q) : D • N = IsLocalization.coeSubmodule E D • N := by
    apply le_antisymm
    · exact Submodule.smul_le.mpr fun r hr q hq =>
        (IsScalarTower.algebraMap_smul E r q) ▸
          Submodule.smul_mem_smul ((IsLocalization.mem_coeSubmodule E D).mpr ⟨r, hr, rfl⟩) hq
    · apply Submodule.smul_le.mpr
      rintro _ ⟨r, hr, rfl⟩ q hq
      change algebraMap (𝓞 E) E r • q ∈ D • N
      rw [IsScalarTower.algebraMap_smul]
      exact Submodule.smul_mem_smul hr hq
  change D • _ = _
  rw [← eC, scale]
  apply le_antisymm
  · exact eDC ▸ hmul (IsLocalization.coeSubmodule E D) C.coeToSubmodule
  · calc
      testModule f 1 = ((IsLocalization.coeSubmodule E D * C.coeToSubmodule) • testModule f 1) := by
        rw [eDC, Submodule.one_smul]
      _ = IsLocalization.coeSubmodule E D • (C.coeToSubmodule • testModule f 1) :=
        Submodule.smul_assoc _ _ _
      _ ≤ _ := Submodule.smul_mono le_rfl (by simpa using hmul C.coeToSubmodule 1)

/-- The Hermitian dual is the different times the rational trace dual.
This uses only stability under the ring of integers, not a basis of the lattice over it. -/
theorem exists_different_smul_traceDual_eq_dualLattice
    {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {W : Type*} [AddCommGroup W] [Module E W]
    {ι : Type*} [Fintype ι] (h : HermitianForm F E W) (v : Module.Basis ι E W)
    (La : AddSubgroup W) (hLa : IsLattice E La) :
    let φ := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
    ∃ B : Submodule (𝓞 E) (ι → E),
      B.toAddSubgroup = ((traceHerm h v).dualSubmodule (La.map φ).toIntSubmodule).toAddSubgroup ∧
      (differentIdeal ℤ (𝓞 E) • B).toAddSubgroup = (dualLattice h La).map φ := by
  let φ := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
  have hφ : ∀ x, v.equivFun.symm (φ x) = x := v.equivFun.symm_apply_apply
  let f : La → (ι → E) →ₗ[E] E := fun x => (h.toSesq x).comp v.equivFun.symm.toLinearMap
  have hf (x : La) (q : ι → E) : f x q = h.toSesq x (v.equivFun.symm q) := rfl
  let J := Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)
  refine ⟨testModule f J, ?_, ?_⟩
  · ext q
    have trsymm (x y : W) : Algebra.trace ℚ E (h.toSesq x y) = Algebra.trace ℚ E (h.toSesq y x) := by
      rw [← h.conj_toSesq x y]
      exact (Algebra.trace_eq_of_algEquiv (conj F E).toRingEquiv.toRatAlgEquiv _).symm
    have trtest : q ∈ (traceHerm h v).dualSubmodule (La.map φ).toIntSubmodule ↔
        ∀ x : La, Algebra.trace ℚ E (f x q) ∈ (1 : Submodule ℤ ℚ) := by
      constructor
      · intro hq x
        rw [hf, trsymm]
        have hm := hq (φ x) (AddSubgroup.mem_map_of_mem φ x.2)
        rwa [traceHerm_apply, hφ] at hm
      · rintro hq _ ⟨x, hx, rfl⟩
        rw [traceHerm_apply, hφ, trsymm]
        exact hq ⟨x, hx⟩
    change q ∈ testModule f J ↔ q ∈ (traceHerm h v).dualSubmodule (La.map φ).toIntSubmodule
    rw [trtest, mem_testModule]
    constructor
    · intro hh x
      have hm := Submodule.mem_traceDual.mp (hh x) 1 (show (1 : E) ∈ (1 : Submodule (𝓞 E) E) by simp)
      simpa [Algebra.traceForm_apply, Submodule.mem_one] using hm
    · intro hh x
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨a, rfl⟩ := Submodule.mem_one.mp ha
      let a' : 𝓞 E := ⟨conj F E a, a.2.map (conj F E).toRingEquiv.toRatAlgEquiv⟩
      have hm := hh ⟨(a' : E) • x.1, hLa.smul_mem a' _ x.2⟩
      rw [hf, Submodule.mem_one] at hm
      change ∃ n : ℤ, algebraMap ℤ ℚ n = Algebra.trace ℚ E (h.toSesq ((a' : E) • x.1) _) at hm
      rw [LinearMap.map_smulₛₗ₂, smul_eq_mul] at hm
      have hconj : conjHom F E (a' : E) = (a : E) := by
        change conj F E (conj F E (a : E)) = (a : E)
        rw [conj_conj]
      rw [hconj] at hm
      change ∃ n : ℤ, algebraMap ℤ ℚ n =
        Algebra.trace ℚ E (h.toSesq x (v.equivFun.symm q) * (a : E))
      rw [mul_comm _ (a : E)]
      exact hm
  · rw [different_smul_traceTests]
    have im (z : E) : z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z :=
      Submodule.mem_one.trans ⟨fun ⟨a, e⟩ => e ▸ a.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
    have flip (x y : W) (hx : IsIntegral ℤ (h.toSesq x y)) : IsIntegral ℤ (h.toSesq y x) := by
      rw [← h.conj_toSesq]
      exact hx.map (conj F E).toRingEquiv.toRatAlgEquiv
    ext q
    change q ∈ testModule f 1 ↔ q ∈ (dualLattice h La).map φ
    rw [mem_testModule]
    constructor
    · intro hq
      refine ⟨v.equivFun.symm q, fun x hx => ?_, v.equivFun.apply_symm_apply _⟩
      exact (mem_integralClosure_iff ℤ E).mpr (flip _ _ ((im _).mp (hq ⟨x, hx⟩)))
    · rintro ⟨y, hy, rfl⟩ x
      rw [hf, hφ, im]
      exact flip _ _ ((mem_integralClosure_iff ℤ E).mp (hy x x.2))

/-- The trace dual has exactly one field-discriminant factor per coordinate
relative to the Hermitian dual. No choice of basis of the integral lattice is involved. -/
theorem traceHerm_relIndex_eq {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {W : Type*} [AddCommGroup W] [Module E W]
    {ι : Type*} [Fintype ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hT : (traceHerm h v).Nondegenerate) (hf : CoordLatticeFullRank.Statement v)
    (La : AddSubgroup W) (hLa : IsLattice E La) (hint : IsIntegralOn h La) :
    let L := La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
    let T := (traceHerm h v).dualSubmodule L.toIntSubmodule
    L.toIntSubmodule ≤ T ∧ L.relIndex T.toAddSubgroup =
      La.relIndex (dualLattice h La) * (NumberField.discr E).natAbs ^ Fintype.card ι := by
  classical
  let φ := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
  let L := La.map φ
  let H := (dualLattice h La).map φ
  let T := (traceHerm h v).dualSubmodule L.toIntSubmodule
  let d := differentIdeal ℤ (𝓞 E)
  obtain ⟨B, hB, hd⟩ := exists_different_smul_traceDual_eq_dualLattice h v La hLa
  change B.toAddSubgroup = T.toAddSubgroup at hB
  change (d • B).toAddSubgroup = H at hd
  obtain ⟨hfg, hspan⟩ := hf La hLa
  have hlh : L ≤ H := AddSubgroup.map_mono (fun y hy x hx => hint y hy x hx)
  have hhb : H ≤ B.toAddSubgroup := by rw [← hd]; exact Submodule.smul_le_right
  have hlb : L ≤ B.toAddSubgroup := hlh.trans hhb
  have hQ : Submodule.span ℚ (B : Set (ι → E)) = ⊤ :=
    top_unique (hspan.ge.trans (Submodule.span_mono hlb))
  have hE : Submodule.span E (B : Set (ι → E)) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℚ, hQ]
    simp
  have : Module.IsTorsionFree ℤ (ι → E) := .trans_faithfulSMul ℤ ℚ _
  have : Module.Finite ℤ L.toIntSubmodule :=
    Module.Finite.iff_fg.mpr ((Submodule.fg_iff_addSubgroup_fg _).mpr hfg)
  have : Module.Finite ℤ T := Module.Finite.of_injective ((traceHerm h v).dualSubmoduleToDual _)
    ((traceHerm h v).dualSubmoduleToDual_injective hT _ hspan)
  have hfgB : B.FG := by
    have : (B.restrictScalars ℤ).FG := by
      rw [Submodule.fg_iff_addSubgroup_fg]
      change B.toAddSubgroup.FG
      rw [hB]
      exact (Submodule.fg_iff_addSubgroup_fg T).mp (Module.Finite.iff_fg.mp ‹Module.Finite ℤ T›)
    have : Module.Finite ℤ B := Module.Finite.of_fg this
    exact Module.Finite.iff_fg.mp (Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) B)
  have : Module.IsTorsionFree (𝓞 E) (ι → E) := .trans_faithfulSMul (𝓞 E) E _
  have : Submodule.IsLattice E B := Submodule.IsLattice.of_fg E hfgB
  have hi := Submodule.relIndex_ideal_smul d differentIdeal_ne_bot B hfgB
  rw [← Submodule.IsLattice.finrank_span_eq_finrank E B, hE, finrank_top, finrank_fintype_fun_eq_card] at hi
  rw [show Ideal.absNorm d = (NumberField.discr E).natAbs from NumberField.absNorm_differentIdeal E (𝓞 E)] at hi
  refine ⟨?_, ?_⟩
  · change L ≤ T.toAddSubgroup
    rwa [← hB]
  · change L.relIndex T.toAddSubgroup = _
    rw [← hB, ← AddSubgroup.relIndex_mul_relIndex L H B.toAddSubgroup hlh hhb,
      AddSubgroup.relIndex_map_map_of_injective La (dualLattice h La) v.equivFun.injective,
      ← hd, hi]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
