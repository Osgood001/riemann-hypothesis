module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineIndex
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineIndexCoeffs
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineCoeffsFG
public import Mathlib.NumberTheory.NumberField.FractionalIdeal

@[expose] public section

open NumberField Module
open scoped nonZeroDivisors

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

/-- For a fractional ideal containing the integers, the relative additive index
is the norm of the inverse ideal. -/
private theorem index_eq_inverse_norm {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hI : 1 ≤ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (((algebraMap (𝓞 K) K).toAddMonoidHom.range.relIndex
       (I : Submodule (𝓞 K) K).toAddSubgroup : ℕ) : ℚ) =
    FractionalIdeal.absNorm (I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ).val := by
  classical
  let B := integralBasis K
  let e := Fintype.equivOfCardEq ((Module.finrank_eq_card_basis B).symm.trans
    (Module.finrank_eq_card_basis (basisOfFractionalIdeal K I)))
  let C := (basisOfFractionalIdeal K I).reindex e.symm
  have hle : (algebraMap (𝓞 K) K).toAddMonoidHom.range ≤ (I : Submodule (𝓞 K) K).toAddSubgroup :=
    fun x hx => hI ((FractionalIdeal.mem_one_iff _).mpr hx)
  have hB : (algebraMap (𝓞 K) K).toAddMonoidHom.range = AddSubgroup.closure (Set.range B) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    ext x
    exact (mem_span_integralBasis K).symm
  have hC : (I : Submodule (𝓞 K) K).toAddSubgroup = AddSubgroup.closure (Set.range C) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Module.Basis.range_reindex]
    ext x
    exact (mem_span_basisOfFractionalIdeal K).symm
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hle B C hB hC, Units.val_inv_eq_inv_val, map_inv₀]
  apply eq_inv_of_mul_eq_one_left
  rw [← det_basisOfFractionalIdeal_eq_absNorm K I e, ← abs_mul]
  change |C.det B * B.det C| = 1
  rw [Module.Basis.det_mul_det, Module.Basis.det_self, abs_one]

/-- The integral ideal is uniquely determined by the coefficient group: its inverse is the
fractional coefficient ideal. No rank or archimedean minimum is involved. -/
private theorem stable_overgroup_inverse_ideal {K : Type*} [Field K] [NumberField K]
    (A : AddSubgroup K) (hfg : A.FG) (hstable : ∀ b : 𝓞 K, ∀ x ∈ A, (b : K) * x ∈ A)
    (h1 : (1 : K) ∈ A) :
    ∃! J : Ideal (𝓞 K), J ≠ ⊥ ∧
      A = ((J : FractionalIdeal (𝓞 K)⁰ K)⁻¹).val.toAddSubgroup ∧
      (algebraMap (𝓞 K) K).toAddMonoidHom.range.relIndex A = Ideal.absNorm J := by
  let L : Submodule (𝓞 K) K :=
    { A.toAddSubmonoid with smul_mem' := fun b {_} => hstable b _ }
  have hf : L.FG := Submodule.FG.of_restrictScalars ℤ ((Submodule.fg_iff_addSubgroup_fg _).mpr hfg)
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨L, FractionalIdeal.isFractional_of_fg hf⟩
  have hO : 1 ≤ I := by
    intro x hx
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
    change (b : K) ∈ A
    simpa only [mul_one] using hstable b 1 h1
  have hI : I ≠ 0 := by
    intro h
    have h' : (1 : K) ∈ I := h1
    simp [h] at h'
  let U := Units.mk0 I hI
  have hle : I⁻¹ ≤ 1 := calc
    I⁻¹ = I⁻¹ * 1 := (mul_one _).symm
    _ ≤ I⁻¹ * I := by gcongr
    _ = 1 := inv_mul_cancel₀ hI
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hinv : (J : FractionalIdeal (𝓞 K)⁰ K)⁻¹ = I := by rw [hJ, inv_inv]
  have hrepr : A = ((J : FractionalIdeal (𝓞 K)⁰ K)⁻¹).val.toAddSubgroup := by
    rw [hinv]
  refine ⟨J, ⟨FractionalIdeal.coeIdeal_ne_zero.mp (hJ ▸ inv_ne_zero hI), hrepr, ?_⟩, ?_⟩
  · have hN := index_eq_inverse_norm U hO
    change ((algebraMap (𝓞 K) K).toAddMonoidHom.range.relIndex A : ℚ) =
      FractionalIdeal.absNorm I⁻¹ at hN
    rw [← hJ, FractionalIdeal.coeIdeal_absNorm] at hN
    exact_mod_cast hN
  · rintro J' ⟨_, hA', _⟩
    apply FractionalIdeal.coeIdeal_injective (K := K)
    apply inv_injective
    apply FractionalIdeal.coeToSubmodule_injective
    exact SetLike.ext fun x => Iff.of_eq <| congrArg (fun H : AddSubgroup K => x ∈ H) (hA'.symm.trans hrepr)

/-- Every nonzero vector of a lattice determines a unique integral denominator ideal.
Its absolute norm is precisely the line index. -/
theorem lineIndex_eq_ideal_norm {E W : Type*} [Field E] [NumberField E] [AddCommGroup W]
    [Module E W] (La : AddSubgroup W) (x : W) (hL : IsLattice E La) (hx : x ∈ La) (hx0 : x ≠ 0) :
    ∃! J : Ideal (𝓞 E), J ≠ ⊥ ∧
      lineCoeffs La x = ((J : FractionalIdeal (𝓞 E)⁰ E)⁻¹).val.toAddSubgroup ∧
      lineIndex E La x = Ideal.absNorm J := by
  rw [LineIndexCoeffs.proof E W La x hx0]
  apply stable_overgroup_inverse_ideal _ (LineCoeffsFG.proof (E := E) W La x hL.fg hx0)
  · intro b z hz
    change ((b : E) * z) • x ∈ La
    rw [mul_smul]
    exact hL.smul_mem b _ hz
  · change (1 : E) • x ∈ La
    simpa

/-- Conversely every nonzero integral ideal norm is attained by the line through one
in a rank-one lattice. This does not require one to be a shortest vector. -/
theorem exists_lineIndex_iff_ideal_norm {E : Type*} [Field E] [NumberField E] (n : ℕ) :
    (∃ La : AddSubgroup E, IsLattice E La ∧ (1 : E) ∈ La ∧ lineIndex E La 1 = n) ↔
    ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧ Ideal.absNorm J = n := by
  constructor
  · rintro ⟨La, hL, h1, rfl⟩
    obtain ⟨J, hJ, -⟩ := lineIndex_eq_ideal_norm La 1 hL h1 one_ne_zero
    exact ⟨J, hJ.1, hJ.2.2.symm⟩
  · rintro ⟨J, hJ, rfl⟩
    let F : FractionalIdeal (𝓞 E)⁰ E := J
    let I := F⁻¹
    let A := (I : Submodule (𝓞 E) E).toAddSubgroup
    have hf : F ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
    have hO : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ I := calc
      1 = F * I := (mul_inv_cancel₀ hf).symm
      _ ≤ 1 * I := by gcongr; exact FractionalIdeal.coeIdeal_le_one
      _ = I := one_mul _
    have h1 : (1 : E) ∈ A := hO (FractionalIdeal.one_mem_one _)
    have hL : IsLattice E A := by
      constructor
      · exact fun b _ h => (I : Submodule (𝓞 E) E).smul_mem b h
      · apply (Submodule.fg_iff_addSubgroup_fg ((I : Submodule (𝓞 E) E).restrictScalars ℤ)).mp
        apply Module.Finite.iff_fg.mp
        exact (inferInstance : Module.Finite ℤ I)
      · apply top_unique
        intro z _
        simpa using (Submodule.span E (A : Set E)).smul_mem z (Submodule.subset_span h1)
    have hc : lineCoeffs A (1 : E) = A := by ext z; change z • (1 : E) ∈ A ↔ z ∈ A; simp
    have he := index_eq_inverse_norm (Units.mk0 I (inv_ne_zero hf)) hO
    have hn : (intSubgroup E).relIndex A = Ideal.absNorm J := by
      change ((intSubgroup E).relIndex A : ℚ) = FractionalIdeal.absNorm (F⁻¹)⁻¹ at he
      rw [inv_inv, FractionalIdeal.coeIdeal_absNorm] at he
      exact_mod_cast he
    exact ⟨A, hL, h1, by rwa [LineIndexCoeffs.proof E E _ _ one_ne_zero, hc]⟩

theorem LineIndexNeZero.proof (E W : Type*) [Field E] [NumberField E] [AddCommGroup W]
    [Module E W] : LineIndexNeZero.Statement E W := by
  intro La x hL hx hx0
  obtain ⟨J, ⟨hJ, _, h⟩, _⟩ := lineIndex_eq_ideal_norm La x hL hx hx0
  exact h ▸ Ideal.absNorm_eq_zero_iff.not.mpr hJ

end GroundTheory.Heights₂.Heights.FiniteCovolume
