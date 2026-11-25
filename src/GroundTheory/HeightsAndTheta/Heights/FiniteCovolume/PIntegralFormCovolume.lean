module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StIntegralFormCovolume

@[expose] public section

open Module

namespace AddSubgroup

theorem relIndex_dvd_pow_of_zsmul_mem {Q : Type*} [AddCommGroup Q] (H B : AddSubgroup Q)
    [Free ℤ B.toIntSubmodule] [Module.Finite ℤ B.toIntSubmodule] (k : ℤ)
    (h : ∀ y ∈ B, k • y ∈ H) : H.relIndex B ∣ k.natAbs ^ finrank ℤ B := by
  let A := B.map (nsmulAddMonoidHom (α := Q) k.natAbs)
  have hAB : A.relIndex B = k.natAbs ^ finrank ℤ B := relIndex_map_nsmul _ _
  have hAH : A ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    change k.natAbs • y ∈ H
    have hm := h y hy
    cases k with
    | ofNat n => simpa using hm
    | negSucc n => simpa using H.neg_mem hm
  rw [← hAB]
  exact relIndex_dvd_of_le_left B hAH

end AddSubgroup

namespace LinearMap.BilinForm

/-- A multiple of the trace-dual landing in any subgroup bounds the relative index of that subgroup. -/
theorem relIndex_dual_dvd_pow_of_zsmul_mem {Q : Type*} [AddCommGroup Q] [Module ℚ Q]
    [FiniteDimensional ℚ Q] (T : LinearMap.BilinForm ℚ Q) (hT : T.Nondegenerate) (L H : AddSubgroup Q)
    (hfg : L.FG) (hspan : Submodule.span ℚ (L : Set Q) = ⊤) (k : ℤ)
    (h : ∀ y ∈ T.dualSubmodule L.toIntSubmodule, k • y ∈ H) :
    H.relIndex (T.dualSubmodule L.toIntSubmodule).toAddSubgroup ∣ k.natAbs ^ finrank ℚ Q := by
  classical
  let B := T.dualSubmodule L.toIntSubmodule
  have : Module.IsTorsionFree ℤ Q := .trans_faithfulSMul ℤ ℚ Q
  have : Module.Finite ℤ L.toIntSubmodule :=
    Module.Finite.iff_fg.mpr ((Submodule.fg_iff_addSubgroup_fg _).mpr hfg)
  have : Module.Finite ℤ B := Module.Finite.of_injective (T.dualSubmoduleToDual _)
    (T.dualSubmoduleToDual_injective hT _ hspan)
  let b := Free.chooseBasis ℤ B
  have hr : finrank ℤ B ≤ finrank ℚ Q := by
    rw [finrank_eq_card_basis b]
    exact ((LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (b.linearIndependent.map' B.subtype B.ker_subtype)).fintype_card_le_finrank
  exact (@AddSubgroup.relIndex_dvd_pow_of_zsmul_mem Q _ H B.toAddSubgroup
    (inferInstanceAs (Free ℤ B)) (inferInstanceAs (Module.Finite ℤ B)) k h).trans
    (pow_dvd_pow _ hr)

theorem relIndex_dual_le_pow_of_zsmul_mem {Q : Type*} [AddCommGroup Q] [Module ℚ Q]
    [FiniteDimensional ℚ Q] (T : LinearMap.BilinForm ℚ Q) (hT : T.Nondegenerate) (L H : AddSubgroup Q)
    (hfg : L.FG) (hspan : Submodule.span ℚ (L : Set Q) = ⊤) (k : ℤ) (hk : k ≠ 0)
    (h : ∀ y ∈ T.dualSubmodule L.toIntSubmodule, k • y ∈ H) :
    H.relIndex (T.dualSubmodule L.toIntSubmodule).toAddSubgroup ≤ k.natAbs ^ finrank ℚ Q :=
  Nat.le_of_dvd (pow_pos (Int.natAbs_pos.mpr hk) _)
    (T.relIndex_dual_dvd_pow_of_zsmul_mem hT L H hfg hspan k h)

end LinearMap.BilinForm

open Module Matrix
namespace LinearMap.BilinForm

theorem relIndex_dual_eq_abs_det {Q ι : Type*} [AddCommGroup Q] [Module ℚ Q]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ Q) (T : LinearMap.BilinForm ℚ Q) (hT : T.Nondegenerate)
    (L : Submodule ℤ Q) (hb : L = Submodule.span ℤ (Set.range b)) (integral : L ≤ T.dualSubmodule L) :
    (L.toAddSubgroup.relIndex (T.dualSubmodule L).toAddSubgroup : ℚ) = |(toMatrix b T).det| := by
  classical
  let d := T.dualBasis hT b
  have h := AddSubgroup.relIndex_eq_abs_det L.toAddSubgroup (T.dualSubmodule L).toAddSubgroup integral b d
  have h₁ : L.toAddSubgroup = AddSubgroup.closure (Set.range b) := by
    apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure]
    exact hb
  have h₂ : (T.dualSubmodule L).toAddSubgroup = AddSubgroup.closure (Set.range d) := by
    apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure]
    change T.dualSubmodule L = _
    rw [hb, T.dualSubmodule_span_of_basis hT]
  rw [h h₁ h₂, Basis.det_apply]
  have e : d.toMatrix b = (toMatrix b T)ᵀ := by
    ext i j
    simp [d, Basis.toMatrix_apply, toMatrix_apply, T.dualBasis_repr_apply]
  rw [e, det_transpose]

end LinearMap.BilinForm

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory Matrix

noncomputable section

variable (Q V K : Type*) [AddCommGroup Q] [Module ℚ Q] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype K]

/-- In fixed real coordinates and Haar normalization, the squared covolume of a full
integral rational lattice is proportional to its index in the bilinear dual. -/
theorem IntegralFormCovolume.index_formula (ψ : Q →+ V) (e : Basis K ℚ Q)
    (T : LinearMap.BilinForm ℚ Q) (μ : Measure V)
    (hμ : μ.IsAddHaarMeasure) (hT : T.Nondegenerate)
    (hli : LinearIndependent ℝ (fun k => ψ (e k))) (hrank : finrank ℝ V = Fintype.card K) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : AddSubgroup Q, L.FG → Submodule.span ℚ (L : Set Q) = ⊤ →
      L.toIntSubmodule ≤ T.dualSubmodule L.toIntSubmodule →
      ∃ _ : DiscreteTopology (AddSubgroup.toIntSubmodule (L.map ψ)),
        IsZLattice ℝ (AddSubgroup.toIntSubmodule (L.map ψ)) ∧
        ZLattice.covolume (AddSubgroup.toIntSubmodule (L.map ψ)) μ ^ 2 =
          C * (L.relIndex (T.dualSubmodule L.toIntSubmodule).toAddSubgroup : ℝ) := by
  classical
  have : FiniteDimensional ℚ Q := Module.Finite.of_basis e
  have hQ : finrank ℚ Q = Fintype.card K := finrank_eq_card_basis e
  let b₀ : Basis K ℝ V := basisOfLinearIndependentOfCardEqFinrank' _ hli hrank.symm
  have hb₀ : ∀ i, b₀ i = ψ (e i) := fun i => by simp [b₀]
  have hGe : (LinearMap.BilinForm.toMatrix e T).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e).1 hT
  have := hμ
  have hvol : 0 < μ.real (ZSpan.fundamentalDomain b₀) := by
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr (ZSpan.measure_fundamentalDomain_ne_zero b₀),
      (ZSpan.fundamentalDomain_isBounded b₀).measure_lt_top⟩
  refine ⟨μ.real (ZSpan.fundamentalDomain b₀) ^ 2 /
    |((LinearMap.BilinForm.toMatrix e T).det : ℝ)|, div_pos (sq_pos_of_pos hvol) (abs_pos.mpr (by exact_mod_cast hGe)), ?_⟩
  intro L hfg hspan hint
  set M := AddSubgroup.toIntSubmodule L with hM
  have : Module.Finite ℤ M := Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg M).2 hfg)
  have : Module.IsTorsionFree ℤ Q := .trans_faithfulSMul ℤ ℚ Q
  have hψq : ∀ (q : ℚ) (y : Q), ψ (q • y) = (q : ℝ) • ψ y := fun q y => by
    simpa using map_ratCast_smul ψ ℚ ℝ q y

  let x₀ := Module.Free.chooseBasis ℤ M
  have hli₀ : LinearIndependent ℚ (M.subtype ∘ x₀) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1
      (x₀.linearIndependent.map' M.subtype (Submodule.ker_subtype M))
  have hspan₀ : Submodule.span ℤ (Set.range (M.subtype ∘ x₀)) = M := by
    rw [Set.range_comp, Submodule.span_image, x₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanq : Submodule.span ℚ (Set.range (M.subtype ∘ x₀)) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℤ, hspan₀]
    exact hspan
  let xq₀ : Basis _ ℚ Q := Basis.mk hli₀ hspanq.ge
  let σ := Fintype.equivOfCardEq ((finrank_eq_card_basis xq₀).symm.trans hQ)
  let x := x₀.reindex σ
  let xq := xq₀.reindex σ
  have hxq : ∀ i, xq i = (x i : Q) := fun i => by simp [xq, x, xq₀]
  have hspanx : Submodule.span ℤ (Set.range fun i => xq i) = M := by
    have : (fun i => xq i) = M.subtype ∘ x := funext hxq
    rw [this, Set.range_comp, Submodule.span_image, x.span_eq, Submodule.map_top,
      Submodule.range_subtype]

  set P := e.toMatrix xq with hP
  have hψe : ∀ y, ψ y = ∑ i, (e.repr y i : ℝ) • b₀ i := fun y => by
    calc ψ y = ψ (∑ i, e.repr y i • e i) := by rw [e.sum_repr]
      _ = _ := by rw [map_sum]; simp only [hψq, hb₀]
  have hmat : b₀.toMatrix (fun j => ψ (xq j)) = P.map (Rat.cast : ℚ → ℝ) := by
    ext i j
    rw [Basis.toMatrix_apply, hψe, b₀.repr_sum_self]
    simp [P, Basis.toMatrix_apply]
  have hdetP : b₀.det (fun j => ψ (xq j)) = (P.det : ℝ) := by
    rw [Basis.det_apply, hmat]
    simpa using (RingHom.map_det (Rat.castHom ℝ) P).symm
  have hP0 : P.det ≠ 0 := by
    rw [hP, ← Basis.det_apply]
    exact (e.isUnit_det xq).ne_zero
  have hw : LinearIndependent ℝ (fun j => ψ (xq j)) :=
    ((Basis.is_basis_iff_det b₀).2 (by rw [hdetP]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast hP0))).1
  let bx : Basis K ℝ V := basisOfLinearIndependentOfCardEqFinrank' _ hw hrank.symm
  have hL : AddSubgroup.toIntSubmodule (L.map ψ) = Submodule.span ℤ (Set.range bx) := by
    change M.map ψ.toIntLinearMap = _
    rw [← hspanx, Submodule.map_span, ← Set.range_comp]
    congr 1
    simp [bx, Function.comp_def]

  have hG : (LinearMap.BilinForm.toMatrix xq T).det =
      P.det ^ 2 * (LinearMap.BilinForm.toMatrix e T).det := by
    rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix e xq T, det_mul, det_mul, det_transpose]
    ring
  have indexq := T.relIndex_dual_eq_abs_det xq hT M hspanx.symm hint
  rw [hG, abs_mul, abs_pow, sq_abs] at indexq
  have hindex : (L.relIndex (T.dualSubmodule M).toAddSubgroup : ℝ) =
      (P.det : ℝ) ^ 2 * |((LinearMap.BilinForm.toMatrix e T).det : ℝ)| := by exact_mod_cast indexq
  rw [hL]
  refine ⟨inferInstance, inferInstance, ?_⟩
  let bZ : Basis K ℤ (Submodule.span ℤ (Set.range bx)) :=
    Basis.span (bx.linearIndependent.restrict_scalars' ℤ)
  have hcoe : ((↑) ∘ bZ : K → V) = fun j => ψ (xq j) := funext fun i => by
    simp [bZ, Basis.span_apply, bx]
  rw [ZLattice.covolume_eq_det_mul_measureReal _ μ bZ b₀, hcoe, hdetP, hindex, mul_pow, sq_abs]
  field_simp [ne_of_gt (abs_pos.2 (show ((LinearMap.BilinForm.toMatrix e T).det : ℝ) ≠ 0 by exact_mod_cast hGe))]

theorem IntegralFormCovolume.proof : IntegralFormCovolume.Statement Q V K := by
  intro ψ e T μ hμ hT hli hrank
  have : FiniteDimensional ℚ Q := Module.Finite.of_basis e
  obtain ⟨C, hC, hformula⟩ := IntegralFormCovolume.index_formula Q V K ψ e T μ hμ hT hli hrank
  refine ⟨C, fun L k hk hfg hspan hint hdual => ?_⟩
  obtain ⟨hd, hL, hvol⟩ := hformula L hfg hspan (fun x hx y hy => by
    obtain ⟨n, hn⟩ := hint x hx y hy
    exact Submodule.mem_one.mpr ⟨n, hn.symm⟩)
  have hindex := T.relIndex_dual_le_pow_of_zsmul_mem hT L L hfg hspan k hk (fun y hy =>
    hdual y fun x hx => by
      obtain ⟨n, hn⟩ := Submodule.mem_one.mp (hy x hx)
      exact ⟨n, hn.symm⟩)
  refine ⟨hd, hL, hvol.trans_le (mul_le_mul_of_nonneg_left ?_ hC.le)⟩
  rw [← finrank_eq_card_basis e]
  have hbound : (L.relIndex (T.dualSubmodule L.toIntSubmodule).toAddSubgroup : ℝ) ≤
      (k.natAbs : ℝ) ^ finrank ℚ Q := by exact_mod_cast hindex
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hbound

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
