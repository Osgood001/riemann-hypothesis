module

import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroNormSqLeMulCovolumeRpow
public import Formalism.LatticeSlopes.CovolAntiSameRank
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram

@[expose] public section

open Module Submodule MeasureTheory

noncomputable section

namespace Formalism.F

universe u

theorem covol_eq_of_linearEquiv_inner {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Submodule ℤ E) (M : Submodule ℤ F) [DiscreteTopology L] [DiscreteTopology M]
    (f : L ≃ₗ[ℤ] M)
    (hf : ∀ x y : L, inner ℝ ((f x : M) : F) ((f y : M) : F) = inner ℝ (x : E) (y : E)) :
    covol M = covol L := by
  classical
  let b := Module.finBasis ℤ L
  rw [covol_eq_gram F M (Fin (Module.finrank ℤ L)) (b.map f), covol_eq_gram E L _ b]
  congr 2
  ext i j
  simp only [Matrix.gram, Matrix.of_apply, Basis.map_apply]
  exact hf (b i) (b j)

/-- Minkowski's short-vector radius, retaining the volume of the Euclidean unit ball. -/
theorem exists_short_vector_of_isZLattice_ball {W : Type u} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ W) :
    ∃ x ∈ L, x ≠ 0 ∧ ‖x‖ ≤
      (2 ^ finrank ℝ W / volume.real (Metric.ball (0 : W) 1) * ZLattice.covolume L)
        ^ ((finrank ℝ W : ℝ)⁻¹) := by
  classical
  obtain ⟨b, hb, hmin⟩ := GlobalTheory.exists_basis_norm_eq_succMin L
  let i : Fin (finrank ℝ W) := ⟨0, hn⟩
  refine ⟨b i, hb i, b.ne_zero i, ?_⟩
  have hpow : ‖b i‖ ^ finrank ℝ W ≤ ∏ j : Fin (finrank ℝ W), GlobalTheory.succMin L (j + 1) := by
    rw [show ‖b i‖ ^ finrank ℝ W = ∏ _j : Fin (finrank ℝ W), ‖b i‖ by simp]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
    rw [hmin]
    exact GlobalTheory.succMin_mono_of_isZLattice (L := L) (by simp [i]) j.2
  calc ‖b i‖ = (‖b i‖ ^ finrank ℝ W) ^ ((finrank ℝ W : ℝ)⁻¹) := by
         rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
           mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), Real.rpow_one]
       _ ≤ _ := Real.rpow_le_rpow (by positivity)
         (hpow.trans (GlobalTheory.prod_succMin_le_two_pow_div_mul_covolume L)) (by positivity)

theorem exists_short_vector_of_isZLattice (hC : CovolEqCovolume.{u}) {W : Type u} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ W) :
    ∃ x ∈ L, x ≠ 0 ∧
      ‖x‖ ≤ Real.sqrt (finrank ℝ W : ℝ) * covol L ^ ((1 : ℝ) / (finrank ℝ W : ℝ)) := by
  obtain ⟨x, hx, hx0, hball⟩ := exists_short_vector_of_isZLattice_ball L hn
  refine ⟨x, hx, hx0, hball.trans ?_⟩
  rw [← hC W L]
  have hvol := GlobalTheory.two_pow_div_volume_unitBall_le W
  have hc : 0 ≤ covol L := (hC W L ▸ ZLattice.covolume_pos L volume).le
  trans (((finrank ℝ W : ℝ) ^ ((finrank ℝ W : ℝ) / 2)) * covol L) ^ ((finrank ℝ W : ℝ)⁻¹)
  · gcongr
  apply le_of_eq
  rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hc,
    ← Real.rpow_mul (Nat.cast_nonneg _), Real.sqrt_eq_rpow, one_div]
  congr 2
  all_goals simp [div_eq_mul_inv, mul_comm, Nat.cast_ne_zero.2 hn.ne']

theorem shortVector_of (hC : CovolEqCovolume.{u}) : ShortVector.{u} := by
  intro E _ _ _ L hL hne
  classical
  have : DiscreteTopology L := hL

  have hsub : ∀ x ∈ L, x ∈ Submodule.span ℝ (L : Set E) := fun x hx => Submodule.subset_span hx
  let L₀ : Submodule ℤ (Submodule.span ℝ (L : Set E)) :=
    L.comap ((Submodule.span ℝ (L : Set E)).subtype.restrictScalars ℤ)
  let e : L ≃ₗ[ℤ] L₀ :=
    { toFun := fun y => ⟨⟨y, hsub y y.2⟩, y.2⟩
      invFun := fun x => ⟨((x : Submodule.span ℝ (L : Set E)) : E), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : DiscreteTopology L₀ := by
    refine DiscreteTopology.of_continuous_injective (f := e.symm) ?_ e.symm.injective
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have himg : (Submodule.span ℝ (L : Set E)).subtype '' (L₀ : Set _) = (L : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub x hx⟩, hx, rfl⟩
  have : IsZLattice ℝ L₀ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (Submodule.span ℝ (L : Set E)).injective_subtype
    rw [Submodule.map_span, himg, Submodule.map_top, Submodule.range_subtype]
  let : MeasurableSpace (Submodule.span ℝ (L : Set E)) := borel _
  have : BorelSpace (Submodule.span ℝ (L : Set E)) := ⟨rfl⟩
  have hcov : covol L₀ = covol L :=
    covol_eq_of_linearEquiv_inner L L₀ e (fun _ _ => rfl)
  have hrk : finrank ℝ (Submodule.span ℝ (L : Set E)) = rk L := by
    rw [← ZLattice.rank ℝ L₀]
    exact e.finrank_eq.symm
  have : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hpos : 0 < finrank ℝ (Submodule.span ℝ (L : Set E)) := by
    rw [hrk]
    exact Module.finrank_pos
  obtain ⟨x, hx, hx0, hxn⟩ := exists_short_vector_of_isZLattice hC L₀ hpos
  refine ⟨(x : E), hx, ?_, ?_⟩
  · intro h0
    exact hx0 (Subtype.ext h0)
  · rw [hrk, hcov] at hxn
    exact hxn

end Formalism.F
