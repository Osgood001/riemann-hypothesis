module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Blichfeldt
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PlanarCell
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory Submodule

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

private theorem packingBasis [MeasurableSpace V] [BorelSpace V]
    (o : Orientation ℝ V (Fin d)) (b : Fin d → V) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ z : Fin d → ℤ, z ≠ 0 → lam ≤ ‖∑ i, (z i : ℝ) • b i‖) :
    ∃ B : Basis (Fin d) ℝ V, volume (ZSpan.fundamentalDomain B) = ENNReal.ofReal |o.volumeForm b| ∧
      ∀ x ∈ span ℤ (Set.range B), x ≠ 0 → lam ≤ ‖x‖ := by
  classical
  have hd : finrank ℝ V = d := Fact.out
  have hcomb : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨z, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hz : z ≠ 0 := by
      rintro rfl
      simp at hx0
    simpa [← Int.cast_smul_eq_zsmul ℝ] using hmin z hz
  have hdisc : DiscreteTopology (span ℤ (Set.range b)) :=
    DiscreteTopology.of_forall_le_norm hlam fun x hx => hcomb x x.2 (by simpa using hx)
  have hZ : LinearIndependent ℤ b := by
    rw [Fintype.linearIndependent_iff]
    intro z hz
    by_contra hne
    have hz' : z ≠ 0 := fun h => hne (fun i => by simp [h])
    have h1 := hmin z hz'
    have h2 : ∑ i, (z i : ℝ) • b i = 0 := by simpa [Int.cast_smul_eq_zsmul] using hz
    rw [h2, norm_zero] at h1
    linarith
  have hR : LinearIndependent ℝ b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc,
      Set.finrank, finrank_span_eq_card hZ]
  have hcard : Fintype.card (Fin d) = finrank ℝ V := by simp [hd]
  let B : Basis (Fin d) ℝ V := Basis.mk hR (hR.span_eq_top_of_card_eq_finrank' hcard).ge
  have hB : ⇑B = b := Basis.coe_mk _ _

  have hF : volume (ZSpan.fundamentalDomain B) = ENNReal.ofReal |o.volumeForm b| := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped B volume), ← o.measure_eq_volume,
      AlternatingMap.measure_parallelepiped, hB]
  exact ⟨B, hF, hB ▸ hcomb⟩

theorem MinkowskiVolumeForm.proof : MinkowskiVolumeForm.Statement V d := by
  classical
  intro o b lam hlam hmin
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have hd : finrank ℝ V = d := Fact.out

  obtain ⟨B, hF, hcomb⟩ := packingBasis V d o b lam hlam hmin
  let e : OrthonormalBasis (Fin d) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hd)
  set σ : ℝ := lam / Real.sqrt d with hσ
  have hσ0 : 0 ≤ σ := div_nonneg hlam.le (Real.sqrt_nonneg _)
  let φ : V →ₗ[ℝ] (Fin d → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap ∘ₗ e.repr.toLinearEquiv.toLinearMap
  let P : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Ioo (-σ) σ
  let s : Set V := φ ⁻¹' P
  have hs_mem : ∀ v, v ∈ s ↔ ∀ i, |e.repr v i| < σ := by
    intro v
    simp only [s, P, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo, abs_lt]
    rfl
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    rw [hs_mem] at hx ⊢
    intro i
    simpa using hx i
  have hconv : Convex ℝ s := (convex_pi fun _ _ => convex_Ioo _ _).linear_preimage φ
  have hvol : volume s = ENNReal.ofReal (2 * σ) ^ d := by
    have hmp : MeasurePreserving (fun v : V => WithLp.ofLp (e.repr v)) volume volume :=
      (PiLp.volume_preserving_ofLp (Fin d)).comp e.measurePreserving_repr
    rw [show s = (fun v : V => WithLp.ofLp (e.repr v)) ⁻¹' P from rfl,
      hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  by_contra hlt
  push Not at hlt
  have hlt' : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ V < volume s := by
    rw [hd]
    have h : ENNReal.ofReal (|o.volumeForm b| * 2 ^ d) < ENNReal.ofReal ((2 * σ) ^ d) := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), mul_pow, mul_comm]
      exact mul_lt_mul_of_pos_left hlt (by positivity)
    rwa [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (mul_nonneg zero_le_two hσ0),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← hF, ← hvol] at h
  have hcount : Countable (span ℤ (Set.range B)).toAddSubgroup := by
    change Countable (span ℤ (Set.range B))
    infer_instance
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' B volume) hsymm hconv hlt'
  have hx0' : x ≠ 0 := by
    rintro rfl
    exact hx0 rfl
  have h1 : lam ≤ ‖x‖ := hcomb x hxL hx0'
  have h2 : ‖x‖ < lam := by
    rw [hs_mem] at hxs
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · exact absurd (@Subsingleton.elim _ (finrank_zero_iff.1 (hd.trans hd0)) x 0) hx0'
    · have hσpos : 0 < σ := div_pos hlam (Real.sqrt_pos.2 (by exact_mod_cast hdpos))
      have hsq : (d : ℝ) * σ ^ 2 = lam ^ 2 := by
        rw [hσ, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        field_simp
      rw [← e.repr.norm_map, EuclideanSpace.norm_eq]
      calc Real.sqrt (∑ i, ‖e.repr x i‖ ^ 2) < Real.sqrt (∑ _i : Fin d, σ ^ 2) := by
            apply Real.sqrt_lt_sqrt (by positivity)
            apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hdpos⟩⟩)
            intro i _
            rw [Real.norm_eq_abs, sq_lt_sq, abs_of_pos hσpos, abs_abs]
            exact hxs i
        _ = lam := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsq,
              Real.sqrt_sq hlam.le]
  linarith

/-- Blichfeldt's bound in even dimension, expressed using the oriented basis volume. -/
theorem MinkowskiVolumeForm.blichfeldt_even [Nontrivial V] (m : ℕ) (heven : d = 2 * m)
    (o : Orientation ℝ V (Fin d)) (b : Fin d → V) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ z : Fin d → ℤ, z ≠ 0 → lam ≤ ‖∑ i, (z i : ℝ) • b i‖) :
    Real.pi ^ m * lam ^ d ≤ 2 ^ m * ((m + 1).factorial : ℝ) * |o.volumeForm b| := by
  classical
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have hd : finrank ℝ V = d := Fact.out

  obtain ⟨B, hF, hcomb⟩ := packingBasis V d o b lam hlam hmin
  have : Countable (span ℤ (Set.range B)).toAddSubgroup :=
    inferInstanceAs (Countable (span ℤ (Set.range B)))
  have hb := blichfeldt_ball_le (ZSpan.isAddFundamentalDomain' B volume) hlam
    hcomb
  rw [hF] at hb
  have hh := (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp hb
  generalize hA : |o.volumeForm b| = A at hh ⊢
  rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even (hd.trans heven), hd, heven,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ lam / Real.sqrt 2),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi ^ m / (m.factorial : ℝ)),
    div_pow, pow_mul (Real.sqrt 2), Real.sq_sqrt (by norm_num)] at hh
  push_cast at hh
  rw [heven, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  have hf : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  field_simp at hh
  nlinarith

/-- A positive lower bound can be replaced by an attained minimum. -/
private theorem exists_shortest_of_gap {V : Type*} [NormedAddCommGroup V] [ProperSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ x ∈ L, x ≠ 0 → lam ≤ ‖x‖) (w : V) (hw : w ∈ L) (hw0 : w ≠ 0) :
    ∃ v ∈ L, v ≠ 0 ∧ lam ≤ ‖v‖ ∧ ∀ x ∈ L, x ≠ 0 → ‖v‖ ≤ ‖x‖ := by
  let S := (L : Set V) ∩ {x : V | lam ≤ ‖x‖}
  have hL : IsClosed (L : Set V) := AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup)
  have hS : IsClosed S := hL.inter (isClosed_le continuous_const continuous_norm)
  obtain ⟨v, hv, heq⟩ := hS.exists_infDist_eq_dist ⟨w, hw, hmin w hw hw0⟩ 0
  refine ⟨v, hv.1, norm_pos_iff.mp (hlam.trans_le hv.2), hv.2, fun x hx hx0 ↦ ?_⟩
  simpa [heq] using
    (Metric.infDist_le_dist_of_mem (x := (0 : V)) (show x ∈ S from ⟨hx, hmin x hx hx0⟩))

private theorem exists_plane_isometry_map_norm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (hd : Module.finrank ℝ V = 2) {u : V} (hu : u ≠ 0) :
    ∃ e : V ≃ₗᵢ[ℝ] ℂ, e u = (‖u‖ : ℂ) := by
  let e := (Complex.isometryOfOrthonormal
    ((stdOrthonormalBasis ℝ V).reindex (finCongr hd))).symm
  have h : e u ≠ 0 := by simpa using hu
  let c : Circle := ⟨(‖u‖ : ℂ) / e u, by
    apply mem_sphere_zero_iff_norm.2
    rw [norm_div, Complex.norm_real, norm_norm, e.norm_map, div_self (norm_ne_zero_iff.mpr hu)]⟩
  refine ⟨e.trans (rotation c), ?_⟩
  change ((‖u‖ : ℂ) / e u) * e u = _
  exact div_mul_cancel₀ _ h

/-- The sharp planar lattice inequality: the covolume is at least
`sqrt 3 / 2` times the square of a lower bound for the first minimum. -/
theorem MinkowskiVolumeForm.planar (hd : d = 2) (o : Orientation ℝ V (Fin d))
    (b : Fin d → V) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ z : Fin d → ℤ, z ≠ 0 → lam ≤ ‖∑ i, (z i : ℝ) • b i‖) :
    Real.sqrt 3 * lam ^ 2 ≤ 2 * |o.volumeForm b| := by
  classical
  subst d
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  obtain ⟨B, hF, hcomb⟩ := packingBasis V 2 o b lam hlam hmin
  obtain ⟨u, hu, hu0, hlamu, hminu⟩ := exists_shortest_of_gap (span ℤ (Set.range B)) hlam hcomb
    (B 0) (subset_span ⟨0, rfl⟩) (B.ne_zero 0)
  obtain ⟨e, heu⟩ := exists_plane_isometry_map_norm (V := V) Fact.out hu0
  let C := B.map e.toLinearEquiv
  let L := span ℤ (Set.range B)
  let A := span ℤ (Set.range C)
  have hmap : L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap = A := by
    dsimp only [L]
    rw [map_span, ← Set.range_comp]
    rfl
  have hreal : (‖u‖ : ℂ) ∈ A := by
    rw [← hmap, ← heu]
    exact ⟨u, hu, rfl⟩
  have hshort : ∀ z ∈ A, z ≠ 0 → ‖u‖ ≤ ‖z‖ := by
    intro z hz hz0
    rw [← hmap] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    change ‖u‖ ≤ ‖e v‖
    rw [e.norm_map]
    exact hminu v hv (fun h => hz0 (by simp [h]))
  have : Countable A.toAddSubgroup := by
    change Countable (span ℤ (Set.range C))
    infer_instance
  have hp := planar_cell_bound (ZSpan.isAddFundamentalDomain' C volume) (norm_pos_iff.mpr hu0) hreal hshort
  have he : ZSpan.fundamentalDomain C = e.symm ⁻¹' ZSpan.fundamentalDomain B := by
    ext z
    simp only [ZSpan.mem_fundamentalDomain, Set.mem_preimage, C, Basis.map_repr]
    rfl
  rw [he, e.symm.measurePreserving.measure_preimage
    (ZSpan.fundamentalDomain_measurableSet B).nullMeasurableSet, hF] at hp
  have hbound := (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp hp
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlam.le hlamu 2) (Real.sqrt_nonneg 3)
  linarith

end GroundTheory.Heights₂.Heights.FiniteCovolume
