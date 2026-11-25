module

public import Mathlib.Algebra.Order.Round
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Set

/-- Rounding along a shortest real period excludes all nonzero lattice points in this strip
with real coordinate of absolute value less than one period. -/
private theorem rectangle_avoids (L : AddSubgroup ℂ) {τ : ℝ} (ht : 0 < τ)
    (htL : (τ : ℂ) ∈ L) (hmin : ∀ z ∈ L, z ≠ 0 → τ ≤ ‖z‖)
    (z : ℂ) (hz : z ∈ L) (hr : |z.re| < τ) (hi : |z.im| < Real.sqrt 3 / 2 * τ) :
    z = 0 := by
  by_cases h : z.im = 0
  · by_contra hn
    have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using h)
    have hb := hmin z hz hn
    rw [he, Complex.norm_real, Real.norm_eq_abs] at hb
    linarith
  let k := round (z.re / τ)
  let w := z - k • (τ : ℂ)
  have wi : w.im = z.im := by simp [w]
  have wr : w.re = z.re - (k : ℝ) * τ := by simp [w]
  have wn : w ≠ 0 := fun he => h (by simpa [he] using wi.symm)
  have hnorm := hmin w (L.sub_mem hz (L.zsmul_mem htL k)) wn
  have hround := mul_le_mul_of_nonneg_right (abs_sub_round (z.re / τ)) ht.le
  have habs : |w.re| ≤ τ / 2 := by
    rw [wr, show z.re - (k : ℝ) * τ = (z.re / τ - k) * τ by
      rw [sub_mul, div_mul_cancel₀ _ ht.ne'], abs_mul, abs_of_pos ht]
    linarith
  have hre := sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
  have him := sq_lt_sq' (abs_lt.mp hi).1 (abs_lt.mp hi).2
  have hsq : (Real.sqrt 3 / 2 * τ) ^ 2 = 3 / 4 * τ ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [hsq] at him
  have hw := sq_le_sq' (by linarith [norm_nonneg w] : -‖w‖ ≤ τ) hnorm
  rw [Complex.sq_norm, Complex.normSq_apply, wi] at hw
  nlinarith

/-- The sharp planar covolume bound for a lattice with a shortest vector along the real axis. -/
theorem planar_cell_bound {L : AddSubgroup ℂ} [Countable L] {F : Set ℂ}
    (hF : IsAddFundamentalDomain L F volume) {τ : ℝ} (ht : 0 < τ) (htL : (τ : ℂ) ∈ L)
    (hmin : ∀ z ∈ L, z ≠ 0 → τ ≤ ‖z‖) :
    ENNReal.ofReal (Real.sqrt 3 / 2 * τ ^ 2) ≤ volume F := by
  let s := Complex.measurableEquivRealProd ⁻¹' (Ioo 0 τ ×ˢ Ioo 0 (Real.sqrt 3 / 2 * τ))
  have hm := (measurableSet_Ioo (a := (0 : ℝ)) (b := τ)).prod (measurableSet_Ioo (a := (0 : ℝ)) (b := Real.sqrt 3 / 2 * τ))
  have hvol : volume s = ENNReal.ofReal (Real.sqrt 3 / 2 * τ ^ 2) := by
    change volume (Complex.measurableEquivRealProd ⁻¹' _) = _
    rw [Complex.volume_preserving_equiv_real_prod.measure_preimage hm.nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
      sub_zero, sub_zero, ← ENNReal.ofReal_mul ht.le]
    congr 1
    ring
  rw [← hvol]
  by_contra! hlt
  obtain ⟨x, y, hxy, h⟩ := exists_pair_mem_lattice_not_disjoint_vadd hF
    ((hm.preimage Complex.measurableEquivRealProd.measurable).nullMeasurableSet) hlt
  obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, he⟩ := Set.not_disjoint_iff.mp h
  have hv' : (0 < v.re ∧ v.re < τ) ∧ 0 < v.im ∧ v.im < Real.sqrt 3 / 2 * τ := hv
  have hw' : (0 < w.re ∧ w.re < τ) ∧ 0 < w.im ∧ w.im < Real.sqrt 3 / 2 * τ := hw
  change (y : ℂ) + w = (x : ℂ) + v at he
  have hdiff : (x : ℂ) - y = w - v := by linear_combination -he
  have hz := rectangle_avoids L ht htL hmin ((x : ℂ) - y) (L.sub_mem x.2 y.2)
    (by rw [hdiff, Complex.sub_re, abs_lt]; constructor <;> linarith only [hv'.1.1, hv'.1.2, hw'.1.1, hw'.1.2])
    (by rw [hdiff, Complex.sub_im, abs_lt]; constructor <;> linarith only [hv'.2.1, hv'.2.2, hw'.2.1, hw'.2.2])
  exact hxy (Subtype.ext (sub_eq_zero.mp hz))

end GroundTheory.Heights₂.Heights.FiniteCovolume
