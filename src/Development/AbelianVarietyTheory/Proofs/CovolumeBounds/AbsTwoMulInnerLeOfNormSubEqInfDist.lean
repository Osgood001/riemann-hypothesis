module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin

@[expose] public section

noncomputable section

open Module Submodule
open scoped InnerProductSpace

namespace GlobalTheory

open Finset

private theorem round_step {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (v y : V) (x : ℝ) :
    ∃ k : ℤ, B ((x - k) • v + y) ((x - k) • v + y) ≤
      B y y + Int.fract x * (1 - Int.fract x) * B v v := by
  let f := Int.fract x
  let Q (u : ℝ) := B (u • v + y) (u • v + y)
  let D := B y y + f * (1 - f) * B v v
  have h : (1 - f) * Q f + f * Q (f - 1) = D := by
    simp only [Q, D, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  by_cases h0 : Q f ≤ D
  · exact ⟨⌊x⌋, h0⟩
  · refine ⟨⌊x⌋ + 1, ?_⟩
    have h1 : Q (f - 1) ≤ D := by
      by_contra! hn
      have ha := mul_lt_mul_of_pos_left (lt_of_not_ge h0) (sub_pos.mpr (Int.fract_lt_one x))
      have hb := mul_le_mul_of_nonneg_left hn.le (Int.fract_nonneg x)
      change _ < (1 - f) * Q f at ha
      change _ ≤ f * Q (f - 1) at hb
      linarith
    have eqf : x - (⌊x⌋ + 1 : ℤ) = f - 1 := by
      change x - (↑(⌊x⌋ + 1 : ℤ) : ℝ) = x - ⌊x⌋ - 1
      rw [Int.cast_add, Int.cast_one]; ring
    rw [eqf]
    exact h1

/-- Round real coefficients to integers with error at most the sum of coordinate variances. -/
theorem exists_int_round_bilin {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (v : ι → V) (x : ι → ℝ) :
    ∃ k : ι → ℤ,
      let u := ∑ i, (x i - k i) • v i
      B u u ≤ ∑ i, Int.fract (x i) * (1 - Int.fract (x i)) * B (v i) (v i) := by
  classical
  suffices H : ∀ s : Finset ι, ∃ k : ι → ℤ,
      let u := ∑ i ∈ s, (x i - k i) • v i
      B u u ≤ ∑ i ∈ s, Int.fract (x i) * (1 - Int.fract (x i)) * B (v i) (v i) by exact H univ
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨k, hk⟩ := ih
    let u := ∑ j ∈ s, (x j - k j) • v j
    obtain ⟨m, hm⟩ := round_step B (v i) u (x i)
    refine ⟨Function.update k i m, ?_⟩
    have hu : ∑ j ∈ s, (x j - (Function.update k i m j : ℤ)) • v j = u := by
      refine sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
    simp only [sum_insert hi, Function.update_self, hu]
    exact hm.trans (by change B u u ≤ _ at hk; linarith)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_int_comb_norm_sub_sq_le (k : ℕ) (v : Fin k → E) {x : E}
    (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) / 4 := by
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℝ).1 hx
  obtain ⟨z, hz⟩ := exists_int_round_bilin (innerₗ E) v c
  refine ⟨∑ i, z i • v i, sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩), ?_⟩
  simp only [innerₗ_apply_apply, real_inner_self_eq_norm_sq] at hz
  have heq : (∑ i, c i • v i) - ∑ i, z i • v i = ∑ i, (c i - z i) • v i := by
    simp only [sub_smul, sum_sub_distrib, Int.cast_smul_eq_zsmul]
  rw [heq]
  apply hz.trans
  rw [sum_div]
  refine sum_le_sum fun i _ => ?_
  nlinarith [mul_nonneg (sq_nonneg (Int.fract (c i) - 1 / 2)) (sq_nonneg ‖v i‖)]

variable {L : Submodule ℤ E}

end GlobalTheory
