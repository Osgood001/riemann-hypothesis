module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic

/-!
# A lower bound for the first mixed term

The usual polarization test measures powers of linear combinations. To show that degree
`k + 1` can require that many probes, take the ring `ℝ[X]` and the elements `X, 1`.
For any `r ≤ k` proposed directions we construct a measurement that misses all of them,
but disagrees with the zero measurement on the first mixed term `X * 1^k`.
-/

@[expose] public section

namespace GlobalTheory

open Polynomial Finset

noncomputable section

/-- Reverse the binomial expansion: on `(X + t)^(k + 1)` this functional returns `q(t)`.
It vanishes on constants, covering probes whose `X` coefficient is zero. -/
private def pencilWitness (k : ℕ) (q : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ :=
  ∑ j ∈ range (k + 1), (q.coeff j / (k + 1).choose (k + 1 - j)) • Polynomial.lcoeff ℝ (k + 1 - j)

private theorem pencilWitness_power (k : ℕ) {q : ℝ[X]} (hd : q.natDegree ≤ k) (t : ℝ) :
    pencilWitness k q ((X + C t) ^ (k + 1)) = q.eval t := by
  rw [q.eval_eq_sum_range' (n := k + 1) (by omega)]
  simp only [pencilWitness, LinearMap.sum_apply, LinearMap.smul_apply, lcoeff_apply,
    smul_eq_mul, coeff_X_add_C_pow]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  have hchoose : ((k + 1).choose (k + 1 - j) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.sub_le _ _)).ne'
  rw [show k + 1 - (k + 1 - j) = j by omega]
  rw [mul_comm (t ^ j), ← mul_assoc, div_mul_cancel₀ _ hchoose]

private theorem pencilWitness_C (k : ℕ) (q : ℝ[X]) (a : ℝ) : pencilWitness k q (C a) = 0 := by
  simp only [pencilWitness, LinearMap.sum_apply, LinearMap.smul_apply, lcoeff_apply, smul_eq_mul]
  apply sum_eq_zero
  intro j hj
  have hj := mem_range.mp hj
  have : k + 1 - j ≠ 0 := by omega
  simp [coeff_C, this]

private theorem pencilWitness_X (k : ℕ) {q : ℝ[X]} (hd : q.natDegree = k) (hm : q.Monic) :
    pencilWitness k q X ≠ 0 := by
  have hq : q.coeff k = 1 := hd ▸ (hm : q.leadingCoeff = 1)
  simp only [pencilWitness, LinearMap.sum_apply, LinearMap.smul_apply, lcoeff_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp [hq]
    exact_mod_cast Nat.succ_ne_zero k
  · intro j hj he
    have hj := mem_range.mp hj
    have : k + 1 - j ≠ 1 := by omega
    simp [coeff_X, Ne.symm this]
  · simp

/-- With fewer than k + 1 homogeneous powers, two additive measurements can disagree on the
first mixed term while agreeing on every supplied probe. Allow arbitrary real probe directions. -/
theorem exists_measurement_missing_linear_term {r k : ℕ} (hr : r ≤ k) (a b : Fin r → ℝ) :
    ∃ L : ℝ[X] →+ ℝ, (∀ i, L ((C (a i) * X + C (b i)) ^ (k + 1)) = 0) ∧ L X ≠ 0 := by
  let q : ℝ[X] := X ^ (k - r) * ∏ j, (X - C (b j / a j))
  have hd : q.natDegree = k := by
    dsimp [q]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (monic_prod_X_sub_C _ _).ne_zero]
    simp [Nat.sub_add_cancel hr]
  have hm : q.Monic := (monic_X_pow _).mul (monic_prod_X_sub_C _ _)
  refine ⟨(pencilWitness k q).toAddMonoidHom, ?_, pencilWitness_X k hd hm⟩
  intro i
  change pencilWitness k q _ = 0
  by_cases ha : a i = 0
  · simp only [ha, map_zero, zero_mul, zero_add, ← map_pow, pencilWitness_C]
  · have h : C (a i) * X + C (b i) = C (a i) * (X + C (b i / a i)) := by
      rw [mul_add, ← map_mul, mul_div_cancel₀ _ ha]
    rw [h, mul_pow, ← map_pow, ← smul_eq_C_mul, map_smul, pencilWitness_power k hd.le]
    simp only [q, eval_mul, eval_pow, eval_X, eval_prod, eval_sub, eval_C]
    rw [prod_eq_zero (mem_univ i) (by simp), mul_zero, smul_zero]

end

end GlobalTheory
