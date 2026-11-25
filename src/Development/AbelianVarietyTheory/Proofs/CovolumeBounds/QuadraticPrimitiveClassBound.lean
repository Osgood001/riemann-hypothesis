module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PrimitiveIdealEuler
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr

@[expose] public section

open NumberField NumberField.InfinitePlace Module Finset
open scoped Real

namespace GlobalTheory.QuadraticZeta

variable {K : Type*} [Field K] [NumberField K]

private theorem idealCount_pow_diff (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (idealCount K (p ^ (k + 1)) : ℤ) - idealCount K (p ^ k) = kroneckerAt (discr K) p ^ (k + 1) := by
  induction k with
  | zero =>
    have h := idealCount_prime_mul h2 hp 1
    have one : idealCount K 1 = 1 := by simp [idealCount, Ideal.absNorm_eq_one_iff]
    simp only [mul_one, one, Nat.cast_one, ite_eq_right hp.not_dvd_one, mul_zero, sub_zero] at h
    simp only [zero_add, pow_one, pow_zero, one, Nat.cast_one, h]
    ring
  | succ k ih =>
    have h := idealCount_prime_mul h2 hp (p ^ (k+1))
    rw [← pow_succ', ite_eq_left (dvd_pow_self p (by omega : k+1 ≠ 0)),
      pow_succ p k, Nat.mul_div_cancel _ hp.pos, ← pow_succ] at h
    rw [h, pow_succ _ (k + 1)]
    linear_combination kroneckerAt (discr K) p * ih

/-- The primitive-ideal coefficient computed from the discriminant alone.
The zero ideal is not primitive. -/
def primitiveCount (D : ℤ) (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors,
    ((1 + kroneckerAt D p) * kroneckerAt D p ^ (n.factorization p - 1)).toNat

/-- In a quadratic number field the discriminant Euler product counts the actual
scalar-primitive integral ideals of positive norm. -/
theorem ncard_primitive_eq_primitiveCount (h2 : finrank ℚ K = 2) {n : ℕ} (hn : n ≠ 0) :
    (scalarSieveFibre K n.primeFactors n).ncard = primitiveCount (discr K) n := by
  rw [ncard_primitive_ideal_norm_euler hn, h2, primitiveCount, ite_eq_right hn]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  generalize n.factorization p = k at *
  change idealCount K (p ^ k) - (if 2 ≤ k then idealCount K (p ^ (k - 2)) else 0) = _
  cases k with
  | zero => contradiction
  | succ k =>
    cases k with
    | zero =>
      have h := idealCount_pow_diff h2 hprime 0
      have one : idealCount K 1 = 1 := by simp [idealCount, Ideal.absNorm_eq_one_iff]
      simp only [zero_add, pow_one, pow_zero, one, Nat.cast_one] at h
      change idealCount K (p ^ 1) - 0 = ((1 + kroneckerAt (discr K) p) * kroneckerAt (discr K) p ^ 0).toNat
      rw [pow_one, Nat.sub_zero, pow_zero, mul_one]
      omega
    | succ k =>
      rw [ite_eq_left (by omega), show k + 1 + 1 - 2 = k by omega, show k + 1 + 1 - 1 = k + 1 by omega]
      have h := idealCount_pow_diff h2 hprime (k+1)
      have h' := idealCount_pow_diff h2 hprime k
      have eq : (idealCount K (p ^ (k + 1 + 1)) : ℤ) - idealCount K (p ^ k) =
          (1 + kroneckerAt (discr K) p) * kroneckerAt (discr K) p ^ (k+1) := by
        rw [pow_succ (kroneckerAt (discr K) p) (k+1)] at h
        linear_combination h + h'
      omega

/-- A finite discriminant-only sum bounds the actual class number, with no ideal
enumeration in the summand. -/
theorem classNumber_le_sum_primitiveCount (h2 : finrank ℚ K = 2) :
    classNumber K ≤ ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, primitiveCount (discr K) n := by
  refine (classNumber_le_sum_scalarSieve K).trans_eq (sum_congr rfl fun n hn => ?_)
  exact ncard_primitive_eq_primitiveCount h2 (mem_Ioc.mp hn).1.ne'


/-- A computable discriminant-only class-number upper bound. Here 4|D|/9
comes from squaring the elementary quadratic Minkowski estimate 2√|D|/3. -/
def primitiveClassBound (D : ℤ) : ℕ :=
  ∑ n ∈ Ioc 0 (Nat.sqrt (4 * D.natAbs / 9)), primitiveCount D n

theorem classNumber_le_primitiveClassBound (K : Type*) [Field K] [NumberField K]
    (h2 : finrank ℚ K = 2) : classNumber K ≤ primitiveClassBound (discr K) := by
  let m := ⌊minkowskiBound K⌋₊
  have hplaces := card_add_two_mul_card_eq_rank K
  rw [h2] at hplaces
  have hc : (4 / Real.pi) ^ nrComplexPlaces K ≤ (4 / 3 : ℝ) := calc
    _ ≤ (4 / 3 : ℝ) ^ nrComplexPlaces K := by gcongr; exact Real.pi_gt_three.le
    _ ≤ (4 / 3 : ℝ) ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = _ := pow_one _
  have habs : |(discr K : ℝ)| = ((discr K).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hm : (m : ℝ) ≤ (4 / 3 : ℝ) * (1 / 2 * √((discr K).natAbs : ℝ)) := by
    apply (Nat.floor_le (zero_le_one.trans (one_le_minkowskiBound K))).trans
    rw [minkowskiBound, h2, habs]
    norm_num
    gcongr
  have hsq := mul_self_le_mul_self (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hm
  have hr : (m : ℝ)^2 * 9 ≤ 4 * ((discr K).natAbs : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (discr K).natAbs : (0 : ℝ) ≤ (discr K).natAbs)]
  have hcut : m ≤ Nat.sqrt (4 * (discr K).natAbs / 9) :=
    Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide)).mpr (by exact_mod_cast hr))
  exact (classNumber_le_sum_primitiveCount h2).trans
    (sum_le_sum_of_subset (Ioc_subset_Ioc_right hcut))

/-- All nine classical negative fundamental discriminants are certified by this
finite bound; no converse (the classification theorem) is asserted. -/
theorem classNumber_eq_one_of_heegner_discr (K : Type*) [Field K] [NumberField K]
    (h2 : finrank ℚ K = 2) (hD : discr K ∈ [-3, -4, -7, -8, -11, -19, -43, -67, -163]) :
    classNumber K = 1 := by
  refine Nat.le_antisymm ((classNumber_le_primitiveClassBound K h2).trans ?_) (classNumber_pos K)
  generalize discr K = D at hD ⊢
  fin_cases hD <;> decide +kernel

end GlobalTheory.QuadraticZeta
