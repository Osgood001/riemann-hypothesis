module

public import Mathlib

@[expose] public section

noncomputable section

namespace Formalism.LogFactorialBounds

open Finset Real

lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (b := Nat.log p n + 2) (by omega)]
  have h₁ : 1 ∈ Finset.Ico 1 (Nat.log p n + 2) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  simpa only [pow_one] using
    Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h₁

lemma sum_div_mul_log_le_log_factorial (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial : ℕ) := by
  have hs : n.factorial.primeFactors = Nat.primesLE n := by
    ext p
    rw [Nat.mem_primeFactors_of_ne_zero (Nat.factorial_ne_zero n), Nat.mem_primesLE]
    exact ⟨fun ⟨hp, hd⟩ => ⟨hp.dvd_factorial.mp hd, hp⟩,
      fun ⟨hle, hp⟩ => ⟨hp, hp.dvd_factorial.mpr hle⟩⟩
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, hs]
  refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
  exact_mod_cast div_le_factorization_factorial (Nat.prime_of_mem_primesLE hp) n

lemma log_factorial_le (n : ℕ) : Real.log (n.factorial : ℕ) ≤ n * Real.log n := by
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
  exact_mod_cast Nat.factorial_le_pow n

lemma sum_primesLE_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hprim : ∑ p ∈ Nat.primesLE n, Real.log p ≤ n * Real.log 4 := by
    simpa only [Chebyshev.theta_eq_sum_primesLE_log, mul_comm] using
      Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hterm : ∀ p ∈ Nat.primesLE n,
      (n : ℝ) * (Real.log p / p) ≤ ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hpp := (Nat.mem_primesLE.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hdiv : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0, add_mul, one_mul]
      exact_mod_cast (Nat.lt_div_mul_add (a := n) hpp.pos).le
    calc (n : ℝ) * (Real.log p / p) = ((n : ℝ) / p) * Real.log p := by ring
      _ ≤ (((n / p : ℕ) : ℝ) + 1) * Real.log p :=
        mul_le_mul_of_nonneg_right hdiv (Real.log_natCast_nonneg p)
      _ = ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  have hsum : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p
      ≤ n * (Real.log n + Real.log 4) := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ Nat.primesLE n, (n : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ Nat.primesLE n, (((n / p : ℕ) : ℝ) * Real.log p + Real.log p) :=
          Finset.sum_le_sum hterm
      _ = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p
          + ∑ p ∈ Nat.primesLE n, Real.log p := Finset.sum_add_distrib
      _ ≤ Real.log (n.factorial : ℕ) + n * Real.log 4 :=
          add_le_add (sum_div_mul_log_le_log_factorial n) hprim
      _ ≤ n * (Real.log n + Real.log 4) := by
          rw [mul_add]
          exact add_le_add (log_factorial_le n) le_rfl
  exact le_of_mul_le_mul_left hsum hnpos

end Formalism.LogFactorialBounds
