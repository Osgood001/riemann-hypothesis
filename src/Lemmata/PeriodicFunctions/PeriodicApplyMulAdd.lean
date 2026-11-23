module

public import Mathlib

@[expose] public section

open NumberField IsDedekindDomain Module

namespace Bl.PeriodicFunctions

variable {K : Type} [Field K]

theorem goal1 (M m : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) :
    ∑ i ∈ Finset.range (M * m), g i = (m : K) * ∑ i ∈ Finset.range M, g i := by
  rw [Nat.mul_comm M m]
  induction m with
  | zero => simp
  | succ n ih =>
    have shift (x : ℕ) : g (x + n * M) = g x := Function.Periodic.nat_mul hg n x
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    simp only [Nat.add_comm (n * M), shift, Nat.cast_succ, add_mul, one_mul]

end Bl.PeriodicFunctions
