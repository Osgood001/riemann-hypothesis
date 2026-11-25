module

public import Formalism.GrowthSums.StatementA

@[expose] public section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

theorem le_padicValRat_sum_of_pos {p : ℕ} [Fact p.Prime] (s : ℤ) {F : ℕ → ℚ} {S : Finset ℕ}
    (hS : S.Nonempty) (hpos : ∀ i ∈ S, 0 < F i) (hv : ∀ i ∈ S, s ≤ padicValRat p (F i)) :
    s ≤ padicValRat p (∑ i ∈ S, F i) := by
  refine (Finset.sum_induction_nonempty F (fun q => 0 < q ∧ s ≤ padicValRat p q)
    ?_ hS (fun i hi => ⟨hpos i hi, hv i hi⟩)).2
  intro a b ha hb
  have hab := add_pos ha.1 hb.1
  exact ⟨hab, (le_min ha.2 hb.2).trans (padicValRat.min_le_padicValRat_add hab.ne')⟩

theorem padicValNat_le_of_lt_pow {p t y : ℕ} [hp : Fact p.Prime] (hy : 1 ≤ y)
    (hyP : y < p ^ (t + 1)) : padicValNat p y ≤ t := by
  by_contra h
  push Not at h
  have hdvd : p ^ (t + 1) ∣ y :=
    (pow_dvd_pow p (Nat.succ_le_of_lt h)).trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (not_le.2 hyP)

theorem padicValHarmonicPowerSum : HarmonicVal := by
  intro p t s hp
  have : Fact p.Prime := ⟨hp⟩
  have hPpos : (0 : ℚ) < ((p ^ (t + 1) : ℕ) : ℚ) := by
    have : 0 < p ^ (t + 1) := pow_pos hp.pos _
    exact_mod_cast this
  have hP0 : ((p ^ (t + 1) : ℕ) : ℚ) ≠ 0 := hPpos.ne'
  rw [Finset.mul_sum]
  refine le_padicValRat_sum_of_pos (p := p) (s : ℤ)
    (F := fun y => ((p ^ (t + 1) : ℕ) : ℚ) ^ s * (1 / (y : ℚ) ^ s))
    (S := Ico 1 (p ^ (t + 1))) ?_ ?_ ?_
  · refine ⟨1, ?_⟩
    rw [Finset.mem_Ico]
    exact ⟨le_rfl, Nat.one_lt_pow (Nat.succ_ne_zero t) hp.one_lt⟩
  · intro y hy
    rw [Finset.mem_Ico] at hy
    have hy0 : (0 : ℚ) < (y : ℚ) := by exact_mod_cast (show 0 < y by omega)
    exact mul_pos (pow_pos hPpos _) (one_div_pos.2 (pow_pos hy0 _))
  · intro y hy
    rw [Finset.mem_Ico] at hy
    have hy0 : (y : ℚ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
    have hvy : padicValNat p y ≤ t := padicValNat_le_of_lt_pow hy.1 hy.2
    rw [padicValRat.mul (pow_ne_zero _ hP0) (one_div_ne_zero (pow_ne_zero _ hy0)),
      padicValRat.pow _, one_div, padicValRat.inv, padicValRat.pow _,
      padicValRat.of_nat, padicValRat.of_nat, Nat.multiplicity_prime_pow]
    have hm : (s : ℤ) * (padicValNat p y : ℤ) ≤ (s : ℤ) * (t : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hvy) (by positivity)
    push_cast
    rw [padicValRat.of_nat, ← Nat.padicValNat_def]
    linarith only [hm]

theorem powerSumPolynomial : PowerSumPoly := by
  intro s
  classical
  have hdeg : (Polynomial.bernoulli (s + 1)).natDegree = s + 1 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
        rw [Polynomial.coeff_bernoulli, ite_eq_right hi.not_ge]
    · simp [Polynomial.coeff_bernoulli]
  have hs : ((s : ℚ) + 1) ≠ 0 := by positivity
  refine ⟨Polynomial.C (1 / ((s : ℚ) + 1)) *
    (Polynomial.bernoulli (s + 1) - Polynomial.C (bernoulli (s + 1))), ?_, ?_⟩
  · rw [Polynomial.natDegree_C_mul (one_div_ne_zero hs), Polynomial.natDegree_sub_C, hdeg]
  · intro n
    have h := Polynomial.sum_range_pow_eq_bernoulli_sub n s
    simp only [Nat.succ_eq_add_one] at h
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
    rw [← h, ← mul_assoc, one_div_mul_cancel hs, one_mul]

end Formalism.GrowthSums
