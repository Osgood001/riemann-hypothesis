module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.Data.Set.Card

@[expose] public section

open NumberField Module
namespace GlobalTheory

variable (K : Type*) [Field K] [NumberField K]

/-- Ideals of norm `n` not divisible by the scalar ideals `(p)` for `p ∈ S`.
This removes rational content, not individual prime ideals above `p`. -/
def scalarSieveFibre (S : Finset ℕ) (n : ℕ) : Set (Ideal (𝓞 K)) :=
  {I | I.absNorm = n ∧ ∀ p ∈ S, ¬ Ideal.span {(p : 𝓞 K)} ∣ I}

private theorem absNorm_scalar (p : ℕ) :
    (Ideal.span {(p : 𝓞 K)}).absNorm = p ^ finrank ℚ K := by
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]

/-- Sieving one further rational prime is exact, whether it splits, ramifies, or stays inert. -/
theorem ncard_scalarSieveFibre_insert (S : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hS : ∀ q ∈ S, q.Coprime p) (n : ℕ) :
    (scalarSieveFibre K (insert p S) n).ncard =
      (scalarSieveFibre K S n).ncard -
        if p ^ finrank ℚ K ∣ n then (scalarSieveFibre K S (n / p ^ finrank ℚ K)).ncard else 0 := by
  classical
  let P : Ideal (𝓞 K) := Ideal.span {(p : 𝓞 K)}
  let a := p ^ finrank ℚ K
  let T := scalarSieveFibre K S n
  let D := {I ∈ T | P ∣ I}
  have hP : P ≠ 0 := by simpa [P] using (Nat.cast_ne_zero.mpr hp.ne_zero : (p : 𝓞 K) ≠ 0)
  have ha : 0 < a := pow_pos hp.pos _
  have hPT : scalarSieveFibre K (insert p S) n = T \ D := by
    ext I
    simp only [scalarSieveFibre, T, D, P, Set.mem_sdiff, Set.mem_ofPred_eq, Finset.mem_insert]
    aesop
  have hfin : T.Finite := (Ring.HasFiniteQuotients.finite_absNorm_eq n).subset (fun _ h => h.1)
  have hDT : D ⊆ T := fun _ h => h.1
  rw [hPT, Set.ncard_sdiff hDT (hfin.subset hDT)]
  by_cases hd : a ∣ n
  · rw [ite_eq_left hd]
    have hD : D = (fun J => P * J) '' scalarSieveFibre K S (n / a) := by
      have hcop {q : ℕ} (hq : q ∈ S) : IsCoprime (Ideal.span {(q : 𝓞 K)}) P := by
        apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
        simpa only [map_natCast] using (hS q hq).isCoprime.map (Int.castRingHom (𝓞 K))
      ext I
      constructor
      · rintro ⟨⟨hn, hs⟩, J, rfl⟩
        have he : a * J.absNorm = n := by simpa only [a, P, map_mul, absNorm_scalar] using hn
        exact ⟨J, ⟨by rw [← he, Nat.mul_div_cancel_left _ ha],
            fun q hq h => hs q hq (dvd_mul_of_dvd_right h _)⟩, rfl⟩
      · rintro ⟨J, ⟨hn, hs⟩, rfl⟩
        refine ⟨⟨?_, fun q hq h => hs q hq ((hcop hq).dvd_of_dvd_mul_left h)⟩, dvd_mul_right _ _⟩
        change (P * J).absNorm = n
        rw [map_mul, hn, absNorm_scalar, Nat.mul_div_cancel' hd]
    rw [hD, Set.ncard_image_of_injective _ (mul_right_injective₀ hP)]
  · rw [ite_eq_right hd]
    have he : D = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro I ⟨⟨hn, _⟩, h⟩
      apply hd
      simpa only [a, P, absNorm_scalar, hn] using map_dvd Ideal.absNorm h
    rw [he, Set.ncard_empty]

/-- For a nonzero norm it suffices to sieve its own rational prime factors. -/
theorem scalarSieveFibre_primeFactors {n : ℕ} (hn : n ≠ 0) :
    scalarSieveFibre K n.primeFactors n =
      {I | I.absNorm = n ∧ ∀ p : ℕ, p.Prime → ¬Ideal.span {(p : 𝓞 K)} ∣ I} := by
  ext I
  constructor
  · rintro ⟨hI, h⟩
    refine ⟨hI, fun p hp hd => ?_⟩
    have hN := map_dvd Ideal.absNorm hd
    rw [absNorm_scalar, hI] at hN
    exact h p (hp.mem_primeFactors ((dvd_pow_self p (finrank_pos (R := ℚ) (M := K)).ne').trans hN) hn) hd
  · rintro ⟨hI, h⟩
    exact ⟨hI, fun p hp => h p (Nat.prime_of_mem_primeFactors hp)⟩

end GlobalTheory
