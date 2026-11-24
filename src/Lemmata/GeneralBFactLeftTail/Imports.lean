module

public import Mathlib

@[expose] public section

open NumberField IsDedekindDomain Matrix

namespace Bl.general_b_fact_left_tail

variable {F : Type} [Field F] [NumberField F]

theorem goal1 (g : ℕ) (hg : g.Prime) : ∃ v : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ v.asIdeal := by
  have hP : (Ideal.span {(g : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by aesop)).2 (Nat.prime_iff_prime_int.mp hg)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 F)
    (Ideal.span {(g : ℤ)}) ⊥ (by simp)
  have hgQ : (g : 𝓞 F) ∈ Q := by
    have h1 : (g : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 F)) := by
      rw [← Ideal.under_def, hQc]
      exact Ideal.subset_span rfl
    simpa using h1
  refine ⟨⟨Q, hQ, ?_⟩, hgQ⟩
  intro h
  exact hg.ne_zero (by simp_all)

end Bl.general_b_fact_left_tail
