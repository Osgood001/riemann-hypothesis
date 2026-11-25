import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

theorem exists_denom_mul_mem_radical {A : Type*} [CommRing A]
    (D P : Ideal A) [P.IsPrime] (f : A)
    (h : ∀ Q : Ideal A, Q.IsPrime → D ≤ Q → Q ≤ P → f ∈ Q) :
    ∃ s ∉ P, s * f ∈ D.radical := by
  let S := Localization.AtPrime P
  let a := algebraMap A S
  have hf : a f ∈ (D.map a).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hDQ, hQ⟩
    apply h (Q.comap a) (Ideal.comap_isPrime a Q) (Ideal.map_le_iff_le_comap.mp hDQ)
    intro x hx
    by_contra hxP
    exact hQ.ne_top <| Ideal.eq_top_of_isUnit_mem _ hx
      (IsLocalization.map_units S (⟨x, hxP⟩ : P.primeCompl))
  obtain ⟨n, hn⟩ := hf
  rw [← map_pow] at hn
  obtain ⟨s, hs, hsf⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl S D (f ^ n)).mp hn
  refine ⟨s, hs, n + 1, ?_⟩
  have he : (s * f) ^ (n + 1) = s ^ n * f * (s * f ^ n) := by ring
  rw [he]
  exact D.mul_mem_left _ hsf

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
