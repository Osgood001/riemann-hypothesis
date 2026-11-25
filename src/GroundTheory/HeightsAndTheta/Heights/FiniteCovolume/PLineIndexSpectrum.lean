module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineIndexNeZero
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

import Mathlib.Tactic.Simproc.Factors

@[expose] public section

open NumberField

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

/-- Exponents allowed at `p`: sums of the residue degrees of primes above `p`.
Repetitions are allowed, even for ramified primes. -/
noncomputable def residueExponents (E : Type*) [Field E] [NumberField E] (p : ℕ) : AddSubmonoid ℕ :=
  AddSubmonoid.closure (Set.range fun P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) =>
    P.1.inertiaDeg ℤ)

variable {E : Type*} [Field E] [NumberField E]

private theorem factorization_absNorm_mem (I : Ideal (𝓞 E)) (p : ℕ) :
    I.absNorm.factorization p ∈ residueExponents E p := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ I h => simp [Ideal.isUnit_iff.mp h]
  | h₃ I P hI hP ih =>
    rw [map_mul, Nat.factorization_mul
      (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero) (Ideal.absNorm_eq_zero_iff.not.mpr hI),
      Finsupp.add_apply]
    apply add_mem _ ih
    have : P.IsPrime := Ideal.isPrime_of_prime hP
    have : NeZero P := ⟨hP.ne_zero⟩
    let q := (P.under ℤ).absNorm
    have hq : q.Prime := Nat.absNorm_under_prime P
    have : P.LiesOver (Ideal.span {(q : ℤ)}) := Int.liesOver_span_absNorm P
    rw [← Ideal.pow_inertiaDeg q P, hq.factorization_pow]
    by_cases heq : q = p
    · subst p
      simp only [Finsupp.single_eq_same]
      exact AddSubmonoid.subset_closure ⟨Ideal.primesOver.mk _ P, rfl⟩
    · simp [Finsupp.single_eq_of_ne (Ne.symm heq)]

private theorem pow_mem_absNorm (p k : ℕ) (h : k ∈ residueExponents E p) :
    p ^ k ∈ MonoidHom.mrange (Ideal.absNorm (S := 𝓞 E)) := by
  induction h using AddSubmonoid.closure_induction with
  | mem n hn =>
    obtain ⟨P, rfl⟩ := hn
    exact ⟨P.1, (Ideal.pow_inertiaDeg p P.1).symm⟩
  | zero => simp
  | add a b _ _ ha hb => simpa [pow_add] using mul_mem ha hb

/-- The possible line indices are characterized prime by prime; no class-number or
Galois hypothesis is needed. -/
theorem exists_lineIndex_iff_local (n : ℕ) :
    (∃ La : AddSubgroup E, IsLattice E La ∧ (1 : E) ∈ La ∧ lineIndex E La 1 = n) ↔
    n ≠ 0 ∧ ∀ p ∈ n.primeFactors, n.factorization p ∈ residueExponents E p := by
  rw [exists_lineIndex_iff_ideal_norm]
  constructor
  · rintro ⟨I, hI, rfl⟩
    exact ⟨Ideal.absNorm_eq_zero_iff.not.mpr hI, fun p _ => factorization_absNorm_mem I p⟩
  · rintro ⟨hn, h⟩
    have hm : n ∈ MonoidHom.mrange (Ideal.absNorm (S := 𝓞 E)) := by
      rw [← Nat.prod_factorization_pow_eq_self hn]
      exact Submonoid.prod_mem _ fun p hp => pow_mem_absNorm _ _ (h p hp)
    obtain ⟨I, he⟩ := hm
    exact ⟨I, Ideal.absNorm_eq_zero_iff.not.mp (he ▸ hn), he⟩

/-- On an arbitrary lattice line the local tests are necessary, even when the
ambient space is not one dimensional. -/
theorem lineIndex_factorization_mem {W : Type*} [AddCommGroup W] [Module E W]
    (La : AddSubgroup W) (x : W) (hL : IsLattice E La) (hx : x ∈ La) (hx0 : x ≠ 0) (p : ℕ) :
    (lineIndex E La x).factorization p ∈ residueExponents E p := by
  obtain ⟨I, hI, -⟩ := lineIndex_eq_ideal_norm La x hL hx hx0
  rw [hI.2.2]
  exact factorization_absNorm_mem I p

/-- To reduce an upper bound `B` to one it suffices to rule out norms of prime ideals
at most `B`; arbitrary ideals need not be checked. -/
theorem lineIndex_eq_one_of_residue_gap {W : Type*} [AddCommGroup W] [Module E W]
    (La : AddSubgroup W) (x : W) (hL : IsLattice E La) (hx : x ∈ La) (hx0 : x ≠ 0)
    {B : ℕ} (hB : lineIndex E La x ≤ B)
    (gap : ∀ p ≤ B, p.Prime → ∀ P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E),
      B < p ^ P.1.inertiaDeg ℤ) : lineIndex E La x = 1 := by
  obtain ⟨I, hI, -⟩ := lineIndex_eq_ideal_norm La x hL hx hx0
  rw [hI.2.2] at hB ⊢
  by_contra! h
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
  have hpos := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  obtain ⟨P, hP, hunder, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hpd
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hunder.symm⟩
  have hlarge := gap p ((Nat.le_of_dvd hpos hpd).trans hB) hp ⟨P, hP.isPrime, this⟩
  rw [Ideal.pow_inertiaDeg] at hlarge
  exact (Nat.not_lt_of_ge ((Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)).trans hB)) hlarge

open NumberField.RingOfIntegers in
/-- When `p` does not divide the exponent of the additive quotient by `ℤ[θ]`,
the local test uses the degrees of the irreducible factors of the defining polynomial modulo `p`. -/
theorem residueExponents_eq_factorDegrees (θ : 𝓞 E) {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ exponent θ) : residueExponents E p =
    AddSubmonoid.closure (Set.range fun Q : monicFactorsMod θ p => Q.1.natDegree) := by
  unfold residueExponents
  congr 1
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  ext n
  constructor
  · rintro ⟨P, rfl⟩
    refine ⟨e P, ?_⟩
    simpa [e] using (NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      hp (e P).2).symm
  · rintro ⟨Q, rfl⟩
    exact ⟨e.symm Q,
      NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp Q.2⟩

/-- In a Galois field all residue degrees above a prime coincide, so local
membership is exactly divisibility. This includes ramified primes. -/
theorem residueExponents_galois [IsGalois ℚ E] {p k : ℕ} [Fact p.Prime] :
    k ∈ residueExponents E p ↔ (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 E) ∣ k := by
  let q := Ideal.span {(p : ℤ)}
  have hf (P : q.primesOver (𝓞 E)) : q.inertiaDegIn (𝓞 E) = P.1.inertiaDeg ℤ :=
    Ideal.inertiaDegIn_eq_inertiaDeg q P.1 Gal(E/ℚ)
  constructor
  · intro h
    induction h using AddSubmonoid.closure_induction with
    | mem n hn => obtain ⟨P, rfl⟩ := hn; exact (hf P) ▸ dvd_refl _
    | zero => exact dvd_zero _
    | add a b _ _ ha hb => exact dvd_add ha hb
  · rintro ⟨j, rfl⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)))
    have hm : P.1.inertiaDeg ℤ ∈ residueExponents E p := AddSubmonoid.subset_closure ⟨P, rfl⟩
    rw [← hf P] at hm
    simpa [mul_comm, nsmul_eq_mul] using (residueExponents E p).nsmul_mem hm j

/-- In a cyclotomic field this test uses only arithmetic of natural numbers.
At a prime dividing the conductor, remove its entire prime-power part first. -/
theorem exists_lineIndex_iff_cyclotomic {c : ℕ} [NeZero c] [IsCyclotomicExtension {c} ℚ E]
    (n : ℕ) :
    (∃ La : AddSubgroup E, IsLattice E La ∧ (1 : E) ∈ La ∧ lineIndex E La 1 = n) ↔
    n ≠ 0 ∧ ∀ p ∈ n.primeFactors,
      Nat.ModEq (c / p ^ c.factorization p) (p ^ n.factorization p) 1 := by
  have : IsGalois ℚ E := IsCyclotomicExtension.isGalois {c} ℚ E
  rw [exists_lineIndex_iff_local]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro p
  apply forall_congr'
  intro h
  have hp := Nat.prime_of_mem_primeFactors h
  have : Fact p.Prime := ⟨hp⟩
  rw [residueExponents_galois]
  let m := c / p ^ c.factorization p
  have hpc : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (NeZero.ne c)
  have he : (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 E) = orderOf (p : ZMod m) := by
    have hc := (Nat.ordProj_mul_ordCompl_eq_self c p).symm
    cases e : c.factorization p with
    | zero =>
      have hm : m = c := by simp [m, e]
      rw [hm] at hpc ⊢
      exact IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p E hpc
    | succ j =>
      exact IsCyclotomicExtension.Rat.inertiaDegIn_eq c E (k := j)
        (by simpa only [e, m] using hc) hpc
  rw [he, orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rfl

/-- Both inclusions matter: through eight, seven and eight actually occur in the
seventh cyclotomic field, whereas none of two through six does. -/
theorem exists_lineIndex_seventh_le_eight [IsCyclotomicExtension {7} ℚ E] {n : ℕ} (hn : n ≤ 8) :
    (∃ La : AddSubgroup E, IsLattice E La ∧ (1 : E) ∈ La ∧ lineIndex E La 1 = n) ↔
    n = 1 ∨ n = 7 ∨ n = 8 := by
  rw [exists_lineIndex_iff_cyclotomic (c := 7)]
  interval_cases n <;>
    simp only [Nat.primeFactors, ← Nat.primeFactorsList_count_eq, Nat.primeFactorsList_ofNat] <;>
    decide

end GroundTheory.Heights₂.Heights.FiniteCovolume
