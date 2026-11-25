module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PrimitiveIdealNorm
public import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section

open NumberField Module

namespace GlobalTheory

variable {K : Type*} [Field K] [NumberField K]

private abbrev scalar (K : Type*) [Field K] [NumberField K] (a : ℕ) : Ideal (𝓞 K) :=
  Ideal.span {(a : 𝓞 K)}

private theorem scalar_le (I : Ideal (𝓞 K)) {a : ℕ} (ha : I.absNorm = a) :
    scalar K a ≤ I := ha ▸ Ideal.span_singleton_absNorm_le I

private theorem scalar_coprime {a b : ℕ} (hab : a.Coprime b) :
    IsCoprime (scalar K a) (scalar K b) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr hab.cast

private theorem scalar_coprime_ideal {a b : ℕ} (hab : a.Coprime b) (I : Ideal (𝓞 K))
    (hI : I.absNorm = b) : IsCoprime (scalar K a) I :=
  Ideal.isCoprime_iff_sup_eq.mpr <| top_unique <|
    (scalar_coprime (K := K) hab).sup_eq.ge.trans (sup_le_sup_left (scalar_le I hI) _)

private theorem crt_mul {a b : ℕ} (hab : a.Coprime b) (I : Ideal (𝓞 K))
    (hn : I.absNorm = a * b) :
    (I ⊔ scalar K a) * (I ⊔ scalar K b) = I := by
  let A := scalar K a
  let B := scalar K b
  have hAB : A * B ≤ I := by
    rw [show A * B = scalar K (a * b) by simp [A, B, scalar, Ideal.span_singleton_mul_span_singleton]]
    exact scalar_le I hn
  have hsum : A * I ⊔ I * B = I := by
    rw [mul_comm A I, ← Ideal.mul_sup, (scalar_coprime (K := K) hab).sup_eq, ← Ideal.one_eq_top, mul_one]
  rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]
  apply le_antisymm
  · exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_right) (sup_le Ideal.mul_le_left hAB)
  · nth_rewrite 1 [← hsum]
    exact sup_le (le_trans le_sup_right le_sup_left) (le_trans le_sup_left le_sup_right)

private theorem left_norm {a b i j d : ℕ} (hab : a.Coprime b) (h : i * j = a * b)
    (hi : i ∣ a ^ d) (hj : j ∣ b ^ d) : i = a := by
  apply Nat.dvd_antisymm
  · exact ((hab.pow_left d).coprime_dvd_left hi).dvd_of_dvd_mul_right (h ▸ dvd_mul_right i j)
  · exact ((hab.pow_right d).coprime_dvd_right hj).dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right a b)

private theorem crt_norms {a b : ℕ} (hab : a.Coprime b) (I : Ideal (𝓞 K))
    (hn : I.absNorm = a * b) :
    (I ⊔ scalar K a).absNorm = a ∧ (I ⊔ scalar K b).absNorm = b := by
  have hd (t : ℕ) : (I ⊔ scalar K t).absNorm ∣ t ^ finrank ℚ K := by
    rw [← RingOfIntegers.rank K, ← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hp := (map_mul Ideal.absNorm _ _).symm.trans ((congrArg Ideal.absNorm (crt_mul hab I hn)).trans hn)
  exact ⟨left_norm hab hp (hd a) (hd b),
    left_norm hab.symm ((mul_comm _ _).trans (hp.trans (mul_comm _ _))) (hd b) (hd a)⟩

private theorem recover {a b : ℕ} (hab : a.Coprime b) {I J : Ideal (𝓞 K)}
    (hI : I.absNorm = a) (hJ : J.absNorm = b) : I * J ⊔ scalar K a = I := by
  rw [Ideal.mul_sup_eq_of_coprime_right (scalar_coprime_ideal hab J hJ).symm.sup_eq,
    sup_eq_left.mpr (scalar_le I hI)]

private theorem primitive_mul {a b : ℕ} (hab : a.Coprime b) {I J : Ideal (𝓞 K)}
    (hI : I.absNorm = a) (hJ : J.absNorm = b) {p : ℕ} (hp : p.Prime) :
    ¬ scalar K p ∣ I * J ↔ (¬ scalar K p ∣ I) ∧ ¬ scalar K p ∣ J := by
  constructor
  · exact fun h => ⟨fun hI => h (dvd_mul_of_dvd_left hI _), fun hJ => h (dvd_mul_of_dvd_right hJ _)⟩
  · rintro ⟨hi,hj⟩ hd
    by_cases hpa : p ∣ a
    · exact hi ((scalar_coprime_ideal (hab.coprime_dvd_left hpa) J hJ).dvd_of_dvd_mul_right hd)
    · exact hj ((scalar_coprime_ideal (hp.coprime_iff_not_dvd.mpr hpa) I hI).dvd_of_dvd_mul_left hd)

/-- The norm fibre with a fixed set of rational scalar primes sieved out.
The empty set gives the ordinary ideal norm fibre. -/
abbrev scalarFreeFibre (K : Type*) [Field K] [NumberField K] (S : Set ℕ) (n : ℕ) :
    Set (Ideal (𝓞 K)) :=
  {I | I.absNorm = n ∧ ∀ p ∈ S, ¬Ideal.span {(p : 𝓞 K)} ∣ I}

/-- Multiplication bijects coprime norm fibres, including after excluding any chosen
rational scalar primes. Its inverse splits `I` as `(I + (a))(I + (b))`. -/
@[no_expose] noncomputable def scalarFreeFibreMulEquiv (S : Set ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {a b : ℕ} (hab : a.Coprime b) :
    scalarFreeFibre K S a × scalarFreeFibre K S b ≃ scalarFreeFibre K S (a * b) where
  toFun := fun ⟨I,J⟩ => ⟨I.1 * J.1, (map_mul Ideal.absNorm _ _).trans
    (congrArg₂ (· * ·) I.2.1 J.2.1), fun p hp =>
      (primitive_mul hab I.2.1 J.2.1 (hS p hp)).mpr ⟨I.2.2 p hp, J.2.2 p hp⟩⟩
  invFun I :=
    let ha := (crt_norms hab I.1 I.2.1).1
    let hb := (crt_norms hab I.1 I.2.1).2
    let h (p : ℕ) (hp : p ∈ S) :=
      (primitive_mul hab ha hb (hS p hp)).mp
        (by rw [crt_mul hab I.1 I.2.1]; exact I.2.2 p hp)
    (⟨I.1 ⊔ scalar K a, ha, fun p hp => (h p hp).1⟩,
      ⟨I.1 ⊔ scalar K b, hb, fun p hp => (h p hp).2⟩)
  left_inv := fun ⟨I,J⟩ => Prod.ext (Subtype.ext <| recover hab I.2.1 J.2.1)
    (Subtype.ext <| (congrArg (· ⊔ scalar K b) (mul_comm I.1 J.1)).trans <| recover hab.symm J.2.1 I.2.1)
  right_inv := fun I => Subtype.ext (crt_mul hab I.1 I.2.1)

@[simp] theorem scalarFreeFibreMulEquiv_apply (S : Set ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {a b : ℕ} (hab : a.Coprime b) (I : scalarFreeFibre K S a) (J : scalarFreeFibre K S b) :
    (scalarFreeFibreMulEquiv S hS hab (I, J)).1 = I.1 * J.1 := by
  unfold scalarFreeFibreMulEquiv
  rfl

theorem ncard_scalarFreeFibre_mul (S : Set ℕ) (hS : ∀ p ∈ S, Nat.Prime p) {a b : ℕ}
    (hab : a.Coprime b) : (scalarFreeFibre K S (a * b)).ncard =
      (scalarFreeFibre K S a).ncard * (scalarFreeFibre K S b).ncard := by
  simpa only [Nat.card_coe_set_eq, Nat.card_prod] using
    (Nat.card_congr (scalarFreeFibreMulEquiv (K := K) S hS hab)).symm

/-- The actual primitive coefficients in the class-number bound are multiplicative. -/
theorem ncard_primitive_ideal_norm_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    (scalarSieveFibre K (a * b).primeFactors (a * b)).ncard =
      (scalarSieveFibre K a.primeFactors a).ncard * (scalarSieveFibre K b.primeFactors b).ncard := by
  rw [scalarSieveFibre_primeFactors K (mul_ne_zero ha hb),
    scalarSieveFibre_primeFactors K ha, scalarSieveFibre_primeFactors K hb]
  exact ncard_scalarFreeFibre_mul {p | p.Prime} (fun _ h => h) hab

private theorem ncard_scalarFreeFibre_one (S : Set ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    (scalarFreeFibre K S 1).ncard = 1 := by
  apply Set.ncard_eq_one.mpr
  refine ⟨⊤, Set.ext fun I => ⟨fun h => Ideal.absNorm_eq_one_iff.mp h.1, ?_⟩⟩
  rintro rfl
  refine ⟨Ideal.absNorm_eq_one_iff.mpr rfl, fun p hp hd => ?_⟩
  have h := map_dvd Ideal.absNorm hd
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Ideal.absNorm_eq_one_iff.mpr rfl] at h
  exact (hS p hp).not_dvd_one ((dvd_pow_self p (finrank_pos (R := ℚ) (M := K)).ne').trans h)

/-- The scalar-primitive coefficient of any positive norm is the product of its
prime-power coefficients (including norm one as the empty product). -/
theorem ncard_primitive_ideal_norm_prod {n : ℕ} (hn : n ≠ 0) :
    (scalarSieveFibre K n.primeFactors n).ncard =
      ∏ p ∈ n.primeFactors, (scalarSieveFibre K {p} (p ^ n.factorization p)).ncard := by
  let S : Set ℕ := {p | p.Prime}
  let f (m : ℕ) := (scalarFreeFibre K S m).ncard
  have h := Nat.multiplicative_factorization f
    (fun _ _ => ncard_scalarFreeFibre_mul S (fun _ h => h))
    (ncard_scalarFreeFibre_one S (fun _ h => h)) hn
  rw [scalarSieveFibre_primeFactors _ hn]
  change f n = _
  rw [h, Nat.prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  rw [← Nat.primeFactors_prime_pow hk hprime, scalarSieveFibre_primeFactors _ (pow_ne_zero _ hprime.ne_zero)]
  rfl

/-- Exact prime-power Euler factors use only ordinary norm counts. Removing a scalar
prime subtracts the unrestricted coefficient one field degree earlier. -/
theorem ncard_primitive_ideal_norm_euler {n : ℕ} (hn : n ≠ 0) :
    (scalarSieveFibre K n.primeFactors n).ncard =
      ∏ p ∈ n.primeFactors,
        ({I : Ideal (𝓞 K) | I.absNorm = p ^ n.factorization p}.ncard -
          if finrank ℚ K ≤ n.factorization p then
            {I : Ideal (𝓞 K) | I.absNorm = p ^ (n.factorization p - finrank ℚ K)}.ncard else 0) := by
  rw [ncard_primitive_ideal_norm_prod hn]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have empty_fibre (k : ℕ) : scalarSieveFibre K ∅ k = {I | I.absNorm = k} := by
    ext; simp [scalarSieveFibre]
  have h := ncard_scalarSieveFibre_insert K ∅ hprime (by simp) (p ^ n.factorization p)
  simp only [Finset.insert_empty, empty_fibre, Nat.pow_dvd_pow_iff_le_right hprime.one_lt] at h
  rw [h]
  split_ifs with hle
  · rw [Nat.pow_div hle hprime.pos]
  · rfl

end GlobalTheory
