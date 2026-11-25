module

public import Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded

@[expose] public section

namespace Formalism.LogVandermondeBounds.StandardLattice

open Polynomial

/-- Exact prime-power torsion forces its top cyclotomic factor. -/
private theorem cyclotomic_prime_pow_dvd_minpoly {A : Type*} [Ring A] [Algebra ℚ A]
    {f : A} {p k : ℕ} (hp : p.Prime) (hpow : f ^ (p ^ (k + 1)) = 1)
    (hprev : f ^ (p ^ k) ≠ 1) : cyclotomic (p ^ (k + 1)) ℚ ∣ minpoly ℚ f := by
  let _ : Fact p.Prime := ⟨hp⟩
  by_contra h
  have hdvd : minpoly ℚ f ∣ cyclotomic (p ^ (k + 1)) ℚ * (X ^ p ^ k - 1) := by
    rw [cyclotomic_prime_pow_mul_X_pow_sub_one]
    exact minpoly.dvd _ _ (by simp [hpow])
  have hirr := cyclotomic.irreducible_rat (pow_pos hp.pos (k + 1))
  have he := minpoly.dvd_iff.1 ((hirr.coprime_iff_not_dvd.2 h).symm.dvd_of_dvd_mul_left hdvd)
  exact hprev (by simpa [sub_eq_zero] using he)

/-- The full prime-power order is visible in the rational dimension bound. -/
private theorem prime_pow_totient_le_finrank {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {f : V →ₗ[ℚ] V} {p k : ℕ} (hp : p.Prime)
    (hpow : f ^ (p ^ (k + 1)) = 1) (hprev : f ^ (p ^ k) ≠ 1) :
    p ^ k * (p - 1) ≤ Module.finrank ℚ V := by
  have h := natDegree_le_of_dvd
    ((cyclotomic_prime_pow_dvd_minpoly hp hpow hprev).trans f.minpoly_dvd_charpoly)
    f.charpoly_monic.ne_zero
  simpa [LinearMap.charpoly_natDegree, natDegree_cyclotomic, Nat.totient_prime_pow hp (Nat.succ_pos k)] using h

/-- A matrix of exact order p^(k+1) needs at least φ(p^(k+1)) rational dimensions. -/
theorem primePowerOrderFinrank (K : Type*) [Field K] [NumberField K]
    (n : ℕ) {p k : ℕ} (A : Matrix (Fin n) (Fin n) K) (hp : p.Prime)
    (hpow : A ^ (p ^ (k + 1)) = 1) (hprev : A ^ (p ^ k) ≠ 1) :
    p ^ k * (p - 1) ≤ Module.finrank ℚ K * n := by
  let r : Module.End K (Fin n → K) →* Module.End ℚ (Fin n → K) :=
    ⟨⟨fun f => f.restrictScalars ℚ, rfl⟩, fun _ _ => rfl⟩
  let φ := r.comp (Matrix.toLinAlgEquiv' (n := Fin n) (R := K)).toMonoidHom
  have hinj : Function.Injective φ :=
    (LinearMap.restrictScalars_injective ℚ).comp Matrix.toLinAlgEquiv'.injective
  have h := prime_pow_totient_le_finrank (f := φ A) hp
    (by rw [← map_pow, hpow, map_one])
    (fun e => hprev (hinj (by rwa [map_pow, map_one])))
  simpa [Module.finrank_pi_fintype, mul_comm] using h

theorem primeOrderFinrank : PrimeOrderFinrank := by
  intro K _ _ n p A hp hx hA
  simpa using primePowerOrderFinrank K n (k := 0) A hp (by simpa) (by simpa)

/-- An arbitrary prime-primary element is killed by the uniform prime power
at which the top cyclotomic degree would exceed the ambient dimension. -/
theorem primePowerTorsionBound {K : Type*} [Field K] [NumberField K]
    {n p j : ℕ} (hp : p.Prime) (hdim : Module.finrank ℚ K * n < p ^ j * (p - 1))
    (x : GL (Fin n) K) {a : ℕ} (hx : x ^ p ^ a = 1) : x ^ p ^ j = 1 := by
  induction a with
  | zero => simp [show x = 1 by simpa using hx]
  | succ a ih =>
    by_cases h : a < j
    · exact orderOf_dvd_iff_pow_eq_one.1 $ (orderOf_dvd_iff_pow_eq_one.2 hx).trans
        (pow_dvd_pow _ (Nat.succ_le_of_lt h))
    · apply ih
      by_contra hn
      have hu := primePowerOrderFinrank K n (k := a) x.val hp
        (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hx)
        (fun e => hn (Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using e)))
      have hle := Nat.mul_le_mul_right (p - 1) (Nat.pow_le_pow_right hp.pos (Nat.le_of_not_gt h))
      exact hdim.not_ge (hle.trans hu)

/-- No finiteness assumption is necessary to bound the exponent of a linear p-group. -/
theorem pGroupExponentDvd {K : Type*} [Field K] [NumberField K] {n p j : ℕ} (hp : p.Prime)
    (hdim : Module.finrank ℚ K * n < p ^ j * (p - 1))
    (Γ : Subgroup (GL (Fin n) K)) (hΓ : IsPGroup p Γ) : Monoid.exponent Γ ∣ p ^ j := by
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.2
  intro x
  obtain ⟨a, ha⟩ := hΓ x
  apply Subtype.ext
  exact primePowerTorsionBound hp hdim x.val (congrArg Subtype.val ha)

/-- Multiplication by a primitive root attains the dimension bound over ℚ. -/
theorem primePowerMatrixAttained (p k : ℕ) (hp : p.Prime) :
    ∃ A : GL (Fin (p ^ k * (p - 1))) ℚ, orderOf A = p ^ (k + 1) := by
  let n := p ^ (k + 1)
  let _ : NeZero n := ⟨(pow_pos hp.pos _).ne'⟩
  let _ : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let z := IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)
  let μ := Algebra.lmul ℚ (CyclotomicField n ℚ)
  have hz : orderOf (μ z) = n :=
    (orderOf_injective μ.toMonoidHom Algebra.lmul_injective z).trans
      (IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)).eq_orderOf.symm
  have hd := (IsCyclotomicExtension.finrank (n := n) (CyclotomicField n ℚ)
    (cyclotomic.irreducible_rat (NeZero.pos n))).trans (Nat.totient_prime_pow hp (Nat.succ_pos k))
  let e := LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq ℚ _ hd)
  have hA := (orderOf_injective e.toMonoidHom e.injective (μ z)).trans hz
  have hfin : IsOfFinOrder (e (μ z)) := orderOf_pos_iff.1 (hA.trans_gt (pow_pos hp.pos _))
  exact ⟨hfin.unit, orderOf_units.symm.trans hA⟩

end Formalism.LogVandermondeBounds.StandardLattice
