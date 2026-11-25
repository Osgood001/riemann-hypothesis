module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

namespace GridInterpolation

/-- A finite LCM of nonzero natural numbers needs at most one witness per distinct prime. -/
private theorem exists_subset_lcm_card_le_primeFactors (S : Finset ℕ)
    (hS : ∀ x ∈ S, x ≠ 0) :
    ∃ T ⊆ S, T.card ≤ (S.lcm id).primeFactors.card ∧ T.lcm id = S.lcm id := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, Finset.Subset.rfl, by simp, rfl⟩
  have hL : S.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr hS
  have hmax (p : ℕ) : ∃ x ∈ S, (S.lcm id).factorization p = x.factorization p := by
    rw [Finset.factorization_lcm (f := id) hS]
    exact S.exists_mem_eq_sup hne _
  let pick (p : ℕ) := Classical.choose (hmax p)
  have hpick (p : ℕ) : pick p ∈ S ∧ (S.lcm id).factorization p = (pick p).factorization p :=
    Classical.choose_spec (hmax p)
  let T := (S.lcm id).primeFactors.image pick
  have hsub : T ⊆ S := by
    intro t ht
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
    exact (hpick p).1
  refine ⟨T, hsub, Finset.card_image_le, Nat.dvd_antisymm (Finset.lcm_mono hsub) ?_⟩
  have hT : T.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr fun t ht => hS t (hsub ht)
  apply (Nat.factorization_le_iff_dvd hL hT).mp
  intro p
  by_cases hmem : p ∈ (S.lcm id).primeFactors
  · rw [(hpick p).2]
    have hin : pick p ∈ T := Finset.mem_image_of_mem pick hmem
    exact (Nat.factorization_le_iff_dvd (hS _ (hpick p).1) hT).mpr
      (Finset.dvd_lcm (f := id) hin) p
  · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hmem
    rw [hmem]
    exact Nat.zero_le _

/-- Finitely many roots generate, by products and nonnegative powers alone, a root of the LCM order. -/
private theorem exists_root_of_lcm (s : Finset ℂ) (hs : ∀ x ∈ s, orderOf x ≠ 0) :
    ∃ z : ℂ, IsPrimitiveRoot z (s.lcm orderOf) ∧
      ∀ H : Submonoid ℂ, (s : Set ℂ) ⊆ H → z ∈ H := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, IsPrimitiveRoot.one, fun H _ => H.one_mem⟩
  | insert a s _ ih =>
    have hs' : ∀ x ∈ s, orderOf x ≠ 0 := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨b, hb, hmem⟩ := ih hs'
    have h := (IsPrimitiveRoot.orderOf a).pow_mul_pow_lcm hb
      (hs a (Finset.mem_insert_self ..)) (Finset.lcm_ne_zero_iff.mpr hs')
    refine ⟨_, by simpa [Finset.lcm_insert, lcm_eq_nat_lcm] using h, fun H hS => ?_⟩
    apply H.mul_mem (H.pow_mem (hS (Finset.mem_insert_self ..)) _)
    exact H.pow_mem (hmem H fun x hx => hS (Finset.mem_insert_of_mem hx)) _

/-- One actual value per prime divisor of the true joint order suffices, even for an
infinitely indexed collection. The single primitive root need not itself be an input. -/
private theorem exists_sparse_root_tests (S : Set ℂ) {R : ℕ} (hR : R ≠ 0)
    (hS : ∀ z ∈ S, z ^ R = 1) :
    ∃ e : ℕ, e ∣ R ∧ ∃ T : Finset ℂ, (T : Set ℂ) ⊆ S ∧ T.card ≤ e.primeFactors.card ∧ T.lcm orderOf = e ∧
      ∃ ζ : ℂ, IsPrimitiveRoot ζ e ∧ ∀ H : Submonoid ℂ,
        (ζ ∈ H ↔ S ⊆ H) ∧ ((T : Set ℂ) ⊆ H ↔ S ⊆ H) := by
  classical
  let A := R.divisors.filter (fun n => ∃ z ∈ S, orderOf z = n)
  have hA n : n ∈ A ↔ ∃ z ∈ S, orderOf z = n := by
    constructor
    · exact fun hn => (Finset.mem_filter.mp hn).2
    · rintro ⟨z, hz, rfl⟩
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨orderOf_dvd_of_pow_eq_one (hS z hz), hR⟩,
        z, hz, rfl⟩
  have hdvd n (hn : n ∈ A) : n ∣ R := (Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1).1
  obtain ⟨Q, hQ, hcard, he⟩ := exists_subset_lcm_card_le_primeFactors A
    (fun n hn => ne_zero_of_dvd_ne_zero hR (hdvd n hn))
  let pick (n : ℕ) := if h : ∃ z ∈ S, orderOf z = n then h.choose else 1
  have hpick n (hn : n ∈ A) : pick n ∈ S ∧ orderOf (pick n) = n := by
    have hw := (hA n).mp hn
    simpa [pick, hw] using hw.choose_spec
  let T := Q.image pick
  have hsub : (T : Set ℂ) ⊆ S := by
    rintro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    exact (hpick n (hQ hn)).1
  have hT : T.lcm orderOf = A.lcm id := by
    rw [Finset.lcm_image]
    exact (Finset.lcm_congr rfl fun n hn => (hpick n (hQ hn)).2).trans he
  have heR : A.lcm id ∣ R := Finset.lcm_dvd hdvd
  have : NeZero (A.lcm id) := ⟨ne_zero_of_dvd_ne_zero hR heR⟩
  obtain ⟨ζ, hζ, hzmem⟩ := exists_root_of_lcm T fun z hz =>
    ne_zero_of_dvd_ne_zero hR (orderOf_dvd_of_pow_eq_one (hS z (hsub hz)))
  rw [hT] at hζ
  refine ⟨A.lcm id, heR, T, hsub, Finset.card_image_le.trans hcard, hT, ζ, hζ, fun H => ?_⟩
  have hpow (h : ζ ∈ H) : S ⊆ H := by
    intro z hz
    have hd : orderOf z ∣ A.lcm id := Finset.dvd_lcm (f := id) ((hA _).2 ⟨z, hz, rfl⟩)
    obtain ⟨j, _, hj⟩ := hζ.eq_pow_of_pow_eq_one (orderOf_dvd_iff_pow_eq_one.mp hd)
    exact hj ▸ H.pow_mem h j
  exact ⟨⟨hpow, fun h => hzmem H (hsub.trans h)⟩, ⟨fun h => hpow (hzmem H h), hsub.trans⟩⟩

/-- The order is the least annihilator, and the same original samples work for all complex fields. -/
theorem exists_sparse_root_field_tests (S : Set ℂ) {R : ℕ} (hR : R ≠ 0) (hS : ∀ z ∈ S, z ^ R = 1) :
    ∃ e : ℕ, e ∣ R ∧ (∀ m, e ∣ m ↔ ∀ z ∈ S, z ^ m = 1) ∧
      ∃ T : Finset ℂ, (T : Set ℂ) ⊆ S ∧ T.card ≤ e.primeFactors.card ∧ T.lcm orderOf = e ∧
      ∃ ζ : ℂ, IsPrimitiveRoot ζ e ∧ ∀ F : IntermediateField ℚ ℂ,
        (ζ ∈ F ↔ S ⊆ F) ∧ ((T : Set ℂ) ⊆ F ↔ S ⊆ F) := by
  obtain ⟨e, he, T, hT, hc, horder, ζ, hζ, hall⟩ := exists_sparse_root_tests S hR hS
  refine ⟨e, he, fun m => ?_, T, hT, hc, horder, ζ, hζ, fun F => hall F.toSubalgebra.toSubsemiring.toSubmonoid⟩
  let H : Submonoid ℂ :=
    { carrier := {z | z ^ m = 1}
      one_mem' := one_pow m
      mul_mem' := fun ha hb => (mul_pow _ _ m).trans ((congrArg₂ (· * ·) ha hb).trans (one_mul 1)) }
  exact (hζ.pow_eq_one_iff_dvd m).symm.trans (hall H).1

end GridInterpolation
