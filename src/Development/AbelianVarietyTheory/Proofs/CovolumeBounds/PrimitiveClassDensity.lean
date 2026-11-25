module
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

/-! Natural density of integral ideals in a prescribed ideal class with no
rational prime scalar factor. For field degree d > 1 the relative density is
1 / ζ(d), independent of the class and of the splitting of rational primes. -/

@[expose] public section
open NumberField NumberField.InfinitePlace NumberField.Units Module Finset Filter
open scoped nonZeroDivisors Topology Real

namespace GlobalTheory
variable (K : Type*) [Field K] [NumberField K]

-- The class-wise leading constant in Mathlib’s unsieved ideal count.
local notation "classDensity" =>
  2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K /
    (torsionOrder K * Real.sqrt |discr K|)

/-- Integral ideals in a fixed class, under a real norm cutoff, avoiding
rational scalar multiples at the finite set S. -/
def scalarSievedClass (C : ClassGroup (𝓞 K)) (S : Finset ℕ) (x : ℝ) : Set (Ideal (𝓞 K))⁰ :=
  {I | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x ∧ ClassGroup.mk0 I = C ∧
    ∀ q ∈ S, ¬ Ideal.span {(q : 𝓞 K)} ∣ (I : Ideal (𝓞 K))}

private theorem finite_scalarSievedClass (C : ClassGroup (𝓞 K)) (S : Finset ℕ) (x : ℝ) :
    (scalarSievedClass K C S x).Finite :=
  (Ring.HasFiniteQuotients.finite_absNorm_le₀ (S := 𝓞 K) ⌈x⌉₊).subset
    fun _ h => Nat.cast_le.mp (h.1.trans (Nat.le_ceil x))

theorem ncard_scalarSievedClass_insert (C : ClassGroup (𝓞 K)) (S : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hS : ∀ q ∈ S, q.Coprime p) (x : ℝ) :
    (scalarSievedClass K C (insert p S) x).ncard +
      (scalarSievedClass K C S (x / (p : ℝ) ^ finrank ℚ K)).ncard =
      (scalarSievedClass K C S x).ncard := by
  classical
  let P : Ideal (𝓞 K) := Ideal.span {(p : 𝓞 K)}
  have hP : P ≠ 0 := by simpa [P] using (Nat.cast_ne_zero.mpr hp.ne_zero : (p : 𝓞 K) ≠ 0)
  let A : (Ideal (𝓞 K))⁰ := ⟨P, mem_nonZeroDivisors_of_ne_zero hP⟩
  have hC : ClassGroup.mk0 A = 1 := (ClassGroup.mk0_eq_one_iff A.2).mpr ⟨_, rfl⟩
  have hN (J : (Ideal (𝓞 K))⁰) :
      (Ideal.absNorm ((A * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) =
        (p : ℝ) ^ finrank ℚ K * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    change (Ideal.absNorm (P * (J : Ideal (𝓞 K))) : ℝ) = _
    simp only [P, map_mul, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Nat.cast_mul, Nat.cast_pow]
  have hpos : 0 < (p : ℝ) ^ finrank ℚ K := pow_pos (by exact_mod_cast hp.pos) _
  have hcop {q : ℕ} (hq : q ∈ S) : IsCoprime (Ideal.span {(q : 𝓞 K)}) P := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    simpa only [map_natCast] using (hS q hq).isCoprime.map (Int.castRingHom (𝓞 K))
  let T := scalarSievedClass K C S x
  let D := {I ∈ T | P ∣ (I : Ideal (𝓞 K))}
  have hsub : D ⊆ T := fun _ h => h.1
  have hnew : scalarSievedClass K C (insert p S) x = T \ D := by
    ext I
    simp only [scalarSievedClass, T, D, P, Set.mem_sdiff, Set.mem_ofPred_eq, mem_insert]
    aesop
  have hD : D = (fun J => A * J) '' scalarSievedClass K C S (x / (p : ℝ) ^ finrank ℚ K) := by
    ext I
    constructor
    · rintro ⟨⟨hNorm, hClass, hfree⟩, J, hIJ⟩
      have hJ : J ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero I (by simpa [h] using hIJ)
      let J' : (Ideal (𝓞 K))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
      have he : I = A * J' := Subtype.ext hIJ
      refine ⟨J', ⟨(le_div_iff₀ hpos).mpr ?_, ?_, fun q hq hd =>
        hfree q hq (hIJ ▸ dvd_mul_of_dvd_right hd P)⟩, he.symm⟩
      · rw [he, hN] at hNorm
        rwa [mul_comm]
      · simpa only [he, map_mul, hC, one_mul] using hClass
    · rintro ⟨J, ⟨hNorm, hClass, hfree⟩, rfl⟩
      refine ⟨⟨?_, by simpa only [map_mul, hC, one_mul] using hClass, fun q hq h =>
        hfree q hq ((hcop hq).dvd_of_dvd_mul_left h)⟩, dvd_mul_right P _⟩
      rw [hN, mul_comm]
      exact (le_div_iff₀ hpos).mp hNorm
  rw [hnew, ← Set.ncard_image_of_injective (scalarSievedClass K C S _) (mul_right_injective A), ← hD]
  exact Set.ncard_sdiff_add_ncard_of_subset hsub (finite_scalarSievedClass K C S x)

/-- The loss from finitely many rational scalar primes is identical in each ideal class. -/
theorem tendsto_scalarSievedClass (C : ClassGroup (𝓞 K)) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Tendsto (fun x : ℝ => ((scalarSievedClass K C S x).ncard : ℝ) / x) atTop
      (𝓝 (classDensity * ∏ p ∈ S, (1 - ((p : ℝ) ^ finrank ℚ K)⁻¹))) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa only [scalarSievedClass, forall_const, Finset.notMem_empty, false_implies,
      and_true, prod_empty, mul_one, ← Nat.card_coe_set_eq, Set.coe_eq_subtype, Set.mem_ofPred_eq] using
      Ideal.tendsto_norm_le_and_mk_eq_div_atTop K C
  | @insert p S hpS ih =>
    have hp := hS p (mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hcop : ∀ q ∈ S, q.Coprime p := fun q hq => (Nat.coprime_primes (hS' q hq) hp).mpr
      (fun h => hpS (h ▸ hq))
    set a := (p : ℝ) ^ finrank ℚ K
    have ha : 0 < a := pow_pos (by exact_mod_cast hp.pos) _
    have shifted := (ih hS').comp (Tendsto.atTop_div_const ha (tendsto_id (α := ℝ)))
    have H := (ih hS').sub (shifted.div_const a)
    convert H using 1
    · ext x
      have eqn := ncard_scalarSievedClass_insert K C S hp hcop x
      have eqr := congrArg (fun n : ℕ => (n : ℝ)) eqn
      push_cast at eqr
      simp only [Function.comp_apply, id_eq]
      change _ = _ - _ / (x / a) / a
      rw [div_div, div_mul_cancel₀ _ ha.ne']
      rw [← sub_div]
      congr 1
      exact (eq_sub_iff_add_eq).mpr eqr
    · congr 1
      rw [prod_insert hpS, div_eq_mul_inv]
      ring

/-- A uniform linear envelope, including below the first nonzero ideal norm. -/
private theorem exists_class_count_le_mul (C : ClassGroup (𝓞 K)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 0 ≤ x →
      ((scalarSievedClass K C ∅ x).ncard : ℝ) ≤ B * x := by
  let c : ℝ := classDensity
  have hlim : Tendsto (fun x : ℝ => ((scalarSievedClass K C ∅ x).ncard : ℝ) / x)
      atTop (𝓝 c) := by simpa [c] using tendsto_scalarSievedClass K C ∅ (by simp)
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (lt_add_one c)))
  let t := max A 1
  let B := max (max (c + 1) 1) ((scalarSievedClass K C ∅ t).ncard : ℝ)
  have hB : 1 ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨B, zero_lt_one.trans_le hB, fun x hx => ?_⟩
  by_cases hx1 : x < 1
  · have he : scalarSievedClass K C ∅ x = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro I hi
      have hOne : (1 : ℝ) ≤ Ideal.absNorm (I : Ideal (𝓞 K)) := by
        exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
      exact (not_le_of_gt hx1) (hOne.trans hi.1)
    simpa only [he, Set.ncard_empty, Nat.cast_zero] using mul_nonneg (zero_le_one.trans hB) hx
  by_cases hxt : t ≤ x
  · have hxpos : 0 < x := by linarith
    have hbound : ((scalarSievedClass K C ∅ x).ncard : ℝ) ≤ (c + 1) * x :=
      (div_le_iff₀ hxpos).mp ((hA x ((le_max_left A 1).trans hxt)).le)
    exact hbound.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hx)
  · have hsub : scalarSievedClass K C ∅ x ⊆ scalarSievedClass K C ∅ t := fun _ hi =>
      ⟨hi.1.trans (le_of_not_ge hxt), hi.2⟩
    have hle := Set.ncard_le_ncard hsub (finite_scalarSievedClass K C ∅ t)
    calc ((scalarSievedClass K C ∅ x).ncard : ℝ)
      _ ≤ ((scalarSievedClass K C ∅ t).ncard : ℝ) := by exact_mod_cast hle
      _ ≤ B := le_max_right _ _
      _ ≤ B * x := le_mul_of_one_le_right (zero_le_one.trans hB) (le_of_not_gt hx1)


/-- Nonzero integral ideals in a fixed ideal class with no rational scalar prime factor. -/
def scalarPrimitiveClass (C : ClassGroup (𝓞 K)) (x : ℝ) : Set (Ideal (𝓞 K))⁰ :=
  {I | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x ∧ ClassGroup.mk0 I = C ∧
    ∀ p : ℕ, p.Prime → ¬ Ideal.span {(p : 𝓞 K)} ∣ (I : Ideal (𝓞 K))}

private theorem scalarSieve_finite_loss (C : ClassGroup (𝓞 K)) (S T : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime ∧ p ∉ S) (x : ℝ) :
    (scalarSievedClass K C S x).ncard ≤ (scalarSievedClass K C (S ∪ T) x).ncard +
      ∑ p ∈ T, (scalarSievedClass K C ∅ (x / (p : ℝ) ^ finrank ℚ K)).ncard := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hp ih =>
    have hp' := hT p (mem_insert_self p T)
    have hT' := fun q hq => hT q (mem_insert_of_mem hq)
    have hnot : p ∉ S ∪ T := by simp [hp'.2, hp]
    have hcop (q : ℕ) (hq : q ∈ S ∪ T) : q.Coprime p := by
      have hq' : q.Prime := (mem_union.mp hq).elim (hS _) (fun h => (hT' q h).1)
      exact (Nat.coprime_primes hq' hp'.1).mpr fun he => hnot (he ▸ hq)
    have hlose := ncard_scalarSievedClass_insert K C (S ∪ T) hp'.1 hcop x
    have hle (y : ℝ) : (scalarSievedClass K C (S ∪ T) y).ncard ≤
        (scalarSievedClass K C ∅ y).ncard := by
      apply Set.ncard_le_ncard _ (finite_scalarSievedClass K C ∅ y)
      intro I hI
      exact ⟨hI.1, hI.2.1, by simp⟩
    rw [sum_insert hp, union_insert]
    have ht := ih hT'
    have hz := hle (x / (p : ℝ) ^ finrank ℚ K)
    omega

theorem scalarPrimitiveClass_eq_sieve (C : ClassGroup (𝓞 K)) (N : ℕ) (x : ℝ) :
    scalarPrimitiveClass K C x = scalarSievedClass K C
      (N.primesBelow ∪ ⌈x⌉₊.primesLE) x := by
  ext I
  constructor
  · rintro ⟨hn, hc, hfree⟩
    exact ⟨hn, hc, fun p hp => hfree p ((mem_union.mp hp).elim
      Nat.prime_of_mem_primesBelow Nat.prime_of_mem_primesLE)⟩
  · rintro ⟨hn, hc, hfree⟩
    refine ⟨hn, hc, fun p hp hd => ?_⟩
    have hdiv := map_dvd Ideal.absNorm hd
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at hdiv
    have hpow := Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I) hdiv
    have hle := (Nat.le_self_pow (finrank_pos (R := ℚ) (M := K)).ne' p).trans hpow
    exact hfree p (mem_union_right _ (Nat.mem_primesLE.mpr
      ⟨hle.trans (Nat.cast_le.mp (hn.trans (Nat.le_ceil x))), hp⟩)) hd

/-- The normalized error of a finite scalar-prime sieve is bounded uniformly in the norm cutoff by the tail of the degree-p-series. -/
theorem scalarSieve_tail_bound (C : ClassGroup (𝓞 K)) {B : ℝ} (hB : 0 ≤ B)
    (hcount : ∀ y : ℝ, 0 < y → ((scalarSievedClass K C ∅ y).ncard : ℝ) ≤ B * y)
    (hd : 1 < finrank ℚ K) (N : ℕ) {x : ℝ} (hx : 0 < x) :
    ((scalarSievedClass K C N.primesBelow x).ncard : ℝ) / x -
      ((scalarPrimitiveClass K C x).ncard : ℝ) / x ≤
      B * ∑' n : ℕ, if N ≤ n then ((n : ℝ) ^ finrank ℚ K)⁻¹ else 0 := by
  classical
  let S := N.primesBelow
  let T := ⌈x⌉₊.primesLE \ S
  let w (n : ℕ) : ℝ := if N ≤ n then ((n : ℝ) ^ finrank ℚ K)⁻¹ else 0
  have hT (p : ℕ) (hp : p ∈ T) : p.Prime ∧ p ∉ S :=
    ⟨Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1, (mem_sdiff.mp hp).2⟩
  have hw (n : ℕ) : 0 ≤ w n := by dsimp [w]; split <;> positivity
  have hsum : Summable w := by
    apply Summable.of_nonneg_of_le hw _ (Real.summable_nat_pow_inv.mpr hd)
    intro n
    dsimp [w]
    split
    · exact le_rfl
    · positivity
  have hlose := scalarSieve_finite_loss K C S T (fun _ => Nat.prime_of_mem_primesBelow) hT x
  have heq : S ∪ T = S ∪ ⌈x⌉₊.primesLE := by ext n; simp [T]
  rw [heq, ← scalarPrimitiveClass_eq_sieve K C N x] at hlose
  have hreal := Nat.cast_le (α := ℝ).mpr hlose
  push_cast at hreal
  have hsub : (∑ p ∈ T, ((scalarSievedClass K C ∅ (x / (p : ℝ) ^ finrank ℚ K)).ncard : ℝ)) ≤
      (B * x) * ∑ p ∈ T, w p := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hp' := hT p hp
    have hNp : N ≤ p := by
      by_contra! he
      exact hp'.2 (Nat.mem_primesBelow.mpr ⟨he, hp'.1⟩)
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
    simpa [w, hNp, div_eq_mul_inv, mul_assoc] using hcount (x / (p : ℝ) ^ finrank ℚ K) (by positivity)
  have htail := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum T (fun n _ => hw n)) (mul_nonneg hB hx.le)
  rw [← sub_div, div_le_iff₀ hx]
  change _ ≤ (B * ∑' n, w n) * x
  change ((scalarSievedClass K C N.primesBelow x).ncard : ℝ) ≤ _ at hreal
  linarith only [hreal, hsub, htail, mul_right_comm B x (∑' n, w n)]



/-- Pass from finite windows to a limit using a uniform bound on the omitted mass. -/
private theorem tendsto_of_sieve_windows {α : Type*} {l : Filter α} {F : ℕ → α → ℝ}
    {f : α → ℝ} {a e : ℕ → ℝ} {A : ℝ}
    (hF : ∀ N, Tendsto (F N) l (𝓝 (a N))) (ha : Tendsto a atTop (𝓝 A))
    (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ N, ∀ᶠ x in l, f x ≤ F N x ∧ F N x - f x ≤ e N) :
    Tendsto f l (𝓝 A) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  obtain ⟨N, hN, hE⟩ := ((Metric.tendsto_nhds.mp ha _ hthird).and
    (he.eventually_lt_const hthird)).exists
  filter_upwards [Metric.tendsto_nhds.mp (hF N) _ hthird, hbound N] with x hx hgap
  rw [Real.dist_eq, abs_lt] at hN hx ⊢
  obtain ⟨_, _⟩ := hgap
  constructor <;> linarith

/-- The real scalar Euler factors through primes strictly below N. -/
private theorem tendsto_scalarEulerProduct {d : ℕ} (hd : 1 < d) :
    Tendsto (fun N => ∏ p ∈ Nat.primesBelow N, (1 - ((p : ℝ) ^ d)⁻¹)) atTop
      (𝓝 ((riemannZeta (d : ℂ)).re)⁻¹) := by
  have hdR : 1 < (d : ℝ) := by exact_mod_cast hd
  have hdC : 1 < (d : ℂ).re := by simpa using hdR
  have hreal : (riemannZeta (d : ℂ)).re ≠ 0 := by
    simpa using (riemannZeta_re_pos_of_one_lt hdR).ne'
  have hc := Complex.continuous_re.continuousAt.tendsto.comp (riemannZeta_eulerProduct hdC)
  have hprod (N : ℕ) : ((∏ p ∈ Nat.primesBelow N, (1 - ((p : ℝ) ^ d)⁻¹))⁻¹ : ℝ) =
      (∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-(d : ℂ)))⁻¹).re := by
    rw [← Complex.ofReal_re ((∏ p ∈ Nat.primesBelow N, (1 - ((p : ℝ) ^ d)⁻¹))⁻¹)]
    push_cast
    simp only [Complex.cpow_neg, Complex.cpow_natCast, Finset.prod_inv_distrib]
  have hlim : Tendsto (fun N => (∏ p ∈ Nat.primesBelow N, (1 - ((p : ℝ) ^ d)⁻¹))⁻¹)
      atTop (𝓝 (riemannZeta (d : ℂ)).re) := hc.congr fun N => (hprod N).symm
  simpa only [inv_inv] using hlim.inv₀ hreal

/-- Normalization of the scalar density factor in quadratic fields. -/
private theorem scalarEulerFactor_two : ((riemannZeta 2).re)⁻¹ = 6 / Real.pi ^ 2 := by
  rw [riemannZeta_two, ← Complex.ofReal_pow, ← Complex.ofReal_ofNat 6, ← Complex.ofReal_div,
    Complex.ofReal_re, inv_div]

/-- The tail appearing when primes beyond a window are bounded by all integers. -/
private theorem tendsto_scalarSieveError (B : ℝ) {d : ℕ} (hd : 1 < d) :
    Tendsto (fun N : ℕ => B * ∑' n : ℕ, if N ≤ n then ((n : ℝ) ^ d)⁻¹ else 0) atTop (𝓝 0) := by
  let f := fun n : ℕ => ((n : ℝ) ^ d)⁻¹
  have hs : Summable f := Real.summable_nat_pow_inv.mpr hd
  have h := (tendsto_const_nhds (x := ∑' n, f n)).sub hs.hasSum.tendsto_sum_nat
  have eqN (N : ℕ) : (∑' n, f n) - ∑ n ∈ range N, f n =
      ∑' n : ℕ, if N ≤ n then ((n : ℝ) ^ d)⁻¹ else 0 := by
    rw [← hs.sum_add_tsum_compl (s := range N), add_sub_cancel_left]
    rw [_root_.tsum_subtype ((range N : Set ℕ)ᶜ) f]
    simp only [Set.indicator, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range, not_lt, f]
  simpa only [sub_self, mul_zero] using (h.congr eqN).const_mul B

/-- Scalar-primitive ideals in each prescribed ideal class have the same
asymptotic density factor as primitive tuples in the ambient degree. -/
theorem tendsto_scalarPrimitiveClass (C : ClassGroup (𝓞 K)) (hd : 1 < finrank ℚ K) :
    Tendsto (fun x : ℝ => ((scalarPrimitiveClass K C x).ncard : ℝ) / x) atTop
      (𝓝 (classDensity * ((riemannZeta (finrank ℚ K : ℂ)).re)⁻¹)) := by
  classical
  obtain ⟨B, hB, hcount⟩ := exists_class_count_le_mul K C
  refine tendsto_of_sieve_windows (fun N => tendsto_scalarSievedClass K C N.primesBelow
    (fun _ hp => Nat.prime_of_mem_primesBelow hp)) ((tendsto_scalarEulerProduct hd).const_mul _)
    (tendsto_scalarSieveError B hd) ?_
  intro N
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  refine ⟨div_le_div_of_nonneg_right (Nat.cast_le.mpr (Set.ncard_le_ncard ?_
    (finite_scalarSievedClass K C N.primesBelow x))) hx.le,
    scalarSieve_tail_bound K C hB.le (fun y hy => hcount y hy.le) hd N hx⟩
  exact fun I hI => ⟨hI.1, hI.2.1, fun _ hp => hI.2.2 _ (Nat.prime_of_mem_primesBelow hp)⟩

/-- Among all ideals in an individual class, the limiting fraction with no
rational scalar prime divisor is 1/ζ(d), where d is the field degree. -/
theorem tendsto_scalarPrimitiveClass_fraction (C : ClassGroup (𝓞 K)) (hd : 1 < finrank ℚ K) :
    Tendsto (fun x : ℝ => ((scalarPrimitiveClass K C x).ncard : ℝ) /
      ((scalarSievedClass K C ∅ x).ncard : ℝ)) atTop (𝓝 ((riemannZeta (finrank ℚ K : ℂ)).re)⁻¹) := by
  let c : ℝ := classDensity
  have hc : 0 < c := div_pos (mul_pos (mul_pos (by positivity) (by positivity)) (regulator_pos K))
    (mul_pos (Nat.cast_pos.mpr (torsionOrder_pos K))
      (Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))))
  have hraw : Tendsto (fun x : ℝ => ((scalarSievedClass K C ∅ x).ncard : ℝ) / x)
      atTop (𝓝 c) := by simpa [c] using tendsto_scalarSievedClass K C ∅ (by simp)
  have H := (tendsto_scalarPrimitiveClass K C hd).div hraw hc.ne'
  have hval (y : ℝ) : c * y / c = y := by field_simp
  rw [show _ * ((riemannZeta (finrank ℚ K : ℂ)).re)⁻¹ / c =
    ((riemannZeta (finrank ℚ K : ℂ)).re)⁻¹ from hval _] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp
  field_simp

/-- The fraction is 6/π² in every ideal class of every quadratic field. -/
theorem tendsto_scalarPrimitiveClass_fraction_quadratic (C : ClassGroup (𝓞 K)) (hd : finrank ℚ K = 2) :
    Tendsto (fun x : ℝ => ((scalarPrimitiveClass K C x).ncard : ℝ) /
      ((scalarSievedClass K C ∅ x).ncard : ℝ)) atTop (𝓝 (6 / Real.pi ^ 2)) := by
  simpa [hd, scalarEulerFactor_two] using
    tendsto_scalarPrimitiveClass_fraction K C (show 1 < finrank ℚ K by omega)

end GlobalTheory
