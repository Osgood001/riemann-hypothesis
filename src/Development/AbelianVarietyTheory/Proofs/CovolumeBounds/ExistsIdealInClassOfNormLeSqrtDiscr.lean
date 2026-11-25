module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PrimitiveIdealNorm

@[expose] public section

open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset

namespace GlobalTheory

theorem sum_zeta_pow_succ_le (k : ℕ) {X : ℝ} (hX : 1 ≤ X) (N : ℕ) (hN : (N : ℝ) ≤ X) :
    ((∑ n ∈ Ioc 0 N, (ζ ^ (k + 1) : ArithmeticFunction ℕ) n : ℕ) : ℝ)
      ≤ N * (1 + Real.log X) ^ k := by
  have hL : 0 ≤ 1 + Real.log X := by have := Real.log_nonneg hX; linarith
  induction k generalizing N with
  | zero => simp only [zero_add, pow_one, ArithmeticFunction.sum_Ioc_zeta, pow_zero, mul_one, le_refl]
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.sum_Ioc_mul_eq_sum_sum, Nat.cast_sum]
    have hH : ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ ≤ 1 + Real.log X := by
      have h1 := harmonic_le_one_add_log N
      simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h1
      have h2 : Real.log N ≤ Real.log X := by
        rcases Nat.eq_zero_or_pos N with rfl | h
        · simpa using Real.log_nonneg hX
        · exact Real.log_le_log (by exact_mod_cast h) hN
      have h3 : Ioc 0 N = Icc 1 N := rfl
      rw [h3]; linarith
    calc _ ≤ ∑ n ∈ Ioc 0 N, (N * (1 + Real.log X) ^ k) * (n : ℝ)⁻¹ := by
          refine sum_le_sum fun n hn => ?_
          have hn0 : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
          rw [ArithmeticFunction.zeta_apply_ne hn0, one_mul]
          refine (ih (N / n) (le_trans (by exact_mod_cast Nat.div_le_self N n) hN)).trans ?_
          have : ((N / n : ℕ) : ℝ) ≤ N * (n : ℝ)⁻¹ := by
            rw [← div_eq_mul_inv]; exact Nat.cast_div_le
          calc _ ≤ (N * (n : ℝ)⁻¹) * (1 + Real.log X) ^ k := by gcongr
            _ = _ := by ring
      _ ≤ (N * (1 + Real.log X) ^ k) * (1 + Real.log X) := by
          rw [← mul_sum]; gcongr
      _ = _ := by ring

theorem sum_zeta_pow_le {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 1 ≤ X) :
    ((∑ n ∈ Ioc 0 ⌊X⌋₊, (ζ ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ)
      ≤ X * (1 + Real.log X) ^ (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hL : 0 ≤ 1 + Real.log X := by have := Real.log_nonneg hX; linarith
  have h := Nat.floor_le (zero_le_one.trans hX)
  refine (sum_zeta_pow_succ_le k hX _ h).trans ?_
  rw [Nat.add_sub_cancel]
  gcongr

theorem card_finMulAntidiag_eq_zeta_pow (k n : ℕ) :
    (Nat.finMulAntidiag k n).card = (ζ ^ k : ArithmeticFunction ℕ) n := by
  induction k generalizing n with
  | zero =>
    by_cases h : n = 1
    · subst h; simp [Nat.finMulAntidiag_one]
    · simp [Nat.finMulAntidiag_zero_left h, ArithmeticFunction.one_apply_ne h]
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.mul_apply]
    have : ∑ x ∈ n.divisorsAntidiagonal, (ζ : ArithmeticFunction ℕ) x.1 * (ζ ^ k : ArithmeticFunction ℕ) x.2
        = ∑ x ∈ n.divisorsAntidiagonal, (Nat.finMulAntidiag k x.2).card := by
      refine sum_congr rfl fun x hx => ?_
      rw [ArithmeticFunction.zeta_apply_ne (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx),
        one_mul, ih]
    rw [this, ← card_sigma]
    refine card_nbij' (fun f => ⟨(f 0, ∏ i, f (Fin.succ i)), fun i => f (Fin.succ i)⟩)
      (fun y => Fin.cons y.1.1 y.2) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [mem_coe, Nat.mem_finMulAntidiag, Fin.prod_univ_succ] at hf
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag]
      refine ⟨hf, trivial, ?_⟩
      intro h
      exact hf.2 (by rw [← hf.1, h, mul_zero])
    · rintro ⟨⟨a, b⟩, g⟩ hy
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at hy
      simp only [mem_coe, Nat.mem_finMulAntidiag, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [hy.2.1]; exact hy.1
    · intro f _
      exact Fin.cons_self_tail f
    · rintro ⟨⟨a, b⟩, g⟩ hy
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at hy
      simp only [Fin.cons_zero, Fin.cons_succ, hy.2.1]

variable (K : Type*) [Field K] [NumberField K]

private theorem prime_count_le_degree {K : Type*} [Field K] [NumberField K] (p : Ideal ℤ) [p.IsMaximal]
    (hp : p ≠ ⊥) :
    (IsDedekindDomain.primesOverFinset p (𝓞 K)).card ≤ Module.finrank ℚ K := by
  classical
  let := Fintype.ofFinite (p.primesOver (𝓞 K))
  rw [← NumberField.RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank p (𝓞 K)]
  have hcard : (IsDedekindDomain.primesOverFinset p (𝓞 K)).card = Fintype.card (p.primesOver (𝓞 K)) := by
    exact (Fintype.card_of_subtype _ (fun _ => IsDedekindDomain.mem_primesOverFinset_iff hp (𝓞 K))).symm
  rw [hcard, ← Finset.card_univ, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro q _
  exact Nat.mul_pos (q.1.ramificationIdx_pos ℤ) (q.1.inertiaDeg_pos ℤ)

theorem exists_colouring_maximal_ideals :
    ∃ c : Ideal (𝓞 K) → Fin (finrank ℚ K), ∀ p : ℕ, p.Prime → ∀ P Q : Ideal (𝓞 K),
      P.IsMaximal → Q.IsMaximal → (p : 𝓞 K) ∈ P → (p : 𝓞 K) ∈ Q → c P = c Q → P = Q := by
  classical
  have : Nonempty (Fin (finrank ℚ K)) := ⟨⟨0, finrank_pos⟩⟩
  have key : ∀ p : ℕ, ∃ e : Ideal (𝓞 K) → Fin (finrank ℚ K), p.Prime →
      Set.InjOn e {P | P.IsMaximal ∧ (p : 𝓞 K) ∈ P} := by
    intro p
    by_cases hp : p.Prime
    · have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
      have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
        ((Ideal.span_singleton_prime hp'.ne_zero).mpr hp').isMaximal hp0
      let Zp := Ideal.span {(p : ℤ)}
      have hc := prime_count_le_degree (K := K) Zp hp0
      have hsub : {P : Ideal (𝓞 K) | P.IsMaximal ∧ (p : 𝓞 K) ∈ P} ⊆
          (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) : Set _) := by
        rintro P ⟨hP, hpP⟩
        rw [mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]
        refine ⟨hP.isPrime, ⟨hmax.eq_of_le ?_ ?_⟩⟩
        · exact Ideal.comap_ne_top _ hP.ne_top
        · rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
          simpa using hpP
      obtain ⟨e, -, he⟩ := Set.Finite.exists_injOn_of_encard_le
        (t := (Set.univ : Set (Fin (finrank ℚ K))))
        (Finset.finite_toSet (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K))) (by
          rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_univ]
          simpa using hc)
      exact ⟨e, fun _ => he.mono hsub⟩
    · exact ⟨fun _ => Classical.arbitrary _, fun h => absurd h hp⟩
  choose e he using key
  have hmin : ∀ p : ℕ, p.Prime → ∀ P : Ideal (𝓞 K), P.IsMaximal → (p : 𝓞 K) ∈ P →
      (Ideal.absNorm P).minFac = p := by
    intro p hp P hP hpP
    obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    rw [H, hq.pow_minFac hn.ne']
    by_contra hne
    have hco : IsCoprime (q : 𝓞 K) (p : 𝓞 K) :=
      Nat.Coprime.cast ((Nat.coprime_primes hq hp).mpr hne)
    obtain ⟨a, b, hab⟩ := hco
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr
      (hab ▸ P.add_mem (P.mul_mem_left a hqP) (P.mul_mem_left b hpP)))
  refine ⟨fun P => e (Ideal.absNorm P).minFac P, fun p hp P Q hP hQ hpP hpQ h => ?_⟩
  simp only [hmin p hp P hP hpP, hmin p hp Q hQ hpQ] at h
  exact he p hp ⟨hP, hpP⟩ ⟨hQ, hpQ⟩ h

private noncomputable def colouredNormTuple (c : Ideal (𝓞 K) → Fin (finrank ℚ K))
    (I : Ideal (𝓞 K)) (i : Fin (finrank ℚ K)) : ℕ :=
  (((UniqueFactorizationMonoid.normalizedFactors I).filter (fun Q => c Q = i)).map Ideal.absNorm).prod

private theorem ncard_ideal_fibre_le_tuple_filter {n : ℕ} (hn : n ≠ 0)
    {P : Ideal (𝓞 K) → Prop} {T : (Fin (finrank ℚ K) → ℕ) → Prop} [DecidablePred T]
    (hselect : ∀ c I, P I → T (colouredNormTuple K c I)) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = n ∧ P I}.ncard ≤
      ((Nat.finMulAntidiag (finrank ℚ K) n).filter T).card := by
  classical
  obtain ⟨c, hc⟩ := exists_colouring_maximal_ideals K

  have key : ∀ (P : Ideal (𝓞 K)) (p f : ℕ), P.IsMaximal → p.Prime → (p : 𝓞 K) ∈ P →
      Ideal.absNorm P = p ^ f → ∀ s : Multiset (Ideal (𝓞 K)), (∀ Q ∈ s, Q.IsMaximal) →
      ((s.filter (fun Q => c Q = c P)).map Ideal.absNorm).prod ≠ 0 ∧
      (((s.filter (fun Q => c Q = c P)).map Ideal.absNorm).prod).factorization p
        = f * s.count P := by
    intro P p f hP hp hpP hN s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons Q s ih =>
      intro hs
      obtain ⟨ih0, ih⟩ := ih fun R hR => hs R (Multiset.mem_cons_of_mem hR)
      have hQ : Q.IsMaximal := hs Q (Multiset.mem_cons_self Q s)
      obtain ⟨q, g, hg, hqQ, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
      have hQ0 : Ideal.absNorm Q ≠ 0 := H ▸ pow_ne_zero _ hq.ne_zero
      by_cases hcol : c Q = c P
      · rw [Multiset.filter_cons_of_pos (p := fun Q => c Q = c P) s hcol, Multiset.map_cons,
          Multiset.prod_cons, Nat.factorization_mul hQ0 ih0, Finsupp.add_apply, ih]
        refine ⟨mul_ne_zero hQ0 ih0, ?_⟩
        by_cases hQP : Q = P
        · subst hQP
          rw [Multiset.count_cons_self, hN, hp.factorization_pow, Finsupp.single_eq_same]
          ring
        · rw [Multiset.count_cons_of_ne (Ne.symm hQP), H, hq.factorization_pow,
            Finsupp.single_apply, ite_eq_right, zero_add]
          rintro rfl
          exact hQP (hc q hq Q P hQ hP hqQ hpP hcol)
      · rw [Multiset.filter_cons_of_neg (p := fun Q => c Q = c P) s hcol]
        have hQP : P ≠ Q := by rintro rfl; exact hcol rfl
        rw [Multiset.count_cons_of_ne hQP]
        exact ⟨ih0, ih⟩
  have hprod : ∀ s : Multiset (Ideal (𝓞 K)),
      ∏ i, ((s.filter (fun Q => c Q = i)).map Ideal.absNorm).prod = Ideal.absNorm s.prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons Q s ih =>
      rw [Multiset.prod_cons, map_mul, ← ih]
      have : ∀ i, (((Q ::ₘ s).filter (fun Q => c Q = i)).map Ideal.absNorm).prod =
          (if c Q = i then Ideal.absNorm Q else 1) *
            ((s.filter (fun Q => c Q = i)).map Ideal.absNorm).prod := by
        intro i
        rw [Multiset.filter_cons]
        split_ifs <;> simp
      simp_rw [this]
      rw [prod_mul_distrib]
      simp
  have hmax : ∀ I : Ideal (𝓞 K), ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Q.IsMaximal := by
    intro I Q hQ
    have hQ' := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    exact (Ideal.isPrime_of_prime hQ').isMaximal hQ'.ne_zero
  have hne : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → I ≠ ⊥ := by
    rintro I hI rfl
    exact hn (by rw [← hI]; simp)
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn
    (fun I i => (((UniqueFactorizationMonoid.normalizedFactors I).filter
      (fun Q => c Q = i)).map Ideal.absNorm).prod) ?_ ?_ (Finset.finite_toSet _)
  · intro I hI
    refine Finset.mem_filter.mpr ⟨?_, hselect c I hI.2⟩
    rw [Nat.mem_finMulAntidiag, hprod, Ideal.prod_normalizedFactors_eq_self (hne I hI.1)]
    exact ⟨hI.1, hn⟩
  · intro I hI J hJ h
    rw [← Ideal.prod_normalizedFactors_eq_self (hne I hI.1),
      ← Ideal.prod_normalizedFactors_eq_self (hne J hJ.1)]
    congr 1
    ext P
    by_cases hP : P.IsMaximal
    · obtain ⟨p, f, hf, hpP, hp, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
      have h1 := (key P p f hP hp hpP H _ (hmax I)).2
      have h2 := (key P p f hP hp hpP H _ (hmax J)).2
      have h3 := congrFun h (c P)
      simp only at h3
      rw [h3, h2] at h1
      exact (Nat.eq_of_mul_eq_mul_left hf h1).symm
    · rw [Multiset.count_eq_zero_of_notMem fun h => hP (hmax I P h),
        Multiset.count_eq_zero_of_notMem fun h => hP (hmax J P h)]

theorem ncard_ideal_absNorm_eq_le {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard
      ≤ (ζ ^ finrank ℚ K : ArithmeticFunction ℕ) n := by
  classical
  rw [← card_finMulAntidiag_eq_zeta_pow]
  simpa using ncard_ideal_fibre_le_tuple_filter (K := K) hn (P := fun _ => True)
    (T := fun _ => True) (fun _ _ _ => trivial)

/-- If all degree-many primes over a rational prime divide an ideal, the rational prime divides it. -/
private theorem rational_prime_dvd_of_cover (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    {I : Ideal (𝓞 K)}
    (hcard : (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card = finrank ℚ K)
    (hcover : ∀ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K), P ∣ I) :
    Ideal.span {(p : 𝓞 K)} ∣ I := by
  classical
  let Zp := Ideal.span {(p : ℤ)}
  have h0 : Zp ≠ ⊥ := by simpa [Zp] using hp.ne_zero
  have hp' := Nat.prime_iff_prime_int.mp hp
  have hm : Zp.IsMaximal := ((Ideal.span_singleton_prime hp'.ne_zero).mpr hp').isMaximal h0
  let := Fintype.ofFinite (Zp.primesOver (𝓞 K))
  change (IsDedekindDomain.primesOverFinset Zp (𝓞 K)).card = _ at hcard
  rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset h0,
    ← Set.fintypeCard_eq_ncard, ← RingOfIntegers.rank K,
    ← Ideal.sum_ramification_inertia_eq_finrank Zp (𝓞 K), ← Finset.card_univ,
    Finset.card_eq_sum_ones] at hcard
  have he (P : Zp.primesOver (𝓞 K)) : P.val.ramificationIdx ℤ = 1 := by
    have h := (Finset.sum_eq_sum_iff_of_le (fun (Q : Zp.primesOver (𝓞 K)) _ =>
      Nat.mul_pos (Ideal.ramificationIdx_pos ℤ Q.val) (Ideal.inertiaDeg_pos Q.val ℤ))).mp hcard P (mem_univ _)
    exact Nat.eq_one_of_dvd_one ⟨_, h⟩
  have hprod := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 K) h0
  have hf : (Zp.primesOver (𝓞 K)).toFinset = IsDedekindDomain.primesOverFinset Zp (𝓞 K) := by
    ext P
    simp [IsDedekindDomain.mem_primesOverFinset_iff h0]
  rw [hf] at hprod
  rw [show Ideal.span {(p : 𝓞 K)} = Zp.map (algebraMap ℤ (𝓞 K)) by simp [Zp, Ideal.map_span], hprod]
  apply Finset.prod_dvd_of_coprime
  · intro P hP Q hQ hne
    have pP := (IsDedekindDomain.mem_primesOverFinset_iff h0 _).mp hP
    have pQ := (IsDedekindDomain.mem_primesOverFinset_iff h0 _).mp hQ
    have := Ideal.isMaximal_of_mem_primesOver pP
    have := Ideal.isMaximal_of_mem_primesOver pQ
    simpa only [Function.onFun, he ⟨P, pP⟩, he ⟨Q, pQ⟩, pow_one] using Ideal.isCoprime_of_isMaximal hne
  · intro P hP
    have hE := he ⟨P, (IsDedekindDomain.mem_primesOverFinset_iff h0 _).mp hP⟩
    simpa only [hE, pow_one] using hcover P hP

/-- A rational prime occurring in a colour coordinate comes from a prime
factor of the ideal of that colour lying over that rational prime. -/
private theorem exists_coloured_prime_over {K : Type*} [Field K] [NumberField K] {ι : Type*} [DecidableEq ι]
    (c : Ideal (𝓞 K) → ι) (I : Ideal (𝓞 K)) {p : ℕ} (hp : p.Prime) {i : ι}
    (h : p ∣ (((UniqueFactorizationMonoid.normalizedFactors I).filter (fun Q => c Q = i)).map Ideal.absNorm).prod) :
    ∃ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K), c P = i ∧ P ∣ I := by
  obtain ⟨P, hcol, hN⟩ := hp.prime.exists_mem_multiset_map_dvd h
  obtain ⟨hP, hi⟩ := Multiset.mem_filter.mp hcol
  have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hmax := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  obtain ⟨Q, hQ, hQp, hQP⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp P hN
  obtain rfl : P = Q := hmax.eq_of_le hQ.ne_top (Ideal.dvd_iff_le.mp hQP)
  have hp' := Nat.prime_iff_prime_int.mp hp
  have h0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have : (Ideal.span {(p : ℤ)}).IsMaximal := ((Ideal.span_singleton_prime hp'.ne_zero).mpr hp').isMaximal h0
  exact ⟨P, (IsDedekindDomain.mem_primesOverFinset_iff h0 _).mpr ⟨hQ.isPrime, ⟨hQp.symm⟩⟩,
    hi, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP⟩

private theorem all_good_of_colour_witness {α : Type*} {d : ℕ} {s : Finset α} (c : α → Fin d)
    {Good : α → Prop} (hcard : s.card ≤ d)
    (hw : ∀ i, ∃ p ∈ s, c p = i ∧ Good p) :
    s.card = d ∧ ∀ p ∈ s, Good p := by
  classical
  have h : d ≤ (s.filter Good).card := by
    rw [← Fintype.card_fin d, ← Finset.card_univ]
    apply Finset.card_le_card_of_surjOn c
    intro i _
    obtain ⟨p, hp, hi, hg⟩ := hw i
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hg⟩, hi⟩
  have hle := Finset.card_filter_le s Good
  exact ⟨hcard.antisymm (h.trans hle), Finset.card_filter_eq_iff.mp (hle.antisymm (hcard.trans h))⟩

/-- Primitive ideals of norm n inject into product-n tuples with no common prime. -/
theorem ncard_primitive_ideal_absNorm_eq_le {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = n ∧ ∀ p : ℕ, p.Prime → ¬ Ideal.span {(p : 𝓞 K)} ∣ I}.ncard ≤
      ((Nat.finMulAntidiag (finrank ℚ K) n).filter (fun a => Finset.univ.gcd a = 1)).card := by
  classical
  apply ncard_ideal_fibre_le_tuple_filter K hn (P := fun I => ∀ p : ℕ, p.Prime → ¬ Ideal.span {(p : 𝓞 K)} ∣ I)
    (T := fun a => Finset.univ.gcd a = 1)
  intro c I hprim
  by_contra hne
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne
  have h0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hp' := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal := ((Ideal.span_singleton_prime hp'.ne_zero).mpr hp').isMaximal h0
  have hcol := all_good_of_colour_witness c (prime_count_le_degree (K := K) _ h0)
    (fun i => exists_coloured_prime_over c I hp (Finset.dvd_gcd_iff.mp hdvd i (mem_univ _)))
  exact hprim p hp (rational_prime_dvd_of_cover K hp hcol.1 hcol.2)

theorem two_pow_mul_factorial_succ_le (n : ℕ) :
    (2 : ℝ) ^ n * ((n + 1).factorial : ℝ) ≤ ((n : ℝ) + 1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : 2 * ((n : ℝ) + 1) ^ (n + 1) ≤ ((n : ℝ) + 1 + 1) ^ (n + 1) := by
      have hpos : (0 : ℝ) < n + 1 := by positivity
      have h := one_add_mul_le_pow (a := ((n : ℝ) + 1)⁻¹) (by have := inv_pos.mpr hpos; linarith)
        (n + 1)
      have h1 : ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + 1)⁻¹ = 1 := by push_cast; field_simp
      rw [h1] at h
      have h2 : ((n : ℝ) + 1 + 1) = (1 + ((n : ℝ) + 1)⁻¹) * (n + 1) := by field_simp
      rw [h2, mul_pow]
      gcongr
      linarith
    rw [Nat.factorial_succ (n + 1), pow_succ 2 n, pow_succ _ (n + 1)]
    push_cast
    have : (0 : ℝ) ≤ n + 1 + 1 := by positivity
    calc _ = (2 * (2 ^ n * ((n + 1).factorial : ℝ))) * ((n : ℝ) + 1 + 1) := by ring
      _ ≤ (2 * ((n : ℝ) + 1) ^ (n + 1)) * ((n : ℝ) + 1 + 1) := by gcongr
      _ ≤ _ := by gcongr

theorem minkowski_const_le_one :
    (4 / π) ^ InfinitePlace.nrComplexPlaces K *
      (((finrank ℚ K).factorial : ℝ) / (finrank ℚ K : ℝ) ^ finrank ℚ K) ≤ 1 := by
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hpos : 0 < finrank ℚ K := finrank_pos
  obtain ⟨n, hn⟩ : ∃ n, finrank ℚ K = n + 1 := ⟨finrank ℚ K - 1, by omega⟩
  rw [hn] at hr ⊢
  have h1 : (4 / π) ^ InfinitePlace.nrComplexPlaces K ≤ (2 : ℝ) ^ n := by
    have h4 : 4 / π ≤ 2 := by
      rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    calc _ ≤ (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K := by gcongr
      _ ≤ _ := pow_le_pow_right₀ one_le_two (by omega)
  have h2 := two_pow_mul_factorial_succ_le n
  rw [← mul_div_assoc, div_le_one (by positivity)]
  push_cast
  refine le_trans ?_ h2
  gcongr

/-- The Minkowski norm cutoff for ideal-class representatives, with the signature factor retained. -/
noncomputable def minkowskiBound : ℝ :=
  (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
    ((Nat.factorial (finrank ℚ K) : ℝ) / (finrank ℚ K : ℝ) ^ finrank ℚ K * √|(discr K : ℝ)|)

theorem one_le_minkowskiBound : 1 ≤ minkowskiBound K := by
  obtain ⟨I, _, hI⟩ := NumberField.exists_ideal_in_class_of_norm_le (1 : ClassGroup (𝓞 K))
  exact (Nat.one_le_cast.2 (Ideal.absNorm_pos_of_nonZeroDivisors I)).trans hI

theorem minkowskiBound_le_sqrt_abs_discr : minkowskiBound K ≤ √|(discr K : ℝ)| := by
  unfold minkowskiBound
  rw [← mul_assoc]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (minkowski_const_le_one K)

theorem exists_ideal_in_class_of_norm_le_sqrt_discr (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ √|(discr K : ℝ)| := by
  obtain ⟨I, hI, hN⟩ := exists_ideal_in_class_of_norm_le C
  exact ⟨I, hI, hN.trans (minkowskiBound_le_sqrt_abs_discr K)⟩

theorem one_le_sqrt_abs_discr : 1 ≤ √|(discr K : ℝ)| := by
  rw [Real.one_le_sqrt]
  exact_mod_cast Int.one_le_abs (discr_ne_zero K)

/-- The primitive tuple majorant is strictly smaller exactly on norms divisible by a
prime to the degree of the field. -/
theorem primitive_tuple_card_lt_iff {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    ((Nat.finMulAntidiag d n).filter (fun a => Finset.univ.gcd a = 1)).card <
      (Nat.finMulAntidiag d n).card ↔ ∃ p : ℕ, p.Prime ∧ p ^ d ∣ n := by
  classical
  constructor
  · intro hlt
    obtain ⟨a, ha, hg⟩ : ∃ a ∈ Nat.finMulAntidiag d n, Finset.univ.gcd a ≠ 1 := by
      by_contra! hall
      exact (Nat.ne_of_lt hlt) (Finset.card_filter_eq_iff.mpr hall)
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    refine ⟨p, hp, ?_⟩
    have h := Finset.prod_dvd_prod_of_dvd (s := univ) (fun _ => p) a (Finset.dvd_gcd_iff.mp hpg)
    simpa only [prod_const, card_univ, Fintype.card_fin, Nat.prod_eq_of_mem_finMulAntidiag ha] using h
  · rintro ⟨p, hp, m, rfl⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    let a : Fin (k + 1) → ℕ := Fin.cons (p * m) (fun _ => p)
    apply Finset.card_lt_card
    apply Finset.filter_ssubset.mpr
    refine ⟨a, Nat.mem_finMulAntidiag.mpr ⟨?_, hn⟩, ?_⟩
    · simp only [a, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, prod_const, card_univ,
        Fintype.card_fin, pow_succ]
      ring
    · intro hg
      have hpg : p ∣ univ.gcd a := Finset.dvd_gcd_iff.mpr fun i _ =>
        Fin.cases (show p ∣ a 0 by simp [a]) (fun j => show p ∣ a j.succ by simp [a]) i
      exact hp.not_dvd_one (hg ▸ hpg)

/-- Count in any quotient of the ideal class group. A least-norm representative
cannot be divisible by a proper integral ideal trivial in that quotient. -/
theorem exists_minimal_class_image {G : Type*} [Group G] (f : ClassGroup (𝓞 K) →* G)
    (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, f (ClassGroup.mk0 I) = f C ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ minkowskiBound K ∧
      ∀ J : (Ideal (𝓞 K))⁰, f (ClassGroup.mk0 J) = 1 →
        (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) → (J : Ideal (𝓞 K)) = 1 := by
  classical
  let P (n : ℕ) := ∃ I : (Ideal (𝓞 K))⁰, f (ClassGroup.mk0 I) = f C ∧
    Ideal.absNorm (I : Ideal (𝓞 K)) = n
  obtain ⟨A, hA, hM⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  have hA' : P (Ideal.absNorm (A : Ideal (𝓞 K))) := ⟨A, congrArg f hA, rfl⟩
  have hex : ∃ n, P n := ⟨_, hA'⟩
  obtain ⟨I, hI, hnorm⟩ := Nat.find_spec hex
  refine ⟨I, hI, (Nat.cast_le.mpr (hnorm ▸ Nat.find_min' hex hA')).trans hM, ?_⟩
  intro J hJ hdiv
  obtain ⟨B, hIB⟩ := hdiv
  have hB0 : B ≠ 0 := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero I (by simpa [hz] using hIB)
  let B' : (Ideal (𝓞 K))⁰ := ⟨B, mem_nonZeroDivisors_of_ne_zero hB0⟩
  have heq : I = J * B' := Subtype.ext hIB
  have hBC : f (ClassGroup.mk0 B') = f C := by
    simpa only [heq, map_mul, hJ, one_mul] using hI
  have hmin : Ideal.absNorm (I : Ideal (𝓞 K)) ≤ Ideal.absNorm B :=
    hnorm ▸ Nat.find_min' hex (show P (Ideal.absNorm B) from ⟨B', hBC, rfl⟩)
  rw [hIB, map_mul] at hmin
  have hpos := Ideal.absNorm_pos_of_nonZeroDivisors B'
  have hle : Ideal.absNorm (J : Ideal (𝓞 K)) ≤ 1 := by
    by_contra! h
    exact hmin.not_gt (by simpa [B'] using Nat.mul_lt_mul_of_pos_right h hpos)
  rw [Ideal.one_eq_top]
  exact Ideal.absNorm_eq_one_iff.mp (Nat.le_antisymm hle (Ideal.absNorm_pos_of_nonZeroDivisors J))

section

variable {K} {G : Type*} [Group G]

/-- The kernel-reduced norm fibre in the quotient Minkowski bound. -/
def kernelReducedFibre (f : ClassGroup (𝓞 K) →* G) (n : ℕ) : Set (Ideal (𝓞 K)) :=
  {I | I.absNorm = n ∧ ∀ J : (Ideal (𝓞 K))⁰, f (ClassGroup.mk0 J) = 1 →
    (J : Ideal (𝓞 K)) ∣ I → (J : Ideal (𝓞 K)) = 1}

/-- Distinct classes represented by the *kernel-reduced* ideals at one norm. -/
noncomputable def reducedClassImages (f : ClassGroup (𝓞 K) →* G) (n : ℕ) : Set G :=
  (fun I : (Ideal (𝓞 K))⁰ => f (ClassGroup.mk0 I)) '' (Subtype.val ⁻¹' kernelReducedFibre f n)

/-- Kernel-reduced ideals of bounded norm cover exactly the image of the quotient
map, without assuming a finite codomain or surjectivity. -/
theorem range_eq_biUnion_reducedClassImages (f : ClassGroup (𝓞 K) →* G) :
    Set.range f = ⋃ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, reducedClassImages f n := by
  ext a
  simp only [Set.mem_range, Set.mem_iUnion, reducedClassImages, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨C, rfl⟩
    obtain ⟨I, hclass, hM, hfree⟩ := exists_minimal_class_image K f C
    exact ⟨_, mem_Ioc.mpr ⟨Ideal.absNorm_pos_of_nonZeroDivisors I, Nat.le_floor hM⟩,
      I, ⟨rfl, hfree⟩, hclass⟩
  · rintro ⟨n, _, I, _, rfl⟩
    exact ⟨ClassGroup.mk0 I, rfl⟩

theorem ncard_reducedClassImages_le_reduced (f : ClassGroup (𝓞 K) →* G) (n : ℕ) :
    (reducedClassImages f n).ncard ≤ (kernelReducedFibre f n).ncard := by
  have ht : (kernelReducedFibre f n).Finite := (Ring.HasFiniteQuotients.finite_absNorm_eq n).subset fun _ h => h.1
  have hs : (Subtype.val ⁻¹' kernelReducedFibre f n : Set (Ideal (𝓞 K))⁰).Finite :=
    ht.preimage Subtype.val_injective.injOn
  exact (Set.ncard_image_le hs).trans (Set.ncard_le_ncard_of_injOn Subtype.val (fun _ h => h) Subtype.val_injective.injOn ht)

/-- Count distinct represented classes, not representatives, before summing over norms. -/
theorem card_le_sum_reducedClassImages [Fintype G] (f : ClassGroup (𝓞 K) →* G) (hf : Function.Surjective f) :
    Fintype.card G ≤ ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, (reducedClassImages f n).ncard := by
  have h := (Ioc 0 ⌊minkowskiBound K⌋₊).set_ncard_biUnion_le (reducedClassImages f)
  rwa [← range_eq_biUnion_reducedClassImages, Set.range_eq_univ.mpr hf,
    Set.ncard_univ, Nat.card_eq_fintype_card] at h

end

/-- The size of any quotient of the class group is bounded by the number of
small ideals left after excluding all proper divisors killed by that quotient. -/
theorem card_class_image_le_reduced_minkowski {G : Type*} [Group G] [Fintype G]
    (f : ClassGroup (𝓞 K) →* G) (hf : Function.Surjective f) :
    Fintype.card G ≤ ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊,
      {I : Ideal (𝓞 K) | Ideal.absNorm I = n ∧
        ∀ J : (Ideal (𝓞 K))⁰, f (ClassGroup.mk0 J) = 1 → (J : Ideal (𝓞 K)) ∣ I →
          (J : Ideal (𝓞 K)) = 1}.ncard :=
  (card_le_sum_reducedClassImages f hf).trans (sum_le_sum fun n _ => ncard_reducedClassImages_le_reduced f n)

/-- In particular every class can be counted using only ideals with no
rational scalar prime divisor. The finite sieve is exact at each norm. -/
theorem classNumber_le_sum_scalarSieve (K : Type*) [Field K] [NumberField K] :
    classNumber K ≤ ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, (scalarSieveFibre K n.primeFactors n).ncard := by
  classical
  refine (card_class_image_le_reduced_minkowski K (MonoidHom.id (ClassGroup (𝓞 K)))
    Function.surjective_id).trans (sum_le_sum fun n _ => Set.ncard_le_ncard ?_
      ((Ring.HasFiniteQuotients.finite_absNorm_eq n).subset fun _ h => h.1))
  intro I hI
  refine ⟨hI.1, fun p hp hd => ?_⟩
  have hprime := Nat.prime_of_mem_primeFactors hp
  let J : Ideal (𝓞 K) := Ideal.span {(p : 𝓞 K)}
  have hJ : J ≠ 0 := by simpa [J] using (Nat.cast_ne_zero.mpr hprime.ne_zero : (p : 𝓞 K) ≠ 0)
  let J' : (Ideal (𝓞 K))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
  have hcl : ClassGroup.mk0 J' = 1 := (ClassGroup.mk0_eq_one_iff J'.2).mpr ⟨_, rfl⟩
  have h := congrArg Ideal.absNorm (hI.2 J' hcl hd)
  change Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = Ideal.absNorm 1 at h
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, map_one] at h
  exact (one_lt_pow₀ hprime.one_lt finrank_pos.ne').ne' h

/-- Keep only tuples with no common prime divisor in the finite Minkowski bound. -/
theorem classNumber_le_primitive_tuples_minkowski :
    classNumber K ≤ ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊,
      ((Nat.finMulAntidiag (finrank ℚ K) n).filter (fun a => Finset.univ.gcd a = 1)).card := by
  classical
  refine (classNumber_le_sum_scalarSieve K).trans (sum_le_sum fun n hn => ?_)
  have hn' := (mem_Ioc.mp hn).1.ne'
  rw [scalarSieveFibre_primeFactors K hn']
  exact ncard_primitive_ideal_absNorm_eq_le K hn'

/-- For two factors, coprimality forces every prime power dividing n to
belong wholly to one coordinate. The first coordinate's prime support
therefore distinguishes the admissible pairs. -/
theorem card_primitive_pairs_le (n : ℕ) (hn : n ≠ 0) :
    ((Nat.finMulAntidiag 2 n).filter (fun a => Finset.univ.gcd a = 1)).card ≤ 2 ^ n.primeFactors.card := by
  classical
  let T := (Nat.finMulAntidiag 2 n).filter (fun a => Finset.univ.gcd a = 1)
  have facts (a : Fin 2 → ℕ) (ha : a ∈ T) : a 0 * a 1 = n ∧ (a 0).Coprime (a 1) := by
    obtain ⟨h, g⟩ := Finset.mem_filter.mp ha
    exact ⟨by simpa [Fin.prod_univ_two] using (Nat.mem_finMulAntidiag.mp h).1,
      by simpa [Finset.univ_fin2, Finset.gcd_insert, Finset.gcd_singleton, gcd_eq_nat_gcd, Nat.Coprime] using g⟩
  rw [← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn (fun a : Fin 2 → ℕ => (a 0).primeFactors)
  · intro a ha
    exact Finset.mem_powerset.mpr (Nat.primeFactors_mono ((facts a ha).1 ▸ Nat.dvd_mul_right _ _) hn)
  · intro a ha b hb he
    obtain ⟨ha0,ha1⟩ := facts a ha
    obtain ⟨hb0,hb1⟩ := facts b hb
    have H {x y z w : ℕ} (hxy : x * y = n) (hzw : z * w = n) (hcop : z.Coprime w)
        (hs : x.primeFactors = z.primeFactors) : x ∣ z := by
      have hx : x ≠ 0 := fun h => hn (by simpa [h] using hxy.symm)
      have hc : x.Coprime w := by
        by_contra h
        obtain ⟨p, hp, hpx, hpw⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
        have : p ∈ z.primeFactors := hs ▸ Nat.mem_primeFactors.mpr ⟨hp,hpx,hx⟩
        exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, Nat.dvd_of_mem_primeFactors this, hpw⟩ hcop
      exact hc.dvd_of_dvd_mul_right (hzw ▸ hxy ▸ Nat.dvd_mul_right _ _)
    have h0 := Nat.dvd_antisymm (H ha0 hb0 hb1 he) (H hb0 ha0 ha1 he.symm)
    have h1 : a 1 = b 1 := by
      rw [← hb0, h0] at ha0
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (fun h => hn (by simpa [h] using hb0.symm))) ha0
    funext i; fin_cases i <;> assumption

/-- In a quadratic field each prime power can go to only one of the two
coordinates. Thus the finite bound uses distinct prime factors, not divisors. -/
theorem classNumber_le_sum_two_pow_primeFactors (hd : finrank ℚ K = 2) :
    classNumber K ≤ ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, 2 ^ n.primeFactors.card := by
  classical
  refine (classNumber_le_primitive_tuples_minkowski K).trans (sum_le_sum fun n hn => ?_)
  rw [hd]
  exact card_primitive_pairs_le n (mem_Ioc.mp hn).1.ne'

/-- The former unsieved divisor sum follows by forgetting coprimality. -/
theorem classNumber_le_sum_zeta_pow_minkowski :
    classNumber K ≤ ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, (ζ ^ finrank ℚ K : ArithmeticFunction ℕ) n := by
  classical
  refine (classNumber_le_primitive_tuples_minkowski K).trans (sum_le_sum fun n _ => ?_)
  rw [← card_finMulAntidiag_eq_zeta_pow]
  exact card_filter_le _ _

/-- Signature-sensitive bound for the class number of a number field. -/
theorem classNumber_le_minkowski_mul_pow :
    (classNumber K : ℝ) ≤ minkowskiBound K * (1 + Real.log (minkowskiBound K)) ^ (finrank ℚ K - 1) := by
  exact (Nat.cast_le.2 (classNumber_le_sum_zeta_pow_minkowski K)).trans
    (sum_zeta_pow_le finrank_pos (one_le_minkowskiBound K))

theorem classNumber_le_sqrt_discr_mul_pow_pred :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ (finrank ℚ K - 1) := by
  have hM := minkowskiBound_le_sqrt_abs_discr K
  have hpos : 0 < minkowskiBound K := lt_of_lt_of_le zero_lt_one (one_le_minkowskiBound K)
  have hlog := Real.log_nonneg (one_le_minkowskiBound K)
  exact (classNumber_le_minkowski_mul_pow K).trans (by gcongr)

theorem classNumber_le_sqrt_discr_mul_pow :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ finrank ℚ K := by
  refine (classNumber_le_sqrt_discr_mul_pow_pred K).trans ?_
  have := Real.log_nonneg (one_le_sqrt_abs_discr K)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _))
    (Real.sqrt_nonneg _)

theorem classNumber_le_of_finrank_eq_two_mul {f : ℕ} (hf : finrank ℚ K = 2 * f) :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ (2 * f) :=
  hf ▸ classNumber_le_sqrt_discr_mul_pow K

end GlobalTheory
