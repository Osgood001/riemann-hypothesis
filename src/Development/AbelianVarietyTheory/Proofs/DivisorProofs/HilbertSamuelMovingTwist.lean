module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedTwistSectionCount
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeAtNearbyIndices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry Filter Topology Asymptotics
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.VolBr

private theorem exists_nonzero_of_log_count_tendsto {X : Type*} [Zero X]
    (S : ℕ → Set X) (d : ℕ) {a : ℝ} (ha : 0 < a)
    (h : Tendsto (fun n : ℕ => Real.log ((S n).ncard : ℝ) / (n : ℝ) ^ d) atTop (𝓝 a)) :
    ∃ n : ℕ, ∃ u : X, u ≠ 0 ∧ u ∈ S n := by
  obtain ⟨n, hn, hpos⟩ := ((eventually_gt_atTop 0).and (h.eventually (lt_mem_nhds ha))).exists
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := (lt_div_iff₀ (pow_pos hn' d)).mp hpos
  rw [zero_mul] at hlog
  have hcard : 1 < (S n).ncard := by
    exact_mod_cast (Real.log_pos_iff (Nat.cast_nonneg _)).mp hlog
  by_contra! hh
  have hsub : S n ⊆ {0} := fun u hu => by
    by_contra hne
    exact hh n u hne hu
  have hle := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  simp at hle
  omega

private theorem small_error_of_normalized_limit (v : ℕ → ℝ) (d : ℕ) (a : ℝ)
    (h : Tendsto (fun n : ℕ => v n / (n : ℝ) ^ d) atTop (𝓝 a)) :
    (fun n : ℕ => v n - a * (n : ℝ) ^ d) =o[atTop] fun n : ℕ => (n : ℝ) ^ d := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact fun he => (ne_of_gt (pow_pos this d) he).elim
  · have h' := h.sub_const a
    rw [sub_self] at h'
    apply h'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [sub_div]
    field_simp

private theorem tendsto_sublinear_reindex {f : ℕ → ℝ} {a : ℝ} {d : ℕ}
    (hf : Tendsto (fun N : ℕ => f N / (N : ℝ) ^ d) atTop (𝓝 a))
    (m : ℕ → ℕ) (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 0)) (K : ℕ) :
    (∀ᶠ N : ℕ in atTop, K * m N ≤ N) ∧
    Tendsto (fun N : ℕ => f (N - K * m N) / (N : ℝ) ^ d) atTop (𝓝 a) ∧
    Tendsto (fun N : ℕ => f (N + K * m N) / (N : ℝ) ^ d) atTop (𝓝 a) := by
  have hsmall : Tendsto (fun N : ℕ => (K : ℝ) * m N / N) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using hm.const_mul (K : ℝ)
  have hle : ∀ᶠ N : ℕ in atTop, K * m N ≤ N := by
    filter_upwards [(tendsto_order.1 hsmall).2 1 zero_lt_one, eventually_gt_atTop 0] with N hr hN
    have Npos : (0 : ℝ) < N := by exact_mod_cast hN
    exact_mod_cast (show (K : ℝ) * m N ≤ N by linarith [(div_lt_iff₀ Npos).mp hr])
  refine ⟨hle, ?_⟩
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have reindex (Q : ℕ → ℕ) (hQ : Tendsto (fun N : ℕ => (Q N : ℝ) / N) atTop (𝓝 1)) :
      Tendsto (fun N : ℕ => f (Q N) / (N : ℝ) ^ d) atTop (𝓝 a) := by
    simpa only [one_pow, mul_one] using
      (tendsto_comp_div_pow_of_ratio d f a 1 Q zero_lt_one hf hQ).1
  constructor
  · apply reindex
    have h := hconst.sub hsmall
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [hle, eventually_gt_atTop 0] with N hn hN
    have Npos : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [Nat.cast_sub hn, Nat.cast_mul]
    field_simp
  · apply reindex
    have h := hconst.add hsmall
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have Npos : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [Nat.cast_add, Nat.cast_mul]
    field_simp

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

private theorem mapsTo_pow_small_section (P : Pair p) {u : X.functionField} {a b : ℤ}
    (hu : u ∈ P.Bl a b 1) (j c : ℤ) (m : ℕ) :
    Set.MapsTo (fun f => u ^ m * f) (P.Bl j c 1) (P.Bl (m * a + j) (m * b + c) 1) := by
  obtain ⟨hp, hpow⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P a b u hu.1 m
  intro f hf
  obtain ⟨hm, hmul⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P _ _ _ _
    (u ^ m) f hp hf.1
  refine ⟨hm, fun σ y => ?_⟩
  rw [hmul, hpow]
  have hnu (i j : ℤ) (v : X.functionField) : 0 ≤ P.nu i j σ y v :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  exact (mul_le_of_le_one_left (hnu j c f) (pow_le_one₀ (hnu a b u) (hu.2 σ y))).trans (hf.2 σ y)

private theorem lc_le_of_mapsTo (P : Pair p) {i j a b : ℤ} {f : X.functionField → X.functionField}
    (hm : Set.MapsTo f (P.Bl i j 1) (P.Bl a b 1)) (hi : Function.Injective f)
    (hfin : (P.Bl a b 1).Finite) : P.lc i j 1 ≤ P.lc a b 1 := by
  have hcard := Set.ncard_le_ncard_of_injOn f hm hi.injOn hfin
  simp only [Pair.lc]
  rcases Nat.eq_zero_or_pos (P.Bl i j 1).ncard with hz | hp
  · rw [hz, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hcard)

/-- Multiplication by a nonzero unit-ball section of the second line bundle gives
monotonicity in the twist, with no assumption on the first line bundle. -/
theorem lc_mono_twist_of_small (P : Pair p) {s : X.functionField}
    (hs : s ∈ P.Bl 0 1 1) (hs₀ : s ≠ 0) (N : ℤ) {i j : ℕ}
    (hij : i ≤ j) (hfin : (P.Bl N j 1).Finite) :
    P.lc N i 1 ≤ P.lc N j 1 := by
  have hm := mapsTo_pow_small_section P hs N i (j - i)
  have he : ((j - i : ℕ) : ℤ) + i = j := by omega
  simp only [mul_zero, zero_add, mul_one, he] at hm
  exact lc_le_of_mapsTo P hm (mul_right_injective₀ (pow_ne_zero _ hs₀)) hfin

private theorem tendsto_lc_nat_twist (P : Pair p) (d : ℕ) (a : ℝ)
    (hfin : ∀ᶠ N : ℕ in atTop, (P.Bl N 0 1).Finite)
    (hbase : Tendsto (fun N : ℕ => P.lc N 0 1 / (N : ℝ) ^ d) atTop (𝓝 a))
    (e : ℤ) {A B : ℕ} {u v : X.functionField} (hu0 : u ≠ 0) (hu : u ∈ P.Bl A e 1)
    (hv0 : v ≠ 0) (hv : v ∈ P.Bl B (-e) 1) (m : ℕ → ℕ)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 0)) :
    (∀ᶠ N : ℕ in atTop, (P.Bl N ((m N : ℤ) * e) 1).Finite) ∧
      Tendsto (fun N : ℕ => P.lc N ((m N : ℤ) * e) 1 / (N : ℝ) ^ d) atTop (𝓝 a) := by
  obtain ⟨hcut, hlow, -⟩ := tendsto_sublinear_reindex hbase m hm A
  obtain ⟨-, -, hhigh⟩ := tendsto_sublinear_reindex hbase m hm B
  have he := (tendsto_atTop_mono (fun N : ℕ => Nat.le_add_right N (B * m N)) tendsto_id).eventually hfin
  have hmaps (N : ℕ) : Set.MapsTo (fun f => v ^ m N * f)
      (P.Bl N ((m N : ℤ) * e) 1) (P.Bl (N + B * m N : ℕ) 0 1) := by
    have ei : (m N : ℤ) * B + N = ((N + B * m N : ℕ) : ℤ) := by push_cast; ring
    have ej : (m N : ℤ) * -e + (m N : ℤ) * e = 0 := by ring
    simpa only [ei, ej] using mapsTo_pow_small_section P hv N ((m N : ℤ) * e) (m N)
  have hfin' : ∀ᶠ N : ℕ in atTop, (P.Bl N ((m N : ℤ) * e) 1).Finite := by
    filter_upwards [he] with N hN
    exact (hN.preimage (mul_right_injective₀ (pow_ne_zero _ hv0)).injOn).subset (hmaps N)
  refine ⟨hfin', hlow.squeeze' hhigh ?_ ?_⟩
  · filter_upwards [hcut, hfin'] with N hN hNfin
    have ei : (m N : ℤ) * A + ((N - A * m N : ℕ) : ℤ) = N := by
      rw [Nat.cast_sub hN, Nat.cast_mul]
      ring
    have hmap := mapsTo_pow_small_section P hu (N - A * m N : ℕ) 0 (m N)
    rw [ei, add_zero] at hmap
    exact div_le_div_of_nonneg_right (lc_le_of_mapsTo P hmap (mul_right_injective₀ (pow_ne_zero _ hu0)) hNfin)
      (by positivity)
  · filter_upwards [he] with N hN
    exact div_le_div_of_nonneg_right (lc_le_of_mapsTo P (hmaps N) (mul_right_injective₀ (pow_ne_zero _ hv0)) hN)
      (by positivity)

/-- Two nonzero small sections of opposite twists propagate the untwisted asymptotic
to every signed sublinear twist, including eventual finiteness. -/
theorem tendsto_lc_signed_of_small_sections (P : Pair p) (d : ℕ) (a : ℝ)
    (hfin : ∀ᶠ N : ℕ in atTop, (P.Bl N 0 1).Finite)
    (hbase : Tendsto (fun N : ℕ => P.lc N 0 1 / (N : ℝ) ^ d) atTop (𝓝 a))
    (hplus : ∃ K : ℕ, ∃ u : X.functionField, u ≠ 0 ∧ u ∈ P.Bl K 1 1)
    (hminus : ∃ K : ℕ, ∃ u : X.functionField, u ≠ 0 ∧ u ∈ P.Bl K (-1) 1)
    (z : ℕ → ℤ) (hz : Tendsto (fun N : ℕ => ((z N).natAbs : ℝ) / N) atTop (𝓝 0)) :
    (∀ᶠ N : ℕ in atTop, (P.Bl N (z N) 1).Finite) ∧
      Tendsto (fun N : ℕ => P.lc N (z N) 1 / (N : ℝ) ^ d) atTop (𝓝 a) := by
  obtain ⟨K, u, hu0, hu⟩ := hplus
  obtain ⟨L, v, hv0, hv⟩ := hminus
  obtain ⟨hpf, hp⟩ := tendsto_lc_nat_twist P d a hfin hbase 1 hu0 hu hv0 hv _ hz
  obtain ⟨hnf, hn⟩ := tendsto_lc_nat_twist P d a hfin hbase (-1) hv0 hv hu0 (by simpa using hu) _ hz
  simp only [mul_one, mul_neg_one, Int.natCast_natAbs] at hpf hp hnf hn
  constructor
  · filter_upwards [hpf, hnf] with N hpf hnf
    by_cases h : 0 ≤ z N
    · simpa only [abs_of_nonneg h] using hpf
    · simpa only [abs_of_neg (lt_of_not_ge h), neg_neg] using hnf
  · apply (hp.if' (p := fun N => 0 ≤ z N) hn).congr
    intro N
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), neg_neg]

/-- Hilbert–Samuel remains valid if a fixed auxiliary line bundle is taken to an
arbitrary signed sublinear power, when the leading arithmetic intersection is positive. -/
theorem lc_signed_twist_of_pos (hHS : Published.ArithHilbertSamuel) {D : ℕ}
    (hX : IsArithVar p D) (P : Pair p) {a : ℝ} (hnef : P.L.IsNef D)
    (ha : P.L.IsSelfInter a) (hpos : 0 < a) (z : ℕ → ℤ)
    (hz : Tendsto (fun n : ℕ => ((z n).natAbs : ℝ) / n) atTop (𝓝 0)) :
    (∀ᶠ n : ℕ in atTop, (P.Bl n (z n) 1).Finite) ∧
      (fun n : ℕ => P.lc n (z n) 1 - a / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have fixed := lc_fixed_twist_tendsto hHS hX P hnef ha
  have witness (j : ℤ) : ∃ n : ℕ, ∃ u : X.functionField, u ≠ 0 ∧ u ∈ P.Bl n j 1 :=
    exists_nonzero_of_log_count_tendsto (fun n : ℕ => P.Bl n j 1) (D + 1)
      (div_pos hpos (by positivity)) (fixed j).2
  obtain ⟨hf, hlim⟩ := tendsto_lc_signed_of_small_sections P (D + 1) _ (fixed 0).1
    (fixed 0).2 (witness 1) (witness (-1)) z hz
  exact ⟨hf, small_error_of_normalized_limit _ _ _ hlim⟩

private theorem rep_zp (P : Pair p) (b : ℤ) : P.Rep 0 b (zp P.A b) := by
  have hA := (Pair.rep_base k X p P).2.1
  have h := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ b.toNat hA)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-b).toNat hA))
  simpa only [zp, mul_zero, neg_zero, add_zero, mul_one, ← sub_eq_add_neg,
    Int.toNat_sub_toNat_neg] using h

/-- Convert the rational-function ball calculation to the corresponding tensor bundles. -/
theorem signed_twist_of_ball_asymptotic (P : Pair p) (d : ℕ) (c : ℝ) (z : ℕ → ℤ)
    (h : (∀ᶠ n : ℕ in atTop, (P.Bl n (z n) 1).Finite) ∧
      (fun n : ℕ => P.lc n (z n) 1 - c * (n : ℝ) ^ d) =o[atTop] fun n : ℕ => (n : ℝ) ^ d) :
    let S := fun n : ℕ => ((P.L.pow n).tens (zp P.A (z n))).smallSec
    (∀ᶠ n : ℕ in atTop, (S n).Finite) ∧
      (fun n : ℕ => Real.log ((S n).ncard : ℝ) - c * (n : ℝ) ^ d) =o[atTop] fun n : ℕ => (n : ℝ) ^ d := by
  have he (n : ℕ) :
      ((P.L.pow n).tens (zp P.A (z n))).smallSec.encard = (P.Bl n (z n) 1).encard := by
    have hL := Pair.rep_pow k X p P 1 0 P.L n (Pair.rep_base k X p P).1
    have hR : P.Rep n (z n) ((P.L.pow n).tens (zp P.A (z n))) := by
      simpa using Pair.rep_tens k X p P _ _ _ _ _ _ hL (rep_zp P (z n))
    exact SmallBall.encard_eq_Bl P hR _ 1 zero_le_one
      (fun _ => by simp only [HermLB.smallSec, Set.mem_ofPred_eq, one_pow])
  have hc (n : ℕ) :
      ((P.L.pow n).tens (zp P.A (z n))).smallSec.ncard = (P.Bl n (z n) 1).ncard :=
    congrArg ENat.toNat (he n)
  constructor
  · filter_upwards [h.1] with n hn
    exact Set.encard_lt_top_iff.mp (by rw [he]; exact hn.encard_lt_top)
  simpa only [hc, Pair.lc] using h.2

/-- The small-section Hilbert–Samuel formula for signed moving twists. The twist need
not preserve nefness: only its exponent is required to be sublinear in the main degree. -/
theorem _root_.GlobalTheory.Published.ArithHilbertSamuel.signed_twist_of_pos
    (hHS : Published.ArithHilbertSamuel) {D : ℕ} (hX : IsArithVar p D) (L A : HermLB p)
    {a : ℝ} (hnef : L.IsNef D) (ha : L.IsSelfInter a) (hpos : 0 < a)
    (z : ℕ → ℤ) (hz : Tendsto (fun n : ℕ => ((z n).natAbs : ℝ) / n) atTop (𝓝 0)) :
    let S := fun n : ℕ => ((L.pow n).tens (zp A (z n))).smallSec
    (∀ᶠ n : ℕ in atTop, (S n).Finite) ∧
      (fun n : ℕ => Real.log ((S n).ncard : ℝ) - a / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  obtain ⟨P, rfl, rfl⟩ := exists_pair L A
  exact signed_twist_of_ball_asymptotic P _ _ z (lc_signed_twist_of_pos hHS hX P hnef ha hpos z hz)

end GlobalTheory.VolBr
