import Mathlib

open Nat hiding add_le_add log card_univ lt_floor_add_one
open Submodule (IsPrincipal cardQuot_apply)
open Summable hiding norm
open Continuous hiding norm
open Filter.Tendsto hiding norm
open Complex hiding log exp exp_add log_inv
open Int hiding log_inv norm_eq_abs cast_nonneg cast_pos cast_ne_zero
open Finset hiding Icc Ioc
open Subgroup MulChar Inv NumberField Filter Eventually Topology IsDedekindDomain Ideal Set Function Algebra Module Fintype Metric HeightOneSpectrum IsCyclotomicExtension IntermediateField AlgEquiv RingHom Equiv ClassGroup RingOfIntegers FiniteField ZLattice Iff Prod Quotient MonoidHom Or QuasiFinite IsArithFrobAt HasSum IsPrimitiveRoot IsPrime Finite ZMod Real

noncomputable section

open scoped Classical
abbrev DC := DirichletCharacter ℂ
abbrev Pr := Prime
abbrev nh1 := 𝓝[>] (1 : ℝ)
abbrev rN (n : ℕ) : ℝ := n
abbrev zN (n : ℕ) : ℤ := n
abbrev UZ l := (ZMod l)ˣ
abbrev sy := @Eq.symm
abbrev et := @Eq.trans
abbrev hl := @And.left
abbrev hr := @And.right
abbrev hext := @HeightOneSpectrum.ext
abbrev uext := @Units.ext
abbrev fo := @Fact.out
abbrev tlt := @Summable.tsum_le_tsum
abbrev cl := Complex.log
abbrev d1 : DC 1 := 1
lemma nh1_f (h : ∀ᶠ _ in nh1, False) : False := h.exists.choose_spec

variable {E : Type} [Field E] [NumberField E] {l : ℕ} (chi : DC l)

section
variable (E)
abbrev Idl := Ideal $ 𝓞 E
abbrev Prm := HeightOneSpectrum $ 𝓞 E
end

abbrev qN (q : Prm E) := absNorm $ asIdeal q
abbrev qC (q : Prm E) := Coprime $ qN q
abbrev rp (s : ℝ) (a : Idl E) := rN a.absNorm ^ (-s)
abbrev rpq (s : ℝ) (q : Prm E) := rp s q.asIdeal
def cf (s : ℝ) (a : Idl E) := chi a.absNorm * (a.absNorm : ℂ) ^ (-(s : ℂ))

theorem pa_cpow_eq (n : ℕ) (s : ℝ) : (n : ℂ) ^ (-(s : ℂ)) = ↑((n : ℝ) ^ (-s)) := by
  simp [ofReal_cpow n.cast_nonneg]

lemma cf_mul (s : ℝ) (a b : Idl E) : cf chi s (a * b) = cf chi s a * cf chi s b := by
  simp [cf, natCast_mul_natCast_cpow]
  ring

lemma norm_cf_le {s : ℝ} {a : Idl E} : ‖cf chi s a‖ ≤ rp s a := by
  rw [cf, norm_mul, pa_cpow_eq, Complex.norm_of_nonneg]
  grw [chi.norm_le_one]
  simp
  positivity

lemma aN0 {I : Idl E} (h : I ≠ ⊥) : absNorm I ≠ 0 := absNorm_eq_zero_iff.not.mpr h

section
variable (q : Prm E)

theorem two_le_Nrm : 2 ≤ qN q := by
  grind [aN0 q.ne_bot, absNorm_eq_one_iff.not.mpr q.isPrime.ne_top]

section
variable {s : ℝ} (hs : 1 < s)
include hs

theorem Nrm_rpow_le_inv : rpq s q ≤ inv (qN q : ℝ) := by
  rw [← rpow_neg_one]
  apply rpow_le_rpow_of_exponent_le
  exact_mod_cast le_trans one_le_two $ two_le_Nrm q
  linarith

theorem Nrm_rpow_le_half : rpq s q ≤ 1 / 2 := by
  grw [Nrm_rpow_le_inv q hs]
  rw [one_div]
  gcongr
  exact_mod_cast two_le_Nrm q

end
end

section

lemma cont_cf {chi : DC l} {a : Idl E} (ha : a ≠ ⊥) : Continuous (cf chi · a) :=
  mul continuous_const $ const_cpow continuous_ofReal.neg $ inl $ mpr cast_ne_zero $ aN0 ha

section
variable (E)
def Lser (s : ℝ) := ∑' a : Idl E, cf chi s a
def Psum (s : ℝ) := ∑' q : Prm E, cf chi s q.asIdeal
def ab2 (s : ℝ) := ∑' q : Prm E, -cl (1 - cf chi s q.asIdeal)
def PE (s : ℝ) := ∑' q : Prm E, rpq s q
def Pcl {l : ℕ} (a : ZMod l) (s : ℝ) :=
  ∑' q : Prm E, indicator {q | (qN q : ZMod l) = a} (rpq s) q

section
variable {s : ℝ} (hs : 1 < s)
include hs

lemma hasSum_ideal :
    Summable (rp (E := E) s) ∧ dedekindZeta E s = Lser E d1 s := by
  let F n := {I : Idl E // absNorm I = n}
  let cF n := Nat.card $ F n
  have hterm n : LSeries.term (fun n ↦ (cF n : ℂ)) s n = ↑(rN (cF n) * n ^ (-s)) := by
    by_cases hn : n = 0 <;> simp [hn, LSeries.term_def, zero_rpow (by linarith : -s ≠ 0), div_eq_mul_inv, ← cpow_neg, pa_cpow_eq]
  obtain ⟨t, ht0, _, hts⟩ := (((tendsto_sub_one_mul_dedekindZeta_nhdsGT E).eventually_ne $
    mpr ofReal_ne_zero $ dedekindZeta_residue_ne_zero E).and $ Ioo_mem_nhdsGT hs).exists
  have hLs := LSeriesSummable.of_re_le_re (s := t) (s' := s) (by simpa using le_of_lt hts) $
    of_not_not $ mt tsum_eq_zero_of_not_summable $ right_ne_zero_of_mul ht0
  rw [LSeriesSummable, funext hterm] at hLs
  let e := sigmaFiberEquiv (absNorm : Idl E → ℕ)
  have (n : ℕ) : Finite (F n) := (finite_setOfPred_absNorm_eq n).to_subtype
  have hfib n : cF n * n ^ (-s) = ∑' x, rp s (e ⟨n, x⟩) := by
    simp [rp, e, fun x : F n ↦ x.2, cF, F]
  have hsig := mpr (summable_sigma_of_nonneg (f := fun p ↦ rp s $ e p) fun _ ↦ by positivity)
    ⟨fun _ ↦ of_finite, congr (mp summable_ofReal hLs) hfib⟩
  constructor
  exact mp (summable_iff e) hsig
  rw [dedekindZeta, LSeries, tsum_congr hterm, ← ofReal_tsum, tsum_congr hfib,
    ← hsig.tsum_sigma, tsum_eq e, ofReal_tsum, Lser]
  simp [cf, d1, MulChar.one_apply $ isUnit_of_subsingleton _, pa_cpow_eq, rp]

theorem summable_prm_rpow : Summable fun q : Prm E ↦ rpq s q :=
  (hl $ hasSum_ideal E hs).comp_injective fun _ _ ↦ hext

theorem exp_ab2_eq_Lser :
    Complex.exp (ab2 E chi s) = Lser E chi s := by
  let f := cf (E := E) chi s
  have hfS : Summable f := .of_norm_bounded (hasSum_ideal E hs).1 fun _ ↦ norm_cf_le chi
  let T (S : Finset $ Prm E) := {a : Idl E | ∀ q ∈ S, ¬ asIdeal q ∣ a}
  have hfin (S : Finset $ Prm E) : (∏ q ∈ S, (1 - f q.asIdeal)) * Lser E chi s = ∑' a, (T S).indicator f a := by
    induction S using Finset.induction_on with
    | empty => simp [Lser, T, f]
    | insert q S hq ih =>
      rw [prod_insert hq, mul_assoc, ih, sub_mul, one_mul, ← tsum_mul_left]
      set qi := asIdeal q
      have hm : ∑' a, indicator (T S ∩ {a | qi ∣ a}) f a = ∑' a, f qi * indicator (T S) f a := by
        rw [← (mul_right_injective₀ q.ne_bot).tsum_eq fun a ha ↦ (support_indicator_subset ha).2.imp fun _ ↦ sy]
        apply tsum_congr
        intro a
        simp [f, cf_mul, indicator_apply, qi, show qi * a ∈ T S ↔ a ∈ T S from forall₂_congr fun r hr ↦ not_congr $
          r.prime.dvd_mul.trans $ or_iff_right fun hrq ↦ hq $ hext (mp (prime_dvd_prime_iff_eq r.prime q.prime) hrq) ▸ hr]
      rw [← hm, ← (hfS.indicator _).tsum_sub $ hfS.indicator _]
      apply tsum_congr
      intro a
      simp [indicator_apply]
      split_ifs <;> grind
  have hP := (of_norm_bounded (summable_prm_rpow E hs) fun _ ↦ norm_cf_le chi).clog_one_sub.hasSum.cexp
  have hp' (q : Prm E) : 1 - cf chi s q.asIdeal ≠ 0 := fun h ↦ by
    have := norm_cf_le (s := s) (a := asIdeal q) chi
    rw [← mp sub_eq_zero h, norm_one] at this
    linarith [Nrm_rpow_le_half q hs]
  simp [HasProd, SummationFilter.unconditional_filter, exp_log $ hp' _] at hP
  have h1 := tendsto_nhds_unique (b := 1) ((hP.mul_const $ Lser E chi s).congr hfin) $ by
    rw [← tsum_ite_eq (⊤ : Idl E) fun _ ↦ (1 : ℂ)]
    apply tendsto_tsum_of_dominated_convergence (hasSum_ideal E hs).1
    intro a
    apply tendsto_const_nhds.congr'
    by_cases ha1 : a = ⊤
    apply of_forall
    intro
    simp [ha1, indicator_apply, T, f, cf, ← one_eq_top]
    exact fun q _ ↦ q.prime.not_dvd_one
    by_cases ha0 : a = ⊥
    apply of_forall
    intro
    simp [ha0, indicator_apply, f, cf, ne_of_gt $ zero_lt_one.trans hs]
    obtain ⟨m, hm, ham⟩ := exists_le_maximal a ha1
    let q : Prm E := ⟨m, hm.isPrime, ne_bot_of_le_ne_bot ha0 ham⟩
    filter_upwards [eventually_ge_atTop {q}] with S hS
    simp [ha1]
    rw [indicator_of_notMem]
    exact fun h ↦ h q (singleton_subset_iff.mp hS) $ mpr dvd_iff_le ham
    apply of_forall
    intros
    grw [norm_indicator_le_norm_self]
    exact norm_cf_le chi
  rw [← mul_one $ Complex.exp _, ← h1, ← mul_assoc, ab2, tsum_neg, ← Complex.exp_add]
  simp

theorem ab2_sub_Psum :
    ‖ab2 E chi s - Psum E chi s‖ ≤ PE E 2 := by
  have hzs := of_norm_bounded (summable_prm_rpow E hs) fun _ ↦ norm_cf_le chi
  rw [ab2, Psum, PE, ← hzs.clog_one_sub.neg.tsum_sub hzs]
  apply tsum_of_norm_bounded (summable_prm_rpow E one_lt_two).hasSum
  intro q
  set z := cf chi s q.asIdeal
  have := le_trans (norm_cf_le chi) $ Nrm_rpow_le_half q hs
  rw [← norm_neg, neg_sub, sub_neg_eq_add, add_comm, ← sub_neg_eq_add, sub_eq_add_neg 1]
  grw [norm_log_one_add_sub_self_le, norm_neg, inv_le_of_inv_le₀ two_pos,
    le_trans (norm_cf_le chi) $ Nrm_rpow_le_inv q hs]
  simp_all
  linarith
  simp
  linarith

end

def peC := PE E 2 + |log (dedekindZeta_residue E)| + 1

theorem pe_log_bdd : ∀ᶠ s in nh1, |PE E s - log (1 / (s - 1))| ≤ peC E := by
  have hres := dedekindZeta_residue_pos E
  filter_upwards [self_mem_nhdsWithin,
    eventually ((continuousAt_log $ ne_of_gt hres).tendsto.comp $ by
      simpa [norm_of_nonneg $ le_of_lt hres] using comp (tendsto continuous_norm _) $
        tendsto_sub_one_mul_dedekindZeta_nhdsGT E) $ ball_mem_nhds _ zero_lt_one] with s (hs : 1 < s) hball
  have he := congrArg norm $ exp_ab2_eq_Lser E d1 hs
  rw [norm_exp, ← hr $ hasSum_ideal E hs] at he
  have hd := le_trans (abs_re_le_norm _) $ ab2_sub_Psum E d1 hs
  simp [Psum, cf, d1, MulChar.one_apply $ isUnit_of_subsingleton _, pa_cpow_eq, ← ofReal_tsum] at hd
  simp [Real.dist_eq, ← ofReal_one, ← ofReal_sub, abs_of_pos $ mpr sub_pos hs, ← he,
    log_mul (ne_of_gt $ mpr sub_pos hs) $ ne_of_gt $ exp_pos _] at hball
  grind [log_inv, peC, PE]

lemma finite_not_coprime (n : ℕ) (hn : n ≠ 0) :
    {q : Prm E | ¬ qC q n}.Finite := by
  apply subset $ finite_factors (I := span {↑n}) _
  intro q hq
  apply mpr dvd_span_singleton
  set qi := asIdeal q
  obtain ⟨k, hk⟩ := of_not_not fun hd ↦ hq $ show Coprime (absNorm qi) n from
    absNorm_pow_inertiaDeg (qi.under ℤ) qi ▸ ((absNorm_under_prime qi).coprime_iff_not_dvd.mpr hd).pow_left _
  simpa [hk] using qi.mul_mem_right ↑k $ by simpa using absNorm_mem $ qi.under ℤ
  simpa using hn

end

section
variable {E' : Type} [Field E'] [NumberField E'] [Algebra E E']

def under (P : Prm E') : Prm E :=
  ⟨P.asIdeal.under $ 𝓞 E, IsPrime.under _ _, under_ne_bot (𝓞 E) P.ne_bot⟩

def primesOverEquiv (q : Prm E) :
    q.asIdeal.primesOver (𝓞 E') ≃ {P : Prm E' // under P = q} :=
  ⟨fun Q ↦ ⟨⟨Q.1, Q.2.1, ne_bot_of_liesOver_of_ne_bot q.ne_bot Q.1⟩, hext $ sy $ Q.2.2.over⟩,
   fun P ↦ ⟨asIdeal P, P.1.isPrime, ⟨sy $ congrArg asIdeal P.2⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

theorem fibre_sum_le {f : Prm E' → ℝ} (h : Prm E → ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hfh : ∀ a, f a ≤ h (under a)) (hh : Summable h) :
    Summable f ∧ ∑' a, f a ≤ finrank E E' * ∑' b, h b := by
  let e := sigmaFiberEquiv $ under (E := E) (E' := E')
  have (b : Prm E) : Fintype (b.asIdeal.primesOver (𝓞 E')) := (finite_primesOver _).fintype
  have hfb b : ∑' x : {a : Prm E' // under a = b}, f x ≤ finrank E E' * h b := by
    rw [← (primesOverEquiv b).tsum_eq, tsum_fintype]
    apply le_trans $ sum_le_sum fun x _ ↦ (primesOverEquiv b x).2 ▸ hfh _
    rw [sum_const, card_univ, nsmul_eq_mul, IsFractionRing.finrank_eq (𝓞 E) E (𝓞 E') E',
      ← sum_ramification_inertia_eq_finrank b.asIdeal $ 𝓞 E', Fintype.card_eq_sum_ones]
    gcongr
    obtain ⟨Q⟩ := b.asIdeal.nonempty_primesOver (S := 𝓞 E')
    exact le_trans (hf0 _) $ (primesOverEquiv b Q).2 ▸ hfh _
    exact mul_pos (ramificationIdx_pos _ _) $ inertiaDeg_pos _ _
  have hs2 := (mul_left _ hh).of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ hf0 _) hfb
  have hsig : Summable fun p ↦ f $ e p := mpr (summable_sigma_of_nonneg fun _ ↦ hf0 _)
    ⟨fun b ↦ mp (primesOverEquiv b).summable_iff of_finite, hs2⟩
  constructor
  exact mp (summable_iff e) hsig
  rw [← tsum_eq e, hsig.tsum_sigma, ← tsum_mul_left]
  exact tlt hfb hs2 $ mul_left _ hh

end

end

theorem tendsto_log_one_div_sub_one : Tendsto (fun s ↦ log $ 1 / (s - 1)) nh1 atTop := by
  simp_rw [one_div]
  apply tendsto_log_atTop.comp
  apply tendsto_inv_nhdsGT_zero.comp
  apply mpr tendsto_nhdsWithin_iff
  constructor
  simpa using mono_left (tendsto (continuous_sub_right (1 : ℝ)) 1) nhdsWithin_le_nhds
  exact eventually_nhdsWithin_of_forall fun _ h ↦ mpr mem_Ioi $ mpr sub_pos h

section

open mixedEmbedding NumberField.Units InfinitePlace dirichletUnitTheorem ComplexEmbedding

abbrev mN := @mixedEmbedding.norm

def tent (t : ℝ) := max 0 $ 1 - abs t

lemma tent0 (t : ℝ) : 0 ≤ tent t := le_max_left _ _
lemma tent1 (t : ℝ) : tent t ≤ 1 := max_le zero_le_one $ by grind

lemma msm (a b c d : ℝ) : a * b - c * d = a * (b - d) + (a - c) * d := by ring

def embZ : 𝓞 E →ₗ[ℤ] mixedSpace E :=
  ((mixedEmbedding E).comp (algebraMap (𝓞 E) E)).toIntAlgHom.toLinearMap

abbrev ubas (E) [Field E] [NumberField E] :=
  (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)

section
variable (x : mixedSpace E)

def ucoord (i : Fin (rank E)) := (ubas E).repr (logMap x) i

def uphi := if mN x = 0 then 0 else ∏ i, tent (ucoord x i)

def rsgn : ℤ :=
  ∏ w, if 0 ≤ fst x w then 1 else -1

theorem uphi_nonneg : 0 ≤ uphi x := by
  unfold uphi
  split_ifs
  rfl
  exact prod_nonneg fun _ _ ↦ tent0 _
theorem uphi_le_one : uphi x ≤ 1 := by
  unfold uphi
  split_ifs
  exact zero_le_one
  apply prod_le_one₀
  intros
  exact tent0 _
  intros
  exact tent1 _

theorem hasSum_uphi_unit_smul (hx : mN x ≠ 0) :
    HasSum (fun u : (𝓞 E)ˣ ↦ uphi (u • x)) (rN (torsionOrder E)) := by
  let Z := Fin (rank E) → ℤ
  let e : torsion E × Z → (𝓞 E)ˣ | ⟨t, n⟩ => t * ∏ i, fundSystem E i ^ n i
  let eq := ofBijective e ⟨fun p q h ↦ (exist_unique_eq_mul_prod E $ e p).unique rfl h,
    fun u ↦ (exist_unique_eq_mul_prod E u).exists.imp fun _ ↦ sy⟩
  let := ofFinite $ torsion E
  let y := ucoord x
  let F i : Finset ℤ := {-⌊y i⌋, -⌊y i⌋ - 1}
  have ht : HasSum (fun n : Z ↦ ∏ i, tent (y i + n i)) 1 := by
    rw [← prod_eq_one fun i _ ↦ show ∑ n ∈ F i, tent (y i + n) = 1 by
      rw [sum_pair $ by omega]
      grind [tent, floor_le $ y i, lt_floor_add_one $ y i], prod_univ_sum]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    obtain ⟨i, hi⟩ := by simpa [Z, F] using hn
    apply prod_eq_zero $ mem_univ i
    have : n i + ⌊y i⌋ ≤ -2 ∨ 1 ≤ n i + ⌊y i⌋ := by omega
    rify at this
    grind [tent, floor_le $ y i, lt_floor_add_one $ y i]
  apply mp eq.hasSum_iff
  apply HasSum.congr_fun
  simpa [torsionOrder] using mul (hasSum_fintype fun _ : torsion E ↦ (1 : ℝ)) ht
    (mul_of_nonneg of_finite ht.summable (const _ zero_le_one) fun _ ↦ prod_nonneg fun _ _ ↦ tent0 _)
  rintro ⟨t, n⟩
  simp only [uphi, norm_unit_smul, hx, ↓reduceIte]
  apply Fintype.prod_congr
  intro i
  congr 1
  rw [ucoord, show eq (t, n) = e (t, n) from rfl, mul_smul, logMap_torsion_smul _ t.2, logMap_unit_smul _ hx, ofMul_prod, map_sum, map_add]
  simp [map_zsmul, logEmbedding_fundSystem, ← cast_smul_eq_zsmul ℝ,  ucoord, y, Finsupp.single_apply, add_comm]
end

def Gs (s : ℝ) (x : mixedSpace E) : ℂ :=
  chi (rsgn x : ZMod l) * ↑(uphi x * mN x ^ (-s))

lemma log_norm_eq {z : mixedSpace E} (hz : ∀ w, normAtPlace w z ≠ 0) :
    log (mN z) = ∑ w, rN (mult w) * log (normAtPlace w z) := by
  rw [mixedEmbedding.norm_apply, log_prod fun w _ ↦ pow_ne_zero _ (hz w)]
  simp_rw [Real.log_pow]

lemma supp_bound :
    ∃ c0 > 0, ∀ (x : mixedSpace E), uphi x ≠ 0 → ∀ w, c0 * norm x ≤ normAtPlace w x := by
  let B := ∑ i, ‖ubas E i‖
  let C := card (InfinitePlace E) * B
  use exp $ -(2 * C), exp_pos _
  intro x hx w
  have hN : mN x ≠ 0 := fun h ↦ hx $ by simp [uphi, h]
  have hc i : |ucoord x i| < 1 := mp not_le fun h' ↦ hx $ by
    simp [uphi, hN]
    apply prod_eq_zero $ mem_univ i
    grind [tent]
  have hB v : |logMap x v| ≤ B := by
    grw [← norm_eq_abs, norm_le_pi_norm (logMap x) v, ← (ubas E).sum_repr $ logMap x, norm_sum_le]
    apply sum_le_sum
    intro i _
    rw [_root_.norm_smul, norm_eq_abs, ← ucoord]
    grw [(hc i).le]
    simp
  have hpos w := lt_of_le_of_ne (normAtPlace_nonneg w x) (mp mixedEmbedding.norm_ne_zero_iff hN w).symm
  let D w := log (normAtPlace w x) - log (mN x) * inv (rN $ finrank ℚ E)
  have hD0 : ∑ w, ↑(mult w) * D w = 0 := by
    simp [D, mul_sub, sum_sub_distrib, ← log_norm_eq fun w ↦ ne_of_gt $ hpos w, ← sum_mul, ← Nat.cast_sum, sum_mult_eq]
    field_simp [ne_of_gt finrank_pos]
    ring
  have hD w : |D w| ≤ C := by
    suffices key : |↑(mult w) * D w| ≤ C by
      rw [abs_mul, abs_of_nonneg $ cast_nonneg _] at key
      nlinarith [one_le_mult (w := w), abs_nonneg $ D w]
    by_cases hw : w = w₀
    subst hw
    rw [sum_eq_add_sum_subtype_ne _ w₀, add_eq_zero_iff_eq_neg] at hD0
    grw [hD0, abs_neg, abs_sum_le_sum_abs]
    apply le_trans $ sum_le_sum fun v _ ↦ hB v
    simp [C]
    gcongr
    exact sub_le _ _
    apply le_trans $ hB ⟨w, hw⟩
    apply le_mul_of_one_le_left
    positivity
    exact_mod_cast Fintype.card_pos
  obtain ⟨w', -, hw'⟩ := exists_mem_eq_sup' univ_nonempty (normAtPlace · x)
  rw [norm_eq_sup'_normAtPlace, hw', ← exp_log $ hpos w', ← exp_add, ← exp_log $ hpos w]
  apply mpr exp_le_exp
  grind

lemma hexp {a b : ℝ} : |exp a - exp b| ≤ max (exp a) (exp b) * |a - b| := by
  wlog h : b ≤ a generalizing a b
  simpa [abs_sub_comm, max_comm] using this $ le_of_not_ge h
  have := mul_le_mul_of_nonneg_left (add_one_le_exp $ b - a) (exp_pos a).le
  rw [← exp_add, add_sub_cancel] at this
  rw [abs_of_nonneg, max_eq_left, abs_of_nonneg]
  all_goals linarith [mpr exp_le_exp h]

theorem gs_diff_bound (B : ℝ) (hB : 1 ≤ B) :
    ∃ R0 C : ℝ, 1 ≤ R0 ∧ ∀ s ∈ Icc 1 2, ∀ x h : mixedSpace E, norm h ≤ B → R0 ≤ norm x →
      ‖Gs chi s (x + h) - Gs chi s x‖ ≤ C * norm x ^ (-rN (finrank ℚ E) - 1) := by
  obtain ⟨c0, hc0, hsupp⟩ := supp_bound (E := E)
  set n := finrank ℚ E
  set d := rN n
  have hd0 : 0 < d := mpr cast_pos finrank_pos
  let clm i := LinearMap.toContinuousLinearMap $ (ubas E).coord i
  set A := ∑ i, ‖clm i‖
  set m := (2 / c0) ^ n
  let L := (A * 8 + 4 * d) * B / c0 * m
  let R1 := max (2 * B / c0) 1
  have : 1 ≤ R1 := le_max_right _ _
  have hscale s (hs : s ∈ Icc 1 2) (y k : mixedSpace E) (hyu : uphi y ≠ 0) (hk : norm k ≤ B) (hy : R1 ≤ norm y) :
      ‖Gs chi s (y + k) - Gs chi s y‖ ≤ L * norm y ^ (-d - 1) := by
    set y' := y + k
    set t := norm y
    have ht0 : 0 < t := by linarith
    set c2 := c0 / 2 * t with hc2
    have : B ≤ c2 := by linarith [mp (div_le_iff₀ hc0) $ le_trans (le_max_left _ _) hy]
    have hw_y := hsupp y hyu
    have hw_le w := norm_eq_sup'_normAtPlace k ▸ le_sup' (normAtPlace · k) (mem_univ w)
    have hw_diff w : |normAtPlace w y' - normAtPlace w y| ≤ B := by
      apply mpr abs_le
      constructor
      linarith [add_neg_cancel_right y k ▸ normAtPlace_add_le w y' (-k), normAtPlace_neg w k, hw_le w]
      linarith [normAtPlace_add_le w y k, hw_le w]
    have hw_y' w : c2 ≤ normAtPlace w y' := by grind
    have hrsgn : rsgn y' = rsgn y := prod_congr rfl fun w _ ↦ if_congr (by
      have h1 := hw_le w
      have h2 := hw_y w
      simp [y', normAtPlace_apply_of_isReal w.2] at h1 h2 ⊢
      grind) rfl rfl
    set ep := B / c2
    have hlog_w w : |log (normAtPlace w y') - log (normAtPlace w y)| ≤ ep := by
      have := mp abs_le $ hw_diff w
      apply mpr abs_sub_le_iff
      constructor <;>
      · rw [← log_div]
        grw [log_le_sub_one_of_pos, div_sub_one]
        apply div_le_div₀
        all_goals first | positivity | linarith [hw_y w] | (apply _root_.div_pos <;> linarith [hw_y w])
    have hlog_N : |log (mN y') - log (mN y)| ≤ d * ep := by
      rw [log_norm_eq, log_norm_eq, ← sum_sub_distrib]
      grw [abs_sum_le_sum_abs]
      dsimp [d, n, rN]
      rw [← sum_mult_eq, Nat.cast_sum, sum_mul]
      apply sum_le_sum
      intro w _
      rw [← mul_sub, abs_mul, abs_of_nonneg $ cast_nonneg _]
      grw [hlog_w w]
      all_goals intro w; linarith [hw_y w, hw_y' w]
    have hlogMap : ‖logMap y' - logMap y‖ ≤ 4 * ep := by
      apply mpr $ pi_norm_le_iff_of_nonneg _
      intro w
      rw [Pi.sub_apply, norm_eq_abs, logMap_apply, logMap_apply, ← mul_sub, abs_mul, abs_of_nonneg $ cast_nonneg _,
        sub_sub_sub_comm, ← sub_mul]
      grw [show mult w.val ≤ 2 by grind [mult], abs_sub, hlog_w w, abs_mul, abs_inv, abs_of_pos hd0, hlog_N]
      apply le_of_eq
      field_simp
      ring
      positivity
    set M := c2 ^ n
    have hM1 : 1 ≤ M := one_le_pow₀ $ by linarith
    have hM0 := lt_of_lt_of_le zero_lt_one hM1
    have hpowN {z : mixedSpace E} (hz : ∀ w, c2 ≤ normAtPlace w z) : M ≤ mN z := by
      dsimp [M, n]
      rw [mixedEmbedding.norm_apply, ← sum_mult_eq, ← prod_pow_eq_pow_sum]
      gcongr with w
      exact hz w
    have hm_y := hpowN fun w ↦ by linarith [hw_y w]
    have hm_y' := hpowN hw_y'
    have hy0 := lt_of_lt_of_le hM0 hm_y
    have hy'0 := lt_of_lt_of_le hM0 hm_y'
    have hpow_le {N : ℝ} (hN : M ≤ N) : N ^ (-s) ≤ m * t ^ (-d) := by
      grw [rpow_le_rpow_of_nonpos hM0 hN, rpow_le_rpow_of_exponent_le hM1]
      apply le_of_eq
      dsimp [M, m, c2]
      rw [rpow_neg_one, mul_pow, mul_inv, ← inv_pow, inv_div, rpow_neg ht0.le, rpow_natCast]
      all_goals linarith [hl hs]
    have huphi : |uphi y' - uphi y| ≤ A * (4 * ep) := by
      simp [uphi, ne_of_gt hy'0, ne_of_gt hy0]
      trans ∑ i, |ucoord y' i - ucoord y i|
      generalize (univ : Finset $ Fin $ rank E) = S
      induction S using Finset.induction_on with
      | empty => simp
      | insert j S hj ih =>
        rw [prod_insert hj, prod_insert hj, sum_insert hj, msm]
        grw [abs_add_le]
        rw [abs_mul, abs_mul, abs_of_nonneg $ tent0 _, abs_of_nonneg $ prod_nonneg fun _ _ ↦ tent0 _]
        grw [mul_le_of_le_one_left (abs_nonneg _) $ tent1 _, ih, prod_le_one₀]
        clear * -
        grind [tent]
        intros
        exact tent0 _
        intros
        exact tent1 _
      rw [sum_mul]
      apply sum_le_sum
      intro i _
      grw [← hlogMap]
      simpa [ucoord, clm, map_sub] using (clm i).le_opNorm $ logMap y' - logMap y
    unfold Gs
    rw [hrsgn, ← mul_sub, norm_mul, ← ofReal_sub, Complex.norm_real, norm_eq_abs]
    grw [chi.norm_le_one]
    rw [msm]
    grw [abs_add_le]
    rw [abs_mul, abs_mul, abs_of_nonneg $ rpow_nonneg hy0.le $ -s, abs_of_nonneg $ uphi_nonneg y',
      rpow_def_of_pos hy'0, rpow_def_of_pos hy0]
    grw [huphi, uphi_le_one y', hexp, ← rpow_def_of_pos hy'0, ← rpow_def_of_pos hy0,
      max_le (hpow_le hm_y') $ hpow_le hm_y, ← sub_mul, abs_mul, abs_neg,
      abs_of_pos (a := s) $ by linarith [hl hs], hr hs, hlog_N, hpow_le hm_y]
    apply le_of_eq
    rw [rpow_sub ht0, rpow_one]
    ring
  use 2 * R1 + 2 * B, L * 2 ^ (d + 1)
  constructor
  linarith
  intro s hs x h hh hx
  by_cases h1 : uphi x = 0
  by_cases h2 : uphi (x + h) = 0
  simp [Gs, h1, h2]
  positivity
  have hy : norm x / 2 ≤ norm (x + h) := by
    linarith [add_sub_cancel_right x h ▸ norm_sub_le (x + h) h]
  have hc := hscale s hs (x + h) (-h) h2 (by rwa [norm_neg]) $ by linarith
  rw [add_neg_cancel_right, norm_sub_rev] at hc
  grw [hc, rpow_le_rpow_of_nonpos _ hy]
  apply le_of_eq
  rw [div_rpow _ zero_le_two, div_eq_mul_inv, ← rpow_neg zero_le_two]
  ring_nf
  all_goals try linarith
  grw [hscale s hs x h h1 hh]
  gcongr
  apply le_mul_of_one_le_right
  positivity
  apply one_le_rpow one_le_two
  all_goals try linarith

lemma norm_embZ (al : 𝓞 E) : mN (embZ al) = |(norm ℤ al : ℝ)| := by
  simp [embZ, norm_eq_norm, ← coe_norm_int]

lemma rsgn_mul_norm (al : 𝓞 E) : rsgn (embZ al) * norm ℤ al = |norm ℤ al| := by
  have h := norm_eq_prod_embeddings ℚ ℂ (al : E)
  rw [← prod_equiv ((indexEquiv E).trans $ equivRatAlgHom E ℂ) _ _ fun _ ↦ rfl,
    Fintype.prod_sum_type, Fintype.prod_prod_type, eq_ratCast, ← coe_norm_int] at h
  have hr (w : {w : InfinitePlace E // IsReal w}) : w.1.embedding al = ↑((embZ al).1 w) := by simp [embZ]
  simp [conjugate_coe_eq, mul_conj, ← Complex.sq_norm, hr] at h
  norm_cast at h
  apply cast_injective (α := ℝ)
  push_cast
  rw [h, rsgn, Int.cast_prod, ← mul_assoc, ← prod_mul_distrib, abs_mul,
    abs_prod, abs_of_nonneg $ by positivity]
  congr 1
  apply Fintype.prod_congr
  intros
  split_ifs <;> push_cast <;> grind

def gfun (C : Idl E) (s : ℝ) (a : Idl E) :=
  cf chi s a - ↑(absNorm C) * {a : Idl E | C ∣ a}.indicator (cf chi s) a

lemma exists_class_cont [Fact (Pr l)] (B C : Idl E)
    (hB0 : B ≠ ⊥) (hC0 : C ≠ ⊥) (hcop : Coprime C.absNorm (absNorm B * l)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc 1 2, Summable (gfun chi C s) →
      (∑' a, {a | a ≠ ⊥ ∧ IsPrincipal (a * B)}.indicator (gfun chi C s) a) = F s := by
  set nB := absNorm B
  set nC := absNorm C
  have hb := aN0 hB0
  set m := nB * l
  set I := span {(m : 𝓞 E)} * B
  have hIC : IsCoprime I C := by
    apply mpr isCoprime_iff_exists
    obtain ⟨u, v, huv⟩ := mpr isCoprime_iff_coprime $ hcop.mul_right $ hcop.coprime_dvd_right $ dvd_mul_right _ _
    use v * (m * nB), I.mul_mem_left _ $ mul_mem_mul (mem_span_singleton_self _) $ absNorm_mem B,
      u * nC, C.mul_mem_left _ $ absNorm_mem C
    norm_cast
    linarith
  have hI0 := mul_ne_zero (mpr span_singleton_eq_bot.not $ mpr cast_ne_zero $ mul_ne_zero hb (fo : Pr l).ne_zero) hB0
  let IC := I * C
  let Q := 𝓞 E ⧸ IC
  let := @ofFinite _ $ finiteQuotientOfFreeOfNeBot IC $ mul_ne_zero hI0 hC0
  let := @ofFinite _ $ finiteQuotientOfFreeOfNeBot I hI0
  let := @ofFinite _ $ finiteQuotientOfFreeOfNeBot C hC0
  let mk := Ideal.Quotient.mk IC
  let eqv := quotientMulEquivQuotientProd I C hIC
  let f a : ℂ := if a ∈ B then chi ↑(norm ℤ a / nB) else 0
  have hfper a a' (h : a - a' ∈ I) : f a = f a' := by
    by_cases ha : a ∈ B
    have ha' : a' ∈ B := by simpa using sub_mem ha $ mul_le_right h
    simp [f, ha, ha']
    congr 1
    rw [intCast_eq_intCast_iff]
    refine ModEq.mul_left_cancel' (mpr cast_ne_zero hb) ?_
    rw [Int.mul_ediv_cancel' $ absNorm_dvd_norm_of_mem ha, Int.mul_ediv_cancel' $ absNorm_dvd_norm_of_mem ha']
    apply mp $ intCast_eq_intCast_iff _ _ m
    obtain ⟨be, hbe⟩ := mp mem_span_singleton $ mul_le_left h
    rw [eq_add_of_sub_eq hbe]
    simp_rw [norm_eq_matrix_det $ Free.chooseBasis ℤ $ 𝓞 E, ← Int.coe_castRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [map_add, map_mul]
    simp [f, ha]
    exact fun ha' ↦ absurd (by simpa using add_mem (mul_le_right h) ha') ha
  have hm (mu : IC) (y : Q) : mk (mu + out y) = y := by simp [mk, mpr eq_zero_iff_mem mu.2]
  let e : IC × Q ≃ 𝓞 E :=
    ⟨fun ⟨mu, y⟩ ↦ mu + out y,
     fun a ↦ (⟨a - out (mk a), by simp [mk, ← eq_zero_iff_mem]⟩, mk a),
     fun ⟨mu, y⟩ ↦ by ext <;> simp [hm],
     fun a ↦ sub_add_cancel _ _⟩
  let cZ a := f a * (1 - nC * if a ∈ C then 1 else 0)
  let cQ y := f (out (eqv y).1) * (1 - nC * if (eqv y).2 = 0 then 1 else 0)
  have hcQ a : cQ (mk a) = cZ a := by
    simp [cQ, cZ, eqv, mk, IC, eq_zero_iff_mem, hfper _ a $ mp Ideal.Quotient.eq $ out_eq _]
  have hmean : ∑ y : Q, cQ y = 0 := by
    rw [← eqv.symm.toEquiv.sum_comp, sum_prod_type]
    simp [cQ, ← mul_sum, sum_sub_distrib, nC, absNorm_apply, cardQuot_apply]
  obtain ⟨R0, C0, hR1, hRC⟩ := gs_diff_bound (E := E) chi ((∑ y : Q, ‖embZ (out y)‖) + 1) $
    le_add_of_nonneg_left $ by positivity
  set A := ∑ y : Q, ‖cQ y‖
  set r : ℝ := -(finrank ℚ E) - 1
  set C1 := max C0 $ 2 * R0 ^ (-r)
  let u (mu : IC)  := A * (C1 * ‖embZ mu.1‖ ^ r + if mu = 0 then 2 else 0)
  have hu :=
    mul_left A $ add (mul_left C1 $ (summable_norm_rpow (mixedEmbedding.integerLattice E) r $ by
        rw [rank ℝ, mixedEmbedding.finrank]
        linarith).comp_injective (i := fun mu : IC ↦ (⟨embZ mu, mu, rfl⟩)) fun _ _ h ↦
      by ext
         exact mixedEmbedding_injective E $ congrArg (·.1) h)
      (hasSum_ite_eq 0 2).summable
  let F s  := ∑' mu : IC, ∑ y : Q, cQ y * (Gs chi s (embZ (mu.1 + out y)) - Gs chi s (embZ mu.1))
  have (x : mixedSpace E) : Continuous fun s ↦ Gs chi s x := by
    by_cases h : mN x = 0
    simpa [Gs, uphi, h] using continuous_const
    unfold Gs
    fun_prop
  let nb : ℂ := nB
  use fun s ↦ inv (torsionOrder E : ℂ) * nb ^ (s : ℂ) * F s
  constructor
  apply (mul continuous_const $ const_cpow continuous_ofReal $ inl $ mpr cast_ne_zero hb).continuousOn.mul
  apply continuousOn_tsum _ hu
  swap
  intro
  fun_prop
  intro mu s hs
  set g := Gs (E := E) chi s
  have hbd al : ‖g (embZ al)‖ ≤ 1 := by
    by_cases h0 : norm ℤ al = 0
    simp [g, Gs, uphi, norm_embZ, h0]
    have := uphi_nonneg $ embZ al
    dsimp [g, Gs]
    rw [norm_mul, norm_embZ, Complex.norm_of_nonneg]
    grw [chi.norm_le_one, uphi_le_one, rpow_le_one_of_one_le_of_nonpos]
    norm_num
    exact_mod_cast one_le_abs h0
    linarith [hl hs]
    positivity
  set z := embZ mu.1
  grw [norm_sum_le]
  dsimp [ A]
  rw [sum_mul]
  gcongr with y
  rw [norm_mul]
  gcongr
  have h2 : ‖g (embZ (mu + out y)) - g z‖ ≤ 2 := by
    grw [norm_sub_le, hbd, hbd]
    norm_num
  split_ifs with hmu
  grw [h2]
  apply le_add_of_nonneg_left
  positivity
  rw [add_zero]
  by_cases hR : R0 ≤ norm z
  grw [map_add embZ, hRC s hs z (embZ $ out y) _ hR, le_max_left C0 _]
  apply le_add_of_le_of_nonneg _ zero_le_one
  apply single_le_sum _ $ mem_univ y
  intros
  positivity
  dsimp [C1]
  grw [h2, ← le_max_right C0 _, ← rpow_le_rpow_of_nonpos _ (mp not_le hR).le]
  rw [mul_assoc, ← rpow_add]
  simp
  linarith
  grind
  simpa [z, embZ] using hmu
  intro s hs hg
  let g := gfun chi C s
  let ph al := cZ al * Gs chi s (embZ al)
  set S := {a : Idl E | a ≠ ⊥ ∧ IsPrincipal (a * B)}
  choose gen hgen using fun a : S ↦ a.2.2.principal
  have gen_ne a : gen a ≠ 0 := fun h ↦ mul_ne_zero a.2.1 hB0 $ et (hgen a) $ by simp [h]
  let Ps : S × (𝓞 E)ˣ → 𝓞 E | ⟨a, u⟩ => gen a * u
  have hspan a u : span {Ps (a, u)} = a * B :=
    et (span_singleton_mul_right_unit u.isUnit _) $ sy $ hgen a
  have hinj : Injective Ps := fun ⟨a, u⟩ ⟨a', u'⟩ h ↦ by
    obtain rfl : a = a' := Subtype.ext $ mul_right_cancel₀ hB0 $ by rw [← hspan, ← hspan, h]
    exact Prod.ext rfl $ uext $ mul_left_cancel₀ (gen_ne a) h
  let f' : S × (𝓞 E)ˣ → ℂ | ⟨a, u⟩ => ↑(uphi (u • embZ (gen a))) * g a
  have hPout : support ph ⊆ range Ps := fun al hal ↦ by
    have halb : al ∈ B := of_not_not fun h ↦ hal $ by simp [ph, cZ, f, h]
    obtain ⟨d, hd⟩ := mpr dvd_iff_le $ mpr (span_singleton_le_iff_mem _) halb
    have hdb := mul_comm B d ▸ sy hd
    have hdS : d ∈ S := ⟨fun h ↦ hal $ by simp [by simpa [h] using hd, ph, Gs, uphi], ⟨al, hdb⟩⟩
    obtain ⟨u, hu⟩ := mp span_singleton_eq_span_singleton $ et (sy $ hgen ⟨d, hdS⟩) hdb
    exact ⟨(⟨d, hdS⟩, u), hu⟩
  have hPeq : ∀ p, ph (Ps p) = nb ^ (-(s : ℂ)) * f' p := fun ⟨aS, u⟩ ↦ by
    set al := Ps (aS, u)
    have hal : al ∈ B := mp (span_singleton_le_iff_mem _) $ (hspan aS u).trans_le mul_le_right
    have hN : (norm ℤ al).natAbs = absNorm aS.1 * nB := by
      rw [← absNorm_span_singleton, hspan aS u, map_mul]
    have hC : (al ∈ C) ↔ C ∣ aS := by
      rw [← span_singleton_le_iff_mem, ← dvd_iff_le, hspan,
        (hIC.of_isCoprime_of_dvd_left $ mpr dvd_iff_le mul_le_right).symm.dvd_mul_right_iff]
    simp [ph, cZ, f, hal, Gs, f', g, gfun, indicator_apply, cf, hC, norm_embZ, ← cast_abs, ← natCast_natAbs, hN, ← pa_cpow_eq, natCast_mul_natCast_cpow, -cast_natAbs, -unitSMul_smul, nb, nC]
    rw [show chi (absNorm aS.1) = chi ↑(norm ℤ al / nB) * chi (rsgn $ embZ al) by
        rw [← map_mul, ← Int.cast_mul, mul_comm, ← Int.mul_ediv_assoc _ $ absNorm_dvd_norm_of_mem hal,
          rsgn_mul_norm, ← natCast_natAbs, hN, Nat.cast_mul, mul_ediv_cancel]
        simp
        positivity,
      show embZ al = u • embZ (gen aS) by simp [al, Ps, embZ, unitSMul_smul, mul_comm]]
    split_ifs <;> ring
  have hw a := hasSum_uphi_unit_smul (embZ $ gen a) $ by simp [norm_embZ, gen_ne a]
  have hfs : Summable f' := .of_norm $ mpr (summable_prod_of_nonneg fun _ ↦ norm_nonneg _) $ by
    have hnfib a : HasSum (fun u ↦ ‖f' (a, u)‖) $ torsionOrder E * ‖g a‖ := by
      convert (hw a).mul_right ‖g a‖ with u
      simp [f', abs_of_nonneg $ uphi_nonneg _]
    exact ⟨fun a ↦ summable $ hnfib a,
      congr (mul_left _ $ hg.norm.subtype S) fun a ↦ sy (hnfib a).tsum_eq⟩
  have hFeq : F s = ∑' al, ph al := by
    rw [← tsum_eq e, Summable.tsum_prod]
    apply sy
    apply tsum_congr
    intro mu
    rw [tsum_fintype]
    simp [ph, e, ← hcQ, hm, mul_sub, sum_sub_distrib, ← sum_mul, hmean]
    exact mpr (e.summable_iff (f := ph)) $ mp (hinj.summable_iff fun _ ↦ mp notMem_support ∘ mt (@hPout _)) $
      congr (mul_left _ hfs) fun p ↦ sy $ hPeq p
  rw [hFeq, ← hinj.tsum_eq hPout, tsum_congr hPeq, tsum_mul_left, hfs.tsum_prod,
    tsum_congr fun a ↦ tsum_eq $ mul_right _ $ mpr hasSum_ofReal $ hw a,
    tsum_mul_left, ofReal_natCast, tsum_subtype S g, cpow_neg]
  field_simp [torsionOrder_ne_zero E, nb, nB, hb]
  rfl

end

section
variable [Fact $ Pr l]

lemma psum_orth (a : UZ l) {s : ℝ}
    (hS : Summable fun q : Prm E ↦ rpq s q) :
    ∑ chi : DC l, re (chi ↑(inv a) * Psum E chi s) =
      rN (l - 1) * Pcl E (a : ZMod l) s := by
  rw [← re_sum]
  trans re $ (totient l : ℂ) * ↑(Pcl E (a : ZMod l) s)
  congr 1
  simp_rw [Psum, Pcl, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun chi _ ↦ (of_norm_bounded hS fun _ ↦ norm_cf_le chi).mul_left _, ofReal_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro q
  simp_rw [cf, ← mul_assoc, ← sum_mul, ← inv_coe_unit, DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit, indicator_apply]
  split_ifs <;> simp_all [pa_cpow_eq]
  simp [totient_prime fo]

section
variable (hirr : Irreducible $ Polynomial.cyclotomic l E)
include hirr

theorem k_holds (chi : DC l) (hchi : chi ≠ 1) :
    ∃ L1 : ℂ, Tendsto (Lser E chi) nh1 (𝓝 L1) := by
  choose I hb using fun C : ClassGroup (𝓞 E) ↦ mk0_surjective C⁻¹
  let B C := (I C).val
  have hB0 C := nonZeroDivisors.ne_zero (I C).property
  let m := ∏ C, absNorm (B C)
  have ⟨q, hqcop, hqX⟩ : ∃ q : Prm E, qC q (m * l) ∧ chi (qN q) ≠ 1 := by
    have hlp : Pr l := fo
    set M := CyclotomicField l E
    have := isGalois {l} E M
    by_contra H
    push Not at H
    let eM := autEquivPow M hirr
    let Hsub := (chi.toUnitHom.comp eM.toMonoidHom).ker
    set K := fixedField Hsub
    set k := finrank E K
    have hk : 1 < k := lt_of_le_of_ne finrank_pos fun h1 ↦ hchi $ ext fun u ↦ by
      simpa [Hsub] using congrArg Units.val $ mp mem_ker $ show eM.symm u ∈ Hsub by
        rw [← fixingSubgroup_fixedField Hsub]
        simp [K, mp finrank_eq_one_iff $ sy h1]
    set S : Set (Prm E) := {q | ¬ qC q (m * l)}
    set N := ∑' q, indicator S (1 : Prm E → ℝ) q
    set B0 := peC K + k * (N + peC E)
    apply nh1_f
    filter_upwards [pe_log_bdd E, pe_log_bdd K, eventually tendsto_log_one_div_sub_one $ eventually_gt_atTop $ abs B0, self_mem_nhdsWithin] with s h1 h2 hlog hs1
    let OE := 𝓞 E
    let OK := 𝓞 K
    have hSE := summable_prm_rpow E hs1
    let e := sigmaFiberEquiv $ under (E := E) (E' := K)
    have hsig : Summable fun p ↦ rpq s (e p) := e.summable_iff.mpr $ summable_prm_rpow K hs1
    let g := Sᶜ.indicator $ rpq s
    have : k * ∑' q, g q ≤ PE K s := by
      rw [← tsum_mul_left, PE, ← e.tsum_eq, hsig.tsum_sigma]
      apply tlt _ (mul_left _ $ hSE.indicator Sᶜ) $ hr $ mp (summable_sigma_of_nonneg fun _ ↦ by positivity) hsig
      intro q
      by_cases hq : q ∈ S
      simpa [g, hq] using tsum_nonneg fun _ ↦ by positivity
      simp only [indicator_apply, mem_compl_iff, hq]
      have hcop := mp not_not hq
      set qi := asIdeal q
      have hsplit : ∀ Q : primesOver qi OK, ramificationIdx Q.1 OE = 1 ∧ inertiaDeg Q.1 OE = 1 ∧ absNorm Q.1 = qN q
        | ⟨Q, hQp, hQl⟩ => by
          have hQ0 := ne_bot_of_liesOver_of_ne_bot q.ne_bot Q
          obtain ⟨⟨P, hPp, hPl⟩⟩ := Q.nonempty_primesOver (S := 𝓞 M)
          have := LiesOver.trans P Q qi
          have := isMaximal q
          have := isMaximal hQp hQ0
          have := isMaximal hPp $ ne_bot_of_liesOver_of_ne_bot hQ0 P
          have hz0 := zeta_spec l E M
          set zi := hz0.toInteger
          let G := Gal(M/E)
          have htau (tau : G) (n : ℕ) (h : tau • zi - zi ^ n ∈ P) :
              (hz0.autToPow E tau : ZMod l) = n := by
            set z0 : ZMod l := ↑(hz0.autToPow E tau)
            set k0 := z0.val
            have hp := hz0.toInteger_isPrimitiveRoot.idealQuotient_mk
              (absNorm_eq_one_iff.not.mpr hPp.ne_top) $ (absNorm_pow_inertiaDeg qi P) ▸ (hcop.coprime_dvd_right $ dvd_mul_left l m).pow_left _
            rw [← natCast_zmod_val z0, natCast_eq_natCast_iff]
            change k0 ≡ n [MOD l]
            rw [eq_orderOf hp, ← (hp.isOfFinOrder hlp.ne_zero).pow_eq_pow_iff_modEq, ← map_pow, ← map_pow,
              show zi ^ k0 = tau • zi from ext $ hz0.autToPow_spec E tau]
            exact mpr Ideal.Quotient.eq h
          obtain ⟨sg, hsg⟩ := exists_of_isInvariant OE G P
          have hcardE : Nat.card (OE ⧸ P.under OE) = qN q := by
            rw [← over_def P qi, qN, absNorm_apply, cardQuot_apply]
          have hsH : sg ∈ Hsub := mpr mem_ker $ uext $ by
            simpa [eM, G, htau sg (qN q) $ hcardE ▸ hsg zi] using H q hcop
          have hN := sy $ absNorm_pow_inertiaDeg qi Q
          have h2 := two_le_Nrm q
          have hf : inertiaDeg Q OE = 1 := by
            let := Ideal.Quotient.field Q
            let := ofFinite $ OK ⧸ Q
            apply le_antisymm _ $ inertiaDeg_pos Q OE
            apply mp $ Nat.pow_le_pow_iff_right h2
            rw [← hN, pow_one, absNorm_apply, cardQuot_apply, card_eq_fintype_card, ← card_univ,
              ← X_pow_card_sub_X_natDegree_eq (OK ⧸ Q) h2]
            apply Polynomial.card_le_degree_of_subset_roots
            intro z _
            obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
            have hyP : x - x ^ qN q ∈ Q := hPl.over.ge $ by
              simpa [show sg • algebraMap OK (𝓞 M) x = algebraMap OK (𝓞 M) x from ext $ x.1.2 ⟨sg, hsH⟩, hcardE] using
                hsg $ algebraMap OK (𝓞 M) x
            simp [Polynomial.mem_roots $ X_pow_card_sub_X_ne_zero _ h2,
              by simpa using sy $ mpr Ideal.Quotient.eq hyP]
          refine ⟨?_, hf, by rw [hN, hf, pow_one]⟩
          refine eq_one_of_mul_eq_one_right $ et (sy $ ramificationIdx_tower Q P) ?_
          rw [← ramificationIdxIn_eq_ramificationIdx qi P G,
            ← card_inertia_eq_ramificationIdxIn (G := G) qi P,
            mpr $ eq_bot_iff_forall $ P.inertia G, card_bot]
          intro g hg
          apply eM.injective
          apply uext
          simpa [eM] using htau g 1 $ by simpa using hg zi
      let := (finite_primesOver (S := OK) qi).fintype
      have hsum := sum_ramification_inertia_eq_finrank qi OK
      simp [← IsFractionRing.finrank_eq OE E OK K, OE, hsplit] at hsum
      rw [← (primesOverEquiv q).tsum_eq, tsum_fintype]
      simp [rpq, rp, e, primesOverEquiv, hsplit, qi, OK, hsum, k]
    have : PE E s - ∑' q, g q ≤ N := by
      rw [PE, ← hSE.tsum_sub $ hSE.indicator Sᶜ]
      apply tlt _ (hSE.sub $ hSE.indicator Sᶜ) $ summable_of_hasFiniteSupport $
        subset (finite_not_coprime E (m * l) $ mul_ne_zero (mpr prod_ne_zero_iff fun C _ ↦ aN0 $ hB0 C) hlp.ne_zero) support_indicator_subset
      intro q
      simp [S, indicator_apply]
      split_ifs <;> linarith [Nrm_rpow_le_half q hs1]
    nlinarith [neg_le_of_abs_le h1, le_of_abs_le h2, le_abs_self B0, abs_nonneg B0, mpr (ofNat_le_cast (α := ℝ)) hk]
  set c0 := asIdeal q
  have hc0 := ne_bot q
  choose F hF hFeq using fun C ↦ exists_class_cont chi (B C) c0 (hB0 C) hc0 $ hqcop.coprime_dvd_right $ 
    mul_dvd_mul_right (dvd_prod_of_mem _ $ mem_univ C) l
  let den s := 1 - ↑(absNorm c0) * cf chi s c0
  have hdenc : Continuous den := sub continuous_const $ mul continuous_const $ cont_cf hc0
  have hden1 : den 1 ≠ 0 := by
    dsimp [den, cf]
    rw [cpow_neg_one, mul_left_comm, mul_inv_cancel₀ $ mpr cast_ne_zero $ aN0 hc0]
    simpa [sub_eq_zero] using hqX.symm
  use (∑ C, F C 1) / den 1
  apply ((((continuousOn_finsetSum _ fun C _ ↦ hF C) 1 ⟨le_rfl, one_le_two⟩).div hdenc.continuousWithinAt hden1).mono_of_mem_nhdsWithin
    (mem_of_superset (Ioc_mem_nhdsGT one_lt_two) Ioc_subset_Icc_self)).tendsto.congr'
  filter_upwards [Ioc_mem_nhdsGT one_lt_two, nhdsWithin_le_nhds $ hdenc.continuousAt.eventually_ne hden1] with s hs hs0
  apply mpr $ div_eq_iff hs0
  apply sy
  have h1 := of_norm_bounded (hl $ hasSum_ideal E $ hl hs) fun _ ↦ norm_cf_le chi
  have h2 := mul_left ↑(absNorm c0) $ h1.indicator {a | c0 ∣ a}
  have hg : Summable (gfun chi c0 s) := sub h1 h2
  trans ∑' a, gfun chi c0 s a
  dsimp [gfun, Lser]
  rw [h1.tsum_sub h2, tsum_mul_left,
    ← (mul_right_injective₀ hc0).tsum_eq (f := {a | c0 ∣ a}.indicator $ cf chi s) fun a ha ↦ (support_indicator_subset ha).imp fun _ ↦ sy]
  simp [c0, cf_mul, den, tsum_mul_left]
  ring
  dsimp
  rw [← sum_congr rfl fun C _ ↦ hFeq C s hs hg, ← Summable.tsum_finsetSum fun C _ ↦ hg.indicator _]
  apply tsum_congr
  intro a
  by_cases ha0 : a = ⊥
  simp [ha0, gfun, cf, ne_of_gt $ zero_lt_one.trans $ hl hs]
  have hcl C : IsPrincipal (a * B C) ↔ mk0 ⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩ = C := by
    rw [← mul_inv_eq_one, ← hb C, ← map_mul, mk0_eq_one_iff]
    rfl
  simp [ha0, indicator_apply, hcl]

theorem cyc_holds (a : UZ l) (T : Finset ℕ) :
    ∃ q : Idl E, q.IsPrime ∧ Pr q.absNorm ∧ absNorm q ∉ T ∧
      (absNorm q : ZMod l) = a := by
  by_contra hno
  simp at hno
  let OE := 𝓞 E
  let Q := Prm E
  let fnp (q : Q) := if Pr (qN q) then 0 else inv $ rN $ qN q
  let g (q : Q) := fnp q + if qN q ∈ T then 1 else 0
  have hnp : Summable fnp := by
    refine hl $ fibre_sum_le (rpq 2)
      (fun _ ↦ by dsimp [fnp]; split_ifs <;> positivity) ?_ $ summable_prm_rpow ℚ one_lt_two
    intro q
    dsimp [fnp]
    split_ifs with hp
    positivity
    let p := under (E := ℚ) q
    set qi := asIdeal q
    set pi := asIdeal p
    have : qi.LiesOver pi := ⟨rfl⟩
    have hQp : Pr (qN p) := by
      rw [qN, absNorm_apply, cardQuot_apply, card_congr (quotientEquiv pi (pi.under ℤ) Rat.ringOfIntegersEquiv $
        et (congrArg (Ideal.comap · pi) $ RingHom.ext_int _ _) $ comap_symm Rat.ringOfIntegersEquiv).toEquiv,
        ← cardQuot_apply, ← absNorm_apply]
      exact absNorm_under_prime pi
    have hf := absNorm_pow_inertiaDeg pi qi
    have : 2 ≤ qi.inertiaDeg (𝓞 ℚ) := lt_of_le_of_ne (inertiaDeg_pos qi $ 𝓞 ℚ) fun (h1 : 1 = _) ↦ hp $ by
      rw [qN, ← hf, ← h1, pow_one]
      exact hQp
    rw [rpq, rp, rpow_neg $ cast_nonneg _, rpow_two]
    gcongr
    have := hQp.pos
    positivity
    exact_mod_cast (Nat.pow_le_pow_right hQp.pos this).trans_eq hf
  have hlp : Pr l := fo
  set k := rN $ l - 1
  set M := CyclotomicField l E
  let Sc : Set Q := {q | ¬ qC q l}
  let fB := indicator Sc fun _ ↦ (1 : ℝ)
  have hBf : Summable fB := summable_of_hasFiniteSupport $ subset (finite_not_coprime E l hlp.ne_zero) support_indicator_subset
  set A1 := PE E 2
  set B1 := ∑' q, fB q
  set C1 := peC E + peC M + k * (A1 + B1)
  have hC1 : ∀ᶠ s in nh1, PE E s - C1 ≤ k * Pcl E (1 : ZMod l) s := by
    filter_upwards [self_mem_nhdsWithin, pe_log_bdd E, pe_log_bdd M] with s hs hEs hMs
    have hA := summable_prm_rpow E one_lt_two
    let S1 : Set Q := {q | (qN q : ZMod l) = 1}
    have hP1 := (summable_prm_rpow E hs).indicator S1
    let h q := indicator S1 (rpq s) q + rpq 2 q + fB q
    have key := hr $ fibre_sum_le (E' := M) (f := rpq s) h (fun _ ↦ by positivity) ?_ $ add (add hP1 hA) hBf
    rw [finrank M hirr, totient_prime hlp, (add hP1 hA).tsum_add hBf, hP1.tsum_add hA, ← PE, ← PE, ← Pcl] at key
    grind
    intro P
    let q := under (E := E) P
    set Pi := asIdeal P
    simp only [h, fB, Sc, S1, indicator_apply, mem_ofPred_eq]
    have : 0 ≤ rpq 2 q := by positivity
    have : 0 ≤ rpq s q := by positivity
    by_cases hc : qC q l
    have : Pi.LiesOver q.asIdeal := ⟨rfl⟩
    have hN := absNorm_pow_inertiaDeg q.asIdeal Pi
    have := inertiaDeg_pos Pi OE
    have := two_le_Nrm q
    by_cases h1 : Pi.inertiaDeg OE = 1
    rw [h1, pow_one] at hN
    have := isMaximal P
    let := Ideal.Quotient.field Pi
    have hpr := (zeta_spec l E M).toInteger_isPrimitiveRoot.idealQuotient_mk
      (absNorm_eq_one_iff.not.mpr P.isPrime.ne_top) $ hN ▸ hc
    have hd := orderOf_dvd_natCard (isUnit hpr hlp.ne_zero).unit
    rw [← eq_orderOf $ hpr.isUnit_unit hlp.ne_zero, Nat.card_units, ← cardQuot_apply, ← absNorm_apply, ← hN] at hd
    have : (qN q : ZMod l) = 1 := by
      simpa [Nat.cast_sub $ le_trans one_le_two ‹_›, sub_eq_zero] using mpr (natCast_eq_zero_iff _ _) hd
    grind
    have : rpq s P ≤ rpq 2 q := by
      grw [Nrm_rpow_le_inv P hs]
      rw [rpq, rp, rpow_neg $ cast_nonneg _, rpow_two]
      gcongr
      norm_cast
      apply le_of_le_of_eq _ hN
      apply Nat.pow_le_pow_right
      all_goals grind
    split_ifs <;> linarith
    split_ifs <;> linarith [Nrm_rpow_le_half P hs]
  let DC' := {chi : DC l // chi ≠ 1}
  have hsplit (f : DC l → ℝ) : ∑ chi : DC l, f chi = f 1 + ∑ chi : DC', f chi := by
    rw [← add_sum_erase univ f $ mem_univ 1, sum_subtype _ (p := (· ≠ 1)) fun _ ↦ by simp]
  choose L1 hL using fun chi : DC' ↦ k_holds hirr chi chi.2
  have hLe chi := (hL chi).congr' $ eventually_nhdsWithin_of_forall (s := Ioi 1) fun s hs ↦ sy $ exp_ab2_eq_Lser E chi.1 hs
  have hLn chi := ((tendsto continuous_norm $ L1 chi).comp $ hLe chi).congr fun _ ↦ norm_exp _
  have hre_sub (chi : DC l) {s} (hs : 1 < s) := neg_le_of_abs_le $ le_trans (sub_re _ _ ▸ abs_re_le_norm _) $ ab2_sub_Psum E chi hs
  let C chi := log (‖L1 chi‖ + 1) + A1
  have hup (chi : DC') : ∀ᶠ s in nh1, re (Psum E chi.1 s) ≤ C chi := by
    filter_upwards [eventually (hLn chi) $ gt_mem_nhds $ lt_add_one ‖L1 chi‖,
      self_mem_nhdsWithin] with s hs hs1
    linarith [mpr (lt_log_iff_exp_lt $ by positivity) hs, hre_sub chi hs1]
  choose B hB using fun chi : DC' ↦
    show ∃ B, ∀ᶠ s in nh1, ‖Psum E chi.1 s‖ ≤ B by
      set c0 := chi.1
      let f := ab2 E c0
      have hL0 : L1 chi ≠ 0 := fun h0 ↦ nh1_f $ by
        set M0 := C1 + (∑ chi' ∈ univ.erase chi, C chi') + A1 + 1
        filter_upwards [eventually (hLn chi) $ gt_mem_nhds $ by simpa [h0] using exp_pos $ -M0,
          mpr eventually_all hup, hC1, self_mem_nhdsWithin] with s hs0 hsup hs1 hgt
        have hS := summable_prm_rpow E hgt
        have ho := psum_orth (1 : UZ l) hS
        simp at ho
        rw [hsplit, ← add_sum_erase _ _ $ mem_univ chi] at ho
        have : re (Psum E (1 : DC l) s) ≤ PE E s :=
          le_trans (re_le_norm _) $ tsum_of_norm_bounded hS.hasSum fun _ ↦ norm_cf_le _
        linarith [mp exp_lt_exp hs0, sum_le_sum (s := univ.erase chi) fun chi' _ ↦ hsup chi', hre_sub c0 hgt]
      let L0 := cl $ L1 chi
      let g' s := Complex.exp $ f s - L0
      have hdiv : Tendsto g' nh1 (𝓝 1) := by
        simpa [g', Complex.exp_sub, L0, Complex.exp_log hL0, div_self hL0] using (hLe chi).div_const $ L1 chi
      obtain ⟨u, hu1, hu⟩ := mp mem_nhdsGT_iff_exists_Ioo_subset
        (eventually hdiv $ ball_mem_nhds 1 $ half_pos zero_lt_one)
      have hfI : ContinuousOn f (Ioo 1 u) := by
        rintro s0 ⟨hs0, -⟩
        set a0 := (1 + s0) / 2 with ha0
        have h2 (q : Q) {s} (hs : a0 < s) := le_trans (norm_cf_le c0) $ Nrm_rpow_le_half q (s := s) $ by linarith
        apply ContinuousAt.continuousWithinAt
        apply ContinuousOn.continuousAt _ $ Ioi_mem_nhds $ by linarith
        apply continuousOn_tsum _ $ mul_left (3 / 2) $ summable_prm_rpow E _
        intro q s hs
        rw [norm_neg, sub_eq_add_neg]
        grw [norm_log_one_add_half_le_self, norm_neg, norm_cf_le]
        dsimp [ rp]
        grw [rpow_le_rpow_of_exponent_le _ $ neg_le_neg hs.le]
        exact_mod_cast le_trans one_le_two $ two_le_Nrm q
        simpa using h2 q hs
        intro q
        apply ContinuousOn.neg
        apply (sub continuous_const $ cont_cf q.ne_bot).continuousOn.clog
        intro s hs
        rw [sub_eq_add_neg]
        apply mem_slitPlane_of_norm_lt_one
        simp
        linarith [h2 q hs]
        linarith
      have h1 {s} (hs : s ∈ Ioo 1 u) : ‖g' s - 1‖ < 1 / 2 := by simpa [dist_eq_norm] using hu hs
      let d0 := 2 * π * I
      have hd0 : d0 ≠ 0 := by simp [d0]
      obtain ⟨c, -, hc⟩ := isPreconnected_Ioo.eqOn_const_of_mapsTo
        Complex.isClosedEmbedding_intCast.isInducing.isDiscrete_range
        (f := fun s ↦ (f s - L0 - cl (g' s)) / d0)
        (by
          apply ContinuousOn.div_const
          apply (hfI.sub continuousOn_const).sub
          apply (hfI.sub continuousOn_const).cexp.clog
          intro s hs
          change g' s ∈ _
          rw [← add_sub_cancel 1 $ g' s]
          apply mem_slitPlane_of_norm_lt_one
          linarith [h1 hs])
        (fun s _ ↦ (mp exp_eq_exp_iff_exists_int $ sy $ exp_log $ exp_ne_zero $ f s - L0).imp fun n hn ↦ by
          dsimp
          rw [hn, add_sub_cancel_left, mul_div_cancel_right₀ _ hd0]) $ range_nonempty _
      use norm (c * d0 + L0) + 1 + A1
      filter_upwards [Ioo_mem_nhdsGT hu1] with s hs
      rw [← sub_sub_cancel (f s) $ Psum E c0 s]
      grw [norm_sub_le, ab2_sub_Psum E c0 hs.1, show f s = c * d0 + L0 + cl (g' s) by grind, norm_add_le]
      linarith [add_sub_cancel 1 (g' s) ▸ norm_log_one_add_half_le_self (h1 hs).le, h1 hs]
  have : 0 < k := mpr cast_pos $ Nat.sub_pos_of_lt hlp.one_lt
  set S := ∑ chi : DC', B chi
  apply nh1_f
  filter_upwards [mpr eventually_all hB, pe_log_bdd E,
    eventually tendsto_log_one_div_sub_one $ eventually_ge_atTop $ k * ((∑' q, g q) + 1) + S + B1 + peC E,
    self_mem_nhdsWithin] with s hsB hs3b hlog hgt
  have hS := summable_prm_rpow E hgt
  have : Pcl E (a : ZMod l) s ≤ ∑' q, g q := by
    apply tlt _ (hS.indicator _) $ hnp.add $ summable_of_hasFiniteSupport $
      subset ((T.finite_toSet.biUnion fun n _ ↦ finite_setOfPred_absNorm_eq (S := OE) n).preimage
        fun _ _ _ _ ↦ hext) fun q h ↦
        mem_biUnion (by simpa using h) rfl
    intro q
    simp [fnp, indicator_apply]
    split_ifs with hc hp hT
    all_goals first | positivity | exact absurd hc $ hno q.asIdeal q.isPrime hp hT | linarith [Nrm_rpow_le_inv q hgt, Nrm_rpow_le_half q hgt]
  have h1 := psum_orth a hS
  rw [hsplit, one_apply_coe, one_mul] at h1
  have : PE E s - B1 - S ≤ k * Pcl E (a : ZMod l) s := by
    rw [sub_eq_add_neg, ← h1]
    apply add_le_add
    have hcs1 := of_norm_bounded hS fun _ ↦ norm_cf_le (1 : DC l)
    rw [PE, Psum, re_tsum hcs1, ← hS.tsum_sub hBf]
    apply tlt _ (sub hS hBf) $ reCLM.summable hcs1
    intro q
    by_cases hc : qC q l
    simp [cf, pa_cpow_eq, fB, Sc, hc, MulChar.one_apply $ mpr (isUnit_iff_coprime _ _) hc]
    simp [cf, fB, Sc, hc, MulChar.map_nonunit _ $ (isUnit_iff_coprime _ _).not.mpr hc]
    linarith [Nrm_rpow_le_half q hgt]
    rw [← sum_neg_distrib]
    gcongr with chi
    apply neg_le_of_abs_le
    grw [abs_re_le_norm, norm_mul, chi.1.norm_le_one, one_mul, hsB chi]
  nlinarith [neg_le_of_abs_le hs3b]

end

end

section

open Polynomial

theorem AlpogeRHCore2.chebotarev :
    ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (σ : Gal(K/ℚ)) (T : Finset ℕ),
      ∃ p : ℕ, p.Prime ∧ p ∉ T ∧ ∃ P : Ideal (𝓞 K), ∃ _ : P.IsPrime,
        P.LiesOver (Ideal.span {(p : ℤ)}) ∧ Algebra.IsUnramifiedAt ℤ P ∧ IsArithFrobAt ℤ σ P := by
  intro K _ _ _ sg T
  let OK := 𝓞 K
  let D := (discr K).natAbs
  have hN p (hp : Pr p) (hpN : D < p) (P : Ideal OK) [P.IsPrime] (hPl : P.LiesOver $ span {zN p}) :=
    mp (not_dvd_discr_iff_forall_mem K OK $ mp prime_iff_prime_int hp)
      (fun h ↦ not_dvd_of_pos_of_lt (mpr natAbs_pos $ discr_ne_zero K) hpN $ mp ofNat_dvd_left h) P inferInstance $
      by simpa using hPl.over.le $ mem_span_singleton_self $ zN p
  obtain ⟨l, hlp, hlgt, hlmod⟩ := exists_prime_gt_modEq_one (max D $ T.sup id) (orderOf_pos sg).ne'
  have hlp0 := hlp.pos
  have : Fact (Pr l) := ⟨hlp⟩
  have hirr : Irreducible (cyclotomic l K) := by
    let lZ := span {zN l}
    obtain ⟨P, hPmax, hPl⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := OK) lZ
    have := hN l hlp (by omega) P hPl
    let g := comp (cyclotomic l ℤ) $ X + 1
    have hmon : g.Monic := (cyclotomic.monic l ℤ).comp (monic_X_add_C 1) $ by simp
    let fZ := algebraMap ℤ OK
    rw [← map_cyclotomic l $ algebraMap OK K, ← Monic.irreducible_iff_irreducible_map_fraction_map $ cyclotomic.monic l OK,
      ← MulEquiv.irreducible_iff (algEquivAevalXAddC 1).toMulEquiv]
    suffices Irreducible (g.map fZ) by
      simpa [algEquivAevalXAddC_apply, ← comp_eq_aeval, g, map_comp, map_cyclotomic]
    refine ((hmon.map fZ).isEisensteinAt_of_mem_of_notMem hPmax.ne_top ?_ ?_).irreducible
      inferInstance (hmon.map _).isPrimitive ?_
    intro n hn
    rw [coeff_map]
    exact hPl.over.le $ (cyclotomic_comp_X_add_one_isEisensteinAt l).mem $ hmon.natDegree_map fZ ▸ hn
    intro hl2
    apply mpr (ramificationIdx'_ne_one_iff $ mpr map_le_iff_le_comap hPl.over.le) _ $
      et (ramificationIdx'_eq_ramificationIdx lZ P $ by simp [lZ, hlp.ne_zero]) $ P.ramificationIdx_eq_one ℤ
    simpa [g, lZ, map_span, coeff_zero_eq_eval_zero, eval_comp] using hl2
    simp [hmon.natDegree_map, g, natDegree_comp, natDegree_cyclotomic, totient_prime hlp, hlp.one_lt]
  let M := CyclotomicField l K
  let OM := 𝓞 M
  have : IsGalois ℚ M := by
    obtain ⟨p, hp⟩ := Normal.exists_isSplittingField ℚ K
    let p' := if p = 0 then 1 else p
    have : IsSplittingField ℚ K p' := by
      dsimp [p']
      split_ifs with h
      constructor
      simp
      simpa [h] using hp.adjoin_rootSet
      assumption
    let qX : ℚ[X] := X ^ l - 1
    have : IsSplittingField K M $ qX.map $ algebraMap ℚ K := by simpa [qX] using isSplittingField_X_pow_sub_one l K M
    have := IsSplittingField.mul (K := K) (L := M) p' qX (by grind) $ X_pow_sub_C_ne_zero hlp0 1
    have := Normal.of_isSplittingField (E := M) $ p' * qX
    exact ⟨⟩
  set zt := zeta l K M
  have hzt := zeta_spec l K M
  have hzpow {a b : ℕ} : zt ^ a = zt ^ b ↔ (a : ZMod l) = b := by
    rw [(hzt.isOfFinOrder hlp.ne_zero).pow_eq_pow_iff_modEq, ← eq_orderOf hzt, ← natCast_eq_natCast_iff]
  obtain ⟨ta, htgen⟩ := IsCyclic.exists_generator (α := UZ l)
  have hcard := (card_units_eq_totient l).trans $ totient_prime hlp
  obtain ⟨g, hg, hgz⟩ : ∃ g : Gal(M/ℚ), restrictNormalHom K g = sg ∧ g zt = zt ^ (ta : ZMod l).val := by
    obtain ⟨g0, hg0⟩ := restrictNormalHom_surjective (K₁ := K) M sg
    let h1 := fromZetaAut (hzt.map_of_injective g0.injective) hirr
    let h := (autEquivPow M hirr).symm ta * h1.symm
    use h.restrictScalars ℚ * g0
    constructor
    rw [map_mul, hg0]
    ext x
    apply (algebraMap K M).injective
    simp [restrictNormalHom]
    dsimp [h]
    rw [mpr (symm_apply_eq h1) $ sy $ fromZetaAut_spec _ hirr,
      ← hzt.autToPow_spec K, show hzt.autToPow K _ = ta from (autEquivPow M hirr).apply_symm_apply ta]
  have hpow m : (g ^ m) zt = zt ^ (↑(ta ^ m) : ZMod l).val := by
    induction m with
    | zero => simp [val_one]
    | succ m ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hgz, map_pow, ih, ← pow_mul, hzpow]
      simp [pow_succ]
  set E := fixedField $ zpowers g
  obtain ⟨q, hq, hqp, hqT, hqmod⟩ := cyc_holds (E := E) (by
    have hint := IsIntegral.isIntegral (R := E) zt
    have hdeg := card_le_degree_of_subset_roots (p := (minpoly E zt).map $ algebraMap E M)
      (Z := univ.image fun u : UZ l ↦ zt ^ (u : ZMod l).val) fun z hz ↦ by
      obtain ⟨u, -, rfl⟩ := mp mem_image hz
      obtain ⟨k, rfl⟩ := mpr mem_powers_iff_mem_zpowers $ htgen u
      rw [mem_roots $ map_ne_zero $ minpoly.ne_zero hint, IsRoot, eval_map_algebraMap, ← hpow k]
      simpa using aeval_algHom_apply ({ (g ^ k).toRingHom with commutes' := fun x ↦ x.2 ⟨g ^ k, npow_mem_zpowers g k⟩ } : M →ₐ[E] M) zt $ minpoly E zt
    rw [Finset.card_image_of_injective _ fun u v huv ↦ uext $ by simpa using mp hzpow huv,
      card_univ, hcard, natDegree_map] at hdeg
    rw [eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) $ cyclotomic.monic l E]
    exact minpoly.irreducible hint
    apply minpoly.dvd
    simpa [← eval_map_algebraMap] using hzt.isRoot_cyclotomic hlp0
    rwa [natDegree_cyclotomic, totient_prime hlp]) ta $ T ∪ range (D + 1) ∪ {l}
  simp at hqT
  rcases hqT with ⟨hql, hqT, hqD⟩
  set p := absNorm q with hpdef
  have := hq.isMaximal fun h ↦ hqp.ne_zero $ hpdef ▸ h ▸ absNorm_bot
  obtain ⟨P, hPmax, hPq⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := OM) q
  have hPunder := sy hPq.over
  obtain ⟨ph, hp0⟩ := exists_of_isInvariant (𝓞 E) Gal(M/E) P
  set phQ := ph.restrictScalars ℚ
  have hPZ : P.under ℤ = span {zN p} := by
    rw [← under_under (B := 𝓞 E), hPunder,
      ← (mpr (liesOver_span_iff hq.ne_top $ mp prime_iff_prime_int hqp) $ by simpa using absNorm_mem q).over]
  have hcardZ : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hPZ, card_congr (quotientSpanNatEquivZMod p).toEquiv, card_zmod]
  have hph : IsArithFrobAt ℤ phQ P := fun x ↦ by
    rw [hcardZ, hpdef, ← hPunder, absNorm_apply, cardQuot_apply]
    exact hp0 x
  have hphK : restrictNormalHom K phQ = sg := by
    obtain ⟨k, hk : g ^ k = phQ⟩ := mpr mem_powers_iff_mem_zpowers $ show phQ ∈ _ by
      rw [← fixingSubgroup_fixedField $ zpowers g]
      exact ph.commutes
    have hp' : (g ^ k) zt = zt ^ p := by
      rw [hk]
      exact et (congrArg (·.1) $ hcardZ ▸ hph.apply_of_pow_eq_one hzt.toInteger_isPrimitiveRoot.pow_eq_one fun h ↦ hql $
        mp (prime_dvd_prime_iff_eq hqp hlp) $ mp ofNat_dvd $ mp mem_span_singleton $ by simpa [← hPZ] using h) $ SubmonoidClass.coe_pow _ _
    rw [hpow, hzpow, natCast_zmod_val, hqmod] at hp'
    rw [← hk, map_pow, hg, ← pow_one sg]
    apply mpr (isOfFinOrder_of_finite sg).pow_eq_pow_iff_modEq
    apply ModEq.of_dvd $ mp (modEq_iff_dvd' hlp.one_lt.le) $ sy hlmod
    rw [← hcard, ← card_eq_fintype_card, ← orderOf_eq_card_of_forall_mem_zpowers htgen]
    apply mp (isOfFinOrder_of_finite ta).pow_eq_pow_iff_modEq
    simpa using uext hp'
  set Q := P.under OK
  have hQp : Q.LiesOver $ span {zN p} := ⟨sy $ et (under_under P) hPZ⟩
  use p, hqp, hqT, Q, inferInstance, hQp, hN _ hqp (by omega) Q hQp
  intro y
  rw [← hphK, Ideal.mem_comap, under_under]
  simpa [show algebraMap OK OM (restrictNormalHom K phQ • y) = phQ • algebraMap OK OM y from
    ext $ restrictNormal_commutes phQ K y] using hph $ algebraMap OK OM y

end

end
