import Mathlib

open Polynomial Filter Topology Metric
open MvPolynomial (eval continuous_eval)
open Fin (tail succ cons)
open Finset (range single_le_sum prod_ne_zero_iff prod_eq_zero mem_univ)
open Set (mem_insert_of_mem mem_insert)
open Function (update)
open IntermediateField (adjoin)
open MvPolynomial (rename eval_rename comp_aeval_apply)
open Multiset (prod_map_le_prod_map₀ map_const' prod_replicate mem_of_mem_filter mem_map_of_mem mem_toFinset)
open Ideal.Quotient (mk mk_surjective eq_zero_iff_mem)
local notation "𝕏" => MvPolynomial.X
local notation "ℭ" => MvPolynomial.C
set_option hygiene false in
local notation "𝓡" => MvPolynomial (Fin s) ℂ
set_option hygiene false in
local notation "𝓐" => MvPolynomial σ ℂ ⧸ W

namespace AlpogeRHCore7

/-- If a monic family of bounded degree is small at `t₀`, it has a root near `t₀`. -/
theorem ex_root {α : Type*} {l : Filter α} {Q : α → ℂ[X]} {k : ℕ} {t₀ : ℂ}
    (hQ : ∀ a, (Q a).Monic ∧ (Q a).natDegree = k)
    (h0 : Tendsto (fun a => (Q a).eval t₀) l (𝓝 0)) {V : Set ℂ} (hV : V ∈ 𝓝 t₀) :
    ∀ᶠ a in l, ∃ t ∈ V, (Q a).eval t = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  filter_upwards [(tendsto_norm_zero.comp h0) (Iio_mem_nhds (pow_pos hε k))] with a ha
  by_contra! hfar
  have hs := IsAlgClosed.splits (Q a)
  have hle : ∀ r ∈ (Q a).roots, ε ≤ ‖t₀ - r‖ := fun r hr => by
    by_contra! hlt
    exact hfar r (hball (by rw [mem_ball, dist_comm, dist_eq_norm]; exact hlt))
      ((mem_roots (hQ a).1.ne_zero).1 hr)
  have := prod_map_le_prod_map₀ (fun _ => ε) (fun r => ‖t₀ - r‖) (fun _ _ => hε.le) hle
  rw [map_const', prod_replicate, ← hs.natDegree_eq_card_roots, (hQ a).2] at this
  refine absurd ha (not_lt.2 (this.trans_eq ?_))
  rw [Function.comp_apply, hs.eval_eq_prod_roots_of_monic (hQ a).1]
  exact (Q a).roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun r : ℂ => t₀ - r)

theorem roots_branch {Q : ℂ → ℂ[X]} {k : ℕ} {s₀ : ℂ}
    (hQ : ∀ s, (Q s).Monic ∧ (Q s).natDegree = k)
    (hc : ∀ t, ContinuousAt (fun s => (Q s).eval t) s₀) (hnd : (Q s₀).roots.Nodup) :
    ∃ τ : ℂ → ℂ → ℂ, (∀ t ∈ (Q s₀).roots, ContinuousAt (τ t) s₀ ∧ τ t s₀ = t) ∧
      ∀ᶠ s in 𝓝 s₀, (Q s).roots = (Q s₀).roots.map (fun t => τ t s) := by
  have hex : ∀ t s, ∃ x, (Q s).roots ≠ 0 → x ∈ (Q s).roots ∧
      ∀ y ∈ (Q s).roots, dist x t ≤ dist y t := fun t s =>
    if h : (Q s).roots = 0 then ⟨t, fun h' => absurd h h'⟩
    else (Multiset.exists_min_image (dist · t) h).imp fun _ hx _ => hx
  choose τ hτ using hex
  have hcard : ∀ s, (Q s).roots.card = k := fun s =>
    ((IsAlgClosed.splits (Q s)).natDegree_eq_card_roots).symm.trans (hQ s).2
  have hcont : ∀ t ∈ (Q s₀).roots, Tendsto (τ t) (𝓝 s₀) (𝓝 t) := fun t ht => by
    have h0 : (Q s₀).eval t = 0 := (mem_roots (hQ s₀).1.ne_zero).1 ht
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [ex_root hQ
      (by simpa [h0] using (hc t).tendsto) (ball_mem_nhds t hε)] with s ⟨y, hy, hy0⟩
    have hy' : y ∈ (Q s).roots := (mem_roots (hQ s).1.ne_zero).2 hy0
    exact ((hτ t s (fun h0 => by simp [h0] at hy')).2 y hy').trans_lt (mem_ball.1 hy)
  have hfix : ∀ t ∈ (Q s₀).roots, τ t s₀ = t := fun t ht =>
    dist_le_zero.1 (((hτ t s₀ (fun h0 => by simp [h0] at ht)).2 t ht).trans_eq (dist_self t))
  refine ⟨τ, fun t ht => ⟨by rw [ContinuousAt, hfix t ht]; exact hcont t ht, hfix t ht⟩, ?_⟩
  have hne : ∀ᶠ s in 𝓝 s₀, ∀ t ∈ (Q s₀).roots.toFinset, ∀ t' ∈ (Q s₀).roots.toFinset,
      t ≠ t' → τ t s ≠ τ t' s := by
    simp only [Filter.eventually_all_finset]
    intro t ht t' ht'
    by_cases h : t = t'
    · exact Eventually.of_forall fun _ h' => absurd h h'
    exact (((hcont t (by simpa using ht)).sub (hcont t' (by simpa using ht'))).eventually_ne
      (sub_ne_zero.2 h)).mono fun _ h' _ => sub_ne_zero.1 h'
  filter_upwards [hne] with s hs
  have hM : ((Q s₀).roots.map fun t => τ t s).Nodup :=
    hnd.map_on fun t ht t' ht' he =>
      by_contra fun h => hs t (by simpa using ht) t' (by simpa using ht') h he
  refine (Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hM).2 fun x hx => ?_)
    (by rw [Multiset.card_map, hcard, hcard])).symm
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hx
  refine (hτ t s fun h => ?_).1
  have := hcard s
  rw [h, Multiset.card_zero, ← hcard s₀] at this
  exact (fun h0 => by simp [h0] at ht : (Q s₀).roots ≠ 0) (Multiset.card_eq_zero.1 this.symm)

theorem poly1 {g : ℂ → ℂ} {K R₀ : ℝ} {M : ℕ} (hg : Differentiable ℂ g) (hR₀ : 0 < R₀)
    (hb : ∀ z, R₀ < ‖z‖ → ‖g z‖ ≤ K * (1 + ‖z‖) ^ M) :
    ∃ q : ℂ[X], q.natDegree ≤ M ∧ ∀ z, g z = q.eval z := by
  have h0 : ∀ n, M < n → iteratedDeriv n g 0 = 0 := by
    intro n hn
    have hlim : Tendsto (fun R : ℝ => (C (n.factorial * K) * (1 + X) ^ M : ℝ[X]).eval R /
        (X ^ n : ℝ[X]).eval R) atTop (𝓝 0) := by
      apply div_tendsto_atTop_zero_of_degree_lt
      refine (degree_le_of_natDegree_le (n := M) (by compute_degree)).trans_lt ?_
      simpa using hn
    refine norm_le_zero_iff.1 (ge_of_tendsto hlim ((eventually_gt_atTop R₀).mono fun R hR => ?_))
    simpa [mul_assoc] using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
      (hR₀.trans hR) hg.diffContOnCl fun z hz => by
        simpa [mem_sphere_zero_iff_norm.1 hz] using hb z (by simpa [mem_sphere_zero_iff_norm.1 hz])
  refine ⟨∑ n ∈ range (M + 1), C ((n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0) * X ^ n,
    natDegree_sum_le_of_forall_le _ _ fun n hn => (natDegree_C_mul_X_pow_le _ _).trans
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)), fun z => ?_⟩
  rw [← Complex.taylorSeries_eq_of_entire' 0 z hg, tsum_eq_sum (s := range (M + 1))
    (fun n hn => by simp [h0 n (by simpa using hn)])]
  simp [eval_finsetSum]

theorem removable {E : Set ℂ} (hE : E.Finite) {h : ℂ → ℂ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    (hd : ∀ s ∉ E, DifferentiableAt ℂ h s) (hb : ∀ s ∉ E, ‖h s‖ ≤ φ s) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ s ∉ E, H s = h s := by
  classical
  refine ⟨fun s => if s ∈ E then limUnder (𝓝[≠] s) h else h s, fun e => ?_, fun s hs => if_neg hs⟩
  by_cases he : e ∈ E
  · have hU : ball e 1 ∩ (E \ {e})ᶜ ∈ 𝓝 e :=
      inter_mem (ball_mem_nhds e one_pos) (hE.diff.isClosed.isOpen_compl.mem_nhds (by simp))
    refine ((Complex.differentiableOn_update_limUnder_of_bddAbove (f := h) hU ?_ ?_).differentiableAt
      hU).congr_of_eventuallyEq ?_
    · rintro s ⟨⟨-, hs⟩, hse⟩
      exact (hd s fun h => hs ⟨h, hse⟩).differentiableWithinAt
    · obtain ⟨B, hB⟩ := (isCompact_closedBall e 1).exists_bound_of_continuousOn hφ.continuousOn
      refine ⟨B, ?_⟩
      rintro _ ⟨s, ⟨⟨hs1, hs⟩, hse⟩, rfl⟩
      exact (hb s fun h => hs ⟨h, hse⟩).trans ((le_abs_self _).trans
        (by simpa using hB s (ball_subset_closedBall hs1)))
    · filter_upwards [hU] with s ⟨_, hs⟩
      by_cases hse : s = e
      · subst hse; simp [he]
      · simp [hse, show s ∉ E from fun h => hs ⟨h, hse⟩]
  · exact (hd e he).congr_of_eventuallyEq (by
      filter_upwards [hE.isClosed.isOpen_compl.mem_nhds he] with s hs; exact if_neg hs)

/-- A continuous simple root of a differentiable family of polynomials is differentiable. -/
theorem impdiff {Q : ℂ → ℂ[X]} {k : ℕ} {s₀ : ℂ} {τ : ℂ → ℂ}
    (hk : ∀ s, (Q s).natDegree < k)
    (hA : ∀ j, DifferentiableAt ℂ (fun s => (Q s).coeff j) s₀)
    (hτ : ContinuousAt τ s₀) (h0 : ∀ᶠ s in 𝓝 s₀, (Q s).eval (τ s) = 0)
    (hd : (Q s₀).derivative.eval (τ s₀) ≠ 0) : DifferentiableAt ℂ τ s₀ := by
  set q := Q s₀
  have hq := q.hasStrictDerivAt (τ s₀)
  have key : ∀ j, DifferentiableAt ℂ (fun s => ((Q s).coeff j - q.coeff j) * τ s ^ j) s₀ := fun j =>
    (hasDerivAt_iff_tendsto_slope.2 (((hasDerivAt_iff_tendsto_slope.1 (hA j).hasDerivAt).mul
      (((hτ.pow j).tendsto).mono_left nhdsWithin_le_nhds)).congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [slope_def_field, sub_self, zero_mul, sub_zero, q, Pi.pow_apply]
        ring))).differentiableAt
  have hΛ : DifferentiableAt ℂ (fun s => q.eval (τ s)) s₀ := by
    refine ((DifferentiableAt.sum fun j (_ : j ∈ range k) => key j).neg).congr_of_eventuallyEq ?_
    filter_upwards [h0] with s hs
    rw [eval_eq_sum_range' (hk s₀), ← sub_zero (∑ i ∈ _, _), ← hs, eval_eq_sum_range' (hk s)]
    simp [Finset.sum_sub_distrib, sub_mul, q]
  have hev : (fun s => hq.localInverse _ _ _ hd (q.eval (τ s))) =ᶠ[𝓝 s₀] τ :=
    hτ.tendsto.eventually (hq.eventually_left_inverse hd)
  exact ((hq.to_localInverse hd).hasDerivAt.comp s₀ hΛ.hasDerivAt).differentiableAt.congr_of_eventuallyEq
    hev.symm

theorem lineval {σ : Type*} (q : MvPolynomial σ ℂ) (c e : σ → ℂ) (s : ℂ) :
    (MvPolynomial.aeval (fun i => C (c i) + C (e i) * X) q).eval s =
      eval (c + s • e) q := by
  have := comp_aeval_apply (fun i => C (c i) + C (e i) * X) (aeval s) q
  simp only [coe_aeval_eq_eval] at this
  have e' : (fun i => Polynomial.eval s (C (c i) + C (e i) * X)) = c + s • e := by
    ext i; simp only [eval_add, eval_C, eval_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [this, e']; rfl

theorem sp {N : ℕ} : ∀ (D : ℕ) (S : Fin D → Set ℂ) (c : (Fin D → ℂ) → ℂ), (∀ i, (S i).Infinite) →
    (∀ y ∈ Set.univ.pi S, ∀ i, ∃ p : ℂ[X], p.natDegree ≤ N ∧
      ∀ s ∈ S i, c (update y i s) = p.eval s) →
    ∃ P : MvPolynomial (Fin D) ℂ, ∀ y ∈ Set.univ.pi S, c y = eval y P := by
  intro D
  induction D with
  | zero =>
    intro S c _ _
    exact ⟨ℭ (c 0), fun y _ => by
      rw [MvPolynomial.eval_C]; congr 1; exact Subsingleton.elim _ _⟩
  | succ D ih =>
    intro S c hS hc
    obtain ⟨T, hTS, hT⟩ := (hS 0).exists_subset_card_eq (N + 1)
    have hP : ∀ t ∈ S 0, ∃ P : MvPolynomial (Fin D) ℂ, ∀ y ∈ Set.univ.pi (S ∘ succ),
        c (cons t y) = eval y P := by
      intro t ht
      refine ih _ _ (fun i => hS _) fun y hy i => ?_
      obtain ⟨p, hp, hp'⟩ := hc (cons t y)
        (fun j _ => Fin.cases (by simpa using ht) (fun j => by simpa using hy j trivial) j) i.succ
      exact ⟨p, hp, fun s hs => by rw [← hp' s hs, Fin.cons_update]⟩
    choose! P hP using hP
    refine ⟨∑ t ∈ T, aeval (𝕏 0 : MvPolynomial (Fin (D + 1)) ℂ)
      (Lagrange.basis T id t) * rename succ (P t), fun y hy => ?_⟩
    obtain ⟨p, hpd, hp⟩ := hc y hy 0
    have hdeg : p.degree < T.card := by
      rw [hT]; exact (degree_le_of_natDegree_le hpd).trans_lt (by exact_mod_cast Nat.lt_succ_self N)
    have key := Lagrange.eq_interpolate (s := T) (v := id) (Set.injOn_id _) hdeg
    have hev : ∀ q : ℂ[X], eval y
        (aeval (𝕏 0 : MvPolynomial (Fin (D + 1)) ℂ) q) = q.eval (y 0) := by
      intro q
      show MvPolynomial.aeval y _ = _
      rw [← aeval_algHom_apply]
      simp
    have hy0 : c y = p.eval (y 0) := by
      rw [← hp (y 0) (hy 0 trivial), Function.update_eq_self]
    have hyt : ∀ t ∈ T, p.eval t = eval (tail y) (P t) := fun t ht => by
      rw [← hp t (hTS ht), ← hP t (hTS ht) (tail y) (fun j _ => hy j.succ trivial)]
      conv_lhs => rw [← Fin.cons_self_tail y]
      rw [Fin.update_cons_zero]
    rw [hy0, key, Lagrange.interpolate_apply, eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [map_mul, hev, eval_rename, eval_mul, eval_C, id, hyt t ht,
      mul_comm]
    rfl

theorem polylines {D N : ℕ} (c : (Fin D → ℂ) → ℂ) (δ : MvPolynomial (Fin D) ℂ) (hδ : δ ≠ 0)
    (hline : ∀ a v : Fin D → ℂ, eval a δ ≠ 0 → ∃ p : ℂ[X], p.natDegree ≤ N ∧
      ∀ s : ℂ, eval (a + s • v) δ ≠ 0 → c (a + s • v) = p.eval s) :
    ∃ P : MvPolynomial (Fin D) ℂ, ∀ y, eval y δ ≠ 0 → c y = eval y P := by
  obtain ⟨a, ha⟩ : ∃ a, eval a δ ≠ 0 := by
    by_contra! h; exact hδ (MvPolynomial.funext fun x => by simpa using h x)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1
    (isOpen_ne_fun (continuous_eval δ) continuous_const) a ha
  have hbox : ∀ y ∈ Set.univ.pi (fun i => ball (a i) r), eval y δ ≠ 0 :=
    fun y hy => hball (by rwa [ball_pi _ hr])
  obtain ⟨P, hP⟩ := sp (N := N) D _ c (fun i => infinite_of_mem_nhds (a i) (ball_mem_nhds _ hr))
    (fun y hy i => by
      obtain ⟨p, hp, hp'⟩ := hline y (Pi.single i 1) (hbox y hy)
      refine ⟨p.comp (X - C (y i)), by rw [natDegree_comp]; simpa using hp, fun s hs => ?_⟩
      have e : update y i s = y + (s - y i) • Pi.single i 1 := by
        ext j; by_cases hj : j = i <;> simp [hj, Function.update]
      have hm : update y i s ∈ Set.univ.pi (fun i => ball (a i) r) := fun j _ => by
        by_cases hj : j = i
        · subst hj; simpa using hs
        · simpa [hj] using hy j trivial
      rw [e, hp' _ (by rw [← e]; exact hbox _ hm)]
      simp)
  refine ⟨P, fun y hy => ?_⟩
  obtain ⟨p, -, hp⟩ := hline a (y - a) ha
  have hpq : p = MvPolynomial.aeval (fun i => C (a i) + C ((y - a) i) * X) P := by
    refine eq_of_infinite_eval_eq _ _ (Set.Infinite.mono (s := ball 0 (r / (‖y - a‖ + 1)))
      (fun s hs => ?_) (infinite_of_mem_nhds (0:ℂ) (ball_mem_nhds _ (by positivity))))
    have hm : a + s • (y - a) ∈ Set.univ.pi (fun i => ball (a i) r) := by
      rw [← ball_pi _ hr, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      rw [mem_ball_zero_iff, lt_div_iff₀ (by positivity)] at hs
      nlinarith [norm_nonneg s, norm_nonneg (y - a)]
    show p.eval s = _
    rw [← hp s (hbox _ hm), lineval, hP _ hm]
  have h1 := hp 1 (by simpa using hy)
  rw [one_smul, add_sub_cancel] at h1
  rw [h1, hpq, lineval, one_smul, add_sub_cancel]

theorem cauchy {G : ℂ[X]} (hG : G.Monic) {t : ℂ} (ht : G.eval t = 0) :
    ‖t‖ ≤ ∑ k ∈ range G.natDegree, ‖G.coeff k‖ + 1 := by
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hG.ne_zero ht
  have h2 : cauchyBound G ≤ ∑ k ∈ range G.natDegree, ‖G.coeff k‖₊ + 1 := by
    rw [cauchyBound, hG.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun k hk =>
      single_le_sum (f := fun k => ‖G.coeff k‖₊) (fun _ _ => zero_le) hk
  simpa using NNReal.coe_le_coe.2 (h1.trans_le h2).le

theorem mvgrowth {d : ℕ} (q : MvPolynomial (Fin d) ℂ) :
    ∃ C E : ℕ, ∀ y : Fin d → ℂ, ‖eval y q‖ ≤ C * (1 + ‖y‖) ^ E := by
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨⌈‖a‖⌉₊, 0, fun y => by simpa using Nat.le_ceil _⟩
  | add p q hp hq =>
    obtain ⟨C1, E1, h1⟩ := hp; obtain ⟨C2, E2, h2⟩ := hq
    refine ⟨C1 + C2, E1 + E2, fun y => ?_⟩
    have hy : (1:ℝ) ≤ 1 + ‖y‖ := by simp
    have := pow_le_pow_right₀ hy (Nat.le_add_right E1 E2)
    have := pow_le_pow_right₀ hy (Nat.le_add_left E2 E1)
    rw [map_add]; push_cast
    nlinarith [norm_add_le (eval y p) (eval y q), h1 y, h2 y, C1.cast_nonneg (α := ℝ),
      C2.cast_nonneg (α := ℝ)]
  | mul_X p i hp =>
    obtain ⟨C1, E1, h1⟩ := hp
    refine ⟨C1, E1 + 1, fun y => ?_⟩
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (h1 y) ((norm_le_pi_norm y i).trans (by linarith)) (norm_nonneg _)
      (by positivity)

theorem rootgrowth {d : ℕ} {F : Polynomial (MvPolynomial (Fin d) ℂ)} (hF : F.Monic) :
    ∃ C E : ℕ, ∀ (z : Fin (d + 1) → ℂ) t, (F.map (eval (tail z))).eval t = 0 →
      ‖z 0 - t‖ ≤ (1 + C) * (1 + ‖z‖) ^ E := by
  choose C E h using fun i => mvgrowth (rename succ (F.coeff i))
  set S := range F.natDegree
  refine ⟨∑ i ∈ S, C i, ∑ i ∈ S, E i + 1, fun z t ht => ?_⟩
  have hz : (1:ℝ) ≤ 1 + ‖z‖ := by simp
  have hb := cauchy (hF.map _) ht
  rw [hF.natDegree_map] at hb
  have := Finset.sum_le_sum fun i (hi : i ∈ S) =>
    show ‖(F.map (eval (tail z))).coeff i‖ ≤ C i * (1 + ‖z‖) ^ (∑ i ∈ S, E i + 1) by
      rw [coeff_map, show tail z = z ∘ succ from rfl, ← eval_rename]
      exact (h i z).trans (by
        gcongr
        exact (single_le_sum (fun _ _ => Nat.zero_le _) hi).trans (Nat.le_succ _))
  have h2 : 1 + ‖z‖ ≤ (1 + ‖z‖) ^ (∑ i ∈ S, E i + 1) := le_self_pow₀ hz (by omega)
  push_cast; rw [add_mul, Finset.sum_mul, one_mul]
  linarith [norm_sub_le (z 0) t, norm_le_pi_norm z 0]

theorem hev {d : ℕ} (P : Polynomial (MvPolynomial (Fin d) ℂ)) (y : Fin d → ℂ) (t : ℂ) :
    (P.map (eval y)).eval t = eval y (P.eval (ℭ t)) := by
  rw [eval_map, ← eval₂_at_apply, MvPolynomial.eval_C]

theorem dmprod {s₀ : ℂ} {f : ℂ → ℂ → ℂ} : ∀ m : Multiset ℂ,
    (∀ t ∈ m, DifferentiableAt ℂ (f t) s₀) →
    DifferentiableAt ℂ (fun s => (m.map fun t => f t s).prod) s₀ := by
  intro m
  induction m using Multiset.induction_on with
  | empty => intro _; simp
  | cons t m ih =>
    intro h
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (h t (Multiset.mem_cons_self _ _)).mul (ih fun t' ht' => h t' (Multiset.mem_cons_of_mem ht'))

theorem hyp {d : ℕ} {F : Polynomial (MvPolynomial (Fin d) ℂ)} {δ : MvPolynomial (Fin d) ℂ}
    (hF : F.Monic) (hirr : Irreducible F) (hδ : δ ≠ 0)
    (hsep : ∀ y, eval y δ ≠ 0 → (F.map (eval y)).Separable) :
    IsPreconnected {p : (Fin d → ℂ) × ℂ | eval p.1 δ ≠ 0 ∧
      (F.map (eval p.1)).eval p.2 = 0} := by
  classical
  set Z := {p : (Fin d → ℂ) × ℂ | eval p.1 δ ≠ 0 ∧
      (F.map (eval p.1)).eval p.2 = 0} with hZdef
  set k := F.natDegree
  have hvan : ∀ P : Polynomial (MvPolynomial (Fin d) ℂ),
      (∀ y, eval y δ ≠ 0 → P.map (eval y) = 0) → P = 0 := by
    intro P hP
    ext1 n
    refine (mul_eq_zero.1 (MvPolynomial.funext fun y => ?_ : P.coeff n * δ = 0)).resolve_right hδ
    by_cases hy : eval y δ = 0
    · simp [hy]
    · simpa [hy] using congrArg (coeff · n) (hP y hy)
  obtain ⟨C0, E0, hroot⟩ := rootgrowth hF
  have hmain : ∀ u v : Set ((Fin d → ℂ) × ℂ), IsOpen u → IsOpen v → Z ⊆ u ∪ v →
      (∀ p ∈ Z, p ∈ u → p ∉ v) → (∃ p ∈ Z, p ∈ u) →
      ∃ G : Polynomial (MvPolynomial (Fin d) ℂ), ¬ IsUnit G ∧ ∀ y, eval y δ ≠ 0 →
        G.map (eval y) = (((F.map (eval y)).roots.filter
          (fun t => (y, t) ∈ u)).map (fun t => X - C t)).prod := by
    intro u v hu hv hZ hdisj ⟨p, hpZ, hpu⟩
    let g : (Fin (d + 1) → ℂ) → ℂ := fun z => (((F.map (eval (tail z))).roots.filter
      (fun t => (tail z, t) ∈ u)).map (fun t => z 0 - t)).prod
    have hδ' : rename succ δ ≠ 0 := fun h =>
      hδ (MvPolynomial.rename_injective _ (Fin.succ_injective _) (by simpa using h))
    have hevδ : ∀ z, eval z (rename succ δ) =
        eval (tail z) δ := fun z => by rw [eval_rename]; rfl
    have hgb : ∀ z, ‖g z‖ ≤ ((1 + C0) * (1 + ‖z‖) ^ E0) ^ k := fun z => by
      set m := (F.map (eval (tail z))).roots.filter (fun t => (tail z, t) ∈ u)
      calc ‖g z‖ = (m.map fun t => ‖z 0 - t‖).prod :=
            (m.prod_hom' (NormedField.toMulRingNorm ℂ) (fun t => z 0 - t)).symm
        _ ≤ (m.map fun _ => (1 + C0) * (1 + ‖z‖) ^ E0).prod :=
            prod_map_le_prod_map₀ _ _ (fun _ _ => norm_nonneg _) fun t ht =>
              hroot z t ((mem_roots (hF.map _).ne_zero).1 (mem_of_mem_filter ht))
        _ = ((1 + C0) * (1 + ‖z‖) ^ E0) ^ m.card := by
            rw [map_const', prod_replicate]
        _ ≤ _ := pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (by simp)
            (one_le_pow₀ (by simp))) ((Multiset.card_le_card (Multiset.filter_le _ _)).trans
            ((card_roots' _).trans (hF.natDegree_map _).le))
    have hline : ∀ a b : Fin (d + 1) → ℂ, eval a (rename succ δ) ≠ 0 →
        ∃ p : ℂ[X], p.natDegree ≤ E0 * k ∧ ∀ s : ℂ,
          eval (a + s • b) (rename succ δ) ≠ 0 →
            g (a + s • b) = p.eval s := by
      intro a b ha
      set ℓ : ℂ[X] := MvPolynomial.aeval (fun i => C (a i) + C (b i) * X)
        (rename succ δ)
      have hℓ : ∀ s, ℓ.eval s = eval (a + s • b) (rename succ δ) :=
        lineval _ a b
      have hℓ0 : ℓ ≠ 0 := fun h => ha (by simpa [h] using (hℓ 0).symm)
      set y : ℂ → Fin d → ℂ := fun s => tail a + s • tail b
      have hyl : ∀ s, tail (a + s • b) = y s := fun s => rfl
      have hyc : Continuous y := by fun_prop
      set Q : ℂ → ℂ[X] := fun s => F.map (eval (y s))
      have hQ : ∀ s, (Q s).Monic ∧ (Q s).natDegree = k := fun s => ⟨hF.map _, hF.natDegree_map _⟩
      have hdiff : ∀ s₀ ∉ {s | ℓ.IsRoot s}, DifferentiableAt ℂ (fun s => g (a + s • b)) s₀ := by
        intro s₀ hs₀
        have hs₀' : eval (y s₀) δ ≠ 0 := by
          rw [← hyl, ← hevδ, ← hℓ]; exact hs₀
        have hc : ∀ t, ContinuousAt (fun s => (Q s).eval t) s₀ := fun t => by
          simp only [Q, hev]; exact ((continuous_eval _).comp hyc).continuousAt
        obtain ⟨τ, hτ, hEq⟩ := roots_branch hQ hc (nodup_roots (hsep _ hs₀'))
        have hA : ∀ j, DifferentiableAt ℂ (fun s => (Q s).coeff j) s₀ := fun j => by
          simp only [Q, coeff_map]
          exact (AnalyticAt.aeval_mvPolynomial (fun i => by simp only [y, Pi.add_apply, Pi.smul_apply]; fun_prop) _).differentiableAt
        have hroot : ∀ t ∈ (Q s₀).roots, ∀ᶠ s in 𝓝 s₀, (Q s).eval (τ t s) = 0 := fun t ht =>
          hEq.mono fun s hs => (mem_roots (hQ s).1.ne_zero).1 (hs ▸ mem_map_of_mem _ ht)
        have hτd : ∀ t ∈ (Q s₀).roots, DifferentiableAt ℂ (τ t) s₀ := fun t ht =>
          impdiff (k := k + 1) (fun s => by rw [(hQ s).2]; omega) hA (hτ t ht).1 (hroot t ht)
            (by rw [(hτ t ht).2]; exact (hsep _ hs₀').eval₂_derivative_ne_zero _ ((mem_roots (hQ s₀).1.ne_zero).1 ht))
        have hgood : ∀ᶠ s in 𝓝 s₀, eval (y s) δ ≠ 0 :=
          ((continuous_eval δ).comp hyc).continuousAt.eventually_ne hs₀'
        have hloc : ∀ᶠ s in 𝓝 s₀, ∀ t ∈ (Q s₀).roots.toFinset,
            ((y s, τ t s) ∈ u ↔ (y s₀, t) ∈ u) := by
          refine (Filter.eventually_all_finset _).2 fun t ht' => ?_
          have ht := mem_toFinset.1 ht'
          have hcont : ContinuousAt (fun s => (y s, τ t s)) s₀ :=
            hyc.continuousAt.prodMk (hτ t ht).1
          have h0 : (y s₀, τ t s₀) = (y s₀, t) := by rw [(hτ t ht).2]
          have htZ : (y s₀, t) ∈ Z := ⟨hs₀', (mem_roots (hQ s₀).1.ne_zero).1 ht⟩
          by_cases htu : (y s₀, t) ∈ u
          · filter_upwards [hcont.preimage_mem_nhds (hu.mem_nhds (by rw [h0]; exact htu))]
              with s hs
            exact iff_of_true hs htu
          · filter_upwards [hcont.preimage_mem_nhds
              (hv.mem_nhds (by rw [h0]; exact (hZ htZ).resolve_left htu)), hroot t ht, hgood]
              with s hs hs2 hs3
            exact iff_of_false (fun h => hdisj (y s, τ t s) ⟨hs3, hs2⟩ h hs) htu
        have hform : (fun s => g (a + s • b)) =ᶠ[𝓝 s₀] fun s =>
            (((Q s₀).roots.filter (fun t => (y s₀, t) ∈ u)).map
              (fun t => (a 0 + s * b 0) - τ t s)).prod := by
          filter_upwards [hEq, hloc] with s hs hs'
          show ((((Q s).roots).filter (fun t => (y s, t) ∈ u)).map
            (fun t => (a + s • b) 0 - t)).prod = _
          rw [hs, Multiset.filter_map, Multiset.map_map]
          simp only [Function.comp_def]
          rw [Multiset.filter_congr fun t ht => hs' t (mem_toFinset.2 ht)]
          rfl
        refine DifferentiableAt.congr_of_eventuallyEq ?_ hform
        exact dmprod _ fun t ht => by
          have := hτd t (mem_of_mem_filter ht)
          fun_prop
      have hbd : ∀ s : ℂ, ‖g (a + s • b)‖ ≤ ((1 + C0) * (1 + ‖a‖ + ‖b‖) ^ E0) ^ k *
          (1 + ‖s‖) ^ (E0 * k) := fun s => by
        refine (hgb _).trans ?_
        have h1 : 1 + ‖a + s • b‖ ≤ (1 + ‖a‖ + ‖b‖) * (1 + ‖s‖) := by
          have := norm_add_le a (s • b); rw [norm_smul] at this
          nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg s]
        calc ((1 + C0) * (1 + ‖a + s • b‖) ^ E0) ^ k ≤
              ((1 + C0) * ((1 + ‖a‖ + ‖b‖) * (1 + ‖s‖)) ^ E0) ^ k := by gcongr
          _ = _ := by simp only [mul_pow, ← pow_mul]; ring
      have hE := finite_setOfPred_isRoot hℓ0
      obtain ⟨H, hH, hHe⟩ := removable hE (by fun_prop) hdiff fun s _ => hbd s
      obtain ⟨R, hR0, hR⟩ := hE.isBounded.subset_closedBall_lt 0 0
      obtain ⟨p, hp, hp'⟩ := poly1 hH hR0 fun z hz => by
        rw [hHe z fun h => (not_le.2 hz) (by simpa using hR h)]; exact hbd z
      exact ⟨p, hp, fun s hs => (hHe s (by simpa [IsRoot, hℓ] using hs)).symm.trans (hp' s)⟩
    obtain ⟨P, hP⟩ := polylines g _ hδ' hline
    have hG : ∀ y, eval y δ ≠ 0 → (MvPolynomial.finSuccEquiv ℂ d P).map
        (eval y) = (((F.map (eval y)).roots.filter
          (fun t => (y, t) ∈ u)).map (fun t => X - C t)).prod := fun y hy => Polynomial.funext fun x => by
      rw [← MvPolynomial.eval_eq_eval_mv_eval', ← hP _ (by rwa [hevδ, Fin.tail_cons])]
      simp [g, eval_multiset_prod, Multiset.map_map]
    refine ⟨_, fun hunit => ?_, hG⟩
    obtain ⟨c, hc, hcP⟩ := Polynomial.isUnit_iff.1 hunit
    have := congrArg (Polynomial.eval p.2) (hG p.1 hpZ.1)
    have hmem : p.2 ∈ (F.map (eval p.1)).roots.filter (fun t => (p.1, t) ∈ u) :=
      Multiset.mem_filter.2 ⟨(mem_roots (hF.map _).ne_zero).2 hpZ.2, hpu⟩
    rw [← hcP, Polynomial.map_C, eval_C, eval_multiset_prod, Multiset.prod_eq_zero
      (Multiset.mem_map.2 ⟨_, mem_map_of_mem _ hmem, by simp⟩)] at this
    exact (hc.map (MvPolynomial.eval p.1)).ne_zero this
  intro u v hu hv hZ hpu hqv
  by_contra hne
  have hdisj : ∀ p ∈ Z, p ∈ u → p ∉ v := fun p hp h1 h2 => hne ⟨p, hp, h1, h2⟩
  obtain ⟨G, hGu, hG⟩ := hmain u v hu hv hZ hdisj hpu
  obtain ⟨H, hHu, hH⟩ := hmain v u hv hu (by rwa [Set.union_comm])
    (fun p hp h1 h2 => hdisj p hp h2 h1) hqv
  refine (hirr.isUnit_or_isUnit (sub_eq_zero.1 (hvan _ fun y hy => ?_)).symm).elim hGu hHu
  rw [Polynomial.map_sub, Polynomial.map_mul, hG y hy, hH y hy, ← Multiset.prod_add,
    ← Multiset.map_add, sub_eq_zero]
  conv_rhs => rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hF.map _)]
  congr 2
  conv_rhs => rw [← Multiset.filter_add_not (fun t => (y, t) ∈ u) (F.map (eval y)).roots]
  congr 1
  refine Multiset.filter_congr fun t ht => ?_
  have htZ : (y, t) ∈ Z := ⟨hy, (mem_roots (hF.map _).ne_zero).1 ht⟩
  exact ⟨fun h1 h2 => hdisj _ htZ h2 h1, fun h => (hZ htZ).resolve_left h⟩

theorem dens {σ : Type} [Fintype σ] {s : ℕ} (X : Set (σ → ℂ)) (hX : IsClosed X)
    (π : (σ → ℂ) → (Fin s → ℂ)) (hπ : Continuous π)
    (H : ∀ q : MvPolynomial σ ℂ, ∃ M : Polynomial (𝓡), M.Monic ∧
      (∀ x ∈ X, (M.map (eval (π x))).eval (eval x q) = 0) ∧
      (∀ y t, (M.map (eval y)).eval t = 0 →
        ∃ x ∈ X, π x = y ∧ eval x q = t))
    (δ : 𝓡) (hδ : δ ≠ 0) :
    X ⊆ closure {x ∈ X | eval (π x) δ ≠ 0} := by
  intro x₀ hx₀
  choose M hMm hM1 hM2 using H
  obtain ⟨q, hq⟩ : ∃ q : MvPolynomial σ ℂ, ∀ x ∈ X, π x = π x₀ →
      eval x q = eval x₀ q → x = x₀ := by
    refine ⟨∏ j, ∏ v ∈ ((M (𝕏 j)).map (eval (π x₀))).roots.toFinset.erase
      (x₀ j), (𝕏 j - ℭ v), fun x hx hxy he => ?_⟩
    by_contra hne
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    simp only [map_prod, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at he
    refine prod_ne_zero_iff.2 (fun j _ => prod_ne_zero_iff.2 fun v hv =>
      sub_ne_zero.2 (Finset.ne_of_mem_erase hv).symm) (he ▸ prod_eq_zero (mem_univ j)
        (prod_eq_zero (Finset.mem_erase.2 ⟨hj, ?_⟩) (sub_self _)))
    have := hM1 (𝕏 j) x hx
    rw [hxy, MvPolynomial.eval_X] at this
    exact mem_toFinset.2 ((mem_roots ((hMm _).map _).ne_zero).2 this)
  set t₀ := eval x₀ q
  have ht₀ : ((M q).map (eval (π x₀))).eval t₀ = 0 := hM1 q x₀ hx₀
  have hseq : ∀ n : ℕ, ∃ x ∈ X, eval (π x) δ ≠ 0 ∧
      dist (π x) (π x₀) < 1 / (n + 1) ∧ dist (eval x q) t₀ < 1 / (n + 1) := by
    intro n
    have hε : (0:ℝ) < 1 / (n + 1) := by positivity
    have hroot := ex_root (l := 𝓝 (π x₀)) (Q := fun y => (M q).map (eval y))
      (k := (M q).natDegree) (fun y => ⟨(hMm q).map _, (hMm q).natDegree_map _⟩)
      (by simpa [hev, ← ht₀] using ((continuous_eval _).tendsto (π x₀)))
      (ball_mem_nhds t₀ hε)
    obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 (hroot.and (ball_mem_nhds (π x₀) hε))
    obtain ⟨y, hyη, hyB⟩ : ∃ y ∈ ball (π x₀) η, eval y δ ≠ 0 := by
      by_contra! h
      exact hδ (MvPolynomial.funext_set (fun j => ball (π x₀ j) η)
        (fun j => infinite_of_mem_nhds _ (ball_mem_nhds _ hη)) fun y hy => by
          simpa using h y (by rwa [ball_pi _ hη]))
    obtain ⟨⟨t, ht, ht0⟩, hy'⟩ := hball hyη
    obtain ⟨x, hx, hxy, hxt⟩ := hM2 q y t ht0
    exact ⟨x, hx, hxy ▸ hyB, hxy ▸ hy', hxt ▸ ht⟩
  choose xs hxsX hxsB hxsy hxst using hseq
  have h1n : Tendsto (fun n : ℕ => (1:ℝ) / (n + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hy : Tendsto (fun n => π (xs n)) atTop (𝓝 (π x₀)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => (hxsy n).le) h1n)
  have ht : Tendsto (fun n => eval (xs n) q) atTop (𝓝 t₀) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => (hxst n).le) h1n)
  choose B hB using fun j => ((((continuous_finsetSum _ fun i _ =>
    (continuous_eval ((M (𝕏 j)).coeff i)).norm).add continuous_const).tendsto _).comp
      hy).bddAbove_range
  have hbdd : Bornology.IsBounded (Set.range xs) := by
    refine isBounded_iff_forall_norm_le.2 ⟨∑ j, |B j|, ?_⟩
    rintro _ ⟨n, rfl⟩
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    have hc := cauchy ((hMm (𝕏 j)).map (eval (π (xs n))))
      (by simpa using hM1 (𝕏 j) (xs n) (hxsX n))
    rw [(hMm _).natDegree_map] at hc
    simp only [coeff_map] at hc
    exact hc.trans ((hB j ⟨n, rfl⟩).trans ((le_abs_self _).trans
      (single_le_sum (fun j _ => abs_nonneg (B j)) (mem_univ j))))
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd (fun n => Set.mem_range_self n)
  have haX : a ∈ X := hX.mem_of_tendsto hlim (Eventually.of_forall fun n => hxsX _)
  have hpa : π a = π x₀ :=
    tendsto_nhds_unique ((hπ.tendsto a).comp hlim) (hy.comp hφ.tendsto_atTop)
  have hqa : eval a q = t₀ :=
    tendsto_nhds_unique (((continuous_eval q).tendsto a).comp hlim)
      (ht.comp hφ.tendsto_atTop)
  rw [← hq a haX hpa hqa]
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ⟨hxsX _, hxsB _⟩)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem irreducibleBasicOpenConnected :
    ∀ (σ : Type) [Fintype σ] (W : Ideal (MvPolynomial σ ℂ)) (g : MvPolynomial σ ℂ),
      W.IsPrime → g ∉ W →
      IsPreconnected (MvPolynomial.zeroLocus ℂ W \ {x : σ → ℂ | eval x g = 0}) := by
  intro σ _ W g hW hg
  set X := MvPolynomial.zeroLocus ℂ W
  have hXm : ∀ x, x ∈ X ↔ ∀ w ∈ W, eval x w = 0 := fun x => by
    simp [X, MvPolynomial.mem_zeroLocus_iff]
  have hXW : ∀ x ∈ X, ∀ b b' : MvPolynomial σ ℂ, mk W b = mk W b' →
      eval x b = eval x b' := fun x hx b b' h => by
    rw [← sub_eq_zero, ← map_sub]
    exact (hXm x).1 hx _ (Ideal.Quotient.eq.1 h)
  obtain ⟨s, φ, hφi, hφint⟩ := exists_integral_inj_algHom_of_fg ℂ (𝓐)
  letI : Algebra (𝓡) (𝓐) := φ.toRingHom.toAlgebra
  have hφa : ∀ r, algebraMap (𝓡) (𝓐) r = φ r := fun _ => rfl
  haveI : Algebra.IsIntegral (𝓡) (𝓐) := ⟨hφint⟩
  haveI : Module.IsTorsionFree (𝓡) (𝓐) :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := 𝓡)
      (A := 𝓐)).2 hφi
  choose p hp using fun i : Fin s => mk_surjective (I := W) (φ (𝕏 i))
  set π : (σ → ℂ) → (Fin s → ℂ) := fun x i => eval x (p i)
  have hπ : Continuous π := continuous_pi fun i => continuous_eval _
  set Φ : 𝓡 →ₐ[ℂ] MvPolynomial σ ℂ := MvPolynomial.aeval p
  have hΦ : (mk W).comp Φ.toRingHom = φ.toRingHom :=
    MvPolynomial.ringHom_ext (fun c => by simp [Φ]; rfl) (fun i => by simp [Φ, hp])
  have hΦev : ∀ x, (MvPolynomial.eval x).comp Φ.toRingHom = MvPolynomial.eval (π x) :=
    fun x => MvPolynomial.ringHom_ext (fun c => by simp [Φ]) (fun i => by simp [Φ, π])
  -- evaluation of polynomial relations at points of X
  have hkey : ∀ x ∈ X, ∀ (b q : MvPolynomial σ ℂ) (P : Polynomial (𝓡)),
      mk W b = aeval (mk W q) P →
      eval x b = (P.map (eval (π x))).eval (eval x q) := by
    intro x hx b q P h
    rw [hXW x hx b (P.eval₂ Φ.toRingHom q) (by rw [h, hom_eval₂, hΦ]; rfl),
      hom_eval₂, hΦev, eval_map]
  -- contraction
  have hund : ∀ b : 𝓐, b ≠ 0 → ∃ r : 𝓡, r ≠ 0 ∧ ∃ c, c * b = φ r := fun b hb => by
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Ideal.IsIntegral.under_ne_bot (𝓡) (I := Ideal.span {b}) (by simpa using hb))
    exact ⟨r, hr0, Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hr)⟩
  have hContr : ∀ b : MvPolynomial σ ℂ, b ∉ W → ∃ r : 𝓡, r ≠ 0 ∧
      ∀ x ∈ X, eval x b = 0 → eval (π x) r = 0 := by
    intro b hb
    obtain ⟨r, hr0, c, hc⟩ := hund _ fun h => hb (eq_zero_iff_mem.1 h)
    obtain ⟨c', rfl⟩ := mk_surjective c
    refine ⟨r, hr0, fun x hx hbx => ?_⟩
    have := hXW x hx (c' * b) (Φ r) (by rw [map_mul, hc]; exact (RingHom.congr_fun hΦ r).symm)
    rw [map_mul, hbx, mul_zero] at this
    rw [← hΦev x]; exact this.symm
  -- primitive element
  have hPE : ∃ f : MvPolynomial σ ℂ, ∀ j : σ, ∃ D : 𝓡, D ≠ 0 ∧
      ∃ Qj : Polynomial (𝓡),
        φ D * mk W (𝕏 j) = aeval (mk W f) Qj := by
    let K := FractionRing (𝓐)
    let L := FractionRing (𝓡)
    have hinj : Function.Injective ((algebraMap (𝓐) K).comp φ.toRingHom) :=
      (IsFractionRing.injective (𝓐) K).comp hφi
    letI : Algebra L K := (IsFractionRing.lift hinj).toAlgebra
    have hRK : ∀ r, algebraMap L K (algebraMap (𝓡) L r) =
        algebraMap (𝓐) K (φ r) := fun r => IsFractionRing.lift_algebraMap hinj r
    have htr : ∀ (Q : Polynomial (𝓡)) (a : 𝓐),
        algebraMap _ K (aeval a Q) =
          aeval (algebraMap _ K a) (Q.map (algebraMap _ L)) := by
      intro Q a
      rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
      congr 1
      exact RingHom.ext fun r => (hRK r).symm
    have hint : ∀ j : σ, IsIntegral L (algebraMap _ K (mk W (𝕏 j))) :=
      fun j => by
        obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := 𝓡)
          (mk W (𝕏 j))
        refine ⟨P.map (algebraMap _ L), hPm.map _, ?_⟩
        have := htr P (mk W (𝕏 j))
        rw [aeval_def, hP, map_zero, aeval_def] at this
        exact this.symm
    set S : Set K := Set.range fun j : σ => algebraMap _ K (mk W (𝕏 j))
    haveI := IntermediateField.finiteDimensional_adjoin (K := L) (S := S)
      (by rintro _ ⟨j, rfl⟩; exact hint j)
    obtain ⟨⟨α, hαS⟩, hα⟩ := Field.exists_primitive_element L (adjoin L S)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓐) α
    obtain ⟨r, hr0, b', hb'⟩ := hund b (nonZeroDivisors.ne_zero hb)
    obtain ⟨f, hf⟩ := mk_surjective (a * b')
    refine ⟨f, fun j => ?_⟩
    obtain ⟨qj, hqj⟩ : (⟨_, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩ : adjoin L S) ∈
        (aeval (R := L) (⟨_, hαS⟩ : adjoin L S)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ← IntermediateField.adjoin_toSubalgebra, hα]
      trivial
    have e := congrArg Subtype.val hqj
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← IntermediateField.aeval_coe] at e
    have hb'K : algebraMap (𝓐) K b' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ K)).2
      (left_ne_zero_of_mul (by rw [hb']; exact (map_ne_zero_iff _ hφi).2 hr0 : b' * b ≠ 0))
    have hα' : algebraMap _ K a / algebraMap _ K b =
        algebraMap L K (algebraMap _ L r)⁻¹ * algebraMap _ K (mk W f) := by
      rw [map_inv₀, hRK, ← hb', hf, map_mul, map_mul, ← div_eq_inv_mul,
        mul_comm (algebraMap _ K a), mul_div_mul_left _ _ hb'K]
    obtain ⟨D, hDm, hD'⟩ := IsLocalization.integerNormalization_spec
      (nonZeroDivisors (𝓡)) (qj.comp (C (algebraMap _ L r)⁻¹ * Polynomial.X))
    refine ⟨D, nonZeroDivisors.ne_zero hDm, IsLocalization.integerNormalization
      (nonZeroDivisors (𝓡)) (qj.comp (C (algebraMap _ L r)⁻¹ * Polynomial.X)), ?_⟩
    apply IsFractionRing.injective (𝓐) K
    rw [htr, hD', ← algebraMap_smul L D, smul_eq_C_mul, map_mul, map_mul, aeval_C, hRK, aeval_comp]
    simp only [map_mul, aeval_C, aeval_X, ← hα', e]
  obtain ⟨f, hf⟩ := hPE
  choose D hD0 Qj hQj using hf
  have hfint : IsIntegral (𝓡) (mk W f) :=
    Algebra.IsIntegral.isIntegral _
  set F := minpoly (𝓡) (mk W f)
  have hH : ∀ q : MvPolynomial σ ℂ, (minpoly (𝓡) (mk W q)).Monic ∧
      (∀ x ∈ X, ((minpoly (𝓡) (mk W q)).map
        (eval (π x))).eval (eval x q) = 0) ∧
      (∀ y t, ((minpoly (𝓡) (mk W q)).map
        (eval y)).eval t = 0 → ∃ x ∈ X, π x = y ∧ eval x q = t) := by
    intro q
    have hq : IsIntegral (𝓡) (mk W q) := Algebra.IsIntegral.isIntegral _
    refine ⟨minpoly.monic hq, fun x hx => ?_, fun y t ht => ?_⟩
    · rw [← hkey x hx 0 q _ (by rw [map_zero, minpoly.aeval]), map_zero]
    · set a := mk W q
      set f : Polynomial (𝓡) →+* 𝓐 := (aeval a).toRingHom
      have hf : f.IsIntegral := RingHom.IsIntegral.tower_top
        (C : 𝓡 →+* Polynomial (𝓡)) f (by
          have : f.comp C = φ.toRingHom := RingHom.ext fun r => by simp [f, hφa]
          rw [this]; exact hφint)
      set ev : Polynomial (𝓡) →+* ℂ :=
        (evalRingHom t).comp (mapRingHom (eval y))
      have hI : (RingHom.ker ev).map f ≠ ⊤ := fun h =>
        (RingHom.ker_isMaximal_of_surjective ev fun c =>
          ⟨C (ℭ c : 𝓡), by simp [ev]⟩).ne_top
          ((Ideal.map_eq_top_iff_of_ker_le f (fun P hP => by
            obtain ⟨c, rfl⟩ := minpoly.isIntegrallyClosed_dvd hq hP
            rw [RingHom.mem_ker, map_mul]; exact mul_eq_zero_of_left ht _) hf).1 h)
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ (Ideal.comap_ne_top (mk W) hI)
      obtain ⟨x, hx⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
      have hmem : ∀ (b : MvPolynomial σ ℂ) (P : Polynomial (𝓡)),
          mk W b = aeval a P → ev P = 0 → eval x b = 0 := by
        intro b P hb hP
        have h2 : b ∈ M := hJM (by
          rw [Ideal.mem_comap, hb]; exact Ideal.mem_map_of_mem f hP)
        rw [hx] at h2
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x b).1 h2
      refine ⟨x, (hXm x).2 fun w hw => hmem w 0 (by simp [eq_zero_iff_mem.2 hw])
        (by simp), funext fun i => ?_, ?_⟩
      · have := hmem (p i - ℭ (y i)) (C (𝕏 i - ℭ (y i)))
          (by simp [hp, hφa]; rfl) (by simp [ev])
        rwa [map_sub, MvPolynomial.eval_C, sub_eq_zero] at this
      · have := hmem (q - ℭ t) (Polynomial.X - Polynomial.C (ℭ t))
          (by simp [a, hφa]; rfl) (by simp [ev])
        rwa [map_sub, MvPolynomial.eval_C, sub_eq_zero] at this
  obtain ⟨rg, hrg0, hrg⟩ := hContr g hg
  -- the derivative of F does not vanish at f
  have hF' : aeval (mk W f) (derivative F) ≠ 0 := fun h =>
    (minpoly.natDegree_pos hfint).ne' (natDegree_eq_zero_of_derivative_eq_zero
      (eq_zero_of_dvd_of_natDegree_lt (minpoly.isIntegrallyClosed_dvd hfint h)
        (natDegree_derivative_lt (minpoly.natDegree_pos hfint).ne')))
  obtain ⟨b1, hb1⟩ := mk_surjective (aeval (mk W f) (derivative F))
  obtain ⟨r1, hr10, hr1⟩ := hContr b1 (fun h => hF' (by rw [← hb1]; exact eq_zero_iff_mem.2 h))
  set δ := rg * r1 * ∏ j, D j
  have hδ : δ ≠ 0 := mul_ne_zero (mul_ne_zero hrg0 hr10) (prod_ne_zero_iff.2 fun j _ => hD0 j)
  have hδD : ∀ y, eval y δ ≠ 0 → ∀ j, eval y (D j) ≠ 0 := fun y hy j h =>
    hy (by simp only [δ, map_mul, map_prod]; rw [prod_eq_zero (mem_univ j) h, mul_zero])
  -- parametrization of points over good base points
  have hpar : ∀ x ∈ X, eval (π x) δ ≠ 0 → ∀ j,
      x j = ((Qj j).map (eval (π x))).eval (eval x f) /
        eval (π x) (D j) := fun x hx hδx j => by
    rw [eq_div_iff (hδD _ hδx j), ← hkey x hx (Φ (D j) * 𝕏 j) f _
      (by rw [map_mul, ← hQj j]; congr 1; exact RingHom.congr_fun hΦ (D j)), map_mul,
      MvPolynomial.eval_X, mul_comm]
    exact congrArg (· * x j) (RingHom.congr_fun (hΦev x) (D j)).symm
  have hZ := hyp (minpoly.monic hfint) (minpoly.irreducible hfint) hδ fun y hy =>
    (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ _ _).2 fun t => or_iff_not_imp_left.2 fun ht h => by
      obtain ⟨x, hx, rfl, rfl⟩ := (hH f).2.2 y t (by simpa using ht)
      have := hr1 x hx (by rw [hkey x hx b1 f _ hb1, ← derivative_map]; simpa using h)
      exact hy (by simp only [δ, map_mul, this, mul_zero, zero_mul])
  set Ψ : (Fin s → ℂ) × ℂ → (σ → ℂ) := fun q j =>
    ((Qj j).map (eval q.1)).eval q.2 / eval q.1 (D j)
  have hΨ : ContinuousOn Ψ {q : (Fin s → ℂ) × ℂ | eval q.1 δ ≠ 0 ∧
      (F.map (eval q.1)).eval q.2 = 0} := by
    refine continuousOn_pi.2 fun j => ContinuousOn.div ?_ ?_ fun q hq => hδD _ hq.1 j
    · simp only [eval_map, eval₂_eq_sum_range]
      exact (continuous_finsetSum _ fun i _ => ((continuous_eval _).comp
        continuous_fst).mul (continuous_snd.pow i)).continuousOn
    · exact ((continuous_eval _).comp continuous_fst).continuousOn
  have hXc : IsClosed X := isClosed_of_closure_subset fun x hx => (hXm x).2 fun w hw =>
    (isClosed_eq (continuous_eval w) continuous_const).closure_subset_iff.2
      (fun y hy => (hXm y).1 hy w hw) hx
  refine (hZ.image Ψ hΨ).subset_closure ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨x, hx, hxy, hxt⟩ := (hH f).2.2 q.1 q.2 hq.2
    have : Ψ q = x := funext fun j => by
      rw [hpar x hx (by rw [hxy]; exact hq.1) j, hxy, hxt]
    rw [this]
    exact ⟨hx, fun hgx => hq.1 (by rw [← hxy]; simp only [δ, map_mul, hrg x hx hgx, zero_mul])⟩
  · intro x hx
    refine closure_mono ?_ (dens X hXc π hπ (fun q => ⟨_, hH q⟩) δ hδ hx.1)
    rintro x ⟨hx, hδx⟩
    exact ⟨(π x, eval x f), ⟨hδx, (hH f).2.1 x hx⟩, funext fun j => (hpar x hx hδx j).symm⟩

end AlpogeRHCore7
