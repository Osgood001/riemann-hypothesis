import B4

noncomputable section

open MeasureTheory Matrix Finset Filter Function Subgroup MulAction QuotientGroup Topology Metric
open Set hiding center
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

-- === Shared helpers for B5 ===

lemma no_eig_of_ell {F I : Type} [Field F] (σ : I → F →+* ℝ) (v : I) (γ : GL2 F)
    (h : σ v γ.val.trace ^ 2 < 4 * σ v γ.val.det) {s : Fin 2 → F} (hs : s ≠ 0) (c : F) : s ᵥ* γ.val ≠ c • s := fun heq => by
  set M := γ.val
  have h0 : s 0 * M 0 0 + s 1 * M 1 0 = c * s 0 := by simpa [vecMul, dotProduct, Fin.sum_univ_two] using congrFun heq 0
  have h1 : s 0 * M 0 1 + s 1 * M 1 1 = c * s 1 := by simpa [vecMul, dotProduct, Fin.sum_univ_two] using congrFun heq 1
  have hp : c ^ 2 - (M 0 0 + M 1 1) * c + (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0 := by
    by_cases hs0 : s 0 = 0
    · have hs1 : s 1 ≠ 0 := fun h1' => hs (funext fun i => by fin_cases i <;> simp [hs0, h1'])
      exact (mul_eq_zero.1 (show s 1 * (c ^ 2 - (M 0 0 + M 1 1) * c + (M 0 0 * M 1 1 - M 0 1 * M 1 0)) = 0 by
        linear_combination (M 0 0 - c) * h1 - M 0 1 * h0)).resolve_left hs1
    · exact (mul_eq_zero.1 (show s 0 * (c ^ 2 - (M 0 0 + M 1 1) * c + (M 0 0 * M 1 1 - M 0 1 * M 1 0)) = 0 by
        linear_combination (M 1 1 - c) * h0 - M 1 0 * h1)).resolve_left hs0
  have hσ := congrArg (σ v) hp; rw [trace_fin_two, det_fin_two] at h; simp at hσ h
  nlinarith [sq_nonneg (2 * σ v c - (σ v (M 0 0) + σ v (M 1 1)))]

lemma isEll_conj {F : Type} [Field F] (δ γ : PG F) : IsEll (δ * γ * δ⁻¹) ↔ IsEll γ := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ; obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  simp only [IsEll, fix_conj, fix_mk]
  exact ⟨fun h s hs ⟨c, hc⟩ => h (s ᵥ* (d⁻¹ : GL2 F).val) (vecMul_ne hs d⁻¹) ⟨c, by simpa [vecMul_vecMul] using hc⟩,
    fun h s hs ⟨c, hc⟩ => h (s ᵥ* d.val) (vecMul_ne hs d) ⟨c, hc⟩⟩

lemma orbit_reps {G α : Type} [Group G] [MulAction G α] :
    ∃ f : α → α, (∀ p, f p ∈ orbit G p) ∧ (∀ p q, q ∈ orbit G p → f q = f p) ∧
      ∀ ω, ∃! r, r ∈ range f ∧ r ∈ orbit G ω := by
  let f (p : α) := Quotient.out (Quotient.mk (orbitRel G α) p)
  have hf1 p : f p ∈ orbit G p := orbitRel_apply.1 (Quotient.mk_out p)
  have hf2 p q (h : q ∈ orbit G p) : f q = f p := congrArg Quotient.out (Quotient.sound (orbitRel_apply.2 h))
  exact ⟨f, hf1, hf2, fun ω => ⟨f ω, ⟨⟨ω, rfl⟩, hf1 ω⟩, by rintro r ⟨⟨p, rfl⟩, hr⟩; rw [← hf2 ω (f p) hr, hf2 p (f p) (hf1 p)]⟩⟩

-- === F4: Imaginary part bound (finiteness of totally elliptic conjugacy classes) ===

theorem imaginary_part_bound_proof : B1b → B1c → E0d → Mult → F4 := by
  intro _ _ _ _ F I Gf _ _ _ D hD a
  have : Nontrivial I := hD.two
  obtain ⟨c0, hc0, hmink⟩ := hD.mink; obtain ⟨S0, C, c, hc, hnorm⟩ := hD.normal c0 hc0
  obtain ⟨Cm, hCm⟩ := hD.mul a⁻¹
  let W : Set D.Om := (fun x : Gf => ((x : Gf ⧸ D.H) : D.Om)) '' (S0 : Set Gf)
  let T (ω : D.Om) : Set D.Om := {ω3 | ∃ h ∈ D.H, ω3 = ((D.rep ω * h * a : Gf) : Gf ⧸ D.H)}
  let Good (q : (D.Cj × D.Om) × D.Xs) : Prop :=
    D.el q.1.1 • q.2 = q.2 ∧ Sg C c q.2 ∧ q.1.2 ∈ W ∧ D.HtY ![0, 1] (q.1.2, q.2) ^ 2 ≤ Cm ∧ D.el q.1.1 • q.1.2 ∈ T q.1.2
  let key (q : (D.Cj × D.Om) × D.Xs) : D.Om × D.Om × (I → Bool) := (q.1.2, D.el q.1.1 • q.1.2, fun v => decide (0 < (q.2 v).1.im))
  have hfiber (k : D.Om × D.Om × (I → Bool)) : (Prod.fst '' {q | Good q ∧ key q = k}).Finite := by
    rcases Set.eq_empty_or_nonempty {q | Good q ∧ key q = k} with h0 | ⟨q0, hq0⟩
    · rw [h0, image_empty]; exact finite_empty
    have ⟨⟨hfix0, hsg0, _, _, _⟩, hk0⟩ := hq0
    have hhf : 0 < D.hf ![0, 1] (D.rep q0.1.2) := hD.pos _ e01_ne _
    set B : ℝ := max 1 Cm / D.hf ![0, 1] (D.rep q0.1.2); set U : ℝ := C * max 1 B
    have hbox q (hq : q ∈ {q | Good q ∧ key q = k}) : q.1.2 = q0.1.2 ∧ D.el q.1.1 • q.1.2 = D.el q0.1.1 • q0.1.2 ∧
        ∀ v, (|(q.2 v).1.re| ≤ C ∧ c ≤ |(q.2 v).1.im| ∧ |(q.2 v).1.im| ≤ U) ∧ 0 < (q0.2 v).1.im * (q.2 v).1.im := by
      obtain ⟨⟨-, hsg, -, hht, -⟩, hk⟩ := hq
      have hkk := hk.trans hk0.symm; simp only [key, Prod.mk.injEq] at hkk; obtain ⟨e1, e2, e3⟩ := hkk
      refine ⟨e1, e2, fun v => ⟨⟨(hsg v).1, (hsg v).2.1, ?_⟩, ?_⟩⟩
      · have hP : (∏ u, |(q.2 u).1.im|) ≤ B := by
          rw [show D.HtY ![0, 1] (q.1.2, q.2) = (∏ u, |(q.2 u).1.im|) * D.hf ![0, 1] (D.rep q.1.2) by simp [Dat.HtY, Dat.Ht], e1] at hht
          exact (le_div_iff₀ hhf).2 (by by_cases h1 : (∏ u, |(q.2 u).1.im|) * D.hf ![0, 1] (D.rep q0.1.2) ≤ 1; exact le_max_of_le_left h1; exact le_max_of_le_right (by nlinarith))
        obtain ⟨v0, hv0⟩ := Finite.exists_min fun u => |(q.2 u).1.im|
        have hC0 : 0 ≤ C := (abs_nonneg _).trans (hsg v).1
        have hm : |(q.2 v0).1.im| ≤ max 1 B := by
          by_cases hle : |(q.2 v0).1.im| ≤ 1
          · exact hle.trans (le_max_left _ _)
          · push Not at hle
            have hP' : |(q.2 v0).1.im| ^ Fintype.card I ≤ ∏ u, |(q.2 u).1.im| :=
              (Finset.prod_const _).symm.trans_le (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun u _ => hv0 u)
            exact le_max_of_le_right ((le_self_pow₀ hle.le Fintype.card_ne_zero).trans (hP'.trans hP))
        exact (hsg v).2.2 v0 |>.trans (mul_le_mul_of_nonneg_left hm hC0)
      · have hde := congrFun e3 v
        rcases lt_or_gt_of_ne (q0.2 v).2 with hx | hx <;> rcases lt_or_gt_of_ne (q.2 v).2 with hy | hy
        · exact mul_pos_of_neg_of_neg hx hy
        · simp [not_lt.2 hx.le, hy] at hde
        · simp [hx, not_lt.2 hy.le] at hde
        · exact mul_pos hx hy
    obtain ⟨v0⟩ := (inferInstance : Nonempty I)
    have hU : 0 < U := by have := ((hbox q0 hq0).2.2 v0).1; linarith [this.2.1, this.2.2]
    set δ0 : ℝ := c ^ 2 / (C ^ 2 + U ^ 2); have hδ0 : 0 < δ0 := by positivity
    obtain ⟨C', hC'⟩ := hD.count q0.1.2 (δ0 ^ 2 / 4) C c (by positivity) hc
    refine ((hC' q0.2 hsg0).1.image (fun g : PG F => ((D.el q0.1.1 * g : PG F), q0.1.2) : PG F → D.Cj × D.Om)).subset ?_
    rintro _ ⟨q, hq, rfl⟩; obtain ⟨e1, e2, hv⟩ := hbox q hq; obtain ⟨⟨hfix, -⟩, -⟩ := hq
    refine ⟨(D.el q0.1.1)⁻¹ * D.el q.1.1, ⟨by conv_lhs => rw [mul_smul, ← e1, e2, inv_smul_smul], fun v => ?_⟩,
      by show ((D.el q0.1.1 * ((D.el q0.1.1)⁻¹ * D.el q.1.1) : PG F), q0.1.2) = q.1; rw [mul_inv_cancel_left, ← e1]; rfl⟩
    have hklb : δ0 ≤ kap (q0.2 v) (q.2 v) := by
      obtain ⟨⟨hzr, hzi1, hzi2⟩, _⟩ := (hbox q0 hq0).2.2 v; obtain ⟨⟨hwr, hwi1, hwi2⟩, hzw⟩ := hv v
      rw [kap, ite_eq_left hzw, nsq_sub_conj]
      have hp : c ^ 2 ≤ (q0.2 v).1.im * (q.2 v).1.im := by rw [← abs_of_pos hzw, abs_mul]; nlinarith [mul_le_mul hzi1 hwi1 hc.le (abs_nonneg _)]
      have hzr' := abs_le.1 hzr; have hwr' := abs_le.1 hwr
      have hre : ((q0.2 v).1.re - (q.2 v).1.re) ^ 2 ≤ 4 * C ^ 2 := by nlinarith [mul_nonneg (show 0 ≤ 2 * C - ((q0.2 v).1.re - (q.2 v).1.re) by linarith) (show 0 ≤ 2 * C + ((q0.2 v).1.re - (q.2 v).1.re) by linarith)]
      have him2 : ((q0.2 v).1.im + (q.2 v).1.im) ^ 2 ≤ 4 * U ^ 2 := by
        nlinarith [sq_abs (q0.2 v).1.im, sq_abs (q.2 v).1.im, mul_le_mul hzi2 hzi2 (abs_nonneg _) hU.le,
          mul_le_mul hwi2 hwi2 (abs_nonneg _) hU.le, mul_le_mul hzi2 hwi2 (abs_nonneg _) hU.le]
      rw [div_le_div_iff₀ (by positivity) (by nlinarith [sq_nonneg ((q0.2 v).1.re - (q.2 v).1.re), sq_nonneg (q0.2 v).1.im, sq_nonneg (q.2 v).1.im])]
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hre him2) (sq_nonneg c), mul_le_mul_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ C ^ 2 + U ^ 2)]
    have k1 : kap (q0.2 v) ((((D.el q0.1.1)⁻¹ * D.el q.1.1) • q0.2 : D.Xs) v) = kap (q0.2 v) ((D.el q.1.1 • q0.2 : D.Xs) v) := by
      have := kap_smulX D (D.el q0.1.1) q0.2 (((D.el q0.1.1)⁻¹ * D.el q.1.1) • q0.2) v
      rw [hfix0, ← mul_smul, mul_inv_cancel_left] at this; exact this.symm
    have k2 : kap (q.2 v) ((D.el q.1.1 • q0.2 : D.Xs) v) = kap (q0.2 v) (q.2 v) := by
      have := kap_smulX D (D.el q.1.1) q.2 q0.2 v; rw [hfix] at this; exact this.trans (kap_symm _ _)
    show δ0 ^ 2 / 4 ≤ kap (q0.2 v) ((((D.el q0.1.1)⁻¹ * D.el q.1.1) • q0.2 : D.Xs) v)
    rw [k1]; nlinarith [kap_tri (q0.2 v) (q.2 v) ((D.el q.1.1 • q0.2 : D.Xs) v), k2, mul_le_mul hklb hklb hδ0.le (hδ0.le.trans hklb)]
  have hTf ω : (T ω).Finite := ((hD.dbl a).image fun x : Gf ⧸ D.H => (D.rep ω : Gf) • x).subset $ by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨((h * a : Gf) : Gf ⧸ D.H), ⟨h, hh, rfl⟩, by change ((D.rep ω * (h * a) : Gf) : Gf ⧸ D.H) = _; rw [mul_assoc]⟩
  have hW : W.Finite := S0.finite_toSet.image _
  refine ⟨Prod.fst '' {q | Good q}, ((hW.prod ((hW.biUnion fun ω _ => hTf ω).prod finite_univ)).biUnion fun k _ => hfiber k).subset
    (by rintro _ ⟨q, hq, rfl⟩; exact mem_biUnion ⟨hq.2.2.1, mem_biUnion hq.2.2.1 hq.2.2.2.2, mem_univ _⟩ ⟨q, ⟨hq, rfl⟩, rfl⟩), fun γ ω hell hs => ?_⟩
  let z : D.Xs := fun v => ell_fp (D.r v γ.out) (by rw [r_tr, r_det]; exact hell v)
  have hz : γ • z = z := funext fun v => by rw [smulX_out]; exact ell_fix_comm (by rw [r_tr, r_det]; exact hell v) rfl
  obtain ⟨s, hs0, hsz⟩ := hmink z (D.rep ω); obtain ⟨g, hg⟩ := row_exists s hs0
  obtain ⟨b, -, ⟨x', hx', h, hh, hbx⟩, hsg⟩ := hnorm ((g : PG F) • z) (D.rep ((g : PG F) • ω)) (by
    change c0 ≤ D.HtY ![0, 1] ((g : PG F) • ((ω, z) : D.Y)); rw [htY_smul D hD _ e01_ne, hg]; exact hsz)
  set δ := b * g
  have hδω : (δ : PG F) • ω = ((x' : Gf ⧸ D.H) : D.Om) := by
    rw [show (δ : PG F) = (b : PG F) * (g : PG F) from rfl, mul_smul]
    have e2 := D.mk_smulO b (D.rep ((g : PG F) • ω)); rw [rep_spec] at e2; rw [e2, hbx]
    exact QuotientGroup.eq.2 (by simpa using inv_mem hh)
  have hfixδ : ((δ : PG F) * γ * (δ : PG F)⁻¹) • ((δ : PG F) • z) = (δ : PG F) • z := by rw [mul_smul, mul_smul, inv_smul_smul, hz]
  have hTmem : ((δ : PG F) * γ * (δ : PG F)⁻¹) • ((δ : PG F) • ω) ∈ T ((δ : PG F) • ω) := by
    have hω' : (δ : PG F) • ω = ((D.j δ * D.rep ω : Gf) : Gf ⧸ D.H) := by have := D.mk_smulO δ (D.rep ω); rwa [rep_spec] at this
    refine ⟨_, QuotientGroup.eq.1 ((rep_spec D _).trans hω'), ?_⟩
    rw [mul_smul, mul_smul, inv_smul_smul, hs, D.mk_smulO, mul_inv_cancel_left, mul_assoc]
  have h10 : ((δ : PG F) * γ * (δ : PG F)⁻¹).out 1 0 ≠ 0 := fun h0 => by
    obtain ⟨v⟩ := (inferInstance : Nonempty I)
    have hfix : Fix ![0, 1] ((δ : PG F) * ((γ.out : GL2 F) : PG F) * (δ : PG F)⁻¹) := by
      rw [QuotientGroup.out_eq']
      exact ⟨((δ : PG F) * γ * (δ : PG F)⁻¹).out 1 1, funext fun i => by fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two, h0]⟩
    obtain ⟨c', hc'⟩ := (fix_conj ![0, 1] γ.out δ).1 hfix
    exact no_eig_of_ell D.σ v γ.out (hell v) (vecMul_ne e01_ne δ) c' hc'
  have hht : D.HtY ![0, 1] ((δ : PG F) • ω, (δ : PG F) • z) ^ 2 ≤ Cm := by
    set γ' := (δ : PG F) * γ * (δ : PG F)⁻¹; set ω' := (δ : PG F) • ω; set z' := (δ : PG F) • z
    have hB := htY_smul D hD ![0, 1] e01_ne γ'.out (ω', z')
    rw [QuotientGroup.out_eq', show γ' • ((ω', z') : D.Y) = (γ' • ω', z') from Prod.ext rfl hfixδ] at hB
    have hprod := htY_prod D hD (![0, 1] ᵥ* γ'.out.val) ![0, 1] (by simpa [vecMul, dotProduct, Fin.sum_univ_two] using h10) (ω', z')
    rw [← hB] at hprod
    obtain ⟨h1, hh1, hω1⟩ := hTmem
    have hf1 : D.hf ![0, 1] (D.rep (γ' • ω')) = D.hf ![0, 1] (D.rep ω' * h1 * a) := by
      have hm : (D.rep ω' * h1 * a)⁻¹ * D.rep (γ' • ω') ∈ D.H := QuotientGroup.eq.1 (((rep_spec D (γ' • ω')).trans hω1).symm)
      have := hD.lev ![0, 1] e01_ne (D.rep ω' * h1 * a) _ hm; rwa [mul_inv_cancel_left] at this
    have hf2 : D.hf ![0, 1] (D.rep ω') ≤ Cm * D.hf ![0, 1] (D.rep ω' * h1 * a) := by
      have := hCm ![0, 1] e01_ne (D.rep ω' * h1 * a); rwa [mul_inv_cancel_right, hD.lev ![0, 1] e01_ne _ h1 hh1] at this
    have hpos1 := htY_pos D hD ![0, 1] e01_ne (ω', z'); have hpos2 := htY_pos D hD ![0, 1] e01_ne (γ' • ω', z')
    simp only [show ∀ u, D.HtY ![0, 1] (u, z') = (∏ v, |(z' v).1.im|) * D.hf ![0, 1] (D.rep u) from fun _ => by simp [Dat.HtY, Dat.Ht]] at hprod hpos1 hpos2 ⊢
    rw [hf1] at hprod hpos2
    have hP0 : 0 ≤ ∏ v, |(z' v).1.im| := Finset.prod_nonneg fun _ _ => abs_nonneg _
    have k1 : (∏ v, |(z' v).1.im|) * D.hf ![0, 1] (D.rep ω') ≤ Cm * ((∏ v, |(z' v).1.im|) * D.hf ![0, 1] (D.rep ω' * h1 * a)) := by
      nlinarith [mul_le_mul_of_nonneg_left hf2 hP0]
    have hCm0 : 0 ≤ Cm := by by_contra hn; nlinarith [mul_neg_of_neg_of_pos (not_le.1 hn) hpos2]
    nlinarith [mul_le_mul_of_nonneg_right k1 hpos1.le, mul_le_mul_of_nonneg_left hprod hCm0]
  refine ⟨(δ : PG F), (((δ : PG F) • ((γ, ω) : D.Cj × D.Om)), (δ : PG F) • z), ⟨hfixδ, ?_, ?_, hht, hTmem⟩, rfl⟩
  · change Sg C c ((δ : PG F) • z : D.Xs); rw [show (δ : PG F) = (b : PG F) * (g : PG F) from rfl, mul_smul, D.mk_smulX]; exact hsg
  · change (δ : PG F) • ω ∈ W; rw [hδω]; exact ⟨x', hx', rfl⟩

-- === Fell ===

theorem pf_Fell : C4 → E0a → KernelTermsInvariantBounded → E0d → E1 → E3 → Ecut → Fsum → F2 → F3 → F4 → Fell := by
  intro hC4 hE0a _ _ hE1 hE3 hEcut hFsum hF2 hF3 hF4 F I Gf _ _ _ D hD ι _ a
  have : Nonempty I := by have := hD.two; infer_instance
  obtain ⟨f, hf1, hf2, hR⟩ := orbit_reps (G := PG F) (α := D.Cj × D.Om)
  choose Sa hSa using fun i => hF4 F I Gf D hD (a i)
  let Sset : Set (D.Cj × D.Om) := {p | p ∈ range f ∧ D.TotEll (D.el p.1).out ∧ D.Te a (D.el p.1).out (D.rep p.2) ≠ 0 ∧ Finite (stabilizer (PG F) p)}
  have hSfin : Sset.Finite := (finite_iUnion fun i => (hSa i).1.image f).subset $ by
    rintro p ⟨⟨q, rfl⟩, htot, hte, _⟩
    obtain ⟨i, hi⟩ := kk_supp D a (D.el (f q).1) (f q).2 hte
    obtain ⟨δ, hδ⟩ := (hSa i).2 (D.el (f q).1) (f q).2 htot hi
    exact mem_iUnion.2 ⟨i, δ • f q, hδ, by rw [hf2 (f q) (δ • f q) (mem_orbit _ δ), hf2 q (f q) (hf1 q)]⟩
  refine ⟨hSfin.toFinset, fun p hp => by rw [Set.Finite.mem_toFinset] at hp; exact ⟨hp.2.1, hp.2.2.2⟩, fun k hk b hb => ?_⟩
  let u (γ : PG F) (y : D.Y) : ℂ := if IsEll γ then D.kk k a γ y else 0
  have hu_meas γ : Measurable (u γ) := by by_cases h : IsEll γ <;> simp [u, h, meas_kk D k a hk]
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink; obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hk c₀ hc₀
  have hbd y : ∑' γ, ‖u γ y‖ₑ ≤ (C : ℝ≥0∞) := by
    obtain ⟨s, hs, hsy⟩ := hmink y.2 (D.rep y.1)
    calc _ ≤ ∑' γ, {γ : PG F | ¬Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ :=
            ENNReal.tsum_le_tsum fun γ => by by_cases h : IsEll γ; simp [u, h, indicator_of_mem (show γ ∈ {γ | ¬Fix s γ} from h s hs)]; simp [u, h]
      _ = ∑' γ : {γ : PG F // ¬Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (_root_.tsum_subtype _ _).symm
      _ ≤ C := hC y s hs hsy
  have hfin : ∫⁻ y, oR (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY < ∞ :=
    ((lintegral_mono fun y => by gcongr; exact hbd y).trans_eq (lintegral_mul_const' _ _ ENNReal.coe_ne_top)).trans_lt
      (ENNReal.mul_lt_top (hE3 F I Gf D hD b hb) ENNReal.coe_lt_top)
  obtain ⟨hb', hFs⟩ := hFsum F I Gf D hD b hb; obtain ⟨hmeas', hint', hintY, heq⟩ := hFs u hu_meas hfin
  refine ⟨hintY, heq.trans ?_⟩
  obtain ⟨hcount, hsig, hpres, -⟩ := hE0a F I Gf D hD
  have : Countable (PG F) := hcount; have : Countable D.Cj := hcount; have : Countable D.Om := hD.cO
  have : SigmaFinite (volume : Measure D.Xs) := hsig; have : DiscreteMeasurableSpace (D.Cj × D.Om) := ⟨fun s => s.to_countable.measurableSet⟩
  choose β hβ using fun p : D.Cj × D.Om => (hEcut F I Gf D hD).2 p.2 (stabilizer (PG F) p) fun g hg => congrArg Prod.snd (mem_stabilizer_iff.1 hg)
  have hinv (g : PG F) (y : (D.Cj × D.Om) × D.Xs) : u (D.el (g • y).1.1) ((g • y).1.2, (g • y).2) = u (D.el y.1.1) (y.1.2, y.2) := by
    rcases y with ⟨⟨γ, ω⟩, z⟩; show u (g * D.el γ * g⁻¹) (g • ((ω, z) : D.Y)) = u (D.el γ) (ω, z)
    simp only [u, isEll_conj, kk_conj D k a hk]
  obtain ⟨hintR, hsum⟩ := hC4 (PG F) (D.Cj × D.Om) D.Xs volume hpres (fun p => b (p.1.2, p.2)) hb'
    (fun p => u (D.el p.1.1) (p.1.2, p.2)) hmeas' hinv hint' (range f) hR β fun r _ => hβ r
  let g' (r : D.Cj × D.Om) := ∫ x, β r x • u (D.el r.1) (r.2, x)
  let h' (p : D.Cj × D.Om) := (Nat.card (stabilizer (PG F) p) : ℂ)⁻¹ * (D.Te a (D.el p.1).out (D.rep p.2) * D.orb k (D.el p.1).out)
  have hind : (range f).indicator g' = Sset.indicator h' := funext fun ⟨γ, ω⟩ => by
    by_cases hpR : (γ, ω) ∈ range f
    · rw [indicator_of_mem hpR]
      by_cases hS : (γ, ω) ∈ Sset
      · rw [indicator_of_mem hS]
        have hell : IsEll (D.el γ) := fun s hs ⟨c, hc⟩ => let ⟨v⟩ := ‹Nonempty I›; no_eig_of_ell D.σ v (D.el γ).out (hS.2.1 v) hs c hc
        simp only [g', u, hell, ite_true]
        exact (hF3 F I Gf ι D k a hk (D.el γ) ω hS.2.1 hS.2.2.1).2 (β (γ, ω)) (hβ (γ, ω))
      · rw [indicator_of_notMem hS]; simp only [g', u]
        by_cases hell : IsEll (D.el γ)
        · simp only [hell, ite_true]
          by_cases htot : D.TotEll (D.el γ).out
          · by_cases hte : D.Te a (D.el γ).out (D.rep ω) = 0
            · simp [Dat.kk, Dat.kt, hte]
            · exact (hS ⟨hpR, htot, hte, (hF3 F I Gf ι D k a hk (D.el γ) ω htot hte).1⟩).elim
          · exact hF2 F I Gf ι D k a hk (D.el γ) ω htot (β (γ, ω)) (hβ (γ, ω)) (by simpa only [u, hell, ite_true] using hintR (γ, ω) hpR)
        · simp [hell]
    · rw [indicator_of_notMem hpR, indicator_of_notMem fun h => hpR h.1]
  have h1 := (hasSum_subtype_iff_indicator (f := g')).1 hsum; rw [hind] at h1
  have h2 : HasSum (Sset.indicator h') (geo D k a hSfin.toFinset) := by
    rw [show geo D k a hSfin.toFinset = ∑ p ∈ hSfin.toFinset, Sset.indicator h' p from
      Finset.sum_congr rfl fun p hp => (indicator_of_mem (by simpa using hp) h').symm]
    exact hasSum_sum_of_ne_finset_zero fun p hp => indicator_of_notMem (by simpa using hp) _
  exact h1.unique h2

-- === F5: Kernel trace bound ===

theorem kernel_trace_bound_proof : E0d → E1 → F5 := by
  intro _ hE1 F I Gf ι _ _ _ _ D k a hH
  obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hH 1 one_pos
  refine ⟨C, fun T hT y => ⟨fun hy γ s hs _ => hy s hs, fun hy => ?_⟩⟩
  simp only [Dat.abelian₂, mem_ofPred_eq, not_forall, not_le] at hy; obtain ⟨s, hs, hsT⟩ := hy
  calc ∑' γ : PG F, ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ
      ≤ ∑' γ, {γ : PG F | ¬Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ := ENNReal.tsum_le_tsum fun γ => by
          by_cases hγ : y ∈ D.LamF T γ
          · rw [indicator_of_mem hγ, indicator_of_mem (show γ ∈ {γ | ¬Fix s γ} from fun hf => absurd (hγ s hs hf) (not_le.2 hsT))]
          · rw [indicator_of_notMem hγ]; simp
    _ = ∑' γ : {γ : PG F // ¬Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (_root_.tsum_subtype _ _).symm
    _ ≤ C := hC y s hs (hT.trans hsT).le

-- === ConstantTermVanishingAlt ===

theorem unipotent_integrand_vanishes_proof : B1a → UpperHalfPlaneMeasureCoordinates → ConstantTermVanishingAlt := by
  intro hB1 _ I _ _ φ hφ β hβ hβ0 hβinv A B hA hAB u hu hint
  have : SigmaFinite (volume : Measure P) := hB1.1
  let Y1 := {y : ℝ // y ≠ 0}
  let nu1 : Measure Y1 := (Measure.comap Subtype.val volume).withDensity fun y => oR (1 / |y.1|)
  have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have hemb : MeasurableEmbedding (Subtype.val : Y1 → ℝ) := MeasurableEmbedding.subtype_coe (s := {y : ℝ | y ≠ 0}) hY
  have hmap_wd {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure α) (g : β → ℝ≥0∞) :
      Measure.map f (μ.withDensity fun x => g (f x)) = (Measure.map f μ).withDensity g := Measure.ext fun s hs => by
    rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs, hf.restrict_map, hf.lintegral_map]
  have hmap_nu1 : Measure.map Subtype.val nu1 = (volume : Measure ℝ).withDensity fun y => oR (1 / |y|) := by
    have h0 : Measure.map (Subtype.val : Y1 → ℝ) (Measure.comap Subtype.val volume) = volume := by
      rw [show Measure.map (Subtype.val : Y1 → ℝ) (Measure.comap Subtype.val volume) = volume.restrict (range (Subtype.val : Y1 → ℝ)) from hemb.map_comap volume,
        show range (Subtype.val : Y1 → ℝ) = {0}ᶜ from Set.ext fun _ => by simp]
      exact Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 (measure_singleton 0))
    exact (hmap_wd hemb (Measure.comap Subtype.val volume) fun y => oR (1 / |y|)).trans (by rw [h0])
  have : SigmaFinite nu1 := SigmaFinite.of_map nu1 hemb.measurable.aemeasurable (by rw [hmap_nu1]; infer_instance)
  let scl (t : ℝ) (ht : t ≠ 0) (y : Y1) : Y1 := ⟨t * y.1, mul_ne_zero ht y.2⟩
  have hmpscl (t : ℝ) (ht : t ≠ 0) : MeasurePreserving (scl t ht) nu1 nu1 := by
    have hm : Measurable (scl t ht) := ((measurable_const_mul t).comp measurable_subtype_coe).subtype_mk
    refine ⟨hm, ?_⟩
    have hmr : Measure.map (t * ·) ((volume : Measure ℝ).withDensity fun y => oR (1 / |y|)) = (volume : Measure ℝ).withDensity fun y => oR (1 / |y|) := by
      have hembm : MeasurableEmbedding (t * ·) := (Homeomorph.mulLeft₀ t ht).measurableEmbedding
      have hpt : (volume : Measure ℝ).withDensity (fun y => oR (1 / |y|)) = oR |t| • (volume : Measure ℝ).withDensity fun y => oR (1 / |t * y|) := by
        rw [← withDensity_smul _ (by fun_prop)]; congr 1; funext y; simp only [Pi.smul_apply, smul_eq_mul]
        rw [← ENNReal.ofReal_mul (abs_nonneg t), abs_mul]; congr 1
        rw [one_div, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 ht), one_mul]
      have hc : oR |t| * oR |t⁻¹| = 1 := by rw [← ENNReal.ofReal_mul (abs_nonneg t), ← abs_mul, mul_inv_cancel₀ ht, abs_one, ENNReal.ofReal_one]
      conv_lhs => rw [hpt]
      rw [Measure.map_smul, hmap_wd hembm volume (fun y : ℝ => oR (1 / |y|)), Real.map_volume_mul_left ht, withDensity_smul_measure, smul_smul, hc, one_smul]
      exact hembm.measurable.aemeasurable
    have hv : Measure.map Subtype.val (Measure.map (scl t ht) nu1) = Measure.map Subtype.val nu1 := by
      rw [Measure.map_map hemb.measurable hm, show Subtype.val ∘ scl t ht = (t * ·) ∘ Subtype.val from rfl,
        ← Measure.map_map (measurable_const_mul t) hemb.measurable, hmap_nu1, hmr]
    rw [← hemb.comap_map (Measure.map (scl t ht) nu1), hv, hemb.comap_map]
  let Φ : (I → ℝ) × (I → Y1) ≃ᵐ X I :=
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ Y1 I).symm.trans (MeasurableEquiv.piCongrRight fun _ : I => ptE)
  have hΦ : MeasurePreserving Φ ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) volume :=
    (measurePreserving_pi _ _ fun _ => pt_mp).comp (MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow ℝ Y1 I (fun _ => volume) (fun _ => nu1)))
  let b (y : I → Y1) : ℝ := β (Φ (0, y))
  have hb : Measurable b := hβ.comp (Φ.measurable.comp (measurable_const.prodMk measurable_id))
  have hβΦ x y : β (Φ (x, y)) = b y := (hβinv x 0 (fun v => (y v).1) (fun v => (y v).2) 1 one_pos).trans $
    congrArg β (funext fun v => Subtype.ext (by change ((1 * (y v).1 : ℝ) : ℂ) * ((0 : ℝ) + Complex.I) = ((y v).1 : ℂ) * ((0 : ℝ) + Complex.I); simp))
  have huΦ x y : u (Φ (x, y)) = if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0 := hu x (fun v => (y v).1) (fun v => (y v).2)
  have hint' : Integrable (fun p : (I → ℝ) × (I → Y1) => b p.2 • (if A / ∏ v, (1 + p.1 v ^ 2) ≤ ∏ v, |(p.2 v).1| ∧ ∏ v, |(p.2 v).1| ≤ B then ∏ v, φ v (p.1 v) else 0))
      ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) :=
    ((hΦ.integrable_comp_emb Φ.measurableEmbedding).2 hint).congr (ae_of_all _ fun ⟨x, y⟩ => by change β (Φ (x, y)) • u (Φ (x, y)) = _; rw [hβΦ, huΦ])
  let Lg (y : I → Y1) : ℝ := ∑ v, Real.log |(y v).1|
  have hLgm : Measurable Lg := Finset.measurable_sum _ fun v _ => Real.measurable_log.comp (continuous_abs.measurable.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))
  have hcond (x : I → ℝ) (y : I → Y1) : (A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B) ↔ Lg y ∈ Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B) := by
    have hp : 0 < ∏ v, |(y v).1| := Finset.prod_pos fun v _ => abs_pos.2 (y v).2
    have hq : 0 < ∏ v, (1 + x v ^ 2) := Finset.prod_pos fun _ _ => by positivity
    rw [Set.mem_Icc, show Lg y = Real.log (∏ v, |(y v).1|) from (Real.log_prod fun v _ => abs_ne_zero.2 (y v).2).symm,
      show Real.log A - ∑ v, Real.log (1 + x v ^ 2) = Real.log (A / ∏ v, (1 + x v ^ 2)) by rw [Real.log_div hA.ne' hq.ne', Real.log_prod fun _ _ => by positivity],
      Real.log_le_log_iff (div_pos hA hq) hp, Real.log_le_log_iff hp (hA.trans hAB)]
  let m : Measure ℝ := Measure.map Lg ((Measure.pi fun _ : I => nu1).withDensity fun y => oR (b y))
  have hminv (c : ℝ) (S : Set ℝ) (hS : MeasurableSet S) : m ((c + ·) ⁻¹' S) = m S := by
    have hcard : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    set t := Real.exp (c / Fintype.card I); have ht : 0 < t := Real.exp_pos _
    have hlog : (Fintype.card I : ℝ) * Real.log t = c := by rw [Real.log_exp]; field_simp
    have hS' : MeasurableSet (Lg ⁻¹' S) := hLgm hS
    have hpre : Lg ⁻¹' ((c + ·) ⁻¹' S) = (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' (Lg ⁻¹' S) := Set.ext fun y => by
      simp only [Set.mem_preimage]
      rw [show Lg (fun v => scl t ht.ne' (y v)) = c + Lg y by
        rw [← hlog]; simp only [Lg, scl, abs_mul, abs_of_pos ht]
        rw [Finset.sum_congr rfl fun v _ => Real.log_mul ht.ne' (abs_ne_zero.2 (y v).2), Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    have hscl : MeasurePreserving (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) (Measure.pi fun _ => nu1) (Measure.pi fun _ => nu1) :=
      measurePreserving_pi _ _ fun _ => hmpscl t ht.ne'
    have hpm : MeasurableSet ((fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' (Lg ⁻¹' S)) := hscl.measurable hS'
    rw [Measure.map_apply hLgm ((measurable_const_add c) hS), Measure.map_apply hLgm hS, hpre,
      withDensity_apply _ hpm, withDensity_apply _ hS', ← lintegral_indicator hpm, ← lintegral_indicator hS',
      ← hscl.lintegral_comp ((show Measurable (fun a => oR (b a)) from ENNReal.measurable_ofReal.comp hb).indicator hS')]
    refine lintegral_congr fun y => ?_
    by_cases hy : (fun v => scl t ht.ne' (y v)) ∈ Lg ⁻¹' S
    · rw [indicator_of_mem (show y ∈ _ ⁻¹' _ from hy), indicator_of_mem hy]
      exact congrArg oR (hβinv 0 0 (fun v => (y v).1) (fun v => (y v).2) t ht)
    · rw [indicator_of_notMem (show y ∉ _ ⁻¹' _ from hy), indicator_of_notMem hy]
  have hlt (x : I → ℝ) : Real.log A - ∑ v, Real.log (1 + x v ^ 2) < Real.log B := by
    have : 0 ≤ ∑ v, Real.log (1 + x v ^ 2) := Finset.sum_nonneg fun v _ => Real.log_nonneg (by linarith [sq_nonneg (x v)])
    linarith [Real.log_lt_log hA hAB]
  have : (ae (volume : Measure (I → ℝ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨x0, hx0⟩ := hint'.prod_right_ae.exists
  let J0 := Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)
  have hfin : m J0 ≠ ∞ := by
    have hP0 : (∏ v, φ v (x0 v)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => (hφ v).2.2.2.2 (x0 v)
    have hTint : Integrable ((Lg ⁻¹' J0).indicator b) (Measure.pi fun _ : I => nu1) :=
      (hx0.norm.div_const ‖∏ v, φ v (x0 v)‖).congr (ae_of_all _ fun y => by
        dsimp only; by_cases h : Lg y ∈ J0
        · rw [ite_eq_left ((hcond x0 y).2 h), indicator_of_mem (show y ∈ Lg ⁻¹' J0 from h), norm_smul, Real.norm_of_nonneg (hβ0 _), mul_div_assoc, div_self (norm_ne_zero_iff.2 hP0), mul_one]
        · rw [ite_eq_right (mt (hcond x0 y).1 h), indicator_of_notMem (show y ∉ Lg ⁻¹' J0 from h), smul_zero, norm_zero, zero_div])
    rw [Measure.map_apply hLgm measurableSet_Icc, withDensity_apply _ (hLgm measurableSet_Icc), ← lintegral_indicator (hLgm measurableSet_Icc)]
    exact ((lintegral_congr fun y => by simp only [indicator]; split_ifs <;> simp).trans_lt hTint.lintegral_lt_top).ne
  -- Haar uniqueness on ℝ
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ a c : ℝ, a ≤ c → (m (Icc a c)).toReal = R * (c - a) := by
    have hI : m.IsAddLeftInvariant := ⟨fun c => Measure.ext fun S hS => by rw [Measure.map_apply (measurable_const_add c) hS]; exact hminv c S hS⟩
    set a0 := Real.log A - ∑ v, Real.log (1 + x0 v ^ 2); set ℓ := Real.log B - a0
    have hℓ : 0 < ℓ := by linarith [hlt x0]
    have hL : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Icc (x - ℓ / 2) (x - ℓ / 2 + ℓ), Icc_mem_nhds (by linarith) (by linarith), by
      have h := hminv (a0 - (x - ℓ / 2)) J0 measurableSet_Icc
      rw [preimage_const_add_Icc, show a0 - (a0 - (x - ℓ / 2)) = x - ℓ / 2 by ring, show Real.log B - (a0 - (x - ℓ / 2)) = x - ℓ / 2 + ℓ by ring] at h
      exact h ▸ hfin.lt_top⟩⟩
    refine ⟨(Measure.addHaarScalarFactor m volume : ℝ), fun a c hac => ?_⟩
    have := congrArg (fun μ : Measure ℝ => μ (Icc a c)) (Measure.isAddLeftInvariant_eq_smul m (volume : Measure ℝ))
    rw [this, Measure.smul_apply, Real.volume_Icc, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (sub_nonneg.2 hac)]
  -- Integrate out y then x
  have heq : ∫ z, β z • u z = ∫ p : (I → ℝ) × (I → Y1),
      b p.2 • (if A / ∏ v, (1 + p.1 v ^ 2) ≤ ∏ v, |(p.2 v).1| ∧ ∏ v, |(p.2 v).1| ≤ B then ∏ v, φ v (p.1 v) else 0)
      ∂((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) :=
    (hΦ.integral_comp' (fun z => β z • u z)).symm.trans (integral_congr_ae (ae_of_all _ fun ⟨x, y⟩ => by
      change β (Φ (x, y)) • u (Φ (x, y)) = _; rw [hβΦ, huΦ]))
  rw [heq, integral_prod _ hint']
  have hinner (x : I → ℝ) : ∫ y, b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0) ∂(Measure.pi fun _ : I => nu1) =
      (∏ v, φ v (x v)) * ((R * ((Real.log B - Real.log A) + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ) := by
    let J := Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)
    have hS : MeasurableSet (Lg ⁻¹' J) := hLgm measurableSet_Icc
    have e1 : (fun y : I → Y1 => b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0)) =
        fun y => (((Lg ⁻¹' J).indicator b y : ℝ) : ℂ) * ∏ v, φ v (x v) := funext fun y => by
      by_cases h : Lg y ∈ J
      · rw [ite_eq_left ((hcond x y).2 h), indicator_of_mem (show y ∈ Lg ⁻¹' J from h), real_smul]
      · rw [ite_eq_right (mt (hcond x y).1 h), indicator_of_notMem (show y ∉ Lg ⁻¹' J from h), smul_zero]; simp
    rw [e1, integral_mul_const, integral_complex_ofReal, integral_indicator hS, mul_comm,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => hβ0 _) hb.aestronglyMeasurable,
      ← withDensity_apply _ hS, ← Measure.map_apply hLgm measurableSet_Icc, hR _ _ (hlt x).le,
      show Real.log B - (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) = (Real.log B - Real.log A) + ∑ v, Real.log (1 + x v ^ 2) by ring]
  rw [integral_congr_ae (ae_of_all _ hinner)]
  -- integral_prod_log
  let ψ (w v : I) (t : ℝ) : ℂ := (if v = w then (Real.log (1 + t ^ 2) : ℂ) else 1) * φ v t
  have hP : Integrable (fun x : I → ℝ => ∏ v, φ v (x v)) := by rw [volume_pi]; exact Integrable.fintype_prod fun v => (hφ v).2.1
  have hψP w : Integrable (fun x : I → ℝ => ∏ v, ψ w v (x v)) := by
    rw [volume_pi]; exact Integrable.fintype_prod fun v => by by_cases hv : v = w <;> simp [ψ, hv, (hφ _).2.1, (hφ _).2.2.1]
  have hkey (x : I → ℝ) : (∏ v, φ v (x v)) * ((R * ((Real.log B - Real.log A) + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ) =
      (R * (Real.log B - Real.log A) : ℂ) * ∏ v, φ v (x v) + ∑ w, (R : ℂ) * ∏ v, ψ w v (x v) := by
    have hψw w : ∏ v, ψ w v (x v) = (Real.log (1 + x w ^ 2) : ℂ) * ∏ v, φ v (x v) := by
      simp only [ψ, Finset.prod_mul_distrib]
      rw [Finset.prod_eq_single w (fun _ _ hv => by simp [hv]) (by simp)]; simp
    simp_rw [hψw]; rw [← Finset.mul_sum, ← Finset.sum_mul]; push_cast; ring
  simp_rw [hkey]
  obtain ⟨v0, _, _⟩ := exists_pair_ne I
  have hz0 w : ∏ v, ∫ t, ψ w v t = 0 := by
    obtain ⟨v, hv⟩ := exists_ne w
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simpa [ψ, hv] using (hφ v).2.2.2.1)
  rw [integral_add (hP.const_mul _) (integrable_finsetSum _ fun w _ => (hψP w).const_mul _), integral_const_mul,
    integral_fintype_prod_volume_eq_prod, Finset.prod_eq_zero (Finset.mem_univ v0) (hφ v0).2.2.2.1,
    integral_finsetSum _ fun w _ => (hψP w).const_mul _]
  simp [integral_const_mul, integral_fintype_prod_volume_eq_prod, hz0]

-- === DiagonalTruncatedIntegralZero ===

theorem diagonal_truncated_integral_zero : B1a → UpperHalfPlaneMeasureCoordinates → DiagonalIntegrandVanishes → C1 → E0a → KernelTermsInvariantBounded → E0d → Ecut → Fcen → ConstantTermVanishingAlt → DiagonalTruncatedIntegralZero := by
  intro _ _ _ _ hE0a _ _ hEcut _ hF6c F I Gf ι _ _ _ _ D k a hH T hT γ ω h01 h10 β hβ hint
  obtain ⟨hcount, _, hpres, _, _, _, hbor, _⟩ := hE0a F I Gf D hH.ax
  have := hH.ax.two; have : Countable (PG F) := hcount; have : BorelSpace D.Xs := hbor
  set g := (γ : PG F).out
  have hgq : (g : PG F) = (γ : PG F) := QuotientGroup.out_eq' _
  have ⟨g01, g10⟩ : g 0 1 = 0 ∧ g 1 0 = 0 := by
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (center (GL2 F)) γ; obtain ⟨z1, z2, _⟩ := center_entries z.2
    rw [show g = γ * z.1 from hz]; simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, z1, z2]
  have hkk (z : D.Xs) : D.kk k a (γ : PG F) (ω, z) = D.Te a g (D.rep ω) * ∏ v, (q1 (k v) (z v) (D.r v g • z v) * j1 (k v) (D.r v g) (z v)) := by
    change D.Te a g (D.rep ω) * (qq k z (D.act g z) * D.J k g z) = _
    simp only [qq, Dat.J, Dat.act, Finset.prod_mul_distrib]
  by_cases hc : D.Te a g (D.rep ω) = 0
  · have h0 z : (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z) = 0 := by rw [indicator_apply]; split_ifs <;> simp [hkk, hc]
    simp [h0]
  obtain ⟨i, hi⟩ := kk_supp D a (γ : PG F) ω hc; obtain ⟨htr0, htr1⟩ := kk_reg D k a hH (γ : PG F) ω i hi
  have hne : g 0 0 ≠ g 1 1 := fun h => htr1 (by rw [trace_fin_two, det_fin_two, g01, g10, h]; ring)
  choose φ hφc hφe hφi hφl hφ0 hφn using fun v => diagonal_integrand_vanishes_proof (k v) (hH.four v) (D.r v g)
    (show D.σ v (g 0 1) = 0 by rw [g01, map_zero]) (show D.σ v (g 1 0) = 0 by rw [g10, map_zero]) fun h => hne ((D.σ v).injective h)
  by_cases hz : ∃ v, φ v = 0
  · obtain ⟨v, hv⟩ := hz
    have h0 (z : D.Xs) : D.kk k a (γ : PG F) (ω, z) = 0 := by
      rw [hkk, Finset.prod_eq_zero (Finset.mem_univ v), mul_zero]
      have := hφe v ((z v).1.re / (z v).1.im) (z v).1.im (z v).2
      rw [show pt ((z v).1.re / (z v).1.im) (z v).1.im (z v).2 = z v from ptE.right_inv (z v), hv] at this; exact this
    have h0' z : (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z) = 0 := by rw [indicator_apply]; split_ifs <;> simp [h0]
    simp [h0']
  push Not at hz; have hφn' v x : φ v x ≠ 0 := (hφn v).resolve_left (hz v) x
  have h1pos : 0 < D.hf ![0, 1] (D.rep ω) := hH.ax.pos _ (by simp) _
  have h2pos : 0 < D.hf ![1, 0] (D.rep ω) := hH.ax.pos _ (by simp) _
  have h12 : D.hf ![0, 1] (D.rep ω) * D.hf ![1, 0] (D.rep ω) ≤ 1 := by simpa using hH.ax.prod ![0, 1] ![1, 0] (by simp) (D.rep ω)
  have hH01 (z : D.Xs) : D.HtY ![0, 1] (ω, z) = (∏ v, |(z v).1.im|) * D.hf ![0, 1] (D.rep ω) := by simp [Dat.HtY, Dat.Ht]
  have hH10 (z : D.Xs) : D.HtY ![1, 0] (ω, z) = (∏ v, |(z v).1.im| / ‖(z v).1‖ ^ 2) * D.hf ![1, 0] (D.rep ω) := by simp [Dat.HtY, Dat.Ht]
  have hLam (z : D.Xs) : (ω, z) ∈ D.LamF T (γ : PG F) ↔ D.HtY ![0, 1] (ω, z) ≤ T ∧ D.HtY ![1, 0] (ω, z) ≤ T := by
    simp only [Dat.LamF, mem_ofPred_eq, Fix]
    refine ⟨fun h => ⟨h _ (by simp) ⟨g 1 1, funext fun j => by fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two, show (γ : PG F).out = g from rfl, g10]⟩,
      h _ (by simp) ⟨g 0 0, funext fun j => by fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two, show (γ : PG F).out = g from rfl, g01]⟩⟩,
      fun ⟨h1, h2⟩ s hs ⟨c, hc⟩ => ?_⟩
    change s ᵥ* g.val = c • s at hc
    have e0 : s 0 * g 0 0 = c * s 0 := by simpa [vecMul, dotProduct, Fin.sum_univ_two, g01, g10] using congrFun hc 0
    have e1 : s 1 * g 1 1 = c * s 1 := by simpa [vecMul, dotProduct, Fin.sum_univ_two, g01, g10] using congrFun hc 1
    by_cases hs0 : s 0 = 0
    · have hs1 : s 1 ≠ 0 := fun h => hs (funext fun j => by fin_cases j <;> simp [hs0, h])
      rw [show s = s 1 • ![0, 1] from funext fun j => by fin_cases j <;> simp [hs0], htY_smulc D hH.ax _ (by simp) _ hs1]; exact h1
    · have hs1 : s 1 = 0 := by
        by_contra h
        exact hne ((mul_left_cancel₀ hs0 (show s 0 * g 0 0 = s 0 * c by linear_combination e0)).trans
          (mul_left_cancel₀ h (show s 1 * g 1 1 = s 1 * c by linear_combination e1)).symm)
      rw [show s = s 0 • ![1, 0] from funext fun j => by fin_cases j <;> simp [hs1], htY_smulc D hH.ax _ (by simp) _ hs0]; exact h2
  set S := stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om)
  have hstab (δ : PG F) (hδ : δ ∈ S) : δ * (γ : PG F) * δ⁻¹ = γ ∧ δ • ω = ω := by
    rw [mem_stabilizer_iff] at hδ; exact ⟨(D.smulC δ (γ : PG F)).symm.trans (congrArg Prod.fst hδ), congrArg Prod.snd hδ⟩
  have hdiag (δ : PG F) (hδ : δ ∈ S) : δ.out 0 1 = 0 ∧ δ.out 1 0 = 0 ∧ ∏ v, |D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1)| = 1 := by
    obtain ⟨h3, h2⟩ := hstab δ hδ
    have hcomm := pf_Fcen F g δ.out htr0 (by rw [QuotientGroup.out_eq', hgq]; exact h3)
    have a01 := congrArg (fun m : GL2 F => m 0 1) hcomm; have a10 := congrArg (fun m : GL2 F => m 1 0) hcomm
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, g01, g10, mul_zero, zero_mul, add_zero, zero_add] at a01 a10
    have d01 : δ.out 0 1 = 0 := by by_contra h; exact hne (mul_left_cancel₀ h (by linear_combination -a01))
    have d10 : δ.out 1 0 = 0 := by by_contra h; exact hne (mul_left_cancel₀ h (by linear_combination a10))
    refine ⟨d01, d10, ?_⟩
    have hd11 : δ.out 1 1 ≠ 0 := fun h => δ.out.det_ne_zero (by rw [det_fin_two, h, d01]; ring)
    have hr v (w : P) : (D.r v δ.out • w).1.im = D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1) * w.1.im := by
      rw [diag_smul (show D.σ v (δ.out 0 1) = 0 by rw [d01, map_zero]) (show D.σ v (δ.out 1 0) = 0 by rw [d10, map_zero]), im_ofReal_mul]; rfl
    have key := htY_smul D hH.ax ![0, 1] e01_ne δ.out ((ω, fun _ => iP) : D.Y)
    rw [show ![0, 1] ᵥ* δ.out.val = δ.out 1 1 • ![0, 1] from funext fun j => by fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two, d10],
      htY_smulc D hH.ax _ e01_ne _ hd11, QuotientGroup.out_eq',
      show δ • ((ω, fun _ => iP) : D.Y) = (ω, D.act δ.out fun _ => iP) from Prod.ext h2 (smulX_out D δ _)] at key
    have key2 := (hH01 (D.act δ.out fun _ => iP)).symm.trans (key.trans (hH01 (fun _ => iP)))
    simp only [Dat.act, hr] at key2; simpa [iP, h1pos.ne'] using key2
  obtain ⟨β0, hβ0⟩ := (hEcut F I Gf D hH.ax).2 ω S fun δ hδ => mem_stabilizer_iff.2 (hstab δ hδ).2
  let N (z : D.Xs) : ℝ := (∏ v, |(z v).1.im|) ^ ((Fintype.card I : ℝ)⁻¹)
  have hNpos z : 0 < N z := rpow_pos_of_pos (Finset.prod_pos fun v _ => abs_pos.2 (z v).2) _
  let p (z : D.Xs) : D.Xs := fun v => pt 0 ((z v).1.im / N z) (div_ne_zero (z v).2 (hNpos z).ne')
  have hpc : Continuous p := continuous_pi fun v => by
    have hNc : Continuous (N : (I → P) → ℝ) :=
      (continuous_finsetProd Finset.univ fun (w : I) _ => (continuous_im.comp (continuous_subtype_val.comp (continuous_apply w))).abs).rpow_const
        fun (z : I → P) => Or.inl (Finset.prod_pos fun w _ => abs_pos.2 (z w).2).ne'
    exact continuous_induced_rng.2 $
      (continuous_ofReal.comp ((continuous_im.comp (continuous_subtype_val.comp (continuous_apply v))).div hNc fun (z : I → P) => (hNpos z).ne')).mul continuous_const
  have hpeq (δ : S) (z : D.Xs) : p (δ.1 • z) = δ.1 • p z := by
    obtain ⟨d01, d10, dprod⟩ := hdiag δ.1 δ.2
    have h01' v : (D.r v δ.1.out) 0 1 = 0 := by change D.σ v (δ.1.out 0 1) = 0; rw [d01, map_zero]
    have h10' v : (D.r v δ.1.out) 1 0 = 0 := by change D.σ v (δ.1.out 1 0) = 0; rw [d10, map_zero]
    have hr v (w : P) : (D.r v δ.1.out • w).1.im = D.σ v (δ.1.out 0 0) / D.σ v (δ.1.out 1 1) * w.1.im := by rw [diag_smul (h01' v) (h10' v), im_ofReal_mul]; rfl
    have hN : N (D.act δ.1.out z) = N z := by simp only [N, Dat.act, hr, abs_mul, Finset.prod_mul_distrib, dprod, one_mul]
    rw [smulX_out, smulX_out]; funext v; apply Subtype.ext
    change (((D.r v δ.1.out • z v).1.im / N (D.act δ.1.out z) : ℝ) : ℂ) * ((0 : ℝ) + Complex.I) = (D.r v δ.1.out • p z v).1
    rw [hr, hN, diag_smul (h01' v) (h10' v)]
    change _ = ((D.σ v (δ.1.out 0 0) / D.σ v (δ.1.out 1 1) : ℝ) : ℂ) * ((((z v).1.im / N z : ℝ) : ℂ) * ((0 : ℝ) + Complex.I)); push_cast; ring
  have hβ' : IsCut S (fun z : D.Xs => β0 (p z)) := ⟨hβ0.meas.comp hpc.measurable, fun _ => hβ0.nonneg _, fun z => by
    have : (fun δ : S => β0 (p (δ • z))) = fun δ => β0 (δ • p z) := funext fun δ => congrArg β0 (hpeq δ z)
    show HasSum _ 1; rw [this]; exact hβ0.sum (p z)⟩
  let u (z : D.Xs) : ℂ := (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z)
  have huinv (δ : S) (z : D.Xs) : u (δ • z) = u z := by
    obtain ⟨h3, h2⟩ := hstab δ.1 δ.2
    have hy : ((ω, (δ.1 • z : D.Xs)) : D.Y) = δ.1 • ((ω, z) : D.Y) := Prod.ext h2.symm rfl
    have hk := kk_conj D k a hH δ.1 (γ : PG F) (ω, z); rw [h3] at hk
    have hm : δ.1 • ((ω, z) : D.Y) ∈ D.LamF T (γ : PG F) ↔ ((ω, z) : D.Y) ∈ D.LamF T (γ : PG F) :=
      ⟨fun h => by have := lamF_smul D hH.ax T _ δ.1⁻¹ _ h; rwa [inv_smul_smul, show δ.1⁻¹ * (γ : PG F) * δ.1⁻¹⁻¹ = γ from (congrArg (fun x => δ.1⁻¹ * x * δ.1⁻¹⁻¹) h3.symm).trans (by group)] at this,
       fun h => by have := lamF_smul D hH.ax T _ δ.1 _ h; rwa [h3] at this⟩
    change (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, δ.1 • z) = (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z); rw [hy]
    by_cases h : ((ω, z) : D.Y) ∈ D.LamF T (γ : PG F)
    · rw [indicator_of_mem (hm.2 h), indicator_of_mem h, hk]
    · rw [indicator_of_notMem (mt hm.1 h), indicator_of_notMem h]
  have hC := (action_integral_swap_proof S D.Xs volume (fun δ => hpres δ.1) β (fun z => β0 (p z)) hβ hβ').2 u
    (((meas_kk D k a hH _).indicator (meas_lamF D hH.ax T _)).comp measurable_prodMk_left) huinv hint
  rw [hC.2]
  have hF := hF6c I φ (fun v => ⟨hφc v, hφi v, hφl v, hφ0 v, hφn' v⟩) (fun z => β0 (p z)) (hβ0.meas.comp hpc.measurable) (fun _ => hβ0.nonneg _)
    (fun x x' y hy t ht => congrArg β0 $ funext fun v => Subtype.ext $ by
      have hsc : (∏ w, |t * y w|) ^ ((Fintype.card I : ℝ)⁻¹) = t * (∏ w, |y w|) ^ ((Fintype.card I : ℝ)⁻¹) := by
        simp only [abs_mul, Finset.prod_mul_distrib, Finset.prod_const, abs_of_pos ht, Finset.card_univ]
        rw [mul_rpow (by positivity) (Finset.prod_nonneg fun _ _ => abs_nonneg _), pow_rpow_inv_natCast ht.le Fintype.card_ne_zero]
      simp only [p, N, pt, mul_im, ofReal_re, ofReal_im, add_im, I_im, zero_add, mul_one, add_zero, zero_mul]
      rw [hsc, mul_div_mul_left _ _ ht.ne'])
    (D.hf ![1, 0] (D.rep ω) / T) (T / D.hf ![0, 1] (D.rep ω)) (div_pos h2pos (by linarith))
    ((div_lt_div_iff₀ (by linarith) h1pos).2 (by nlinarith)) (fun z => (D.Te a g (D.rep ω))⁻¹ * u z)
    (fun x y hy => by
      have hPy : 0 < ∏ v, |y v| := Finset.prod_pos fun v _ => abs_pos.2 (hy v)
      have hQ : 0 < ∏ v, (1 + x v ^ 2) := Finset.prod_pos fun _ _ => by positivity
      have hcond : ((ω, fun v => pt (x v) (y v) (hy v)) : D.Y) ∈ D.LamF T (γ : PG F) ↔
          (D.hf ![1, 0] (D.rep ω) / T / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |y v| ∧ ∏ v, |y v| ≤ T / D.hf ![0, 1] (D.rep ω)) := by
        refine (hLam _).trans ?_; rw [hH01 (fun v => pt (x v) (y v) (hy v)), hH10 (fun v => pt (x v) (y v) (hy v))]
        simp only [show ∀ v, |(pt (x v) (y v) (hy v)).1.im| = |y v| from fun _ => by simp [pt],
          show ∀ v, |y v| / ‖(pt (x v) (y v) (hy v)).1‖ ^ 2 = (|y v| * (1 + x v ^ 2))⁻¹ from fun v => by
            rw [Complex.sq_norm, normSq_apply]; simp [pt]
            have h1 : y v * x v * (y v * x v) + y v * y v = |y v| ^ 2 * (1 + x v ^ 2) := by rw [sq_abs]; ring
            have : |y v| ≠ 0 := abs_ne_zero.2 (hy v); have : (1 + x v ^ 2) ≠ 0 := (by positivity); rw [h1]; field_simp,
          Finset.prod_inv_distrib, Finset.prod_mul_distrib, inv_mul_le_iff₀ (mul_pos hPy hQ), div_div,
          div_le_iff₀ (mul_pos (by linarith : 0 < T) hQ), le_div_iff₀ h1pos]
        exact ⟨fun ⟨a, b⟩ => ⟨b.trans_eq (by ring), a⟩, fun ⟨a, b⟩ => ⟨b, a.trans_eq (by ring)⟩⟩
      change _ * (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, _) = _; rw [indicator_apply]
      by_cases hm : ((ω, fun v => pt (x v) (y v) (hy v)) : D.Y) ∈ D.LamF T (γ : PG F)
      · rw [ite_eq_left hm, ite_eq_left (hcond.1 hm), hkk (fun v => pt (x v) (y v) (hy v)), inv_mul_cancel_left₀ hc]; exact Finset.prod_congr rfl fun v _ => hφe v _ _ _
      · rw [ite_eq_right hm, ite_eq_right (mt hcond.2 hm), mul_zero])
    ((hC.1.const_mul (D.Te a g (D.rep ω))⁻¹).congr (ae_of_all _ fun _ => mul_smul_comm _ _ _))
  calc ∫ z, β0 (p z) • u z = D.Te a g (D.rep ω) * ∫ z : X I, β0 (p z) • ((D.Te a g (D.rep ω))⁻¹ * u z) := by
        rw [← integral_const_mul]; exact integral_congr_ae (ae_of_all _ fun z => by dsimp only; rw [mul_smul_comm, mul_inv_cancel_left₀ hc])
    _ = 0 := by rw [hF, mul_zero]

-- === F6: Unipotent terms contribution ===

theorem unipotent_terms_contribution_proof : C1 → E0a → KernelTermsInvariantBounded → E0d → DiagonalTruncatedIntegralZero → F6 := by
  intro _ hE0a _ _ hF6b F I Gf ι _ _ _ _ D k a hH T hT γ ω hγ β hβ hint
  by_cases hTe : D.Te a γ.out (D.rep ω) = 0
  · have h0 z : (D.LamF T γ).indicator (D.kk k a γ) (ω, z) = 0 := by rw [indicator_apply]; split_ifs <;> simp [Dat.kk, Dat.kt, hTe]
    simp [h0]
  obtain ⟨-, -, hP, -⟩ := hE0a F I Gf D hH.ax
  obtain ⟨i, hi⟩ := kk_supp D a γ ω hTe; obtain ⟨-, hdisc⟩ := kk_reg D k a hH γ ω i hi
  simp only [IsEll, not_forall, not_not] at hγ; obtain ⟨s, hs0, c, hc⟩ := hγ
  obtain ⟨δ1, hδ1⟩ := row_exists s hs0
  -- Diagonalize γ.out over F
  obtain ⟨δ0, h01, h10⟩ : ∃ δ : GL2 F, (δ * γ.out * δ⁻¹) 0 1 = 0 ∧ (δ * γ.out * δ⁻¹) 1 0 = 0 := by
    set h := δ1 * γ.out * δ1⁻¹
    have hv : ![0, 1] ᵥ* h.val = c • ![0, 1] := by
      simp only [h, Units.val_mul, ← vecMul_vecMul, hδ1, hc, smul_vecMul]
      rw [← hδ1, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
    have e10 : h 1 0 = 0 := by simpa [vecMul, dotProduct, Fin.sum_univ_two] using congrFun hv 0
    have htr : h.val.trace = γ.out.val.trace := by simp only [h, Units.val_mul]; rw [trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have hdet : h.val.det = γ.out.val.det := by simp only [h, Units.val_mul, det_mul]; rw [mul_right_comm, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul]
    have hne : h 0 0 - h 1 1 ≠ 0 := fun e => hdisc (by rw [← htr, ← hdet, trace_fin_two, det_fin_two, e10]; linear_combination (h 0 0 - h 1 1) * e)
    set t : F := h 0 1 / (h 0 0 - h 1 1); have ht : t * (h 0 0 - h 1 1) = h 0 1 := div_mul_cancel₀ _ hne
    let u : GL2 F := ⟨!![1, t; 0, 1], !![1, -t; 0, 1], by simp [one_fin_two], by simp [one_fin_two]⟩
    have hM : (u * δ1 * γ.out * (u * δ1)⁻¹).val = !![1, t; 0, 1] * !![h 0 0, h 0 1; 0, h 1 1] * !![1, -t; 0, 1] := by
      rw [show u * δ1 * γ.out * (u * δ1)⁻¹ = u * h * u⁻¹ by simp [h]; group, Units.val_mul, Units.val_mul, eta_fin_two h.val, e10]; rfl
    exact ⟨u * δ1, by rw [hM]; simp; linear_combination -ht, by rw [hM]; simp⟩
  -- Transport integral by δ0
  set δ : PG F := (δ0 : PG F)
  have hγ' : δ * γ * δ⁻¹ = ((δ0 * γ.out * δ0⁻¹ : GL2 F) : PG F) := by simp [δ]
  set p : D.Cj × D.Om := (γ, ω)
  have hmem (g : PG F) : g ∈ stabilizer (PG F) (δ • p) ↔ δ⁻¹ * g * δ ∈ stabilizer (PG F) p := by
    simp only [mem_stabilizer_iff, mul_smul]; rw [inv_smul_eq_iff]
  let φ : stabilizer (PG F) p ≃ stabilizer (PG F) (δ • p) :=
    ⟨fun x => ⟨δ * x * δ⁻¹, (hmem _).2 (by simp [show δ⁻¹ * (δ * (x : PG F) * δ⁻¹) * δ = x by group, x.2])⟩,
     fun g => ⟨δ⁻¹ * g * δ, (hmem _).1 g.2⟩,
     fun x => Subtype.ext (by change δ⁻¹ * (δ * (x : PG F) * δ⁻¹) * δ = x; group),
     fun g => Subtype.ext (by change δ * (δ⁻¹ * (g : PG F) * δ) * δ⁻¹ = g; group)⟩
  let e := actEquiv hP δ⁻¹
  have he : MeasurePreserving e volume volume := hP δ⁻¹
  have key w : β (e w) • (D.LamF T γ).indicator (D.kk k a γ) (ω, e w) =
      β (δ⁻¹ • w) • (D.LamF T (δ * γ * δ⁻¹)).indicator (D.kk k a (δ * γ * δ⁻¹)) (δ • ω, w) := by
    have hy : ((δ • ω, w) : D.Y) = δ • ((ω, δ⁻¹ • w) : D.Y) := by rw [Prod.smul_mk, smul_inv_smul]
    change β (δ⁻¹ • w) • (D.LamF T γ).indicator (D.kk k a γ) (ω, δ⁻¹ • w) = _; rw [hy]; congr 1
    have hL : δ • ((ω, δ⁻¹ • w) : D.Y) ∈ D.LamF T (δ * γ * δ⁻¹) ↔ ((ω, δ⁻¹ • w) : D.Y) ∈ D.LamF T γ :=
      ⟨fun h => by have := lamF_smul D hH.ax T _ δ⁻¹ _ h; rwa [inv_smul_smul, show δ⁻¹ * (δ * γ * δ⁻¹) * δ⁻¹⁻¹ = γ by group] at this,
       lamF_smul D hH.ax T γ δ _⟩
    by_cases hm : ((ω, δ⁻¹ • w) : D.Y) ∈ D.LamF T γ
    · rw [indicator_of_mem hm, indicator_of_mem (hL.2 hm), kk_conj D k a hH]
    · rw [indicator_of_notMem hm, indicator_of_notMem (mt hL.1 hm)]
  have hβ' : IsCut (stabilizer (PG F) ((((δ0 * γ.out * δ0⁻¹ : GL2 F) : PG F), δ • ω) : D.Cj × D.Om)) (fun w => β (δ⁻¹ • w)) := by
    rw [show ((((δ0 * γ.out * δ0⁻¹ : GL2 F) : PG F), δ • ω) : D.Cj × D.Om) = δ • p from Prod.ext hγ'.symm rfl]
    refine ⟨hβ.meas.comp (hP δ⁻¹).measurable, fun _ => hβ.nonneg _, fun w => ?_⟩
    rw [← φ.hasSum_iff]; convert hβ.sum (δ⁻¹ • w) using 2 with x
    change β (δ⁻¹ • (δ * (x : PG F) * δ⁻¹) • w) = β ((x : PG F) • δ⁻¹ • w)
    simp only [smul_smul, show δ⁻¹ * (δ * (x : PG F) * δ⁻¹) = (x : PG F) * δ⁻¹ by group]
  have hint' := (he.integrable_comp_emb e.measurableEmbedding).2 hint |>.congr (ae_of_all _ key)
  rw [hγ'] at hint'
  rw [← he.integral_comp' (fun z => β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z)), integral_congr_ae (ae_of_all _ key), hγ']
  exact hF6b F I Gf ι D k a hH T hT (δ0 * γ.out * δ0⁻¹) (δ • ω) h01 h10 _ hβ' hint'

-- === Fhyp ===

theorem pf_Fhyp : C4 → E0a → KernelTermsInvariantBounded → E0d → E2 → E3 → Ecut → Fsum → F5 → F6 → Fhyp := by
  intro hC4 hE0a _ _ hE2 hE3 hEcut hFsum hF5 hF6 F I Gf ι _ _ _ _ D k a hyp b hb hint
  have hax := hyp.ax
  obtain ⟨hcnt, hsf, hpres, -⟩ := hE0a F I Gf D hax
  obtain ⟨-, hE2'⟩ := hE2 F I Gf ι D k a hyp
  have hb3 := hE3 F I Gf D hax b hb
  obtain ⟨C, hC⟩ := hF5 F I Gf ι D k a hyp
  have : Countable (PG F) := hcnt; have : Countable D.Cj := hcnt; have : Countable D.Om := hax.cO
  have hbI : Integrable b D.μY := ⟨hb.meas.aestronglyMeasurable, (lintegral_congr fun y => Real.enorm_eq_ofReal (hb.nonneg y)).trans_lt hb3⟩
  let uT (T : ℝ) (γ : PG F) (y : D.Y) : ℂ := if IsEll γ then 0 else (D.LamF T γ).indicator (D.kk k a γ) y
  have hsumle T (hT : 1 < T) y (hy : y ∉ D.abelian₂ T) : ∑' γ, ‖uT T γ y‖ₑ ≤ C :=
    (ENNReal.tsum_le_tsum fun γ => by dsimp only [uT]; split_ifs <;> simp).trans ((hC T hT y).2 hy)
  have hon T (hT : 1 < T) y (hy : y ∈ D.abelian₂ T) γ : uT T γ y = if IsEll γ then 0 else D.kk k a γ y := by
    dsimp only [uT]; split_ifs; rfl; exact indicator_of_mem ((hC T hT y).1 hy γ) _
  have step1 T (hT : 1 < T) : Integrable (fun y => b y • ∑' γ, uT T γ y) D.μY ∧ ∫ y, b y • ∑' γ, uT T γ y ∂D.μY = 0 := by
    obtain ⟨CT, hCT⟩ := hE2' T
    have hfin : ∫⁻ y, oR (b y) * ∑' γ, ‖uT T γ y‖ₑ ∂D.μY < ∞ := by
      have hle y : ∑' γ, ‖uT T γ y‖ₑ ≤ (CT : ℝ≥0∞) + C := by
        by_cases hy : y ∈ D.abelian₂ T
        · exact ((ENNReal.tsum_le_tsum fun γ => by dsimp only [uT]; split_ifs; simp; rw [indicator_apply]; split_ifs <;> simp).trans (hCT y hy)).trans le_self_add
        · exact (hsumle T hT y hy).trans le_add_self
      exact ((lintegral_mono fun y => by gcongr; exact hle y).trans_eq (lintegral_mul_const' _ _ (by simp))).trans_lt (ENNReal.mul_lt_top hb3 (by simp))
    obtain ⟨hb', hFs⟩ := hFsum F I Gf D hax b hb
    obtain ⟨hm', hi', hiY, heq⟩ := hFs (uT T) (fun γ => by by_cases h : IsEll γ <;> simp [uT, h, (meas_kk D k a hyp γ).indicator (meas_lamF D hax T γ)]) hfin
    refine ⟨hiY, heq.trans ?_⟩
    obtain ⟨f, -, -, hR⟩ := orbit_reps (G := PG F) (α := D.Cj × D.Om)
    choose β hβ using fun r : D.Cj × D.Om => (hEcut F I Gf D hax).2 r.2 (stabilizer (PG F) r) fun g hg => congrArg Prod.snd (mem_stabilizer_iff.1 hg)
    have hinv' (g : PG F) (p : (D.Cj × D.Om) × D.Xs) : uT T (D.el (g • p).1.1) ((g • p).1.2, (g • p).2) = uT T (D.el p.1.1) (p.1.2, p.2) := by
      rcases p with ⟨⟨γ, ω⟩, z⟩; show uT T (g * D.el γ * g⁻¹) (g • ((ω, z) : D.Y)) = uT T (D.el γ) (ω, z)
      dsimp only [uT]; rw [isEll_conj]; split_ifs; rfl
      rw [indicator_apply, indicator_apply, kk_conj D k a hyp]
      have hL : g • ((ω, z) : D.Y) ∈ D.LamF T (g * D.el γ * g⁻¹) ↔ ((ω, z) : D.Y) ∈ D.LamF T (D.el γ) :=
        ⟨fun h => by have := lamF_smul D hax T _ g⁻¹ _ h; rwa [inv_smul_smul, show g⁻¹ * (g * D.el γ * g⁻¹) * g⁻¹⁻¹ = D.el γ by group] at this, lamF_smul D hax T _ g _⟩
      simp only [hL]
    obtain ⟨hI, hS⟩ := hC4 (PG F) (D.Cj × D.Om) D.Xs volume hpres _ hb' _ hm' hinv' hi' (range f) hR β fun r _ => hβ r
    have hz (r : range f) : ∫ x, β r x • uT T (D.el r.1.1) (r.1.2, x) = 0 := by
      by_cases he : IsEll (D.el r.1.1)
      · simp [uT, he]
      · simp only [uT, he, ite_false]
        exact hF6 F I Gf ι D k a hyp T hT (D.el r.1.1) r.1.2 he (β r.1) (hβ r.1) (by simpa only [uT, he, ite_false] using hI r.1 r.2)
    simp only [hz] at hS; exact hS.unique hasSum_zero
  have hT2 (n : ℕ) : (1 : ℝ) < (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
  have hlim : Tendsto (fun n : ℕ => ∫ y, b y • ∑' γ, uT ((n : ℝ) + 2) γ y ∂D.μY) atTop
      (𝓝 (∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY)) :=
    tendsto_integral_of_dominated_convergence (fun y => ‖b y • ∑' γ : PG F, (if IsEll γ then 0 else D.kk k a γ y)‖ + b y * C)
      (fun n => (step1 _ (hT2 n)).1.aestronglyMeasurable) (hint.norm.add (hbI.mul_const _))
      (fun n => ae_of_all _ fun y => by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (hb.nonneg y), ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (hb.nonneg y)
        by_cases hy : y ∈ D.abelian₂ ((n : ℝ) + 2)
        · rw [tsum_congr (hon _ (hT2 n) y hy)]; exact le_add_of_nonneg_right C.2
        · exact (by simpa using ENNReal.toReal_mono ENNReal.coe_ne_top (enorm_tsum_le_tsum_enorm.trans (hsumle _ (hT2 n) y hy)) : ‖∑' γ, uT ((n : ℝ) + 2) γ y‖ ≤ C).trans (le_add_of_nonneg_left (norm_nonneg _)))
      (ae_of_all _ fun y => by
        obtain ⟨T₀, hT₀⟩ := htY_bdd D hax y; obtain ⟨N, hN⟩ := exists_nat_ge T₀
        exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => by
          dsimp only; rw [tsum_congr (hon _ (hT2 n) y (hT₀ _ (by have : (N : ℝ) ≤ n := (by exact_mod_cast hn); linarith)))]⟩))
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (step1 _ (hT2 n)).2.symm))

-- === TF: Final Trace Formula ===

theorem pf_TF : E2 → Ecut → E6 → Fell → Fhyp → TF := by
  intro hE2 hcut hE6 hFell hFhyp F I Gf _ _ _ D hAx ι _ a
  obtain ⟨S, hFam, hS⟩ := hFell F I Gf D hAx ι a
  refine ⟨S, hFam, fun k hH hfd h => ?_⟩
  obtain ⟨⟨b, hb⟩, -⟩ := hcut F I Gf D hAx
  obtain ⟨hi, htr⟩ := hE6 F I Gf ι D k a hH hfd h b hb
  obtain ⟨hie, hge⟩ := hS k hH b hb
  have hsplit y : ∑' γ : PG F, D.kk k a γ y = (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) + ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y := by
    have hf := (hE2 F I Gf ι D k a hH).1 y
    rw [← Summable.tsum_add (Summable.of_norm_bounded hf fun _ => by split_ifs <;> simp) (Summable.of_norm_bounded hf fun _ => by split_ifs <;> simp)]
    exact tsum_congr fun _ => by split_ifs <;> simp
  have hih : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY :=
    (hi.sub hie).congr (ae_of_all _ fun y => by simp only [Pi.sub_apply]; rw [hsplit y, smul_add, add_sub_cancel_left])
  rw [htr, ← hge, show (fun y => b y • ∑' γ : PG F, D.kk k a γ y) = fun y => b y • (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y from funext fun y => by rw [hsplit y, smul_add],
    integral_add hie hih, hFhyp F I Gf ι D k a hH b hb hih, add_zero]

end UpperTheory.Esk
