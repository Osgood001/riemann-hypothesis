module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajAtAddRight

@[expose] public section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology

namespace GlobalTheory.CovTop.Assembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tendsto_exp_mul_rpow {c : ℝ} (hc : 0 < c) (A : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-(x ^ c)) * x ^ A) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / c) 1 one_pos).comp (tendsto_rpow_atTop hc)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp]
  rw [← Real.rpow_mul hx, mul_div_cancel₀ _ hc.ne', mul_comm, neg_mul, one_mul]

theorem exists_loss_le {c : ℝ} (hc : 0 < c) (A B C : ℝ) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → 12 * Real.exp (-(x ^ c)) * (x ^ A + x ^ B + C) ≤ 1 := by
  have h := ((((tendsto_exp_mul_rpow hc A).add (tendsto_exp_mul_rpow hc B)).add
    ((tendsto_exp_mul_rpow hc 0).mul_const C)).const_mul 12)
  have h1 : (12 : ℝ) * (0 + 0 + 0 * C) < 1 := by norm_num
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds h1))
  refine ⟨x0, fun x hx => ?_⟩
  have := hx0 x hx
  simp only [Real.rpow_zero] at this
  nlinarith

/-- The finite-scale bad-rank penalty tends to zero for arbitrary polynomial growth exponents. -/
theorem tendsto_covol_loss {c : ℝ} (hc : 0 < c) (A B C : ℝ) :
    Tendsto (fun x : ℝ => let δ := Real.exp (-(x ^ c))
      3 * δ / (1 - 3 * δ) * (x ^ A + x ^ B + C)) atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-(x ^ c))) atTop (𝓝 0) := by
    simpa using tendsto_exp_mul_rpow hc 0
  have hn := (((tendsto_exp_mul_rpow hc A).add (tendsto_exp_mul_rpow hc B)).add (he.mul_const C)).const_mul 3
  have hd := (tendsto_const_nhds (x := (1 : ℝ))).sub (he.const_mul 3)
  have h := hn.div hd (by norm_num)
  simp only [mul_zero, add_zero, zero_mul, sub_zero, zero_div] at h
  apply h.congr'
  filter_upwards with x
  dsimp
  ring

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

/-- The numerator and denominator are the actual bad and good ranks. When the bad rank
is zero the projection costs nothing. No smallness assumption on the bad fraction is needed. -/
theorem lcv_le_of_rank {C1 C2 : ℝ}
    (hG : GramAt p i) (hR : RecAt p i) (hC : CutAt p i)
    (hK : CoreAt p i C1) (hW : LowAt p i C2) :
    let good := Formalism.HN.rkK (latGood p.R.toRealDat p.F.lv2 i)
    let bad := Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i)
    let T := mainT p i + (C1 + C2) * unitE p
    good + bad = Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) ∧
      Formalism.DivisionValues.lcv ((p.S false).XW i) ((p.S false).M i) / ((p.S false).D : ℝ) ≤
        T + ((bad : ℝ) / good) * (slopeMax_sq (nrmR p.R.toRealDat i) (latAll p.R.toRealDat i) + 2 * Real.log (Fintype.card p.P.Gp) + T) := by
  have : IsTotallyComplex D.what₂.LL := D.tcLL
  obtain ⟨g1, g2, g3, -⟩ := hG
  obtain ⟨c1, c2, c3, -⟩ := hC
  have cut := GlobalTheory.CutNum.slope_good_ge_of_rank D.what₂.LL _ (nrmR p.R.toRealDat i)
    (latType p.R.toRealDat p.F.lv2 i) (latAll p.R.toRealDat i) (eGood p.R.toRealDat i)
    (Fintype.card p.P.Gp) g1 g2 inf_le_left g3 c1 c2 Fintype.card_pos c3
  refine ⟨cut.1, ?_⟩
  let μ := slope_sq (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i)
  let ρ := (Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) : ℝ) / Formalism.HN.rkK (latGood p.R.toRealDat p.F.lv2 i)
  let A := slopeMax_sq (nrmR p.R.toRealDat i) (latAll p.R.toRealDat i) + 2 * Real.log (Fintype.card p.P.Gp)
  let T := mainT p i + (C1 + C2) * unitE p
  have hmu : -μ ≤ T := by
    unfold CoreAt at hK
    unfold LowAt at hW
    dsimp [μ, T]
    linarith
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  calc
    _ ≤ -(μ - ρ * (A - μ)) := hR.trans (neg_le_neg cut.2)
    _ = -μ + ρ * (A - μ) := by ring
    _ ≤ T + ρ * (A + T) := add_le_add hmu (mul_le_mul_of_nonneg_left (by linarith only [hmu]) hρ)

private theorem rank_ratio_le {dg db δ : ℝ} (hg : 0 ≤ dg) (hδ : 0 ≤ δ) (hlt : δ < 1 / 3)
    (hb : db ≤ 3 * δ * (dg + db)) : db / dg ≤ 3 * δ / (1 - 3 * δ) := by
  have hd : 0 < 1 - 3 * δ := by linarith
  rcases hg.eq_or_lt with rfl | hg
  · rw [div_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hδ) hd.le
  · rw [div_le_div_iff₀ hg hd]
    linarith only [hb]

/-- The bad-rank estimate yields a finite, exponentially small covolume error, with
no ceiling to a whole unit. The denominator only needs the bad fraction to be below one. -/
theorem lcv_le_of_bad_fraction {A B PP C1 C2 : ℝ} (hx : 0 < L.sc.x) (h12 : 0 ≤ C1 + C2)
    (hδ : Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) < 1 / 3)
    (hG : GramAt p i) (hR : RecAt p i) (hC : CutAt p i) (hB : BadAt p i) (hL : LamAt p i A)
    (hS : SizeAt p i PP B) (hK : CoreAt p i C1) (hW : LowAt p i C2) :
    let δ := Real.exp (-(L.sc.x ^ (L.sc.ez / 7)))
    Formalism.DivisionValues.lcv ((p.S false).XW i) ((p.S false).M i) / ((p.S false).D : ℝ) ≤
      mainT p i + (C1 + C2 + (3 * δ / (1 - 3 * δ)) * (L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1))) * unitE p := by
  obtain ⟨hr, hv⟩ := lcv_le_of_rank p i hG hR hC hK hW
  let δ := Real.exp (-(L.sc.x ^ (L.sc.ez / 7)))
  let R := (Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) : ℝ) / Formalism.HN.rkK (latGood p.R.toRealDat p.F.lv2 i)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hRδ : R ≤ 3 * δ / (1 - 3 * δ) := by
    apply rank_ratio_le (Nat.cast_nonneg _) (Real.exp_nonneg _) hδ
    unfold BadAt at hB
    rw [← hr, Nat.cast_add] at hB
    exact hB
  obtain ⟨h1, h2, -, hT, -⟩ := hS
  have hE : 0 ≤ unitE p := by linarith
  have hA := (Real.rpow_pos_of_pos hx A).le
  have hB' := (Real.rpow_pos_of_pos hx B).le
  have hmax := hL.trans (mul_le_mul_of_nonneg_left h2 hA)
  have hm := (abs_le.mp hT).2.trans (mul_le_mul_of_nonneg_left h2 hB')
  have hg := hC.2.2.2.trans h2
  let T := mainT p i + (C1 + C2) * unitE p
  let Q := (L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p
  have hQ : 0 ≤ Q := mul_nonneg (by linarith only [hA, hB', h12]) hE
  have hp : slopeMax_sq (nrmR p.R.toRealDat i) (latAll p.R.toRealDat i) + 2 * Real.log (Fintype.card p.P.Gp) + T ≤ Q := by
    dsimp [T, Q]
    linarith only [hg, hmax, hm]
  calc
    _ ≤ _ := hv
    _ ≤ T + R * Q := add_le_add_right (mul_le_mul_of_nonneg_left hp hR0) _
    _ ≤ T + (3 * δ / (1 - 3 * δ)) * Q := add_le_add_right (mul_le_mul_of_nonneg_right hRδ hQ) _
    _ = _ := by dsimp [T, Q, δ]; ring

theorem lcv_le {A B PP C1 C2 : ℝ} (hx : 0 < L.sc.x) (h1 : 0 ≤ C1) (h2 : 0 ≤ C2)
    (hs : 12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * (L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) ≤ 1)
    (hG : GramAt p i) (hR : RecAt p i) (hC : CutAt p i) (hB : BadAt p i) (hL : LamAt p i A) (hS : SizeAt p i PP B)
    (hK : CoreAt p i C1) (hW : LowAt p i C2) :
    Formalism.DivisionValues.lcv ((p.S false).XW i) ((p.S false).M i) / ((p.S false).D : ℝ) ≤ mainT p i + (C1 + C2 + 1) * unitE p := by
  let δ := Real.exp (-(L.sc.x ^ (L.sc.ez / 7)))
  let Q := L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    linarith [Real.rpow_pos_of_pos hx A, Real.rpow_pos_of_pos hx B]
  have hδ : 0 ≤ δ := Real.exp_nonneg _
  have hsmall : 12 * δ ≤ 1 := (le_mul_of_one_le_right (by positivity) hQ).trans hs
  have hCoef : 3 * δ / (1 - 3 * δ) ≤ 12 * δ := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - 3 * δ)).mpr
    nlinarith [mul_nonneg hδ (show 0 ≤ 1 - 12 * δ by linarith)]
  have hfin := lcv_le_of_bad_fraction p i hx (add_nonneg h1 h2) (show δ < 1 / 3 by linarith)
    hG hR hC hB hL hS hK hW
  have hR1 := (mul_le_mul_of_nonneg_right hCoef (zero_le_one.trans hQ)).trans hs
  have hE : 0 ≤ unitE p := zero_le_one.trans (hS.1.trans hS.2.1)
  exact hfin.trans (add_le_add_right (mul_le_mul_of_nonneg_right (add_le_add_right hR1 (C1 + C2)) hE) _)

end GlobalTheory.CovTop.Assembly

end
