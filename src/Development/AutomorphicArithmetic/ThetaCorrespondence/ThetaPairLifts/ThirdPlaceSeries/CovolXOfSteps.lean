module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology
namespace GlobalTheory.CovTop.Assembly
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
/-- The covolume bound with the geometric constants kept fixed. The rank-cut penalty
decays to zero, is uniform in the point and weight, and is not rounded up to one. -/
theorem covolX_with_decaying_error (hG : GlobalTheory.CovTop.GramCondition)
    (hR : GlobalTheory.CovTop.LiftRecursive) (hC : GlobalTheory.CovTop.LiftTruncation)
    (hB : GlobalTheory.CovTop.LiftBadSet) (hL : GlobalTheory.CovTop.LiftLambdaBound)
    (hS : GlobalTheory.CovTop.SizeCondition) :
    Closed FamHyp fun Fm CH => ∃ A B : ℝ, ∀ C1 C2 : ℝ, 0 ≤ C1 + C2 →
      EventuallyAtAllPoints Fm (fun _ _ _ p => ∀ i, CoreAt p i C1) →
      EventuallyAtAllPoints Fm (fun _ _ _ p => ∀ i, LowAt p i C2) →
      EventuallyAtAllPoints Fm fun x _ _ p => ∀ C : ℝ,
        (let δ := Real.exp (-(x ^ (Fm.ez / 7)))
         C1 + C2 + 3 * δ / (1 - 3 * δ) * (x ^ A + x ^ B + (C1 + C2 + 1))) ≤ C →
        (p.S false).L3 (p.N C CH) := by
  refine Closed.imp (Closed.and (Closed.and (Closed.and hG hR) (Closed.and hC hB)) (Closed.and hL hS)) ?_
  rintro eps Fm CH he ⟨⟨⟨⟨_, -, g⟩, ⟨_, -, r⟩⟩, ⟨⟨_, -, c⟩, ⟨_, -, b⟩⟩⟩, ⟨A, -, l⟩, ⟨B, -, s⟩⟩
  refine ⟨A, B, fun C1 C2 h12 k w => ?_⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  have hδ : Tendsto (fun x : ℝ => Real.exp (-(x ^ (Fm.ez / 7)))) atTop (𝓝 0) := by
    simpa using tendsto_exp_mul_rpow (show 0 < Fm.ez / 7 by positivity) 0
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp (hδ.eventually_lt_const (show (0 : ℝ) < 1 / 3 by norm_num))
  obtain ⟨x1, h⟩ := (((g.and r).and (c.and b)).and ((l.and s).and (k.and w)))
  refine ⟨max x0 x1, fun x hx hle ι p hp C hC i => ?_⟩
  obtain ⟨⟨⟨g, r⟩, c, b⟩, ⟨l, s⟩, k, w⟩ := h x hx ((le_max_right _ _).trans hle) ι p hp
  have hx' : 0 < x := (zero_lt_one.trans Fm.one_lt_family_threshold).trans hx
  have ex := Fm.L_x x ι hx
  have ee := Fm.L_ez x ι
  have main := lcv_le_of_bad_fraction p i (ex.symm ▸ hx') h12
    (by rw [ex, ee]; exact hx0 x ((le_max_left _ _).trans hle))
    (g i) (r i) (c i) (b i) (l i) (s i) (k i) (w i)
  have hE : 0 ≤ unitE p := zero_le_one.trans ((s i).1.trans (s i).2.1)
  refine main.trans ?_
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ hE
  simpa only [ex, ee] using hC

/-- For the specified core and lower-bound constants, every positive margin suffices
eventually. No universal unit of slack needs to be reserved. -/
theorem covolX_with_margin (hG : GlobalTheory.CovTop.GramCondition)
    (hR : GlobalTheory.CovTop.LiftRecursive) (hC : GlobalTheory.CovTop.LiftTruncation)
    (hB : GlobalTheory.CovTop.LiftBadSet) (hL : GlobalTheory.CovTop.LiftLambdaBound)
    (hS : GlobalTheory.CovTop.SizeCondition) :
    Closed FamHyp fun Fm CH => ∀ C1 C2 : ℝ, 0 ≤ C1 + C2 →
      EventuallyAtAllPoints Fm (fun _ _ _ p => ∀ i, CoreAt p i C1) →
      EventuallyAtAllPoints Fm (fun _ _ _ p => ∀ i, LowAt p i C2) → ∀ η : ℝ, 0 < η →
      EventuallyAtAllPoints Fm fun _ _ _ p => ∀ C : ℝ, C1 + C2 + η ≤ C → (p.S false).L3 (p.N C CH) := by
  refine Closed.imp (covolX_with_decaying_error hG hR hC hB hL hS) ?_
  rintro eps Fm CH he ⟨A, B, h⟩ C1 C2 h12 k w η hη
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp ((tendsto_covol_loss (show 0 < Fm.ez / 7 by positivity)
    A B (C1 + C2 + 1)).eventually_lt_const hη)
  obtain ⟨x1, hx1⟩ := h C1 C2 h12 k w
  refine ⟨max x0 x1, fun x hx hle ι p hp C hC => ?_⟩
  apply hx1 x hx ((le_max_right _ _).trans hle) ι p hp C
  exact (add_le_add_right (hx0 x ((le_max_left _ _).trans hle)).le (C1 + C2)).trans hC


theorem covolX_of_lift_bounds_and_coreLe : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive → _root_.GlobalTheory.CovTop.LiftTruncation → _root_.GlobalTheory.CovTop.LiftBadSet → _root_.GlobalTheory.CovTop.LiftLambdaBound → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoreBound' → _root_.GlobalTheory.CovTop.LiftLowBound → _root_.GlobalTheory.CovTop.CovolumeBoundOfX := by
  intro hG hR hC hB hL hS hK hW
  refine Closed.imp (Closed.and (covolX_with_margin hG hR hC hB hL hS) (Closed.and hK hW)) ?_
  rintro eps Fm CH he ⟨h, ⟨C1, h1, k⟩, ⟨C2, h2, w⟩⟩
  exact ⟨C1 + C2 + 1, by linarith, h C1 C2 (add_nonneg h1 h2) k w 1 zero_lt_one⟩

end GlobalTheory.CovTop.Assembly
end
end
