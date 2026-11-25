module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.general_b_fact_second_bis_form

theorem goal1 :
  ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Complex E]
  [inst_2 : NormedAddCommGroup.{u_2} F] [inst_3 : NormedSpace.{0, u_2} Complex F] {f : E → F} {y : E} {δ M : Real},
  LT.lt.{0} 0 δ →
    DifferentiableOn.{0, u_1, u_2} Complex f (Metric.ball.{u_1} y δ) →
      (∀ (z : E), Membership.mem.{u_1, u_1} (Metric.ball.{u_1} y δ) z → LE.le.{0} (Norm.norm.{u_2} (f z)) M) →
        LE.le.{0} (Norm.norm.{max u_2 u_1}
          (@fderiv.{0, u_1, u_2} Complex Complex.instDenselyNormedField.toNontriviallyNormedField
            E inst.toAddCommGroup inst_1.toModule
            inst.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
            F inst_2.toAddCommGroup inst_3.toModule
            inst_2.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace f y))
          (HDiv.hDiv.{0, 0, 0} M δ) := by
  intro E F _ _ _ _ f y δ M hδ hf hM
  let reflect : E → E := fun z => y + (y - z)
  have hcenter : reflect y = y := by simp [reflect]
  have hreflect : Set.MapsTo reflect (Metric.ball y δ) (Metric.ball y δ) := by
    intro z hz
    simpa only [Metric.mem_ball, dist_eq_norm, reflect, add_sub_cancel_left, norm_sub_rev y z]
      using hz
  -- The odd part about y has the same derivative at y and is bounded by M.
  let g : E → F := fun z => (1 / 2 : ℂ) • (f z - f (reflect z))
  have hr : HasFDerivAt reflect (-ContinuousLinearMap.id ℂ E) y :=
    ((hasFDerivAt_id y).const_sub y).const_add y
  have hfy := (hf.differentiableAt (Metric.ball_mem_nhds y hδ)).hasFDerivAt
  have hfr : HasFDerivAt (f ∘ reflect) (-fderiv ℂ f y) y := by
    have h : HasFDerivAt f (fderiv ℂ f y) (reflect y) := hcenter.symm ▸ hfy
    simpa only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] using h.comp y hr
  have hg : HasFDerivAt g (fderiv ℂ f y) y := by
    change HasFDerivAt ((1 / 2 : ℂ) • (f - f ∘ reflect)) (fderiv ℂ f y) y
    simpa [sub_neg_eq_add, ← two_smul ℂ, smul_smul] using
      (hfy.sub hfr).const_smul (1 / 2 : ℂ)
  have hdiff : DifferentiableOn ℂ g (Metric.ball y δ) :=
    (hf.sub (hf.comp (by fun_prop) hreflect)).const_smul _
  have hgcenter : g y = 0 := by simp [g, hcenter]
  have hmaps : Set.MapsTo g (Metric.ball y δ) (Metric.closedBall (g y) M) := by
    intro z hz
    rw [hgcenter, Metric.mem_closedBall, dist_zero_right]
    dsimp [g]
    rw [norm_smul, norm_div, norm_one, Complex.norm_two]
    linarith only [norm_sub_le (f z) (f (reflect z)), hM z hz, hM _ (hreflect hz)]
  simpa only [hg.fderiv] using Complex.norm_fderiv_le_div_of_mapsTo_ball hdiff hmaps hδ

end Bl.general_b_fact_second_bis_form
