import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
-- This proof follows the approach visible in the public code of attempt 103322 by Vladyslav Larin (rh-board.pages.dev), shortened by our team.
-- Derived from Mikko Nyman et al., submission #103701, and Fortytwo, #103322. The verifier supervisor tested the proof changes.

open NumberField IsDedekindDomain MeasureTheory Measure Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
  GroundTheory.Global
  GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.Reduction PositivityTheory.Rg.Rs
  PositivityTheory.Affgl.CT Real MeasurableSpace InfinitePlace Complex PositivityTheory.Rg.Rs.An

theorem AlpogeRHCore40.residualSpectrumConstantTermDict : Dict := by
  intro E _ _ _ N
  have pExp (u : ℝ) : posIdele (K := E) (exp u) (exp_pos u) = infId E (expU fun _ => (u : ℂ)) := by
    refine Units.ext $ Prod.ext ?_ ?_
    change _ = 1 - infEq E 1 + infEq E _
    simp
    funext w
    rw [← IdeleGroup.coe_infiniteProj, infiniteProj_posIdele]
    change posRealElem w _ = _
    simp [posRealElem, not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w),
      mult, sqrt_sq (exp_pos u).le, expU, ofReal_exp, infEq]
    rfl
    change _ = 1 - 0 + 0
    simp
    exact FiniteAdeleRing.ext _ $ posIdele_finite _ _
  have hdiag (f : _) (M : _)
      (hM : M.1 = diagonal fun i _ => cexp (f i)) : infGL E N M = tor E f := by
    have entry A : matN N (sInf E) A = A.map _ := rfl
    ext i j
    simp only [tor, coe_diagUnits, pExp]
    by_cases h : i = j <;> simp [infGL, cornerGL, corner, entry, hM, infId, h, expU]
  have htor t : splitCentre E N t = tor E fun _ => t :=
    hdiag _ _ rfl
  refine ⟨fun r t => hdiag _ _ $ congrArg diagonal $ by ext i; split_ifs <;> simp,
    htor, by
      unfold latticeGL lat
      rw [htor]
      rfl,
    fun φ hφ r _ _ => ?_⟩
  have hpi : (pi : MeasurableSpace (BlockIx N r → Ad E)) = borel _ :=
      BorelSpace.measurable_eq
  set ν := unipMeasure E N r
  set D := unipFundamentalDomain E N r
  have hunip (X : UPos N r → Ad E) : unipGL X = unip X := Units.ext rfl
  unfold IsCT
  rw [← hpi]
  refine ⟨⟨ν, D, inferInstance, isAddFundamentalDomain_unipFundamentalDomain, by ext g; simp [ct, ctn, measureReal_def, unipMeasure_unipFundamentalDomain, constantTerm, hunip, D, ν]⟩,
    fun F ⟨μ, 𝓕, hμ, h𝓕, hF⟩ => ?_⟩
  subst hF
  set s := addHaarScalarFactor μ ν
  have e : μ = s • ν := isAddLeftInvariant_eq_smul μ ν
  have hc := (addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne'
  refine ⟨s, by exact_mod_cast hc, funext fun g => ?_⟩
  simp [ct, e, restrict_smul, integral_smul_nnreal_measure, ← hunip, NNReal.smul_def,
    real_smul, ctn, measureReal_def, unipMeasure_unipFundamentalDomain,
    constantTerm_eq_setIntegral hφ.left (h𝓕.mono $ e ▸ absolutelyContinuous_smul $ by exact_mod_cast hc) g, ν]
