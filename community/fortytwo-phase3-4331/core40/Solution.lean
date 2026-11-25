import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
-- Adapted from Fortytwo, Osgood001/riemann-hypothesis PR #19 (a2e6aed);
-- earlier attempts include Vladyslav Larin / Fortytwo #103322, Mikko Nyman
-- et al. #103701, and Larin #104025. The new torus identity below removes
-- the separate positive-idèle, diagonal-matrix, split-centre and lattice proofs.
open NumberField MeasureTheory Measure Matrix GlobalTheory CuspRep UnitaryBC GroundTheory Global
  Automorphic AutomorphicForm Reduction PositivityTheory Rg.Rs Affgl.CT An Real InfinitePlace Complex

theorem AlpogeRHCore40.residualSpectrumConstantTermDict : Dict := by
  unfold Dict
  intros
  expose_names
  have torEq (f : Fin N → ℝ) :
      tor E f = infGL E N (diagUnits N fun i => expU fun _ => f i) := by
    ext1
    change diagonal _ = 1 - Matrix.map 1 (CuspRep.sInf E) + (diagonal _).map _
    ext1 i j
    by_cases e : i = j <;> simp [e]
    apply Prod.ext
    -- Infinite coordinates use the complex exponential; the finite coordinates are one.
    change _ = 1 - infEq _ 1 + _
    simp
    funext w
    simp [← IdeleGroup.coe_infiniteProj, infiniteProj_posIdele, posRealToUnits, posRealElem, ← not_isComplex_iff_isReal, IsTotallyComplex.isComplex,
      sqrt_sq_eq_abs, expU, ofReal_exp]
    rfl
    change _ = 1 - 0 + 0
    ext v
    simp [posIdele_finite]
  simp only [aT, aR, lat, torEq]
  refine ⟨fun r t => by
      congr 2
      ext1
      apply congrArg diagonal
      ext i
      simp +contextual [expU, apply_ite],
    fun _ => rfl, rfl, fun φ hφ r _ _ => ?_⟩
  -- Normalized volume is one; every other Haar measure is a positive multiple.
  set ν := unipMeasure E N r
  have hunip X : @unipGL N r (Ad E) _ X = unip X := Units.ext rfl
  unfold ctn
  simp [measureReal_def, unipMeasure_unipFundamentalDomain]
  unfold IsCT
  rw [← BorelSpace.measurable_eq (α := BlockIx N r → Ad E)]
  refine ⟨⟨ν, _, inferInstance, isAddFundamentalDomain_unipFundamentalDomain, by
    ext g
    simp [ct, constantTerm, hunip, ν]⟩, ?_⟩
  rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
  refine ⟨addHaarScalarFactor μ ν, by exact_mod_cast (addHaarScalarFactor_pos_of_isAddHaarMeasure ..).ne',
    funext fun g => ?_⟩
  rw [constantTerm_eq_setIntegral hφ.left (h𝓕.mono $ absolutelyContinuous_isAddHaarMeasure ν μ) g]
  unfold ct
  nth_rw 1 [isAddLeftInvariant_eq_smul μ ν]
  simp [hunip, ν]
  rfl
