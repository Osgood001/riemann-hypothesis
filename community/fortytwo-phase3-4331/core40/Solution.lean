import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
-- Adapted from Fortytwo, Osgood001/riemann-hypothesis PR #19 (a2e6aed);
-- earlier attempts include Vladyslav Larin / Fortytwo #103322, Mikko Nyman
-- et al. #103701, and Larin #104025. The new torus identity below removes
-- the separate positive-idèle, diagonal-matrix, split-centre and lattice proofs.
open NumberField MeasureTheory Measure Matrix GlobalTheory CuspRep UnitaryBC GroundTheory Global
  Automorphic AutomorphicForm Reduction PositivityTheory Rg.Rs Affgl.CT An Real InfinitePlace Complex

theorem AlpogeRHCore40.residualSpectrumConstantTermDict : Dict := by
  intro E _ _ _ N
  have torEq (f : Fin N → ℝ) :
      tor E f = infGL E N (diagUnits N fun i => expU fun _ => (f i : ℂ)) := by
    apply Units.ext
    change diagonal _ = 1 - Matrix.map 1 (CuspRep.sInf E) + (diagonal _).map _
    simp only [← diagonal_one, diagonal_map (map_zero _), diagonal_sub, diagonal_add]
    congr 1
    funext i
    apply Prod.ext
    -- Infinite coordinates use the complex exponential; the finite coordinates are one.
    change _ = 1 - infEq E 1 + infEq E _
    simp
    funext w
    rw [← IdeleGroup.coe_infiniteProj, infiniteProj_posIdele]
    simp [posRealToUnits, posRealElem, not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w),
      mult, sqrt_sq (exp_pos _).le, expU, ofReal_exp, infEq]
    rfl
    change _ = 1 - 0 + 0
    ext v
    simp [posIdele_finite]
  simp only [aT, aR, lat, torEq]
  refine ⟨fun r t => by
      congr 2
      apply Units.ext
      apply congrArg diagonal
      ext i
      simp +contextual [expU, apply_ite],
    fun _ => rfl, rfl, fun φ hφ r _ _ => ?_⟩
  -- Normalized volume is one; every other Haar measure is a positive multiple.
  set ν := unipMeasure E N r
  have hunip (X : UPos N r → Ad E) : unipGL X = unip X := Units.ext rfl
  unfold ctn
  simp [measureReal_def, unipMeasure_unipFundamentalDomain]
  unfold IsCT
  rw [← BorelSpace.measurable_eq (α := BlockIx N r → Ad E)]
  refine ⟨⟨ν, _, inferInstance, isAddFundamentalDomain_unipFundamentalDomain, by
    ext g
    simp [ct, constantTerm, hunip, ν]⟩, ?_⟩
  rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
  refine ⟨addHaarScalarFactor μ ν, by exact_mod_cast (addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne',
    funext fun g => ?_⟩
  unfold ct
  conv_lhs => rw [isAddLeftInvariant_eq_smul μ ν]
  simp [restrict_smul, integral_smul_nnreal_measure, ← hunip, NNReal.smul_def, real_smul,
    constantTerm_eq_setIntegral hφ.left (h𝓕.mono $ absolutelyContinuous_isAddHaarMeasure ν μ) g, ν]
