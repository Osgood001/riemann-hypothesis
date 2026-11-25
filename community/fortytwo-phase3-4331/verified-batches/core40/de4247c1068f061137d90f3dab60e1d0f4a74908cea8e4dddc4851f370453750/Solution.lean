import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
-- Adapted from Fortytwo, Osgood001/riemann-hypothesis PR #19 (a2e6aed);
-- earlier attempts include Vladyslav Larin / Fortytwo #103322, Mikko Nyman
-- et al. #103701, and Larin #104025. The new torus identity below removes
-- the separate positive-idèle, diagonal-matrix, split-centre and lattice proofs.
-- Renxiu Song, public Playground attempt 107132, diagonal transport and Haar normalization.
open NumberField MeasureTheory Measure Matrix GlobalTheory CuspRep GroundTheory Global Automorphic AutomorphicForm Reduction PositivityTheory Rg.Rs Affgl.CT An Real InfinitePlace Complex

theorem AlpogeRHCore40.residualSpectrumConstantTermDict : Dict := by
  unfold Dict
  intros
  expose_names
  have torEq f :
      tor E f = infGL E N (diagUnits N fun i => expU fun _ => f i) := by
    apply ga_ext <;> simp
    · ext1
      change (diagonal _).map _ = _
      rw [diagonal_map (map_zero _)]
      congr 1
      funext i
      apply (infEq E).symm_apply_eq.mpr
      funext w
      change (_ : Ad E).1 w = _
      simp [← IdeleGroup.coe_infiniteProj, infiniteProj_posIdele, posRealToUnits, posRealElem,
        ← not_isComplex_iff_isReal, IsTotallyComplex.isComplex, sqrt_sq_eq_abs, expU, ofReal_exp]
      rfl
    · apply prodEquiv_diagUnits_posIdele_snd
  simp only [aT, aR, lat, torEq]
  refine ⟨fun r t => by
      congr 2
      ext1
      apply congrArg diagonal
      ext i
      simp +contextual [expU, apply_ite],
    fun _ => rfl, rfl, ?_⟩
  intro φ hφ r _ _
  -- Normalized volume is one; every other Haar measure is a positive multiple.
  set ν := unipMeasure E N r
  have hunip : @unipGL N r (Ad E) _ = unip := by ext; rfl
  unfold ctn
  simp [measureReal_def, unipMeasure_unipFundamentalDomain]
  unfold IsCT
  rw [← BorelSpace.measurable_eq]
  refine ⟨⟨ν, _, inferInstance, isAddFundamentalDomain_unipFundamentalDomain, by
    ext g
    simp [ct, constantTerm, hunip, ν]⟩, ?_⟩
  rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
  refine ⟨addHaarScalarFactor μ ν, by exact_mod_cast (addHaarScalarFactor_pos_of_isAddHaarMeasure ..).ne',
    ?_⟩
  ext
  rw [constantTerm_eq_setIntegral hφ.1 (h𝓕.mono $ absolutelyContinuous_isAddHaarMeasure ..), ct]
  nth_rw 1 [isAddLeftInvariant_eq_smul μ ν]
  simp [hunip, ν]
  rfl
