import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Measure Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
  GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic
  GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.Reduction PositivityTheory.Rg.Rs
  PositivityTheory.Affgl.CT

theorem AlpogeRHCore40.residualSpectrumConstantTermDict : Dict := by
  intro E _ _ _ N
  have pExp (u : ℝ) : posIdele (K := E) (Real.exp u) (Real.exp_pos u) = infId E (expU fun _ : InfinitePlace E => (u : ℂ)) := by
    refine Units.ext $ Prod.ext ?_ ?_
    change _ = 1 - infEq E 1 + infEq E _
    rw [map_one, sub_self, zero_add]
    funext w
    rw [← coe_infiniteProj, infiniteProj_posIdele]
    change posRealElem w _ = _
    simp [posRealElem, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w),
      InfinitePlace.mult, Real.sqrt_sq (Real.exp_pos u).le, expU, Complex.ofReal_exp, infEq]
    rfl
    change _ = (1 : Af E) - 0 + 0
    rw [sub_zero, add_zero]
    exact FiniteAdeleRing.ext _ $ posIdele_finite _ _
  have hdiag (f : Fin N → ℝ) (M : GL (Fin N) (Cinf E))
      (hM : M.1 = diagonal fun i _ => Complex.exp (f i)) : infGL E N M = An.tor E f := by
    have entry A i j :
        matN N (sInf E) A i j = sInf E (A i j) := rfl
    refine Units.ext (Matrix.ext fun i j => ?_)
    simp only [An.tor, coe_diagUnits, pExp]
    by_cases h : i = j <;> simp [infGL, cornerGL, corner, entry, hM, infId, h, expU]
  have htor t : splitCentre E N t = An.tor E fun _ => t :=
    hdiag _ _ rfl
  refine ⟨fun r t => hdiag _ _ $ congrArg diagonal $ by funext i w; split_ifs <;> simp,
    htor, by
      unfold latticeGL An.lat
      rw [htor]
      rfl,
    fun φ hφ r _ _ => ?_⟩
  have hpi : (MeasurableSpace.pi : MeasurableSpace (BlockIx N r → Ad E)) = borel _ :=
    have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
    BorelSpace.measurable_eq
  set ν := unipMeasure E N r
  set D := unipFundamentalDomain E N r
  have hunip {a r : ℕ} (X : UPos a r → Ad E) : AutomorphicForm.unipGL X = unip X := by
    apply Units.ext
    rfl
  unfold IsCT
  generalize borel (BlockIx N r → Ad E) = m at hpi ⊢
  subst hpi
  refine ⟨⟨ν, D, inferInstance, isAddFundamentalDomain_unipFundamentalDomain, funext fun g => by
        simp [ct, An.ctn, Measure.real, unipMeasure_unipFundamentalDomain, constantTerm, hunip, D, ν]⟩,
    fun F ⟨μ, 𝓕, hμ, h𝓕, hF⟩ => ?_⟩
  subst hF
  set s := addHaarScalarFactor μ ν
  have e : μ = s • ν := isAddLeftInvariant_eq_smul μ ν
  have hc := (addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne'
  refine ⟨s, by exact_mod_cast hc, funext fun g => ?_⟩
  simp [ct, e, restrict_smul, integral_smul_nnreal_measure, ← hunip, NNReal.smul_def,
    Complex.real_smul, An.ctn, Measure.real, unipMeasure_unipFundamentalDomain,
    constantTerm_eq_setIntegral hφ.left (h𝓕.mono $ e ▸ absolutelyContinuous_smul $ by exact_mod_cast hc) g, ν]
