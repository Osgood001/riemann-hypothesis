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
    have hc := IsTotallyComplex.isComplex w
    have hw := InfinitePlace.not_isReal_iff_isComplex.2 hc
    change ((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).1 w = _
    rw [← coe_infiniteProj, infiniteProj_posIdele]
    change posRealElem w _ = (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm _
    simp [posRealElem, hw, InfinitePlace.mult, Real.sqrt_sq (Real.exp_pos u).le, expU, Complex.ofReal_exp]
    change _ = (1 : Af E) - 0 + 0
    rw [sub_zero, add_zero]
    exact FiniteAdeleRing.ext _ $ posIdele_finite _ _
  have hdiag (f : Fin N → ℝ) (M : GL (Fin N) (Cinf E))
      (hM : M.1 = diagonal fun i _ => Complex.exp (f i)) : infGL E N M = An.tor E f := by
    have entry (A : Matrix (Fin N) (Fin N) (Cinf E)) i j :
        matN N (sInf E) A i j = sInf E (A i j) := rfl
    refine Units.ext (Matrix.ext fun i j => ?_)
    simp only [An.tor, coe_diagUnits, pExp]
    by_cases h : i = j <;> simp [infGL, cornerGL, corner, entry, hM, infId, diagonal_apply, h, expU]
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
  set a := ν D
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := N) (r := r)
  have h0 : a ≠ 0 := isAddFundamentalDomain_unipFundamentalDomain.measure_ne_zero $ NeZero.ne _
  have htop : a ≠ ⊤ := ((measure_mono hDC).trans_lt hC.measure_lt_top).ne
  have hv : (a.toReal : ℂ) ≠ 0 := by exact_mod_cast (ENNReal.toReal_pos h0 htop).ne'
  have hunip {a r : ℕ} (X : UPos a r → Ad E) : AutomorphicForm.unipGL X = unip X := by
    apply Units.ext
    rfl
  have hL : IsLeftInvariant φ.1 := hφ.left
  unfold IsCT
  generalize borel (BlockIx N r → Ad E) = m at hpi ⊢
  subst hpi
  refine ⟨⟨a⁻¹ • ν, D, IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0),
      isAddFundamentalDomain_unipFundamentalDomain.mono smul_absolutelyContinuous, funext fun g => by
        simp [ct, An.ctn, constantTerm, hunip, Measure.real, restrict_smul, integral_smul_measure,
          ENNReal.toReal_inv, Complex.real_smul, Complex.ofReal_inv]
        rfl⟩,
    fun F ⟨μ, 𝓕, hμ, h𝓕, hF⟩ => ?_⟩
  subst hF
  set s := addHaarScalarFactor μ ν
  have e : μ = s • ν := isAddLeftInvariant_eq_smul μ ν
  have hc : 0 < s := addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  refine ⟨(s : ℂ) * a.toReal, mul_ne_zero (by exact_mod_cast hc.ne') hv, funext fun g => ?_⟩
  simp only [ct, e, restrict_smul, integral_smul_nnreal_measure, ← hunip, NNReal.smul_def,
    Complex.real_smul, An.ctn, Measure.real]
  rw [← constantTerm_eq_setIntegral hL (h𝓕.mono $ e ▸ absolutelyContinuous_smul $ by exact_mod_cast hc.ne') g,
    ← mul_assoc, mul_inv_cancel_right₀ hv]
