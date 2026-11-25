module

public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.CompSt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FlagVolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeNegTransposeGramStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixUnitaryGroupPreservesGramStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjRationalPrincipalCongruenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCosetStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslateStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConjStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeRealSpecialUnitaryEqFlagDomainMassStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThreeStatement
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMassUpperBound
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.HolomorphicSectionSignatureOneOne

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MainStatements.Tam.C

theorem sum_muF_le_flag (hT : TubeSt) (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) [Fintype Comp]
    (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ)
    (hK : IsLevelK V M Kf) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hm : ∀ k, ModelW V hr (X k)) (hM : 3 ≤ M)
    (hΨ : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (X k).Ψ ↔ ∃ ρ, τ = tauE D ρ)
    (P Q : ℕ) (hs : V.SigOK) (hsig : ∀ τ, V.sig τ = (P, Q)) (h2 : 2 ≤ r)
    (x0 : ∀ k, Frame (X k).Ψ r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd (X k))))
    (hF : ∀ k, IsOrth (X k) (x0 k) ∧ IsFundSet (X k) (x0 k) (FF k)) :
    ∑ k, muF (X k) (x0 k) (FF k) ≤ ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * r ^ 2) * (M : ℝ) ^ (2 * D.R.f * r ^ 2) *
      (ReciprocityTheory.ChartRestriction.DS.flagVolume r ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D r)) := by
  subst hr
  classical
  obtain ⟨x1, hx1, hact⟩ := hD.2.2.1
  choose gA hgA using fun c => (hx1 c).2
  have hG : ∀ k, (X k).Gm = -(V.gram)ᵀ := fun k => by
    have := (hm k).1
    simpa [Matrix.reindex_apply] using this
  have hL := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  choose Λk hΛk using fun k => GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (finHom V (gA k))
    hL.2.2.1 hL.2.2.2.1
  have hX' := fun k => GlobalTheory.T.exists_flagDomainData_principalCongruenceLevel D.host.E V.rank M (X k) (Λk k) hM (hΛk k).2.1 (hΛk k).2.2.1
  choose X' hX'Gm hX'Ψ hX'p0 hX'Λ hX'Γ using hX'
  have hfm : ∀ k, ∃ y, IsOrth (X' k) y ∧ ∃ FF', IsFundSet (X' k) y FF' ∧ muF (X' k) y FF' < ⊤ :=
    fun k => GlobalTheory.finMu_all_data D.host.E V.rank (X' k)
  choose y hy FF' hFF' _ using hfm
  have hμ : ∀ k, muF (X k) (x0 k) (FF k) = muF (X' k) (y k) (FF' k) := by
    intro k
    refine GlobalTheory.T.covolume_eq_of_realUnitary_conj D.host.E V.rank (X k) (X' k) (hX'Ψ k)
      (fun τ => if h : τ ∈ (X k).Ψ then archM V (th k ⟨τ, h⟩) (gA k) else 1) (x0 k) (y k) (FF k) (FF' k)
      (hX'Gm k) (hX'p0 k) ?_ ?_ ?_ (hF k).1 (hy k) (hF k).2 (hFF' k)
    · intro τ hτ
      simp only [dite_eq_left hτ]
      rw [hG k]
      exact GlobalTheory.T.archimedeanMatrix_unitaryGroup_preserves_gram D V τ _ (hth k ⟨τ, hτ⟩) (gA k)
    · intro γ hγ
      obtain ⟨γ', h1, h2⟩ := GlobalTheory.T.arithmeticGroup_conj_rational_principalCongruence D V Comp X dict Kf th M x1 hK hth hD (fun c => (hx1 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 γ hγ
      refine ⟨γ', (hX'Γ k γ').2 (by rw [hG k]; exact h1), fun τ hτ => ?_⟩
      simp only [dite_eq_left hτ]
      exact h2 τ hτ
    · intro γ' hγ'
      have h1 := (hX'Γ k γ').1 hγ'
      rw [hG k] at h1
      obtain ⟨γ, hγ, h2⟩ := GlobalTheory.T.principalCongruence_conj_mem_arithmeticGroup D V Comp X dict Kf th M x1 hK hth hD (fun c => (hx1 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 (hΛk k).2.2.2 γ' h1
      refine ⟨γ, hγ, fun τ hτ => ?_⟩
      simp only [dite_eq_left hτ]
      exact h2 τ hτ
  have hdist := GlobalTheory.T.componentRepresentatives_injective_doubleCoset D V Comp X dict Kf th M gA hK hth hD (fun k => by rw [hgA k])
  have hΓ' : ∀ k γ, γ ∈ (X' k).Γ ↔ IsUStab (X' k).Gm (X' k).Λ γ ∧ ∀ x ∈ (X' k).Λ, ∃ z ∈ (X' k).Λ,
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ x - x = M • z := by
    intro k γ
    rw [hX'Γ k γ, hX'Gm k, hX'Λ k]
  have hdet : ∀ k, ∀ γ ∈ (X' k).Γ, (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 := fun k =>
    GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three D.host.E V.rank M (X' k) hM (hΓ' k)
  have hCc := fun k => GlobalTheory.T.covolume_realSpecialUnitary_eq_flagDomain_mass D.host.E V.rank (X' k) (y k) (FF' k) (by omega) (hdet k) (hy k) (hFF' k)
  have hTube := hT D V P Q hs hsig h2 M hM Comp X' gA y hdist (fun k => ⟨(hX'Gm k).trans (hG k),
    fun τ => by rw [hX'Ψ k]; exact hΨ k τ, by rw [hX'Λ k]; exact (hΛk k).1, hΓ' k, hy k⟩)

  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hdeg : fdeg D.host.E = D.R.f := by unfold fdeg; omega
  have hpos := ReciprocityTheory.ChartRestriction.DS.flagScale_pos (show 0 < V.rank by omega)
  have hpow := pow_pos hpos D.R.f
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr hpow) ENNReal.ofReal_ne_top).1
  rw [Finset.sum_congr rfl (fun k _ => hμ k), Finset.mul_sum]
  refine (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)).trans (hTube.trans_eq ?_)
  · simpa [ReciprocityTheory.ChartRestriction.DS.flagScale, hdeg] using hCc k
  · rw [← ENNReal.ofReal_mul hpow.le]
    congr 1
    rw [ReciprocityTheory.ChartRestriction.DS.flagVolume, div_pow]
    field_simp

theorem sum_muF_le (hT : TubeSt) (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) [Fintype Comp]
    (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ)
    (hK : IsLevelK V M Kf) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hm : ∀ k, ModelW V hr (X k)) (hM : 3 ≤ M)
    (hΨ : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (X k).Ψ ↔ ∃ ρ, τ = tauE D ρ)
    (P Q : ℕ) (hs : V.SigOK) (hsig : ∀ τ, V.sig τ = (P, Q)) (h2 : 2 ≤ r)
    (x0 : ∀ k, Frame (X k).Ψ r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd (X k))))
    (hF : ∀ k, IsOrth (X k) (x0 k) ∧ IsFundSet (X k) (x0 k) (FF k)) :
    ∑ k, muF (X k) (x0 k) (FF k) ≤ ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * r ^ 2) * (M : ℝ) ^ (2 * D.R.f * r ^ 2) *
      (ReciprocityTheory.ChartRestriction.DS.volU r ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D r)) := by

  have key := sum_muF_le_flag hT D V r hr Comp X dict Kf th M hK hth hD hm hM hΨ P Q hs hsig h2 x0 FF hF
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hm0 : 0 ≤ Formalism.MainNotions.StandardLattice.massI D r := by
    unfold Formalism.MainNotions.StandardLattice.massI Formalism.HermitianLatticesTheory.mass
    split_ifs
    · exact Finset.sum_nonneg fun _ _ => by positivity
    · exact le_rfl
  have hv : ReciprocityTheory.ChartRestriction.DS.flagVolume r ≤ ReciprocityTheory.ChartRestriction.DS.volU r := by
    exact div_le_self (by unfold ReciprocityTheory.ChartRestriction.DS.volU; positivity)
      (ReciprocityTheory.ChartRestriction.DS.one_le_flagScale (by omega))
  gcongr
  exact ReciprocityTheory.ChartRestriction.DS.flagVolume_nonneg r

private theorem flag_mass_bound {f r M : ℕ} {mass cap : ℝ} (hr : 2 ≤ r)
    (hv : 0 ≤ ReciprocityTheory.ChartRestriction.DS.flagVolume r) (hm : mass ≤ cap) (hc : 0 ≤ cap) :
    (16 : ℝ) ^ (f * r ^ 2) * M ^ (2 * f * r ^ 2) *
      (ReciprocityTheory.ChartRestriction.DS.flagVolume r ^ f * mass) ≤
    (M : ℝ) ^ (2 * f * r ^ 2) * (if 5 ≤ r then (4 : ℝ) else 6) ^ (2 * f * r ^ 2) * cap := by
  have h (a b : ℝ) (hv' : ReciprocityTheory.ChartRestriction.DS.flagVolume r ≤ a ^ (r ^ 2))
      (hab : 16 * a = b ^ 2) :
      (16 : ℝ) ^ (f * r ^ 2) * M ^ (2 * f * r ^ 2) *
        (ReciprocityTheory.ChartRestriction.DS.flagVolume r ^ f * mass) ≤
        (M : ℝ) ^ (2 * f * r ^ 2) * b ^ (2 * f * r ^ 2) * cap := by
    have hvm := (mul_le_mul_of_nonneg_left hm (pow_nonneg hv f)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv hv' f) hc)
    calc _ ≤ (16 : ℝ) ^ (f * r ^ 2) * M ^ (2 * f * r ^ 2) * ((a ^ (r ^ 2)) ^ f * cap) := by gcongr
         _ = _ := by
           rw [← pow_mul, Nat.mul_comm (r ^ 2) f, show 2 * f * r ^ 2 = 2 * (f * r ^ 2) by ring,
             pow_mul b, ← hab, mul_pow]
           ring
  split_ifs with h5
  · exact h 1 4 (by simpa using ReciprocityTheory.ChartRestriction.DS.flagVolume_le_one h5) (by norm_num)
  · exact h (9 / 4) 6 (ReciprocityTheory.ChartRestriction.DS.flagVolume_le_nine_quarters_pow hr) (by norm_num)

end MainStatements.Tam.C

open MainStatements.Tam

theorem MainStatements.Tam.comp_flag_exact : TubeSt → CompStBound fun D M =>
    (16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * (M : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) *
      (ReciprocityTheory.ChartRestriction.DS.flagVolume D.R.r ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D D.R.r) := by
  intro hT D j H Dw l Xo c U dict hL σ hσ x0 FF hF
  obtain ⟨Kf, th, hr, hK, hth, hD, -⟩ := hL.dictU σ hσ
  obtain ⟨hr', hm⟩ := hL.modelW σ hσ
  have hunf := hL.unf σ hσ
  have hΨ : ∀ k (τ : D.host.E →+* ℂ), τ ∈ ((U σ).X k).Ψ ↔ ∃ ρ, τ = tauE D ρ := by
    intro k τ
    have hf := GlobalTheory.HolDictModel.fix_iff (D := D) τ
    rw [← hL.host.2.2.1, ← hL.host.2.1] at hf
    rw [(hunf.2.1 k).2 τ]
    simpa using hf
  have h2r : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have key := MainStatements.Tam.C.sum_muF_le_flag hT D (D.sp.W j) D.R.r hr (U σ).Comp (U σ).X (dict σ) Kf th l.M hK hth hD hm
    l.three_le hΨ (D.R.sigW j).1 (D.R.sigW j).2 (D.sp.W_sig j) (fun τ => D.sp.W_sigval j hL.inR.1 hL.inR.2 τ) h2r
    x0 FF hF

  exact key

theorem MainStatements.Tam.comp_flag (hT : TubeSt) : CompStBound fun D M => flagMassLev D.host.E D.R.r M := by
  apply (comp_flag_exact hT).mono
  intro D M
  have h2r := Formalism.L2.Geo.two_le_r D
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hmass := GlobalTheory.mass_stdLat_le D.host.E (fun _ => rfl) D.R.r
  have hcap : 0 ≤ massB D.host.E D.R.r := by unfold massB; positivity
  unfold flagMassLev
  rw [hfin]
  exact C.flag_mass_bound h2r (ReciprocityTheory.ChartRestriction.DS.flagVolume_nonneg _) hmass hcap

/-- Eventually the flag factor absorbs the entire constant in the tube bound,
uniformly in the field degree and the level. -/
theorem MainStatements.Tam.comp_large_rank (hT : TubeSt) : CompStLargeRank := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1
    ((ReciprocityTheory.ChartRestriction.DS.tendsto_pow_sq_mul_flagVolume 16 (by norm_num)).eventually_le_const zero_lt_one)
  refine ⟨R, fun D hr => ((comp_flag_exact hT) D).mono fun M => ?_⟩
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hw := ReciprocityTheory.ChartRestriction.DS.flagVolume_nonneg D.R.r
  have hf : (16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * ReciprocityTheory.ChartRestriction.DS.flagVolume D.R.r ^ D.R.f ≤ 1 := by
    rw [Nat.mul_comm, pow_mul, ← mul_pow]
    exact pow_le_one₀ (mul_nonneg (by positivity) hw) (hR _ hr)
  have hcap : 0 ≤ massB D.host.E D.R.r := by unfold massB; positivity
  have hm : Formalism.MainNotions.StandardLattice.massI D D.R.r ≤ massB D.host.E D.R.r :=
    GlobalTheory.mass_stdLat_le D.host.E (fun _ => rfl) D.R.r
  rw [hfin]
  calc _ = (M : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) *
        ((16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * ReciprocityTheory.ChartRestriction.DS.flagVolume D.R.r ^ D.R.f *
          Formalism.MainNotions.StandardLattice.massI D D.R.r) := by ring
       _ ≤ _ := by
         apply mul_le_mul_of_nonneg_left _ (by positivity)
         exact (mul_le_mul_of_nonneg_left hm (mul_nonneg (by positivity) (pow_nonneg hw _))).trans
           (mul_le_of_le_one_left hcap hf)

theorem MainStatements.Tam.comp_of_flag (h : CompStBound fun D M => flagMassLev D.host.E D.R.r M) :
    CompSt := by
  apply h.mono
  intro D M
  unfold flagMassLev massLev2
  have hb : 0 ≤ massB D.host.E D.R.r := by unfold massB; positivity
  split_ifs <;> gcongr <;> norm_num

theorem MainStatements.Tam.comp : TubeSt → NumSt → CompSt :=
  fun hT _ => comp_of_flag (comp_flag hT)

end
