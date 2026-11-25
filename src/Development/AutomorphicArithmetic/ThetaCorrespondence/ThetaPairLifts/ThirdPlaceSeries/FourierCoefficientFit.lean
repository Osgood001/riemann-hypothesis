module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinOutOfFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKlingenDeligneRibetOfBoth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FunctionalsSeparateOfHoweUnramOfSiegelWeil
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FourierCoefficientFitOfJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LamLowOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputsOfPublished
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeTateFunctionalEquation
import Development.WeilBound.CoreStatements.AutomorphicKernels.DeligneRibet.NotDvdAbsNorm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStd
import Development.WeilBound.ThetaLifts.Reductions.FiniteClosure.TheoremKOfMod

@[expose] public section

namespace GlobalTheory.BigTop.Fun.Close

/-- The third-place Fourier coefficients fit the original field assignment. -/
theorem fourier_coefficient_fit :
    GlobalTheory.BigTop.Fun.ConstantFunctionFits @GlobalTheory.BigTop.Fun.Fld := by
  let h := GlobalTheory.FunPr.thetaLocalInputs
  have hFE := GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation
  have hJoin := GlobalTheory.JoinFun.joinOut_of_five
    GlobalTheory.CompanionTheory.Hypotheses₂.ellipticMainTheoremCM
    GlobalTheory.CompanionTheory.Hypotheses₂.hilbertClassFieldJ
    (GlobalTheory.siegelKlingenDeligneRibet_of_both
      GlobalTheory.CompanionTheory.Hypotheses₂.siegelKlingen PositivityTheory.PfDRL.deligneRibet)
    GlobalTheory.CompanionTheory.Hypotheses₂.partialZetaFunctionalEquation hFE
  obtain ⟨hAgree, hMatch⟩ := PositivityTheory.ThKR.theoremK_head2
    PositivityTheory.RgEis.Hd.eisBL PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd
  exact fourier_coefficient_fit_of_join_alt h hJoin hFE hAgree hMatch
    (UpperTheory.Lit.functionalsSeparate_of_howeUnram_of_siegelWeil h
      GlobalTheory.Hk3.howeUnram_holds UpperTheory.Lit.Sw47.convergent)
    (GlobalTheory.BigTop.lamLow_of_hypotheses_alt_alt h.cuspRapidDecay
      h.weilSiegelFormulaUnitary UpperTheory.Lit.Sw47.convergent h.doublingMethod
      h.unramifiedDoublingGL h.bernsteinZelevinskyFiniteness h.formalDegreeCompactDual)

end GlobalTheory.BigTop.Fun.Close
