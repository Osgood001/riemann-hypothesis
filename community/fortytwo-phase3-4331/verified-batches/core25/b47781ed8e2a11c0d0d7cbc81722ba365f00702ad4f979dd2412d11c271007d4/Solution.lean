import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesS
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdPre
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntEqFour
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IndepDom
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ParabolicUnipotents
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PsiTContPer
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SecUnfOfCLaw
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts

open GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula

theorem AlpogeRHCore25.siegelWeilStd : SiegelWeilStd :=
  Fin.siegelWeilStd_pre TW.Twp.poisson
    (Act.ctSplit_of_parts Act.indepDom Act.cptDom Act.absConv Act.firstEq
      (Act.secLaw_of (Act.secUnf_of Act.absConv)))
