module

public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ProductMapEquality.PiCdEqMap
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.LevelStabilisers.MemStabOfLev
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.UpperFactors.FactorUpper
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.InverseMultiplication.IsKMInvMul
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ExponentialThreeBound.LeExpThree
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.BoxExistence.ExistsBox
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.MeasureSumBounds.SumMuFLe
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FormalDegreeRankTwo.FinrankEqTwoFdeg
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.Tube0

@[expose] public section

namespace MainStatements.Tam.Plug

theorem low : LowSt := MainStatements.Tam.low MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.num

theorem comp_flag : CompStBound fun D M => flagMassLev D.host.E D.R.r M :=
  MainStatements.Tam.comp_flag (tube0 MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.idx)

theorem comp_large_rank : CompStLargeRank :=
  MainStatements.Tam.comp_large_rank (tube0 MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.idx)

theorem comp : CompSt := MainStatements.Tam.comp_of_flag comp_flag

theorem size : SizeSt := MainStatements.Tam.size

end MainStatements.Tam.Plug
