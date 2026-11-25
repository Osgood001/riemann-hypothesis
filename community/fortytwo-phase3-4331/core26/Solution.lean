import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

namespace AlpogeRHCore26

theorem adelicCovolumeFinite
    {F E : Type} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
    {W : Type} [AddCommGroup W] [Module E W] {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : HermitianForm F E W)
    (v : Basis ι E W) :
    GroundTheory.Heights₂.Heights.FiniteCovolume.AdelicCovolumeFinite.Statement h v :=
  GroundTheory.Heights₂.Heights.FiniteCovolume.AdelicCovolumeFinite.full h v

end AlpogeRHCore26
