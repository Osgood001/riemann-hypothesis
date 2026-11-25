import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyTransition
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyMetric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def BirationalModelExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ),
    IsArithVar P d → ∃ (Ω : Type) (_ : Field Ω) (y : (Σ k, ι k) → Ω), mCoordIdeal y = P ∧ Birational y

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
