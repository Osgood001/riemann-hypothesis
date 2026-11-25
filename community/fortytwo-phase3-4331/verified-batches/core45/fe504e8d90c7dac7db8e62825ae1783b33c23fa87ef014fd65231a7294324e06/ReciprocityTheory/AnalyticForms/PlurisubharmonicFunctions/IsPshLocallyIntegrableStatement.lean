import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology
open scoped ContDiff

noncomputable section

variable {D : ℕ}

def IsPsh (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) : Prop :=
  UpperSemicontinuousOn φ U ∧
    ∀ z w : Fin D → ℂ, (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ U) →
      CircleIntegrable (fun ζ : ℂ => φ (z + ζ • w)) 0 1 ∧
        φ z ≤ Real.circleAverage (fun ζ : ℂ => φ (z + ζ • w)) 0 1






def SubMeanPolydiscStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ),
    IsOpen U → IsPsh U φ → 0 < t → closedBall z t ⊆ U →
    IntegrableOn φ (closedBall z t) volume ∧ φ z ≤ ⨍ x in closedBall z t, φ x







structure Mollifier (D : ℕ) where

  toFun : (Fin D → ℂ) → ℝ
  contDiff : ContDiff ℝ ∞ toFun
  nonneg : ∀ w, 0 ≤ toFun w
  support_subset : Function.support toFun ⊆ ball 0 1
  integral_eq_one : ∫ w, toFun w = 1
  circle_inv : ∀ (c : ℂ) (w : Fin D → ℂ), ‖c‖ = 1 → toFun (c • w) = toFun w














end

end ReciprocityTheory.AnForm.A
