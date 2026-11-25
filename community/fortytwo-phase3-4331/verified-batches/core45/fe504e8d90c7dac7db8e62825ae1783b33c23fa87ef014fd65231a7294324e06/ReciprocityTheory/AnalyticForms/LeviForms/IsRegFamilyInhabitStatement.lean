import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

variable {X : Type*}

def bdry (s : X → X → ℂ) : Set X := {y | s y y = 0}

def rW [TopologicalSpace X] (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ :=
  Real.exp 1 - 2 * logNormSec L s y






def IsPshOn [TopologicalSpace X] {e : ℕ} (A : FinHolAtlas e X) (U : Set X) (P : LocPot X) : Prop :=
  ∀ x j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ U), ∀ w : Fin e → ℂ,
    0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w


def epsT (C t : ℝ) : ℝ := C * Real.log (Real.log (1 / t)) / Real.log (1 / t)

def rLoc {D : ℕ} (S : Finset (Fin D)) (m : Fin D → ℕ) (z : Fin D → ℂ) : ℝ :=
  Real.exp 1 + ∑ i ∈ S, (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2)

def IsAdaptedAtlas [TopologicalSpace X] {e : ℕ} (A B : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) : Prop :=
  A.Compatible B ∧ (∀ j, Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) ∧
    (∀ x, ∃ j, x ∈ (B.chart j).source ∧ B.chart j x ∈ Metric.ball (0 : Fin e → ℂ) 1) ∧
    ∃ M : ℝ, ∀ j, ∃ (S : Finset (Fin e)) (m : Fin e → ℕ), (∀ i ∈ S, 1 ≤ m i) ∧
      (∀ y ∈ (B.chart j).target, ((B.chart j).symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
      ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, (B.chart j).symm y ∉ bdry s →
        |rW L s ((B.chart j).symm y) - rLoc S m y| ≤ M

def IsRegFamily [TopologicalSpace X] {e : ℕ} (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ) : Prop :=
  0 < t₀ ∧ t₀ < 1 ∧ ∀ t, 0 < t → t ≤ t₀ →
    A.Smooth (phT t) ∧
    (∀ y, phT t y ≤ C) ∧ (∀ y ∉ bdry s, ph y ≤ phT t y) ∧
    (∀ y, -C * Real.log (Real.log (1 / t)) ≤ phT t y) ∧
    IsPsh A (th + LocPot.ofFun (phT t) + Θ.rsmul (epsT C t)) ∧
    (∀ y ∉ bdry s, rW L s y ≤ Real.log (1 / t) →
      phT t y ≤ ph y + t ^ ((1 : ℝ) / 3) + epsT C t) ∧
    (∀ y ∉ bdry s, phT t y ≤ ph y + t ^ ((1 : ℝ) / 3) + epsT C t * rW L s y) ∧
    (∀ t', t ≤ t' → t' ≤ t₀ → ∀ y, phT t y ≤ phT t' y + C * epsT C t')

def IsRegFamilyC2 [TopologicalSpace X] {e : ℕ} (A : FinHolAtlas e X) (s : X → X → ℂ)
    (ph : X → ℝ) (phT : ℝ → X → ℝ) : Prop :=
  ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K →
    TendstoUniformlyOn (fun t => phT t ∘ (A.chart j).symm) (ph ∘ (A.chart j).symm)
        (nhdsWithin 0 (Set.Ioi 0)) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (phT t ∘ (A.chart j).symm))
        (fderiv ℝ (ph ∘ (A.chart j).symm)) (nhdsWithin 0 (Set.Ioi 0)) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT t ∘ (A.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph ∘ (A.chart j).symm))) (nhdsWithin 0 (Set.Ioi 0)) K

def IsSingWeight [TopologicalSpace X] {e : ℕ} (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (C₅ : ℝ) : Prop :=
  IsPotential A th ∧ A.SmoothOn (bdry s)ᶜ ph ∧ IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun ph) ∧
    ∀ y ∉ bdry s, -C₅ * Real.log (rW L s y) ≤ ph y ∧ ph y ≤ C₅














end

end ReciprocityTheory.AnForm.P
