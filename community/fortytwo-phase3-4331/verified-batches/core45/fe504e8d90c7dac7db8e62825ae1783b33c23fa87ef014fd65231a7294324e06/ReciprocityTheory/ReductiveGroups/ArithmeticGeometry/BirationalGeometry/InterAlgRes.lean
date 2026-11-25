import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.SNCstep
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Immersion
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mem_mcPts_iff_conePts_pC (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) :
    z ∈ mcPts P ↔ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P) := by
  rw [mcPts_eq_pC]
  exact Iff.rfl



end ReciprocityTheory.ChartRestriction.G.Geo
