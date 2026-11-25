import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]






namespace AnSys

variable {e : ℕ} {σ : Type} (S : AnSys e σ)








end AnSys



structure Realis {D : ℕ} {σ : Type} (S : AnSys D σ) (P : Ideal (MRing ι)) where
  arith : IsArithVar P (D + 1)

  J : Ideal (MRing ι)

  R : AnLogRes P J D

  π : R.X → S.X
  holo : HoloMap R.A S.A π

  deg : ℕ
  deg_pos : 0 < deg

  br : Set S.X
  degree : IsDegreeOff S.A R.A π deg br

  ref : σ → HermLine ι
  ref_smooth : ∀ a, IsSmoothHerm (ref a)
  ref_pot : ∀ a, SamePot R.A Set.univ (potOf R (ref a)) ((S.th a).pullback π holo.1)

  line : σ → ℝ → HermLine ι
  line_deg : ∀ a t, (line a t).a = (ref a).a
  line_smooth : ∀ a t, 0 < t → t ≤ S.t₀ → IsSmoothHerm (line a t)
  line_eq : ∀ a t, 0 < t → t ≤ S.t₀ → ∀ x,
    Real.log ((line a t).h (R.lift x x)) = Real.log ((ref a).h (R.lift x x)) + S.phT a t (π x)

namespace Realis

variable {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (II : IntersectionSystem)



























end Realis

section Weights

variable {D N : ℕ} {Ψ : Type} [Fintype Ψ] {S : AnSys D (Option (Ψ × Fin N))} {P : Ideal (MRing ι)}
  (Re : Realis S P) (II : IntersectionSystem)










end Weights







namespace Inputs


















end Inputs

end GlobalTheory.CompanionTheory.Ar.PB
