import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar

namespace ProjCoord

section OpenImm

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]





end OpenImm

section Chart

variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]




end Chart

section Away

open HomogeneousLocalization

variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]





end Away

section Poly

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem aeval_mul_of_isHomogeneous {B : Type} [CommRing B] [Algebra o B] (x : κ → B) (t : B)
    {g : MvPolynomial κ o} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun j => t * x j) g = t ^ n * aeval x g := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h : ∑ i ∈ d.support, d i = n := by
    have := hg (mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring








end Poly

end ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

end GlobalTheory.CompanionTheory.Ar
