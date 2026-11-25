import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousLiftToJoin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousNonvanishingOnJoinStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)

namespace GlobalTheory.CompanionTheory.Ar.Giv

namespace ResTop

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem coord_ne_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (p : Σ k, ι k)
    (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  unfold mCoordIdeal
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem charZero_of_horizontal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) :
    CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h1 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, map_natCast, map_natCast,
      ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [IsHorizontal] at h
  rw [h, Ideal.mem_bot] at h1
  exact_mod_cast h1

variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem isBlockMap_joinInl : IsBlockMap (Sum.inl : K → K ⊕ K₂) (joinInl ι ι₂) := by
  refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 : k = k' := Sum.inl_injective (congrArg Sigma.fst h)
    subst h1
    have h2 : i = i' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [h2]
  · rintro ⟨k, i⟩ ⟨k', rfl⟩
    exact ⟨⟨k', i⟩, rfl⟩


end ResTop
end GlobalTheory.CompanionTheory.Ar.Giv
