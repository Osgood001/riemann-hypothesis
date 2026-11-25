module

public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.UpperFactors.FactorUpper
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ExponentialThreeBound.LeExpThree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ArchimedeanTamagawaUpperBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LevelSubgroupIndexBounded

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace MainStatements.Tam.A
end MainStatements.Tam.A
namespace MainStatements.Tam
open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in
theorem tamagawa_volume_le_68 (hV : VolSt) (hS : StabSt)
    (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m)
    (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕) (L : ℝ) (hL : Sizes D L) :
    Real.log (μ 𝓕).toReal ≤ 68 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  obtain ⟨hn, hi⟩ := GlobalTheory.CovTop.LevelIndex.level_index_le_half D Tu C t0 hC i P
  have h := A.log_measure_le_log_index_add hV hS MainStatements.Tam.num D Tu C t0 hC i P μ 𝓕 hF L hL hn
  have hs := mul_le_mul_of_nonneg_left hL.2.2.1 (show 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 by positivity)
  linarith only [h, hi, hs]

theorem tamagawa_number_upper_bound : VolSt → StabSt → NumSt → _root_.MainStatements.Tam.ArchimedeanTamagawaUpperBound := by
  intro hV hS _ _ D Tu C t0 hC i P μ 𝓕 hF L hL
  have h := tamagawa_volume_le_68 hV hS D Tu C t0 hC i P μ 𝓕 hF L hL
  have hg : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le ((Nat.one_le_cast).mpr (D.host.g_prime 0).one_le)
      ((Nat.one_le_cast).mpr (D.host.g_prime 1).one_le))
  have hL0 : 0 ≤ L := by linarith [hL.2.2.1]
  have hA : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L := by positivity
  have hB : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D.R.r; linarith))
  linarith only [h, hA, hB]

end MainStatements.Tam
end
end
