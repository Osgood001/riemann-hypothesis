module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMeasureRatioLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HaarMeasureFundamentalDomainNeZeroOfCocompact
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeFundamentalDomainNeTopOfFiniteCovolume
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PlugPairs
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.SupremumConstantLogBound
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.OneMeasureRatio
open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in
theorem log_covolume_ratio_le_index (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0)
    (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : Measure (GA D (Wc D i)))
    (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕)
    (L : ℝ) (hL : Sizes D L) :
    Real.log (ratio D i μ 𝓕) ≤ Real.log ((levW C i P).relIndex (levW C i (LevelP.full _ _ _))) +
      (79 / 2) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  have hn := (GlobalTheory.CovTop.LevelIndex.level_index_le_half D Tu C t0 hC i P).1
  have hv := MainStatements.Tam.A.log_measure_le_log_index_add MainStatements.Tam.vol MainStatements.Tam.stab
    MainStatements.Tam.num D Tu C t0 hC i P μ 𝓕 hF L hL hn
  have hd : ∀ τ, Real.log (dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L :=
    GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL
  have hd1 : ∀ τ, 1 ≤ dimAt D i τ := GlobalTheory.DimAtOne.one_le_dimAt D i
  rcases (ENNReal.toReal_nonneg (a := μ 𝓕)).eq_or_lt with hzero | hvpos
  · have hL0 : 0 ≤ L := le_trans (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D.R.r; linarith)) (log_r_add_three_le D L hL)
    unfold ratio
    rw [← hzero, zero_mul, Real.log_zero]
    have hi := Real.log_nonneg ((Nat.one_le_cast).mpr (Nat.one_le_iff_ne_zero.mpr hn) : (1 : ℝ) ≤ (levW C i P).relIndex (levW C i (LevelP.full _ _ _)))
    positivity
  have hdpos : ∀ τ, 0 < dimAt D i τ := fun τ => zero_lt_one.trans_le (hd1 τ)
  unfold ratio
  rw [Real.log_mul hvpos.ne' (Finset.prod_pos fun τ _ => hdpos τ).ne',
    Real.log_prod (fun τ _ => (hdpos τ).ne')]
  have hsum : ∑ τ, Real.log (dimAt D i τ) ≤ ∑ _τ : D.what₂.Tau, 3 / 2 * (D.R.r : ℝ) ^ 2 * L :=
    Finset.sum_le_sum fun τ _ => hd τ
  rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at hsum
  linarith only [hv, hsum]

open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in
theorem log_covolume_ratio_le_sharp (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0)
    (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : Measure (GA D (Wc D i)))
    (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕)
    (L : ℝ) (hL : Sizes D L) :
    Real.log (ratio D i μ 𝓕) ≤ (139 / 2) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  have h := log_covolume_ratio_le_index D Tu C t0 hC i P μ 𝓕 hF L hL
  have hi := (GlobalTheory.CovTop.LevelIndex.level_index_le_half D Tu C t0 hC i P).2
  have haux := mul_le_mul_of_nonneg_left hL.2.2.1 (show 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 by positivity)
  linarith only [h, hi, haux]

theorem log_covolume_ratio_le (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) :
    Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  have h := Function.const _ (log_covolume_ratio_le_sharp D Tu C t0 hC i P μ 𝓕 hF L hL) hP
  have hL0 : 0 ≤ L := le_trans (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D.R.r; linarith)) (log_r_add_three_le D L hL)
  have hx : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L := by positivity
  linarith only [h, hx]
end GlobalTheory.OneMeasureRatio
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_measure_ratio_bounded (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) :
    Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) :=
  GlobalTheory.OneMeasureRatio.log_covolume_ratio_le hP D Tu C t0 hC i P μ 𝓕 hF L hL
end
