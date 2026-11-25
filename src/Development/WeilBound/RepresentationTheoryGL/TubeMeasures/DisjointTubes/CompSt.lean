module

public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace MainStatements.Tam

def CompStAt (D : D7) (bound : ℕ → ℝ) : Prop := ∀ (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → ∑ k, muF ((U σ).X k) (x0 k) (FF k) ≤ ENNReal.ofReal (bound l.M)

def CompStBound (bound : D7 → ℕ → ℝ) : Prop := ∀ D, CompStAt D (bound D)

theorem CompStAt.mono {D : D7} {b b' : ℕ → ℝ} (h : CompStAt D b)
    (hbb : ∀ M, b M ≤ b' M) : CompStAt D b' := by
  intro j H Dw l Xo c U dict hL σ hσ x0 FF hF
  exact (h j H Dw l Xo c U dict hL σ hσ x0 FF hF).trans (ENNReal.ofReal_le_ofReal (hbb l.M))

theorem CompStBound.mono {b b' : D7 → ℕ → ℝ} (h : CompStBound b)
    (hbb : ∀ D M, b D M ≤ b' D M) : CompStBound b' := fun D => (h D).mono (hbb D)

def CompStLargeRank : Prop := ∃ R : ℕ, ∀ D : D7, R ≤ D.R.r →
  CompStAt D fun M => (M : ℝ) ^ (Module.finrank ℚ D.host.E * D.R.r ^ 2) * massB D.host.E D.R.r

/-- The flag normalization lowers the uniform component bound, already from rank five. -/
def flagMassLev (E : Type) [Field E] [NumberField E] (r M : ℕ) : ℝ :=
  (M : ℝ) ^ (Module.finrank ℚ E * r ^ 2) *
    (if 5 ≤ r then (4 : ℝ) else 6) ^ (Module.finrank ℚ E * r ^ 2) * massB E r

def CompSt : Prop := CompStBound fun D M => massLev2 D.host.E D.R.r M

end MainStatements.Tam

end
