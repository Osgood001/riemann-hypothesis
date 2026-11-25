module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedSymmetricLieTensorsFiniteProjectiveRankStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionMatricesRingHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenRankInteriorEqSignature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSignatureSumEqTwiceDimensionStatement

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BalProj

/-- Signature multiplicities hold at every field point of the framed model,
including the boundary. Neither smoothness nor normal crossings is required. -/
theorem balanced_rank_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y U n v A hv hb hA
  obtain ⟨h1A, haddA, hmulA⟩ := GlobalTheory.T.tangentBasis_actionMatrices_ringHom H Y.t Γ(Y.X, U.1) (chart U) n v A hv hb hA
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.balancedSymmetricLieTensors_finite_projective_rank H c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  have h2 := hrk m
  simp_rw [GlobalTheory.BalProjInt.eigRank_field Y U n v A hv hb hA] at h2
  unfold Datum.mult at h2
  rw [GlobalTheory.T.cmType_signature_sum_eq_twice_dimension E H Dw.p Dw.q] at h2
  unfold Datum.dim
  omega

theorem balanced_finite_projective_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y _ _ _ U n v A hv hb hA
  exact balanced_rank_of_frame E H Dw l Xo c Y U n v A hv hb hA

end GlobalTheory.BalProj
