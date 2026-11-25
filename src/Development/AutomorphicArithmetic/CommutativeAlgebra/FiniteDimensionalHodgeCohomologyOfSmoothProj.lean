module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh

set_option maxSynthPendingDepth 1

noncomputable section

private theorem smulHom_eq {X : Scheme.{0}} (F : X.Modules) (r : Γ(X, ⊤)) :
    GlobalTheory.smulHom F r = GroundTheory.Arith.SchemeCoh.smulHom F r := by
  ext U x
  rfl

private def cohEquiv {X : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] (F : X.Modules)
    (n : ℕ) : coh F n ≃ₗ[R] Sheaf.H.{0} (GroundTheory.Arith.SchemeCoh.modulesAb F) n :=
  { (coh.toH F n) with
    map_smul' := fun r x => by
      have h := coh.toH_map R (smulHom F (algebraMap R Γ(X, ⊤) r)) n x
      rw [← cohOn.smul_eq_map] at h
      refine h.trans ?_
      rw [smulHom_eq]
      rfl }

private theorem finiteType_sec {A : Type} [CommRing A] {Z : Scheme.{0}} (s : Z ⟶ Sp A) [LocallyOfFiniteType s]
    {U : Z.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType A (CechDR.Sec s U) := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : (CechDR.secMap s U).hom.FiniteType := by
    change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appLE ⊤ U le_top).hom.FiniteType
    rw [CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp h (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2)
  exact h2

private theorem isCoherent_Omega {A : Type} [CommRing A] {Z : Scheme.{0}} (s : Z ⟶ Sp A) [LocallyOfFiniteType s] (a : ℕ) :
    GroundTheory.Arith.SchemeCoh.IsCoherent (Omega s a) := by
  refine ⟨inferInstance, fun U hU => ?_⟩
  have := finiteType_sec s hU
  have h : Module.Finite (CechDR.Sec s U) (CechDR.OmU s U a) := inferInstance
  have h' : Module.Finite (CechDR.Sec s U) Γ(Omega s a, U) := Module.Finite.equiv (toOmEquiv s a hU)
  exact h'

/-- Hodge cohomology of a proper scheme is finite over its Noetherian affine base.
Neither smoothness nor integrality is needed for coherence of exterior differentials. -/
theorem UpperTheory.finite_hodgeCohomology_of_proper {A : Type} [CommRing A] [IsNoetherianRing A]
    {Z : Scheme.{0}} (s : Z ⟶ Sp A) [IsProper s] (a b : ℕ) :
    Module.Finite A (hodgeH s a b) := by
  let : Z.Over (Spec (.of A)) := ⟨s⟩
  have : IsProper (Z ↘ Spec (.of A)) := inferInstanceAs (IsProper s)
  have hc : GroundTheory.Arith.SchemeCoh.IsCoherent (Omega s a) := isCoherent_Omega s a
  have h := @GroundTheory.Arith.SchemeCoh.finite_H_of_isProper A _ _ Z _ _ (Omega s a) hc b
  let := algΓ s
  have : Module.Finite A (Sheaf.H.{0} (GroundTheory.Arith.SchemeCoh.modulesAb (Omega s a)) b) := h
  exact Module.Finite.equiv (cohEquiv A (Omega s a) b).symm

/-- Projective complex schemes have finite-dimensional Hodge cohomology. -/
theorem UpperTheory.finiteDimensional_hodgeCohomology_of_proj
    {Z : Scheme.{0}} (s : Z ⟶ Sp ℂ) (hp : IsProjOver s) (a b : ℕ) :
    FiniteDimensional ℂ (hodgeH s a b) := by
  obtain ⟨N, i, hi, his⟩ := hp
  have : IsProper (PSpace.str ℂ N) :=
    inferInstanceAs (IsProper (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase ℂ N))
  have : IsProper s := by rw [← his]; infer_instance
  exact UpperTheory.finite_hodgeCohomology_of_proper s a b

theorem UpperTheory.finiteDimensional_hodgeCohomology_of_smooth_proj :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s → ∀ a b : ℕ, FiniteDimensional ℂ (hodgeH s a b) := by
  intro Z _ s d _ hp a b
  exact UpperTheory.finiteDimensional_hodgeCohomology_of_proj s hp a b

end
