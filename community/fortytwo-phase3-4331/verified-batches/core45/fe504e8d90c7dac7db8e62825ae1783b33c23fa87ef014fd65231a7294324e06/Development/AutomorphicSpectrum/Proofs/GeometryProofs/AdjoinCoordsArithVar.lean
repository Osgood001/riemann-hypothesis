import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZarhinBundleKernelFirstCoordEquations
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectivePointImageReducedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothBasicOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LiftGenericPointOverIsoOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectivePointCoordsExistStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularValuesInAdjoinedFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreProductAffineChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.CompanionTheory.Ar.SncRes
variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem closure_facts {N : ℕ} (x : Fin (N + 1) → Ω) (hx : x ≠ 0) :
    IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage :=
  GlobalTheory.T.projective_point_image_reduced Ω N x hx

theorem smooth_basicOpen {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ)
    (e : ℕ) {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (g₀ : A) (hg : (g₀ : Ω) = valR ζ W σ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)] :
    SmoothOfRelativeDimension e ((Z.basicOpen σ).ι ≫ g) :=
  GlobalTheory.T.standard_smooth_basic_open Ω Z ζ g e W hW h A hA σ g₀ hg

theorem lift_generic {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] (f : X' ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (hd : Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X')) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) :
    ∃ ζ : Sp Ω ⟶ X', ζ ≫ f = ξ ∧ IsDominant ζ ∧ ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U) :=
  GlobalTheory.T.lift_generic_point_over_iso_open Ω X X' ξ f U hd hU

theorem exists_coords {r : ℕ} (p : Sp Ω ⟶ PSpace ℚ r) : ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' :=
  GlobalTheory.T.projective_point_coords_exist Ω r p

theorem val_mem_field {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) {W₀ : X.Opens}
    (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A)
    (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')) :
    valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) :=
  GlobalTheory.T.regular_values_in_adjoined_field Ω X X' ξ f U ζ hζ hU W₀ hW₀ h₀ A hA W' h' s

theorem prod_chart {N r : ℕ} {Z : Scheme.{0}} (j : Z ⟶ pullback (PSpace.str ℚ N) (PSpace.str ℚ r))
    [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0)
    (h₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx) (h₂ : ζ ≫ j ≫ pullback.snd _ _ = point ℚ x' hx')
    (a : Fin (N + 1)) (l : Fin (r + 1)) (ha : x a ≠ 0) (hl : x' l ≠ 0) :
    IsAffineOpen ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) ∧
      ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l),
        Set.range (valMap ζ _ h).hom =
          Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l)) :=
  GlobalTheory.T.segre_product_affine_chart Ω N r Z j ζ x hx x' hx' h₁ h₂ a l ha hl

theorem snc_transfer {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) {W : Z.Opens} (hW : IsAffineOpen W)
    (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) : SncChart A e (valR ζ W σ) :=
  GlobalTheory.T.snc_chart_of_smooth_coords Ω Z ζ g e T hsm hc W hW h A hA σ hσ

theorem form_section {N : ℕ} {Z : Scheme.{0}} (u : Z ⟶ PSpace ℚ N) (η : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0)
    (hu : η ≫ u = point ℚ x hx) {W : Z.Opens} (hW : ⊤ ≤ η ⁻¹ᵁ W) {a : Fin (N + 1)} (hi : W ≤ u ⁻¹ᵁ chart ℚ N a)
    {n : ℕ} {G : MvPolynomial (Fin (N + 1)) ℚ} (hG : G.IsHomogeneous n) :
    ∃ σ : Γ(Z, W), valR η W σ = aeval (fun j => x j / x a) G ∧
      Z.basicOpen σ = W ⊓ u ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G := by
  refine ⟨(u.appLE _ W hi).hom (formOn (chart ℚ N a) a le_rfl n G hG), ?_, ?_⟩
  · have ha : x a ≠ 0 := ne_zero_of_le hu hW hi
    have h : ⊤ ≤ point ℚ x hx ⁻¹ᵁ chart ℚ N a := (le_point_preimage_iff a).2 ha
    rw [valR_appLE η u hi hW, hu, formOn_eq_aeval, valR_eq _ _ h]
    exact (valMap_eval₂Hom point_str h _ G).trans (by simp only [valR_point_ratio ha])
  · rw [Scheme.basicOpen_appLE, basicOpen_formOn]
    refine le_antisymm (le_inf inf_le_left (inf_le_right.trans (u.preimage_mono inf_le_right)))
      (le_inf inf_le_left ?_)
    rintro t ⟨h1, h2⟩
    exact ⟨hi h1, h2⟩

theorem chart_single {N : ℕ} {Z : Scheme.{0}} (i : Z ⟶ PSpace ℚ N) [IsClosedImmersion i] (ζ : Sp Ω ⟶ Z)
    (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (hi : ζ ≫ i = point ℚ x hx) (a : Fin (N + 1)) (ha : x a ≠ 0) :
    IsAffineOpen (i ⁻¹ᵁ chart ℚ N a) ∧ ∃ h : ⊤ ≤ ζ ⁻¹ᵁ (i ⁻¹ᵁ chart ℚ N a),
      Set.range (valMap ζ _ h).hom = Algebra.adjoin ℚ (Set.range fun k => x k / x a) := by
  have hc := (isAffineOpen_chart ℚ N a)
  refine ⟨hc.preimage i, le_preimage_chart hi ha, ?_⟩
  have h₁ : ⊤ ≤ point ℚ x hx ⁻¹ᵁ chart ℚ N a := (le_point_preimage_iff a).2 ha
  rw [← range_valMap_point h₁, ← (i.app_surjective _ hc).range_comp]
  congr 1
  funext s
  have := valR_comp ζ i (chart ℚ N a) s
  rw [hi, valR_eq _ _ h₁, valR_eq _ _ (le_preimage_chart hi ha)] at this
  exact this.symm


section Top
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_smooth (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ)
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) :=
  GlobalTheory.T.exists_standard_smooth_localization Ω K ι y e hA N E c₀ hc

theorem adjoin_seg_le (y : (Σ k, ι k) → Ω) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    IntermediateField.adjoin ℚ ((Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) :
      Subalgebra ℚ Ω) : Set Ω) ≤ blockFnField y := by
  rw [IntermediateField.adjoin_le_iff]
  have h1 : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) ≤
      (blockFnField y).toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    change (∏ k, y ⟨k, E j k⟩) / (∏ k, y ⟨k, E c₀ k⟩) ∈ blockFnField y
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, E j k⟩, ⟨k, E c₀ k⟩, rfl, rfl⟩
  exact h1

end Top

end GlobalTheory.CompanionTheory.Ar.SncRes
