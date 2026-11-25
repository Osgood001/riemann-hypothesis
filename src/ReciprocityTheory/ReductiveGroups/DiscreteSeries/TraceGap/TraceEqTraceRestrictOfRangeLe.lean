module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

section LA

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]

theorem trace_eq_trace_restrict_of_range_le (f : Y →ₗ[ℂ] Y) (Y0 : Submodule ℂ Y)
    (h : LinearMap.range f ≤ Y0) :
    LinearMap.trace ℂ Y f =
      LinearMap.trace ℂ Y0 (f.restrict (fun x _ => h (LinearMap.mem_range_self f x))) := by
  have hm : ∀ x, f x ∈ Y0 := fun x => h (LinearMap.mem_range_self f x)
  calc LinearMap.trace ℂ Y f = LinearMap.trace ℂ Y (Y0.subtype ∘ₗ LinearMap.codRestrict Y0 f hm) := by
        rw [LinearMap.subtype_comp_codRestrict]
    _ = LinearMap.trace ℂ Y0 (LinearMap.codRestrict Y0 f hm ∘ₗ Y0.subtype) :=
        LinearMap.trace_comp_comm' _ _
    _ = _ := by
        congr 1

theorem trace_eq_add_of_isCompl (f : Y →ₗ[ℂ] Y) {K R : Submodule ℂ Y} (hKR : IsCompl K R)
    (hK : ∀ x ∈ K, f x ∈ K) (hR : ∀ x ∈ R, f x ∈ R) :
    LinearMap.trace ℂ Y f = LinearMap.trace ℂ K (f.restrict hK) + LinearMap.trace ℂ R (f.restrict hR) := by
  have hrK : LinearMap.range (f ∘ₗ K.projection R hKR) ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact hK _ (Submodule.projection_apply_mem _ _)
  have hrR : LinearMap.range (f ∘ₗ R.projection K hKR.symm) ≤ R := by
    rintro _ ⟨x, rfl⟩
    exact hR _ (Submodule.projection_apply_mem _ _)
  have h1 : LinearMap.trace ℂ Y f = LinearMap.trace ℂ Y (f ∘ₗ K.projection R hKR) +
      LinearMap.trace ℂ Y (f ∘ₗ R.projection K hKR.symm) := by
    rw [← map_add (f := _), ← LinearMap.comp_add, Submodule.projection_add_projection_eq_id, LinearMap.comp_id]
  rw [h1, trace_eq_trace_restrict_of_range_le _ K hrK, trace_eq_trace_restrict_of_range_le _ R hrR]
  congr 2
  · ext x
    simp
  · ext x
    simp

end LA

section S4

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]

theorem str_eq_str_ker (Dl Γ B : Y →ₗ[ℂ] Y) (hD : ∀ x y, inner ℂ (Dl x) y = inner ℂ x (Dl y))
    (hΓD : ∀ x, Γ (Dl x) = -Dl (Γ x)) (hBD : ∀ x, B (Dl x) = Dl (B x)) :
    ∃ hk : ∀ x ∈ LinearMap.ker Dl, (Γ ∘ₗ B) x ∈ LinearMap.ker Dl,
      LinearMap.trace ℂ Y (Γ ∘ₗ B) = LinearMap.trace ℂ (LinearMap.ker Dl) ((Γ ∘ₗ B).restrict hk) := by
  have hAnti (y : Y) : Dl ((Γ ∘ₗ B) y) = -((Γ ∘ₗ B) (Dl y)) := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hBD, hΓD, neg_neg]
  have hk : ∀ x ∈ LinearMap.ker Dl, (Γ ∘ₗ B) x ∈ LinearMap.ker Dl := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hAnti, hx, map_zero, neg_zero]
  have hV : ∀ x ∈ LinearMap.range Dl, (Γ ∘ₗ B) x ∈ LinearMap.range Dl := by
    rintro _ ⟨y, rfl⟩
    exact ⟨-((Γ ∘ₗ B) y), by rw [map_neg, hAnti, neg_neg]⟩
  have hsym : Dl.IsSymmetric := hD
  have hkr : IsCompl (LinearMap.ker Dl) (LinearMap.range Dl) := by
    simpa only [hsym.orthogonal_range] using
      (Submodule.isCompl_orthogonal (LinearMap.range Dl)).symm
  refine ⟨hk, ?_⟩
  rw [trace_eq_add_of_isCompl _ hkr hk hV]
  let T := (Γ ∘ₗ B).restrict hV
  let e := LinearEquiv.ofInjectiveEndo
    (Dl.restrict fun x _ => LinearMap.mem_range_self Dl x)
    ((LinearMap.injective_restrict_iff _).mpr hkr.disjoint.symm)
  have hconj : e.conj T = -T := by
    ext1 v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, LinearMap.neg_apply]
    exact Subtype.ext (hAnti w)
  have ht := LinearMap.trace_conj' T e
  rw [hconj, map_neg] at ht
  change LinearMap.trace ℂ _ _ + LinearMap.trace ℂ _ T = _
  rw [CharZero.neg_eq_self_iff.mp ht, add_zero]

end S4

end ReciprocityTheory.ChartRestriction.DS.TRGap
