module

public import Mathlib

@[expose] public section

open Polynomial

namespace Bl.ScalarIdentities

private lemma scal {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (S0 : Type) [AddCommGroup S0] [Module K S0] [Module A S0] [IsScalarTower K A S0]
    [FiniteDimensional K S0] [IsSimpleModule A S0] (g : S0 →ₗ[A] S0) :
    ∃ c : K, ∀ v : S0, g v = c • v := by
  have : Nontrivial S0 := IsSimpleModule.nontrivial A S0
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (g.restrictScalars K)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let h : S0 →ₗ[A] S0 := g - Algebra.lsmul K A S0 c
  have h0 : h v = 0 := sub_eq_zero.mpr hv.apply_eq_smul
  have hni : ¬ Function.Injective h := by
    intro hi
    exact hv.2 (hi (h0.trans h.map_zero.symm))
  have hz : h = 0 := (LinearMap.injective_or_eq_zero h).resolve_left hni
  refine ⟨c, fun w => ?_⟩
  have := LinearMap.congr_fun hz w
  exact sub_eq_zero.mp this

theorem goal1 {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (S0 : Type) [AddCommGroup S0] [Module K S0] [Module A S0] [IsScalarTower K A S0]
    [FiniteDimensional K S0] [IsSimpleModule A S0] (φ : S0 →ₗ[K] S0) :
    ∃ u : A, ∀ v : S0, u • v = φ v := by
  classical
  let f : Module.End (Module.End A S0) S0 :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun g v => by
        obtain ⟨c, hc⟩ := scal (K := K) S0 g
        simp only [Module.End.smul_def, RingHom.id_apply, hc, φ.map_smul] }
  let b := Module.finBasis K S0
  obtain ⟨r, hr⟩ := jacobson_density f (Finset.univ.image b)
  refine ⟨r, fun v => ?_⟩
  let ψ : S0 →ₗ[K] S0 := Algebra.lsmul K K S0 r
  have hψ : ψ = φ := b.ext fun i => (hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))).symm
  exact LinearMap.congr_fun hψ v

end Bl.ScalarIdentities
