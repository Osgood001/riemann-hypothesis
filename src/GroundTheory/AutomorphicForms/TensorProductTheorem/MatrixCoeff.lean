module

public import Mathlib
public import Lemmata.OrbitSpans.Basic

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open Set

namespace RestrictedTensor

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

def orbitSpan (ρ : Representation ℂ G V) (v : V) : Subrepresentation ρ :=
  Bl.OrbitSpans.orbitSpan ρ v

theorem mem_orbitSpan_self (ρ : Representation ℂ G V) (v : V) : v ∈ (orbitSpan ρ v).toSubmodule :=
  Bl.OrbitSpans.mem_orbitSpan_self ρ v

theorem orbitSpan_eq_top {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) :
    orbitSpan ρ v = ⊤ := by
  exact Bl.OrbitSpans.orbitSpan_eq_top ρ v hv

theorem mem_span_orbit {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) (x : V) :
    x ∈ Submodule.span ℂ (range fun g => ρ g v) := by
  change x ∈ (orbitSpan ρ v).toSubmodule
  rw [orbitSpan_eq_top hv]
  exact Submodule.mem_top

theorem eq_zero_of_forall_apply {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0)
    {l : Module.Dual ℂ V} (h : ∀ g, l (ρ g v) = 0) : l = 0 := by
  exact LinearMap.ext_on_range (congrArg Subrepresentation.toSubmodule (orbitSpan_eq_top hv)) h

theorem eq_zero_of_forall_apply_act {ρ : Representation ℂ G V} [ρ.IsIrreducible]
    {l : Module.Dual ℂ V} (hl : l ≠ 0) {x : V} (h : ∀ g, l (ρ g x) = 0) : x = 0 := by
  by_contra hx
  exact hl (eq_zero_of_forall_apply (ρ := ρ) hx h)

def orbitMap (ρ : Representation ℂ G V) (v : V) : (G →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun g => ρ g v

theorem orbitMap_apply (ρ : Representation ℂ G V) (v : V) (c : G →₀ ℂ) :
    orbitMap ρ v c = c.sum fun g a => a • ρ g v := by
  rw [orbitMap, Finsupp.linearCombination_apply]

theorem orbitMap_single (ρ : Representation ℂ G V) (v : V) (g : G) (a : ℂ) :
    orbitMap ρ v (Finsupp.single g a) = a • ρ g v := by
  rw [orbitMap, Finsupp.linearCombination_single]

theorem orbitMap_mapDomain (ρ : Representation ℂ G V) (v : V) (h : G) (c : G →₀ ℂ) :
    orbitMap ρ v (Finsupp.mapDomain (h * ·) c) = ρ h (orbitMap ρ v c) := by
  exact LinearMap.congr_fun (Finsupp.lmapDomain_linearCombination ℂ (v := fun g => ρ g v)
    (v' := fun g => ρ g v) (h * ·) (ρ h) (fun g => by simp [map_mul])) c

theorem range_orbitMap (ρ : Representation ℂ G V) (v : V) :
    LinearMap.range (orbitMap ρ v) = Submodule.span ℂ (range fun g => ρ g v) := by
  rw [orbitMap, Finsupp.range_linearCombination]

theorem linearForm_orbitMap (ρ : Representation ℂ G V) (v : V) (l : Module.Dual ℂ V) (h : G)
    (c : G →₀ ℂ) : l (ρ h (orbitMap ρ v c)) = c.sum fun g a => a * l (ρ (h * g) v) := by
  rw [orbitMap_apply, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, map_mul, mul_apply_eq_comp]

theorem nonempty_equiv_of_matrixCoeff_eq {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    [ρ.IsIrreducible] [σ.IsIrreducible] {v : V} {l : Module.Dual ℂ V} {w : W}
    {m : Module.Dual ℂ W} (h : ∀ g, l (ρ g v) = m (σ g w)) (hne : ∃ g, l (ρ g v) ≠ 0) :
    Nonempty (ρ.Equiv σ) := by
  obtain ⟨g₀, hg₀⟩ := hne
  have hv : v ≠ 0 := by rintro rfl; simp at hg₀
  have hm : m ≠ 0 := by rintro rfl; exact hg₀ (by rw [h]; rfl)

  have hker : LinearMap.ker (orbitMap ρ v) ≤ LinearMap.ker (orbitMap σ w) := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    refine eq_zero_of_forall_apply_act (ρ := σ) hm fun k => ?_
    rw [linearForm_orbitMap]
    have := linearForm_orbitMap ρ v l k c
    rw [hc, map_zero, map_zero] at this
    rw [this]
    exact Finsupp.sum_congr fun g _ => by rw [h]
  have hsurj : Function.Surjective (orbitMap ρ v) := by
    rw [← LinearMap.range_eq_top, range_orbitMap]
    exact congrArg Subrepresentation.toSubmodule (orbitSpan_eq_top hv)
  let e := LinearMap.quotKerEquivOfSurjective (orbitMap ρ v) hsurj
  let F : V →ₗ[ℂ] W := ((LinearMap.ker (orbitMap ρ v)).liftQ (orbitMap σ w) hker).comp
    e.symm.toLinearMap
  have hF : ∀ c, F (orbitMap ρ v c) = orbitMap σ w c := by
    intro c
    have : e.symm (orbitMap ρ v c) = Submodule.Quotient.mk c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hFint : ∀ g x, F (ρ g x) = σ g (F x) := by
    intro g x
    obtain ⟨c, rfl⟩ := hsurj x
    rw [← orbitMap_mapDomain, hF, hF, orbitMap_mapDomain]
  let Fi : Representation.IntertwiningMap ρ σ := ⟨F, fun g => LinearMap.ext fun x => hFint g x⟩
  have hFi0 : Fi ≠ 0 := by
    intro h0
    have h1 : F v = w := by
      have := hF (Finsupp.single 1 1)
      rwa [orbitMap_single, orbitMap_single, one_smul, one_smul, map_one,
        one_apply_eq_self, map_one, one_apply_eq_self] at this
    have h2 : F v = 0 := by
      have : Fi v = 0 := by rw [h0]; rfl
      exact this
    apply hg₀
    rw [h, ← h1, h2, map_zero, map_zero]
  rcases Representation.IsIrreducible.bijective_or_eq_zero Fi with hb | h0
  · exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective F hb)
      fun g => LinearMap.ext fun x => hFint g x⟩
  · exact absurd h0 hFi0

end RestrictedTensor

end GroundTheory.Automorphic
