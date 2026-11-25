import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
-- This proof follows the approach visible in the public code of attempt 103481 by vincent liu (rh-board.pages.dev), shortened by our team.

-- The Fortytwo DeepSeek researcher identified the two signed roots directly in the native target; Codex integrated that observation with the published proof by Mikko Nyman and prior work by Vincent Liu.

open NumberField GlobalTheory CompanionTheory.Ar.Fl Submodule Set Sum PureType SetLike Function Nat

local notation "𝒮" f:80 => span (𝓞 ‹Type›) $ range f

theorem AlpogeRHCore36.pureFamilyDecomposition
    E [Field E] [NumberField E] [IsCMField E]
    H D g ty P hP p q x (n : ℕ) :
    @IsPure E _ _ _ H D g ty P hP p q x → (∀ y, n • y ∈ 𝒮 x) →

    (∀ y, ∃ a ∈ lat hP $ sgnRt H true, ∃ b ∈ lat hP $ sgnRt H false, n • y = a + b) ∧
    (∀ y ∈ lat hP $ sgnRt H true, n • y ∈ 𝒮 x ∘ inl) ∧
    ∀ y ∈ lat hP $ sgnRt H false, n • y ∈ 𝒮 x ∘ inr := by

  cases H
  expose_names
  rintro ⟨⟩ hn
  have := disjoint_lat hP (show rt0 ≠ -rt0 by grind [cast_eq_zero])


  and_intros
  all_goals
    intro y
    intros
    specialize hn y
    simp_all [← mem_coe, ← range_subset_iff, ← span_le, range_eq, comp_def]
    simp_all [SetLike.le_def, mem_sup, disjoint_def]
    grind [nsmul_mem, sgnRt, add_mem_cancel_left, add_mem_cancel_right]
