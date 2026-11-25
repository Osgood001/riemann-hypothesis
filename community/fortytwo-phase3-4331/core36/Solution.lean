import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
-- This proof follows the approach visible in the public code of attempt 103481 by vincent liu (rh-board.pages.dev), shortened by our team.

-- The Fortytwo DeepSeek researcher identified the two signed roots directly in the native target; Codex integrated that observation with the published proof by Mikko Nyman and prior work by Vincent Liu.

open NumberField GlobalTheory CompanionTheory.Ar.Fl Submodule Set Sum PureType SetLike Function

local notation "𝒮" f:80 => span (𝓞 ‹Type›) $ range f

theorem AlpogeRHCore36.pureFamilyDecomposition
    E [Field E] [NumberField E] [IsCMField E]
    H D g ty P hP p q x (n : ℕ) :
    @IsPure E _ _ _ H D g ty P hP p q x → (∀ y, n • y ∈ 𝒮 x) →

    (∀ y, ∃ a ∈ lat hP $ sgnRt H true, ∃ b ∈ lat hP $ sgnRt H false, n • y = a + b) ∧
    (∀ y ∈ lat hP $ sgnRt H true, n • y ∈ 𝒮 x ∘ inl) ∧
    ∀ y ∈ lat hP $ sgnRt H false, n • y ∈ 𝒮 x ∘ inr := by

  rintro ⟨hp, hm⟩ hn
  have := disjoint_lat hP (show H.rt0 ≠ -H.rt0 by grind [H.sqrt_neg_disc_sq, H.d_mod, Nat.cast_eq_zero])

  simp only [← mem_coe, ← range_subset_iff, ← span_le] at hp hm
  simp_all [disjoint_def, range_eq, mem_sup, SetLike.le_def, comp_def]

  and_intros
  all_goals
    intro y
    try intro hy; have := nsmul_mem hy n
    grind [hn y, sgnRt, add_mem_cancel_left, add_mem_cancel_right]
