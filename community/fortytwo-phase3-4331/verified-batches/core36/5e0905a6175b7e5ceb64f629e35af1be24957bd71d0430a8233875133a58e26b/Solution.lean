import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
-- Credit: proof and notations from Andrew Pullin, public Fast 36 attempt 111725, https://riemann.verifytask.cn/api/attempt/111725.
-- Levent Alpöge's original formalization. Adapted from Vladyslav Larin's
-- 221-token proof, building on Vincent Liu:
-- vlarin/riemann-hypothesis@f7b0b95fbef89763c756d6e2b82f4edd2f4b5c54.

-- Credit: the scaled span-membership notation is from Astra’s 209-token team proof.
open NumberField GlobalTheory CompanionTheory.Ar.Fl Submodule Set PureType SetLike Function Nat Sum

attribute [grind .] nsmul_mem sgnRt add_mem_cancel_left add_mem_cancel_right cast_eq_zero disjoint_def mem_sup comp_def not_le_iff_exists


set_option hygiene false
notation "𝒮" f => n • y ∈ span (𝓞 E) (range f)

theorem AlpogeRHCore36.pureFamilyDecomposition
    E [Field E] [NumberField E] [IsCMField E]
    H D g ty P hP p q x (n : ℕ) :
    @IsPure E _ _ _ H D g ty P hP p q x → (∀ y, 𝒮 x) →

    dsimp% let L := lat hP ∘ sgnRt H
    (∀ y, ∃ a ∈ L true, ∃ b ∈ L false, n • y = a + b) ∧
    (∀ y ∈ L true, 𝒮 x ∘ inl) ∧
    ∀ y ∈ L false, 𝒮 x ∘ inr := by

  cases H
  rintro ⟨⟩ hn
  and_intros
  all_goals
    intros
    expose_names
    have := disjoint_lat hP $ show rt0 ≠ -rt0 by grind
    specialize hn y
    simp_all [← mem_coe, ← range_subset_iff, ← span_le, range_eq]
    simp_all
    grind
-- Source adapted from Mikko Nyman, Playground #111849. Codex prepared and checked this reduction.
