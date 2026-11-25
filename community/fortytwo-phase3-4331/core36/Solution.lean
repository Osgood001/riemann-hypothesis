import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
-- Levent Alpöge's original formalization. The proof follows Vladyslav Larin /
-- Fortytwo's 230-token version, building on Vincent Liu and Mikko Nyman:
-- vlarin/riemann-hypothesis@f7b0b95fbef89763c756d6e2b82f4edd2f4b5c54.

open NumberField GlobalTheory CompanionTheory.Ar.Fl Submodule Set Sum PureType SetLike Function Nat

local notation "𝒮" f => span (𝓞 ‹Type›) $ range f

theorem AlpogeRHCore36.pureFamilyDecomposition
    E [Field E] [NumberField E] [IsCMField E]
    H D g ty P hP p q x (n : ℕ) :
    @IsPure E _ _ _ H D g ty P hP p q x → (∀ y, n • y ∈ 𝒮 x) →

    dsimp% let L := lat hP ∘ sgnRt H
    (∀ y, ∃ a ∈ L true, ∃ b ∈ L false, n • y = a + b) ∧
    (∀ y ∈ L true, n • y ∈ 𝒮 x ∘ inl) ∧
    ∀ y ∈ L false, n • y ∈ 𝒮 x ∘ inr := by

  cases H
  rintro ⟨⟩ hn
  and_intros
  all_goals
    intros
    expose_names
    have := disjoint_lat hP $ show rt0 ≠ -rt0 by grind [cast_eq_zero]
    specialize hn y
    simp_all [← mem_coe, ← range_subset_iff, ← span_le, range_eq, comp_def]
    simp_all [SetLike.le_def, mem_sup, disjoint_def]
    grind [nsmul_mem, sgnRt, add_mem_cancel_left, add_mem_cancel_right]
