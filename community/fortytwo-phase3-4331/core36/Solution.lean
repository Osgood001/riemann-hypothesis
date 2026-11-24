import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
-- This proof follows the approach visible in the public code of attempt 103481 by vincent liu (rh-board.pages.dev), shortened by our team.

-- The Fortytwo DeepSeek researcher identified the two signed roots directly in the native target; Codex integrated that observation with the published proof by Mikko Nyman and prior work by Vincent Liu.

open NumberField GlobalTheory CompanionTheory.Ar.Fl
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Submodule Set Sum PureType

theorem AlpogeRHCore36.pureFamilyDecomposition
    E [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (D : Datum H) g (ty : Fin g → _) P
    (hP : IsPeriod D ty P) p q (x : Fin p ⊕ Fin q → _) (n : ℕ)
    (hx : IsPure hP x) (hn : ∀ y, n • y ∈ span (𝓞 E) (range x)) :

    (∀ y, ∃ a ∈ lat hP (sgnRt H true), ∃ b ∈ lat hP (sgnRt H false), n • y = a + b) ∧
    (∀ y ∈ lat hP (sgnRt H true), n • y ∈ span (𝓞 E) (range (x ∘ inl))) ∧
    ∀ y ∈ lat hP (sgnRt H false), n • y ∈ span (𝓞 E) (range (x ∘ inr)) := by

  have := disjoint_def.mp $ disjoint_lat hP (show H.rt0 ≠ -H.rt0 by grind [H.sqrt_neg_disc_sq, H.d_mod, Nat.cast_eq_zero])

  simp_rw [range_eq, span_union, mem_sup, mem_span, range_subset_iff] at hn ⊢

  and_intros <;> intro y <;> obtain ⟨a, h, b, k, e⟩ := hn y
  all_goals try intro hy; have := nsmul_mem hy n
  all_goals grind [sgnRt, h _ hx.1, k _ hx.2, Submodule.add_mem_iff_left, add_comm]
