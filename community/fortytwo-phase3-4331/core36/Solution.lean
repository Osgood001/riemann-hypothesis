import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition

open NumberField GlobalTheory GlobalTheory.CompanionTheory.Ar.Fl
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace AlpogeRHCore36

theorem pureFamilyDecomposition :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
      (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ))
      (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P)
      (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (n : ℕ),
      IsPure hP x →
      (∀ y : D.La, n • y ∈ Submodule.span (𝓞 E) (Set.range x)) →
      (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true),
        ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) ∧
      (∀ y ∈ PureType.lat hP (sgnRt H true),
        n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl))) ∧
      ∀ y ∈ PureType.lat hP (sgnRt H false),
        n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) := by
  intro E _ _ _ H D g ty P hP p q x n hx hn
  let A := Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl))
  let B := Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr))
  let L := PureType.lat hP (sgnRt H true)
  let R := PureType.lat hP (sgnRt H false)
  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    apply (Nat.cast_ne_zero.mpr H.d_prime.ne_zero : (H.d : ℂ) ≠ 0)
    linear_combination H.sqrt_neg_disc_sq - (H.rt0 / 2) * h
  have hlatL : A ≤ L :=
    Submodule.span_le.2 (Set.range_subset_iff.mpr hx.1)
  have hlatR : B ≤ R :=
    Submodule.span_le.2 (Set.range_subset_iff.mpr hx.2)
  have hLR : Disjoint L R := by
    apply Submodule.disjoint_def.mpr
    intro z h1 h2
    apply hP.2.1
    rw [map_zero]
    funext j
    by_cases hj : ty j (H.rt : E) = H.rt0
    · have : ty j (H.rt : E) ≠ -H.rt0 := by rw [hj]; exact hne
      exact h2 j (by simpa [sgnRt] using this)
    · exact h1 j (by simpa [sgnRt] using hj)
  rw [Sum.range_eq x, Submodule.span_union] at hn
  change ∀ y, n • y ∈ A ⊔ B at hn
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.mp (hn y)
    exact ⟨a, hlatL ha, b, hlatR hb, e.symm⟩
  · intro y hy
    change n • y ∈ A
    rw [← sup_bot_eq A, ← (hLR.symm.mono_left hlatR).eq_bot, ← sup_inf_assoc_of_le B hlatL]
    exact ⟨hn y, L.smul_of_tower_mem n hy⟩
  · intro y hy
    change n • y ∈ B
    rw [← sup_bot_eq B, ← (hLR.mono_left hlatL).eq_bot, ← sup_inf_assoc_of_le A hlatR, sup_comm B A]
    exact ⟨hn y, R.smul_of_tower_mem n hy⟩

end AlpogeRHCore36
