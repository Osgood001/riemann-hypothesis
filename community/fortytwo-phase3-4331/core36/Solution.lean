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
  have hsplit : ∀ y : D.La, ∃ a ∈ A,
      ∃ b ∈ B, n • y = a + b := by
    intro y
    have h := hn y
    rw [Sum.range_eq x, Submodule.span_union, Submodule.mem_sup] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    exact ⟨a, ha, b, hb, hab.symm⟩
  have hlatL : A ≤ L :=
    Submodule.span_le.2 (Set.range_subset_iff.mpr hx.1)
  have hlatR : B ≤ R :=
    Submodule.span_le.2 (Set.range_subset_iff.mpr hx.2)
  have hboth : ∀ z, z ∈ L → z ∈ R → z = 0 := by
    intro z h1 h2
    apply hP.2.1
    rw [map_zero]
    funext j
    by_cases hj : ty j (H.rt : E) = H.rt0
    · have : ty j (H.rt : E) ≠ -H.rt0 := by rw [hj]; exact hne
      exact h2 j (by simpa [sgnRt] using this)
    · exact h1 j (by simpa [sgnRt] using hj)
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    exact ⟨a, hlatL ha, b, hlatR hb, e⟩
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    have hb0 : b = 0 := hboth b (by
      simpa [e] using L.sub_mem
        (Submodule.smul_of_tower_mem _ n hy) (hlatL ha)) (hlatR hb)
    rw [e, hb0, add_zero]; exact ha
  · obtain ⟨a, ha, b, hb, e⟩ := hsplit y
    have ha0 : a = 0 := hboth a (hlatL ha) (by
      simpa [e] using R.sub_mem
        (Submodule.smul_of_tower_mem _ n hy) (hlatR hb))
    rw [e, ha0, zero_add]; exact hb

end AlpogeRHCore36
