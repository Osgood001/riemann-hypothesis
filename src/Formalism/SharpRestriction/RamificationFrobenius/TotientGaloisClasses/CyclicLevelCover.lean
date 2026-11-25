module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

@[expose] public section

namespace Formalism.HC

open DirichletCharacter

private theorem primitive_eq_iff_induced_eq {m : ℕ} [NeZero m] (ψ ρ : PChar)
    (hψ : ψ.N ∣ m) (hρ : ρ.N ∣ m) :
    ψ = ρ ↔ changeLevel hψ ψ.χ = changeLevel hρ ρ.χ := by
  constructor
  · rintro rfl; rfl
  · obtain ⟨a, χ, hχ⟩ := ψ
    obtain ⟨b, η, hη⟩ := ρ
    intro h
    change changeLevel hψ χ = changeLevel hρ η at h
    have he : a = b := by
      rw [← hχ, ← hη, ← χ.conductor_changeLevel hψ, h, η.conductor_changeLevel]
    subst b
    have heq := changeLevel_injective hψ h
    subst η
    rfl

/-- Two characters at arbitrary levels have the same primitive part exactly when
their lifts to any common multiple agree. -/
theorem PChar.of_eq_iff_common_lift {m n q : ℕ} [NeZero m] [NeZero n] [NeZero q]
    (hm : m ∣ q) (hn : n ∣ q) (χ : DirichletCharacter ℂ m) (η : DirichletCharacter ℂ n) :
    PChar.of χ = PChar.of η ↔ changeLevel hm χ = changeLevel hn η := by
  have lift {a : ℕ} (h : a ∣ q) (θ : DirichletCharacter ℂ a) :
      changeLevel (θ.conductor_dvd_level.trans h) θ.primitiveCharacter = changeLevel h θ := by
    rw [θ.primitiveCharacter.changeLevel_trans θ.conductor_dvd_level h,
      changeLevel_primitiveCharacter]
  exact (primitive_eq_iff_induced_eq _ _ (χ.conductor_dvd_level.trans hm)
    (η.conductor_dvd_level.trans hn)).trans
    (by
      change changeLevel _ χ.primitiveCharacter = changeLevel _ η.primitiveCharacter ↔ _
      rw [lift hm χ, lift hn η])

/-- Restricting an arbitrary-modulus cyclic level to the characters at n gives
a single cyclic subgroup at n. The common comparison modulus is lcm(m,n). -/
theorem Level.exists_zpowers_for_raw_cyclic_kept {m n : ℕ} [NeZero m] [NeZero n]
    (χ : DirichletCharacter ℂ m) :
    ∃ η : DirichletCharacter ℂ n, ∀ θ : DirichletCharacter ℂ n,
      PChar.of θ ∈ (Level.ofSub (Subgroup.zpowers χ)).KEPT ↔ θ ∈ Subgroup.zpowers η := by
  have : NeZero (Nat.lcm m n) := ⟨(Nat.lcm_pos (NeZero.pos m) (NeZero.pos n)).ne'⟩
  let f := changeLevel (R := ℂ) (Nat.dvd_lcm_left m n)
  let g := changeLevel (R := ℂ) (Nat.dvd_lcm_right m n)
  let C := Subgroup.zpowers (f χ)
  let H := C.comap g
  have hcyc : IsCyclic H := isCyclic_of_injective (g.subgroupComap C)
    (g.subgroupComap_injective C (changeLevel_injective _))
  obtain ⟨η, he⟩ := H.isCyclic_iff_exists_zpowers_eq.mp hcyc
  refine ⟨η, fun θ => ?_⟩
  rw [Level.mem_ofSub, he]
  change (∃ ξ ∈ Subgroup.zpowers χ, PChar.of ξ = PChar.of θ) ↔ g θ ∈ Subgroup.zpowers (f χ)
  have same (ξ : DirichletCharacter ℂ m) := PChar.of_eq_iff_common_lift (Nat.dvd_lcm_left m n)
    (Nat.dvd_lcm_right m n) ξ θ
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, h⟩
    exact ⟨z, (f.map_zpow χ z).symm.trans ((same _).mp h)⟩
  · rintro ⟨z, hz⟩
    exact ⟨χ ^ z, ⟨z, rfl⟩, (same _).mpr ((f.map_zpow χ z).trans hz)⟩

/-- Restrict a cyclic level to a target modulus without changing which primitive
characters at that modulus the level keeps. -/
theorem Level.exists_raw_cyclic_replacement {m n : ℕ} [NeZero m] [NeZero n]
    (χ : DirichletCharacter ℂ m) :
    ∃ η : DirichletCharacter ℂ n, ∀ θ : DirichletCharacter ℂ n,
      PChar.of θ ∈ (Level.ofSub (Subgroup.zpowers χ)).KEPT ↔
      PChar.of θ ∈ (Level.ofSub (Subgroup.zpowers η)).KEPT := by
  obtain ⟨η, hη⟩ := Level.exists_zpowers_for_raw_cyclic_kept (n := n) χ
  refine ⟨η, fun θ => (hη θ).trans ?_⟩
  rw [Level.mem_ofSub]
  have same (ξ : DirichletCharacter ℂ n) : PChar.of ξ = PChar.of θ ↔ ξ = θ := by
    simpa only [changeLevel_self] using
      PChar.of_eq_iff_common_lift (dvd_refl n) (dvd_refl n) ξ θ
  simp [same]

/-- Allowing arbitrary positive source moduli does not reduce the number of cyclic
levels needed to cover all primitive parts at n. This is a statement about covers
by these levels, not about every possible analytic proof. -/
theorem Level.cross_modulus_cover_budget_iff_fixed {n : ℕ} [NeZero n] (k : ℕ) :
    (∃ T : Finset ((m : ℕ+) × DirichletCharacter ℂ (m : ℕ)), T.card ≤ k ∧
      ∀ θ : DirichletCharacter ℂ n, ∃ u ∈ T,
        PChar.of θ ∈ (Level.ofSub (Subgroup.zpowers u.2)).KEPT) ↔
    ∃ S : Finset (DirichletCharacter ℂ n), S.card ≤ k ∧
      ∀ θ : DirichletCharacter ℂ n, ∃ η ∈ S,
        PChar.of θ ∈ (Level.ofSub (Subgroup.zpowers η)).KEPT := by
  classical
  constructor
  · rintro ⟨T, hk, h⟩
    choose f hf using fun (u : (m : ℕ+) × DirichletCharacter ℂ (m : ℕ)) =>
      Level.exists_raw_cyclic_replacement (n := n) u.2
    refine ⟨T.image f, Finset.card_image_le.trans hk, fun θ => ?_⟩
    obtain ⟨u, hu, hθ⟩ := h θ
    exact ⟨f u, Finset.mem_image_of_mem _ hu, (hf u θ).mp hθ⟩
  · rintro ⟨S, hk, h⟩
    let f (η : DirichletCharacter ℂ n) : (m : ℕ+) × DirichletCharacter ℂ (m : ℕ) :=
      ⟨⟨n, NeZero.pos n⟩, η⟩
    refine ⟨S.image f, Finset.card_image_le.trans hk, fun θ => ?_⟩
    obtain ⟨η, hη, hθ⟩ := h θ
    exact ⟨f η, Finset.mem_image_of_mem _ hη, hθ⟩

/-- Every nonidentity element of an exponent-two quotient needs its own cyclic
level, even if the source moduli of those levels are unrestricted. -/
theorem Level.card_sub_one_le_cyclic_cover {n : ℕ} [NeZero n] {Q : Type*} [Group Q] [Fintype Q]
    (f : DirichletCharacter ℂ n →* Q) (hf : Function.Surjective f)
    (hQ : ∀ q : Q, q ^ (2 : ℤ) = 1)
    (T : Finset ((m : ℕ+) × DirichletCharacter ℂ (m : ℕ)))
    (hc : ∀ θ : DirichletCharacter ℂ n, ∃ u ∈ T,
      PChar.of θ ∈ (Level.ofSub (Subgroup.zpowers u.2)).KEPT) :
    Fintype.card Q - 1 ≤ T.card := by
  classical
  choose g hg using fun (u : (m : ℕ+) × DirichletCharacter ℂ (m : ℕ)) =>
    Level.exists_zpowers_for_raw_cyclic_kept (n := n) u.2
  have hsub : (Finset.univ : Finset Q).erase 1 ⊆ T.image (fun u => f (g u)) := by
    intro q hq
    obtain ⟨θ, rfl⟩ := hf q
    obtain ⟨u, hu, hθ⟩ := hc θ
    obtain ⟨z, hz⟩ := (hg u θ).mp hθ
    have hpow : f θ = 1 ∨ f θ = f (g u) := by
      rw [← hz, map_zpow]
      rcases Int.even_or_odd' z with ⟨k, rfl | rfl⟩ <;> simp [zpow_add, zpow_mul, hQ]
    exact Finset.mem_image.mpr ⟨u, hu, (hpow.resolve_left (Finset.mem_erase.mp hq).1).symm⟩
  simpa using (Finset.card_le_card hsub).trans Finset.card_image_le

end Formalism.HC
