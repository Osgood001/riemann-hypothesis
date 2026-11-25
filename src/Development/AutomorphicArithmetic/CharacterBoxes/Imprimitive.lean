module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

@[expose] public section

namespace Formalism.HC

private theorem PChar.ext_int {ψ ρ : PChar} (h : ψ.N = ρ.N)
    (ha : ∀ a : ℤ, ψ.χ a = ρ.χ a) : ψ = ρ := by
  obtain ⟨n, χ, hχ⟩ := ψ
  obtain ⟨m, η, hη⟩ := ρ
  change n = m at h
  subst m
  have he : χ = η := by
    apply DFunLike.ext
    intro x
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    exact ha a
  subst η
  rfl

/-- Inducing a character to a multiple modulus does not change its primitive part. -/
theorem PChar.of_changeLevel {n m : ℕ} [NeZero n] [NeZero m] (h : n ∣ m)
    (χ : DirichletCharacter ℂ n) : PChar.of (DirichletCharacter.changeLevel h χ) = PChar.of χ :=
  PChar.ext_int (χ.conductor_changeLevel h) (DirichletCharacter.primitiveCharacter_changeLevel_apply h χ)

/-- Every power contributes its primitive part to the cyclic level of the generator,
even when the generator itself is imprimitive at the original modulus. -/
theorem Level.of_mem_cyc_of_mem_zpowers {n : ℕ} [NeZero n] {χ η : DirichletCharacter ℂ n}
    (h : η ∈ Subgroup.zpowers χ) : PChar.of η ∈ (Level.cyc (PChar.of χ)).KEPT := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  apply (Level.mem_ofSub (Subgroup.zpowers χ.primitiveCharacter) _).mpr
  refine ⟨χ.primitiveCharacter ^ z, ⟨z, rfl⟩, ?_⟩
  calc PChar.of (χ.primitiveCharacter ^ z) =
      PChar.of (DirichletCharacter.changeLevel χ.conductor_dvd_level (χ.primitiveCharacter ^ z)) :=
        (PChar.of_changeLevel χ.conductor_dvd_level _).symm
    _ = _ := congrArg PChar.of (by rw [map_zpow, DirichletCharacter.changeLevel_primitiveCharacter])

/-- If the character group is cyclic, one primitive part supplies a level covering
all characters at the original modulus. There need not be a primitive character of that
modulus (for instance, modulus two). -/
theorem Level.exists_cyc_keeps_all {n : ℕ} [NeZero n] [IsCyclic (DirichletCharacter ℂ n)] :
    ∃ χ : DirichletCharacter ℂ n,
      ∀ η : DirichletCharacter ℂ n, PChar.of η ∈ (Level.cyc (PChar.of χ)).KEPT := by
  obtain ⟨χ, hg⟩ := IsCyclic.exists_generator (α := DirichletCharacter ℂ n)
  exact ⟨χ, fun η => Level.of_mem_cyc_of_mem_zpowers (hg η)⟩

/-- Cyclicity of the ordinary unit group suffices. -/
theorem Level.exists_cyc_keeps_all_of_isCyclic_units {n : ℕ} [NeZero n] [IsCyclic (ZMod n)ˣ] :
    ∃ χ : DirichletCharacter ℂ n,
      ∀ η : DirichletCharacter ℂ n, PChar.of η ∈ (Level.cyc (PChar.of χ)).KEPT := by
  let e := (DirichletCharacter.mulEquiv_units ℂ n).some
  have := isCyclic_of_injective e.toMonoidHom e.injective
  exact Level.exists_cyc_keeps_all

end Formalism.HC

open Formalism.HC

/-- Away from the imaginary axis, adding Euler factors by raising the level
introduces no zeros. The usual principal-character pole is excluded. -/
theorem UpperTheory.Top.changeLevel_zero_iff {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : s.re ≠ 0) (hpole : χ ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction (χ.changeLevel hMN) s = 0 ↔ DirichletCharacter.LFunction χ s = 0 := by
  rw [DirichletCharacter.LFunction_changeLevel hMN χ hpole, mul_eq_zero]
  refine or_iff_left (Finset.prod_ne_zero_iff.mpr fun p hp => ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  by_cases hu : IsUnit (p : ZMod M)
  · intro he
    have hz : χ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -he
    have hn := congrArg norm hz
    rw [norm_mul, ← hu.unit_spec, χ.unit_norm_eq_one hu.unit, one_mul,
      Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re, norm_one] at hn
    have hp₁ : 1 < (p : ℝ) := by exact_mod_cast hp'.one_lt
    rcases lt_or_gt_of_ne hs with h | h
    · exact (ne_of_gt (Real.one_lt_rpow hp₁ (neg_pos.mpr h))) hn
    · exact (ne_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hp₁ (neg_neg_of_pos h))) hn
  · simp [χ.map_nonunit hu]

/-- Only the primitive part of this character needs a zero-free certificate. -/
theorem UpperTheory.Top.imprimitive_of_primitive {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : (PChar.of χ).ZeroFreeAbove (1 / 2)) (s : ℂ) (hs : 1 / 2 < s.re) (hpole : χ ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  have : NeZero χ.conductor := (PChar.of χ).ne
  have hp : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := hpole.imp_left fun hχ he => hχ (by
    rw [← χ.changeLevel_primitiveCharacter, he, DirichletCharacter.changeLevel_one])
  have hz := changeLevel_zero_iff χ.conductor_dvd_level χ.primitiveCharacter s (by linarith) hp
  rw [χ.changeLevel_primitiveCharacter] at hz
  exact fun he => h s hs (hz.mp he)

theorem UpperTheory.Top.imprimitive :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 :=
  fun h _ _ χ => imprimitive_of_primitive χ (h _ trivial)
