module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

variable (L : Type) [Field L] [NumberField L]

def compAt (v : HeightOneSpectrum (𝓞 L)) (a : (AdeleRing (𝓞 L) L)ˣ) : v.adicCompletion L :=
  (a : AdeleRing (𝓞 L) L).2 v

theorem compAt_mul (v : HeightOneSpectrum (𝓞 L)) (a b : (AdeleRing (𝓞 L) L)ˣ) :
    compAt L v (a * b) = compAt L v a * compAt L v b := rfl

theorem compAt_one (v : HeightOneSpectrum (𝓞 L)) : compAt L v 1 = 1 := rfl

def levSub (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) : Subgroup (AdeleRing (𝓞 L) L)ˣ where
  carrier := {a | ∀ v, Valued.v (compAt L v a) = 1 ∧ (v ∈ S → Valued.v (compAt L v a - 1) ≤ WithZero.exp (-(N : ℤ)))}
  one_mem' := fun v => by
    refine ⟨by rw [compAt_one, map_one], fun _ => ?_⟩
    rw [compAt_one, sub_self, map_zero]
    exact zero_le
  mul_mem' := fun {a b} ha hb v => by
    rw [compAt_mul]
    refine ⟨by rw [map_mul, (ha v).1, (hb v).1, one_mul], fun hv => ?_⟩
    have e : compAt L v a * compAt L v b - 1 = compAt L v a * (compAt L v b - 1) + (compAt L v a - 1) := by ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((ha v).2 hv))
    rw [map_mul, (ha v).1, one_mul]
    exact (hb v).2 hv
  inv_mem' := fun {a} ha v => by
    have h1 : compAt L v a * compAt L v a⁻¹ = 1 := by rw [← compAt_mul, mul_inv_cancel, compAt_one]
    have hv1 : Valued.v (compAt L v a⁻¹) = 1 := by
      have := congrArg Valued.v h1
      rwa [map_mul, (ha v).1, one_mul, map_one] at this
    refine ⟨hv1, fun hv => ?_⟩
    have e : compAt L v a⁻¹ - 1 = -(compAt L v a⁻¹ * (compAt L v a - 1)) := by
      linear_combination h1
    rw [e, Valuation.map_neg, map_mul, hv1, one_mul]
    exact (ha v).2 hv

end GlobalTheory.LevelChars

open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

private def killSubgroupEquiv {G : Type*} [CommGroup G] (H : Subgroup G) :
    {ψ : G →* ℂˣ | H ≤ ψ.ker} ≃ (G ⧸ H →* ℂˣ) :=
  (Equiv.subtypeEquivRight fun ψ ↦ by
    change H ≤ ψ.ker ↔ ψ ∈ (MonoidHom.domRestrictHom H ℂˣ).ker
    simp [MonoidHom.mem_ker, MonoidHom.domRestrict_eq_one_iff, IsConcreteLE.le_iff]).trans
    (MonoidHom.domRestrictHomKerEquiv ℂˣ H).toEquiv

/-- The characters trivial on a finite-index subgroup are as numerous as its cosets. -/
theorem card_chars {G : Type*} [CommGroup G] (H : Subgroup G) [H.FiniteIndex] :
    Nat.card {ψ : G →* ℂˣ | H ≤ ψ.ker} = H.index := by
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  exact (Nat.card_congr (killSubgroupEquiv H)).trans
    (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (G ⧸ H) ℂ)

theorem finite_chars {G : Type} [CommGroup G] (H : Subgroup G) [H.FiniteIndex] :
    {ψ : G →* ℂˣ | H ≤ ψ.ker}.Finite := by
  apply Set.finite_coe_iff.mp
  apply Nat.finite_of_card_ne_zero
  rw [card_chars H]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- A family of distinct characters with ratios trivial on a subgroup has at most the
index of the subgroup many members. -/
theorem finite_card_le_index_of_charRatios {G : Type} {A : Type*} [CommGroup G]
    (H : Subgroup G) [H.FiniteIndex] (S : Set A) (ψ : A → G →* ℂˣ)
    (hψ : Function.Injective ψ)
    (h : ∀ a ∈ S, ∀ b ∈ S, H ≤ (ψ a * (ψ b)⁻¹).ker) :
    S.Finite ∧ Nat.card S ≤ H.index := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  let ratio : S → {χ : G →* ℂˣ | H ≤ χ.ker} :=
    fun a ↦ ⟨ψ a * (ψ a₀)⁻¹, h a a.property a₀ ha₀⟩
  have hinj : Function.Injective ratio := fun a b hab ↦
    Subtype.ext (hψ (mul_right_cancel (congrArg Subtype.val hab)))
  have := (finite_chars H).to_subtype
  refine ⟨Set.finite_coe_iff.mp (Finite.of_injective ratio hinj), ?_⟩
  calc
    Nat.card S ≤ Nat.card {χ : G →* ℂˣ | H ≤ χ.ker} :=
      Nat.card_le_card_of_injective ratio hinj
    _ = H.index := card_chars H

/-- Two Hecke characters with the same infinity type and conductor bounds agree on
the principal idèles and the prescribed level subgroup. -/
theorem raySubgroup_le_ker_ratio
    {L : Type} [Field L] [NumberField L] {I : Type} [Fintype I]
    {φ : I → L →+* ℂ} {n : I → ℤ} {S : Set (HeightOneSpectrum (𝓞 L))} {N : ℕ}
    (hA : ∀ ψ : Formalism.L2.Host.HChar L, (∀ k : Lˣ, ψ.inf k = 1) →
      (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) →
      ∀ a ∈ levSub L S N, ψ.1 a = 1)
    {χ χ0 : Formalism.L2.Host.HChar L}
    (hχ : χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N)
    (hχ0 : χ0.HasInf φ n ∧ (∀ v, v ∉ S → χ0.UnrAt v) ∧ ∀ v ∈ S, χ0.LevelLe v N) :
    (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N ≤
      ((χ * χ0⁻¹).1).ker := by
  refine sup_le ?_ fun a ha => MonoidHom.mem_ker.2 (hA (χ * χ0⁻¹) (fun k => ?_) (fun v hv x hx => ?_) (fun v hv x hx hle => ?_) a ha)
  · rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.2 ((χ * χ0⁻¹).2.2 k)
  · have e : χ.inf k = χ0.inf k := Units.ext ((hχ.1 k).trans (hχ0.1 k).symm)
    rw [Formalism.L2.Host.HChar.inf_mul, Formalism.L2.Host.HChar.inf_inv, e, mul_inv_cancel]
  · change χ.loc v x * (χ0.loc v x)⁻¹ = 1
    rw [hχ.2.1 v hv x hx, hχ0.2.1 v hv x hx, inv_one, one_mul]
  · change χ.loc v x * (χ0.loc v x)⁻¹ = 1
    rw [hχ.2.2 v hv x hx hle, hχ0.2.2 v hv x hx hle, inv_one, one_mul]

/-- Prescribing the infinity type and local conductor bounds leaves at most one
character per dual character of the finite idele-class quotient. -/
theorem heckeFin_card_le_of
    (hA : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L),
      (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ levSub L S N, ψ.1 a = 1)
    (hC : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex) :
    ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite ∧
    Nat.card {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N} ≤
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).index := by
  intro L _ _ I _ φ n S N hS
  classical
  have := hC L S N hS
  refine finite_card_le_index_of_charRatios _ _ Subtype.val Subtype.val_injective ?_
  exact fun _ hχ _ hχ0 ↦ raySubgroup_le_ker_ratio (hA L S N) hχ hχ0

theorem heckeFin_of
    (hA : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L),
      (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ levSub L S N, ψ.1 a = 1)
    (hC : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex) :
    ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite :=
  fun L _ _ I _ φ n S N hS ↦ (heckeFin_card_le_of hA hC L I φ n S N hS).1

end GlobalTheory.LevelChars
