module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Field.Subfield.Basic

@[expose] public section

namespace GridInterpolation

/-- Uniformly bounded character values admit one common input; the input group and
character family need not be finite, and no single character need attain the full exponent. -/
private theorem exists_common_character_input_of_pow {A R ι : Type*} [Group A] [CommRing R]
    [IsDomain R] (χ : ι → A →* Rˣ) {N : ℕ} (hN : 0 < N)
    (hχ : ∀ i y, χ i y ^ N = 1) :
    ∃ x : A, Subgroup.closure (Set.range fun i => χ i x) =
      ⨆ y : A, Subgroup.closure (Set.range fun i => χ i y) := by
  let v : A →* (ι → Rˣ) := MonoidHom.pi χ
  let e := Monoid.exponent v.range
  have bounded : Monoid.ExponentExists v.range := by
    refine ⟨N, hN, ?_⟩
    rintro ⟨_, y, rfl⟩
    exact Subtype.ext (funext fun i => hχ i y)
  have : NeZero e := ⟨bounded.exponent_ne_zero⟩
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent bounded
  obtain ⟨x, hx⟩ := g.prop
  have he : orderOf (v x) = e := by rw [hx, Subgroup.orderOf_coe]; exact hg
  have hroots (y : A) :
      Subgroup.closure (Set.range fun i => χ i y) ≤ rootsOfUnity e R := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_rootsOfUnity]
    have ht : v y ^ e = 1 := Subgroup.pow_exponent_eq_one (H := v.range) ⟨y, rfl⟩
    exact congrFun ht i
  let L := Subgroup.closure (Set.range fun i => χ i x)
  have : Finite L := Finite.of_injective _ (Subgroup.inclusion_injective (hroots x))
  have hcard : e ∣ Nat.card L := by
    rw [← he, orderOf_dvd_iff_pow_eq_one]
    ext1 i
    have hi : χ i x ∈ L := Subgroup.subset_closure ⟨i, rfl⟩
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨χ i x, hi⟩ : L)))
  have hL : L = rootsOfUnity e R :=
    Subgroup.eq_of_le_of_card_ge (hroots x)
      ((card_rootsOfUnity R e).trans (Nat.le_of_dvd Nat.card_pos hcard))
  refine ⟨x, le_antisymm (le_iSup (fun y : A => Subgroup.closure (Set.range fun i => χ i y)) x) ?_⟩
  exact (iSup_le hroots).trans hL.ge

/-- A single input tests all character values, both for containment in a subfield
and for annihilation by any power. The two tests use the same input. -/
theorem exists_common_character_tests {A K ι : Type*} [Group A] [Field K]
    (χ : ι → A →* K) {N : ℕ} (hN : 0 < N) (hχ : ∀ i y, χ i y ^ N = 1) :
    ∃ x : A, (∀ S : Subfield K, (∀ i, χ i x ∈ S) ↔ ∀ y i, χ i y ∈ S) ∧
      ∀ n : ℕ, (∀ i, χ i x ^ n = 1) ↔ ∀ y i, χ i y ^ n = 1 := by
  let ψ (i : ι) := (χ i).toHomUnits
  have hψ (i : ι) (y : A) : ψ i y ^ N = 1 := Units.ext (hχ i y)
  obtain ⟨x, hx⟩ := exists_common_character_input_of_pow ψ hN hψ
  have all (H : Subgroup Kˣ) : (∀ i, ψ i x ∈ H) ↔ ∀ y i, ψ i y ∈ H := by
    refine ⟨fun h y i => ?_, fun h => h x⟩
    have hU : Subgroup.closure (Set.range fun i => ψ i x) ≤ H :=
      (Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr h)
    rw [hx, iSup_le_iff] at hU
    exact hU y (Subgroup.subset_closure ⟨i, rfl⟩)
  refine ⟨x, fun S => ?_, fun n => ?_⟩
  · let U : Subgroup Kˣ :=
      { carrier := {u | (u : K) ∈ S}
        one_mem' := S.one_mem
        mul_mem' := S.mul_mem
        inv_mem' := by
          intro a ha
          change (↑(a⁻¹) : K) ∈ S
          rw [Units.val_inv_eq_inv_val]
          exact S.inv_mem ha }
    exact all U
  · simpa only [mem_rootsOfUnity', ψ, MonoidHom.coe_toHomUnits] using all (rootsOfUnity n K)

end GridInterpolation
