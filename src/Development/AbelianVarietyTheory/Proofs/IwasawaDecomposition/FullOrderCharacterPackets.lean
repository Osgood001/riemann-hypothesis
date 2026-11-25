module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.GroupTheory.Sylow

public import Mathlib.Algebra.Field.Subfield.Basic

@[expose] public section

namespace GridInterpolation

/-- A surjective homomorphism pulls back a packet to equally sized fibres. -/
theorem card_preimage_of_surjective_hom {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (s : Set H) :
    Nat.card (f ⁻¹' s) = Nat.card f.ker * Nat.card s := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  change Nat.card (QuotientGroup.mk ⁻¹' (e ⁻¹' s)) = _
  rw [QuotientGroup.card_preimage_mk,
    Nat.card_preimage_of_injective e.injective (by rw [e.surjective.range_eq]; exact Set.subset_univ _)]

theorem full_order_count_cyclic (C : Type*) [Group C] [Finite C] [IsCyclic C] :
    Nat.card {c : C // orderOf c = Nat.card C} = (Nat.card C).totient := by
  classical
  let _ := Fintype.ofFinite C
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    (IsCyclic.card_orderOf_eq_totient (α := C) (d := Fintype.card C) dvd_rfl)

/-- At least the fraction `φ(e)/e` of a finite abelian group has full order `e`.
No part of this bound involves the size of a larger ambient group. -/
theorem totient_mul_card_le_card_full_order_mul_exponent (G : Type*) [CommGroup G] [Finite G] :
    (Monoid.exponent G).totient * Nat.card G ≤
      Nat.card {g : G // orderOf g = Monoid.exponent G} * Monoid.exponent G := by
  let K := AlgebraicClosure ℚ
  obtain ⟨d⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G K
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (G := G) Monoid.ExponentExists.of_finite
  let χ := d.symm g
  have hχ : orderOf χ = Monoid.exponent G := (d.symm.orderOf_eq g).trans hg
  have : Finite χ.range := Finite.of_surjective _ χ.rangeRestrict_surjective
  have : IsCyclic χ.range := isCyclic_of_injective_ringHom
    ((Units.coeHom K).comp χ.range.subtype) (Units.val_injective.comp Subtype.val_injective)
  have hc : Nat.card χ.range = Monoid.exponent G := by
    apply Nat.dvd_antisymm
    · rw [← IsCyclic.exponent_eq_card]
      exact MonoidHom.exponent_dvd χ.rangeRestrict_surjective
    · rw [← hχ, orderOf_dvd_iff_pow_eq_one]
      ext x : 1
      exact congrArg Subtype.val (pow_card_eq_one' (x := χ.rangeRestrict x))
  let f := χ.rangeRestrict
  let s : Set χ.range := {y | orderOf y = Nat.card χ.range}
  have hsub : f ⁻¹' s ⊆ {x | orderOf x = Monoid.exponent G} := by
    intro x hx
    apply Nat.dvd_antisymm (Monoid.order_dvd_exponent x)
    have he : orderOf (f x) = Nat.card χ.range := hx
    simpa only [he, hc] using orderOf_map_dvd f x
  have hle := Nat.card_le_card_of_injective _ (Set.inclusion_injective hsub)
  rw [card_preimage_of_surjective_hom f χ.rangeRestrict_surjective s] at hle
  change Nat.card f.ker * Nat.card {y : χ.range // orderOf y = Nat.card χ.range} ≤
    Nat.card {g : G // orderOf g = Monoid.exponent G} at hle
  rw [full_order_count_cyclic, hc] at hle
  rw [← Subgroup.card_ker_mul_card_of_surjective χ.rangeRestrict_surjective, hc]
  simpa only [f, mul_left_comm, mul_assoc, mul_comm] using! Nat.mul_le_mul_right (Monoid.exponent G) hle

/-- Pulling a menu of characters back from its simultaneous image loses no
proportion. The bound depends only on the exponent of that image. -/
theorem totient_mul_card_le_card_full_image_order_mul_exponent {Q H : Type*}
    [Group Q] [Finite Q] [CommGroup H] (f : Q →* H) :
    (Monoid.exponent f.range).totient * Nat.card Q ≤
      Nat.card {q : Q // orderOf (f q) = Monoid.exponent f.range} * Monoid.exponent f.range := by
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  let e := Monoid.exponent f.range
  let s : Set f.range := {g | orderOf g = e}
  have hcount : Nat.card {q : Q // orderOf (f q) = e} =
      Nat.card f.rangeRestrict.ker * Nat.card s := by
    have ht : {q : Q | orderOf (f q) = e} = f.rangeRestrict ⁻¹' s := by
      ext q
      exact (Subgroup.orderOf_coe (f.rangeRestrict q)).congr_left
    rw [← Set.coe_ofPred, ht, card_preimage_of_surjective_hom _ f.rangeRestrict_surjective]
  change e.totient * Nat.card Q ≤ Nat.card {q : Q // orderOf (f q) = e} * e
  rw [hcount, ← Subgroup.card_ker_mul_card_of_surjective f.rangeRestrict_surjective]
  have hl := totient_mul_card_le_card_full_order_mul_exponent f.range
  change e.totient * Nat.card f.range ≤ Nat.card s * e at hl
  simpa only [mul_assoc, mul_comm, mul_left_comm] using Nat.mul_le_mul_left (Nat.card f.rangeRestrict.ker) hl

/-- A tuple of order `e > 0` generates precisely the `e`th roots of unity
through its coordinates, even if no coordinate itself has order `e`. -/
theorem closure_coordinates_eq_rootsOfUnity {ι R : Type*} [CommRing R] [IsDomain R]
    (a : ι → Rˣ) {e : ℕ} [NeZero e] (ha : orderOf a = e) :
    Subgroup.closure (Set.range a) = rootsOfUnity e R := by
  let L := Subgroup.closure (Set.range a)
  have hle : L ≤ rootsOfUnity e R := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_rootsOfUnity]
    exact congrFun (ha ▸ pow_orderOf_eq_one a) i
  have : Finite L := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hcard : e ∣ Nat.card L := by
    rw [← ha, orderOf_dvd_iff_pow_eq_one]
    ext1 i
    have hi : a i ∈ L := Subgroup.subset_closure ⟨i, rfl⟩
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a i, hi⟩ : L)))
  exact Subgroup.eq_of_le_of_card_ge hle ((card_rootsOfUnity R e).trans (Nat.le_of_dvd Nat.card_pos hcard))

/-- Each individual full-order value vector, not merely one such vector,
tests membership of the complete menu of values in every coefficient field. -/
theorem full_order_input_tests_subfields {Q K ι : Type*} [Group Q] [Finite Q] [Field K]
    (f : Q →* (ι → Kˣ)) {q : Q} (hq : orderOf (f q) = Monoid.exponent f.range)
    (S : Subfield K) : (∀ i, ↑(f q i) ∈ S) ↔ ∀ y i, ↑(f y i) ∈ S := by
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  refine ⟨fun h y i => ?_, fun h => h q⟩
  let U : Subgroup Kˣ :=
    { carrier := {u | (u : K) ∈ S}
      one_mem' := S.one_mem
      mul_mem' := S.mul_mem
      inv_mem' := by
        intro a ha
        change (↑(a⁻¹) : K) ∈ S
        rw [Units.val_inv_eq_inv_val]
        exact S.inv_mem ha }
  have hU : Subgroup.closure (Set.range (f q)) ≤ U := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact h j
  rw [closure_coordinates_eq_rootsOfUnity _ hq] at hU
  apply hU
  rw [mem_rootsOfUnity]
  have hpow : f y ^ Monoid.exponent f.range = 1 := Subgroup.pow_exponent_eq_one (H := f.range) ⟨y, rfl⟩
  exact congrFun hpow i

/-- Once one observation of the fixed menu reaches the known common exponent,
the proportion bound applies to that same menu, without choosing a new one. -/
theorem menu_range_exponent_eq {Q H : Type*} [Group Q] [CommGroup H] (f : Q →* H) {e : ℕ}
    (hkill : ∀ q, (f q) ^ e = 1) {q₀ : Q} (hmax : orderOf (f q₀) = e) :
    Monoid.exponent f.range = e := by
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨_, q, rfl⟩
    exact Subtype.ext (hkill q)
  · rw [← hmax]
    change orderOf ((f.rangeRestrict q₀ : f.range) : H) ∣ _
    rw [Subgroup.orderOf_coe]
    exact Monoid.order_dvd_exponent _

end GridInterpolation
