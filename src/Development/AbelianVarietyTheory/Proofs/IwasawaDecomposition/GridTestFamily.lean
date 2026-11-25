module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformGridCoefficientField
public import Mathlib.Data.Nat.Factors

@[expose] public section

namespace IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

private theorem factorCount_lt_of_lt {A B : IntermediateField F L} [FiniteDimensional F B]
    (h : A < B) :
    (Module.finrank F A).primeFactorsList.length < (Module.finrank F B).primeFactorsList.length := by
  have hlt : Module.finrank F A < Module.finrank F B :=
    lt_of_not_ge fun he => h.ne (eq_of_le_of_finrank_le h.le he)
  obtain ⟨k, hk⟩ := finrank_dvd_of_le_right h.le
  have hpos : Module.finrank F B ≠ 0 := Module.finrank_pos.ne'
  have ha : Module.finrank F A ≠ 0 := by
    intro h0
    exact hpos (by simpa [h0] using hk)
  have hk0 : k ≠ 0 := fun hk0 => hpos (by simpa [hk0] using hk)
  have hk1 : k ≠ 1 := fun hk1 => hlt.ne (by simpa [hk1] using hk.symm)
  have hne : k.primeFactorsList ≠ [] := fun he => ((Nat.primeFactorsList_eq_nil k).mp he).elim hk0 hk1
  have hlen := List.length_pos_iff.mpr hne
  rw [hk, (Nat.perm_primeFactorsList_mul ha hk0).length_eq, List.length_append]
  omega

/-- A compositum only needs one input per prime factor, with multiplicity, in the remaining degree. -/
theorem exists_subfamily_sup_of_degree (base : IntermediateField F L)
    (s : Finset (IntermediateField F L)) :
    FiniteDimensional F ↥(base ⊔ s.sup id) →
    ∃ t ⊆ s, base ⊔ t.sup id = base ⊔ s.sup id ∧
      t.card + (Module.finrank F base).primeFactorsList.length ≤
        (Module.finrank F ↥(base ⊔ s.sup id)).primeFactorsList.length := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨∅, by simp, rfl, ?_⟩
    have he : base ⊔ (∅ : Finset (IntermediateField F L)).sup id = base := by simp
    rw [he]
    simp
  | @insert A s hA ih =>
    intro hdim
    let B := base ⊔ s.sup id
    let C := base ⊔ (insert A s).sup id
    have hle : B ≤ C := sup_le_sup_left (Finset.sup_mono (Finset.subset_insert ..)) _
    have : FiniteDimensional F B :=
      FiniteDimensional.of_injective (inclusion hle).toLinearMap (inclusion hle).injective
    obtain ⟨t, ht, heq, hb⟩ := ih this
    by_cases h : B = C
    · refine ⟨t, ht.trans (Finset.subset_insert ..), heq.trans h, ?_⟩
      change _ ≤ (Module.finrank F ↥C).primeFactorsList.length
      rw [← h]
      exact hb
    · refine ⟨insert A t, Finset.insert_subset_insert _ ht, ?_, ?_⟩
      · simpa [Finset.sup_insert, sup_assoc, sup_left_comm, sup_comm] using congrArg (A ⊔ ·) heq
      · have hlt := factorCount_lt_of_lt (lt_of_le_of_ne hle h)
        rw [Finset.card_insert_of_notMem (fun ha => hA (ht ha))]
        change t.card + _ ≤ (Module.finrank F ↥B).primeFactorsList.length at hb
        change t.card + 1 + _ ≤ (Module.finrank F ↥C).primeFactorsList.length
        omega

end IntermediateField

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.Mem.LiteralAutomorphy
open GlobalTheory.Mem
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridField

/-- An original grid together with its stage over the fixed base. -/
structure GridSample (P : Pre) (sc : Consts) where
  stage : Stages
  base_eq : stage.B.toPre = P
  T : Type
  L : LevCh stage.toD7 T
  grid : GridData L sc

/-- For every candidate field containing the known base, the same sample of original
grids suffices. Each additional grid consumes a prime factor of the remaining degree. -/
theorem exists_grid_samples (P : Pre) (sc : Consts) (B : IntermediateField ℚ ℂ)
    (hB : B ≤ uniformGridField P sc) :
    ∃ samples : Finset (GridSample P sc),
      samples.card + (Module.finrank ℚ B).primeFactorsList.length ≤
        (Module.finrank ℚ (uniformGridField P sc)).primeFactorsList.length ∧
      ∀ M : IntermediateField ℚ ℂ, B ≤ M →
        ((∀ g ∈ samples, FieldHas g.grid M.val.toRingHom) ↔
         ∀ g : GridSample P sc, FieldHas g.grid M.val.toRingHom) := by
  classical
  let s := (gridCoefficientFields_finite P sc).toFinset
  have hs (A : IntermediateField ℚ ℂ) : A ∈ s ↔ A ∈ gridCoefficientFields P sc :=
    Set.Finite.mem_toFinset _
  have hsup : s.sup id = uniformGridField P sc := by
    apply le_antisymm
    · exact Finset.sup_le fun A hA => le_iSup (fun a : gridCoefficientFields P sc => a.val) ⟨A, (hs A).mp hA⟩
    · exact iSup_le fun A => Finset.le_sup (f := id) ((hs A.val).mpr A.property)
  have hbase : B ⊔ s.sup id = uniformGridField P sc := by rw [hsup, sup_eq_right.mpr hB]
  have hd : FiniteDimensional ℚ ↥(B ⊔ s.sup id) := hbase ▸ inferInstance
  obtain ⟨t, ht, he, hc⟩ := IntermediateField.exists_subfamily_sup_of_degree B s hd
  have rep (A : t) : ∃ g : GridSample P sc, gridCoefficientField g.grid = A.val := by
    obtain ⟨X, hX, T, L, G, hG⟩ := (hs A.val).mp (ht A.property)
    exact ⟨⟨X, hX, T, L, G⟩, hG⟩
  choose sample hsample using rep
  refine ⟨t.attach.image sample, ?_, fun M hBM => ⟨?_, fun h g _ => h g⟩⟩
  · rw [hbase] at hc
    have hcard : (t.attach.image sample).card ≤ t.card := by
      simpa only [Finset.card_attach] using Finset.card_image_le (s := t.attach) (f := sample)
    omega
  · intro h g
    have htest : t.sup id ≤ M := by
      refine Finset.sup_le fun A hA => ?_
      let i : t := ⟨A, hA⟩
      rw [show id A = gridCoefficientField (sample i).grid from (hsample i).symm]
      exact (gridCoefficientField_le_iff ..).mpr (h _ (Finset.mem_image_of_mem _ (Finset.mem_attach _ i)))
    have hU : uniformGridField P sc ≤ M := (he.trans hbase) ▸ sup_le hBM htest
    exact (uniformGridField_le_iff ..).mp hU g.stage g.base_eq g.T g.L g.grid

/-- For an abstract field embedded in ℂ, the original predicate depends only on the image. -/
private theorem fieldHas_range_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
    (G : GridData L sc) {K : Type} [Field K] [CharZero K] (e : K →ₐ[ℚ] ℂ) :
    FieldHas G e.fieldRange.val.toRingHom ↔ FieldHas G e.toRingHom := by
  constructor
  · intro h
    have he : e.toRingHom.comp e.equivFieldRange.symm.toRingHom = e.fieldRange.val.toRingHom := by
      ext x
      exact congrArg Subtype.val (e.equivFieldRange.apply_symm_apply x)
    exact FieldHas.map e.equivFieldRange.symm.toRingHom (he ▸ h)
  · exact fun h => FieldHas.map e.equivFieldRange.toRingHom h

/-- One fixed finite test suite works for every embedded candidate field, not just for
a chosen target, and its members are original stage grids. -/
theorem exists_universal_grid_samples (P : Pre) (sc : Consts) :
    ∃ samples : Finset (GridSample P sc),
      samples.card ≤ (Module.finrank ℚ (uniformGridField P sc)).primeFactorsList.length ∧
      ∀ (K : Type) [Field K] (e : K →+* ℂ),
        ((∀ g ∈ samples, FieldHas g.grid e) ↔ ∀ g : GridSample P sc, FieldHas g.grid e) := by
  obtain ⟨samples, hc, h⟩ := exists_grid_samples P sc ⊥ bot_le
  refine ⟨samples, by simpa using hc, ?_⟩
  intro K _ e
  let : CharZero K := ⟨fun i j he => by
    apply Nat.cast_injective (R := ℂ)
    simpa only [map_natCast] using congrArg e he⟩
  let f := e.toRatAlgHom
  have hf : f.toRingHom = e := by ext x; rfl
  simpa only [fieldHas_range_iff (e := f), hf] using h f.fieldRange bot_le

/-- In prime degree a single original grid already realizes the full coefficient field. -/
theorem exists_grid_realizing_prime_degree (P : Pre) (sc : Consts)
    (hp : (Module.finrank ℚ (uniformGridField P sc)).Prime) :
    ∃ g : GridSample P sc, gridCoefficientField g.grid = uniformGridField P sc := by
  by_contra! h
  have hbot : uniformGridField P sc ≤ ⊥ := (uniformGridField_le_iff ..).mpr fun X hX T L G => by
    let g : GridSample P sc := ⟨X, hX, T, L, G⟩
    have hle : gridCoefficientField G ≤ uniformGridField P sc :=
      (gridCoefficientField_le_iff ..).mpr ((uniformGridField_le_iff ..).mp le_rfl X hX T L G)
    apply (gridCoefficientField_le_iff ..).mp
    rcases (Nat.dvd_prime hp).mp (IntermediateField.finrank_dvd_of_le_right hle) with h1 | he
    · apply le_of_eq
      symm
      exact IntermediateField.eq_of_le_of_finrank_eq bot_le (by simp [h1])
    · exact (h g (IntermediateField.eq_of_le_of_finrank_eq hle he)).elim
  exact hp.ne_one (by rw [le_bot_iff.mp hbot]; simp)

end GlobalTheory.GridField
end
