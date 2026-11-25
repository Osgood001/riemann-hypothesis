module
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformGridCoefficientField

@[expose] public section
open IntermediateField
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.Mem.LiteralAutomorphy GlobalTheory.Mem
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridField

/-- One algebraic integer generates the uniform field, with exactly its degree. -/
theorem exists_integral_grid_generator (P : Pre) (sc : Consts) :
    ∃ a : ℂ, IsIntegral ℤ a ∧ adjoin ℚ {a} = uniformGridField P sc ∧
      (minpoly ℚ a).natDegree = Module.finrank ℚ (uniformGridField P sc) := by
  let U := uniformGridField P sc
  obtain ⟨x, hx⟩ := Field.exists_primitive_element ℚ U
  have hxU : adjoin ℚ {(x : ℂ)} = U := by
    rw [← lift_adjoin_simple ℚ U x, hx, lift_top]
  have hxQ : IsAlgebraic ℚ (x : ℂ) :=
    IntermediateField.isAlgebraic_iff.mp (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hxQ).exists_integral_multiple
  let a : ℂ := d • (x : ℂ)
  have ha : adjoin ℚ {a} = U := by
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    simpa [a, zsmul_eq_mul, mul_comm] using
      (adjoin_simple_mul_algebraMap (x : ℂ) (d : ℚ) hd').trans hxU
  refine ⟨a, hi, ha, ?_⟩
  change (minpoly ℚ a).natDegree = Module.finrank ℚ U
  rw [← ha, IntermediateField.adjoin.finrank (hi.tower_top : IsIntegral ℚ a)]

/-- A complex intermediate field works for all the original grids if and only if it
contains the single integral generator. -/
theorem exists_integral_grid_test (P : Pre) (sc : Consts) :
    ∃ a : ℂ, IsIntegral ℤ a ∧
      (minpoly ℚ a).natDegree = Module.finrank ℚ (uniformGridField P sc) ∧
      ∀ M : IntermediateField ℚ ℂ, a ∈ M ↔ ∀ (X : Stages), X.B.toPre = P →
        ∀ (T : Type) (L : LevCh X.toD7 T) (G : GridData L sc), FieldHas G M.val.toRingHom := by
  obtain ⟨a, hi, ha, hd⟩ := exists_integral_grid_generator P sc
  exact ⟨a, hi, hd, fun M => by rw [← adjoin_simple_le_iff, ha, uniformGridField_le_iff]⟩

open scoped Classical in
/-- The trivial field needs no additional test; every other uniform field needs just one. -/
theorem exists_minimal_grid_tests (P : Pre) (sc : Consts) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsIntegral ℤ z) ∧
      S.card = (if uniformGridField P sc = ⊥ then 0 else 1) ∧
      ∀ M : IntermediateField ℚ ℂ, uniformGridField P sc ≤ M ↔ (S : Set ℂ) ⊆ M := by
  classical
  by_cases h : uniformGridField P sc = ⊥
  · exact ⟨∅, by simp, by simp [h], by simp [h]⟩
  · obtain ⟨a, ha, hgen, _⟩ := exists_integral_grid_generator P sc
    refine ⟨{a}, by simpa using ha, by simp [h], fun M => ?_⟩
    rw [← hgen, adjoin_simple_le_iff]
    simp

end GlobalTheory.GridField
