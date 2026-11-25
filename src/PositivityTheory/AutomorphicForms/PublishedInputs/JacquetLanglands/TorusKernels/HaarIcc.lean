module

public import Mathlib

@[expose] public section

noncomputable section
open MeasureTheory

namespace UpperTheory.Esk.UnipotentIntegrandLemmas

theorem haar_Icc (m : Measure ℝ) (hinv : ∀ c : ℝ, ∀ S : Set ℝ, MeasurableSet S → m ((fun x => c + x) ⁻¹' S) = m S)
    (a0 ℓ : ℝ) (hℓ : 0 < ℓ) (hfin : m (Set.Icc a0 (a0 + ℓ)) ≠ ⊤) :
    ∃ R : ℝ, ∀ a c : ℝ, a ≤ c → (m (Set.Icc a c)).toReal = R * (c - a) := by
  have : VAddInvariantMeasure ℝ ℝ m := ⟨hinv⟩
  have : m.IsAddLeftInvariant := ⟨fun c => Measure.ext fun S hS => by
    rw [Measure.map_apply (measurable_const_add c) hS, hinv c S hS]⟩
  have hOpenFinite : m (Set.Ioo a0 (a0 + ℓ)) ≠ ⊤ :=
    ((measure_mono Set.Ioo_subset_Icc_self).trans_lt hfin.lt_top).ne
  have : IsLocallyFiniteMeasure m := isLocallyFiniteMeasure_of_vaddInvariant ℝ isOpen_Ioo
    (Set.nonempty_Ioo.mpr (lt_add_of_pos_right a0 hℓ)) hOpenFinite
  have hm := Measure.isAddLeftInvariant_eq_smul m (volume : Measure ℝ)
  refine ⟨(Measure.addHaarScalarFactor m volume : ℝ), fun a c hac => ?_⟩
  have h2 := congrArg (fun μ : Measure ℝ => μ (Set.Icc a c)) hm
  rw [h2, smul_apply, Real.volume_Icc, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal (sub_nonneg.2 hac)]

end UpperTheory.Esk.UnipotentIntegrandLemmas
