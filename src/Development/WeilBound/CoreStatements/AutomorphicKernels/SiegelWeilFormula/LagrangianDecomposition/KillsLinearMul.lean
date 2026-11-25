module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ContinuousAinApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe

@[expose] public section

noncomputable section

open scoped ContDiff
open MeasureTheory Set Filter Topology Complex

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

theorem kills_linear_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ) (L : V →L[ℝ] ℝ)
    (hT : ∀ (t : ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * ((t • L) x : ℂ)) * f x) →
      T f' = T f)
    (f g : SchwartzMap V ℂ) (hg : ∀ x, g x = (L x : ℂ) * f x) : T g = 0 := by
  apply GlobalTheory.CharFormDeriv.charForm_kills_linear_mul_of_frequently T L f g hg
  apply Filter.Eventually.frequently (Filter.Eventually.of_forall ?_)
  intro t
  apply hT t f (GlobalTheory.CharFormDeriv.modulate L t f)
  intro x
  simp [mul_assoc]

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {κ' κ'' : Type} [Fintype κ']
  [Fintype κ'']

theorem arch_part (T : SchwartzMap (κ' ⊕ κ'' → W) ℂ →L[ℂ] ℂ)
    (hT : ∀ (L : (κ'' → W) →L[ℝ] ℝ) (f f' : SchwartzMap (κ' ⊕ κ'' → W) ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L (x ∘ Sum.inr) : ℂ)) * f x) → T f' = T f)
    (f : SchwartzMap (κ' ⊕ κ'' → W) ℂ) (hf : ∀ x : κ' ⊕ κ'' → W, x ∘ Sum.inr = 0 → f x = 0) : T f = 0 := by
  obtain ⟨n, L, hh, gg, hgg, hsum⟩ := param_hadamard f hf
  let P : (κ' ⊕ κ'' → W) →L[ℝ] (κ'' → W) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Sum.inr j)
  have hres : ∀ i, T (gg i) = 0 := by
    intro i
    refine kills_linear_mul T ((L i).comp P) ?_ (hh i) (gg i) ?_
    · intro t f₁ f₂ h
      apply hT (t • L i) f₁ f₂
      intro x
      rw [h x]
      rfl
    · intro x
      rw [hgg i x]
      rfl
  have hf' : f = ∑ i, gg i := by
    ext x
    rw [hsum x]
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf', map_sum]
  simp [hres]

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
