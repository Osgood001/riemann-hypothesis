module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StDualLatticeMultiple

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

/-- The field discriminant clears the denominator of every element of the inverse different. -/
theorem isIntegral_discr_mul_of_integral_traces (E : Type*) [Field E] [NumberField E]
    (z : E) (hz : ∀ a : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((a : E) * z) = n) :
    IsIntegral ℤ ((NumberField.discr E : E) * z) := by
  have hdual : z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hx
    obtain ⟨n, hn⟩ := hz a
    exact ⟨n, by simpa [Algebra.traceForm_apply, mul_comm] using hn.symm⟩
  have := isIntegral_discr_mul_of_mem_traceDual (1 : Submodule (𝓞 E) E)
    (b := integralBasis E) (fun i => by rw [integralBasis_apply]; exact (RingOfIntegers.basis E i).2)
    (show (1 : E) ∈ (1 : Submodule (𝓞 E) E) by simp) hdual
  simpa [← NumberField.coe_discr, Algebra.smul_def] using this

theorem inverseDifferent_multiple (E : Type*) [Field E] [NumberField E] :
    ∃ δ : ℤ, δ ≠ 0 ∧ ∀ z : E, (∀ a : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((a : E) * z) = n) →
      IsIntegral ℤ ((δ : E) * z) :=
  ⟨NumberField.discr E, NumberField.discr_ne_zero E, isIntegral_discr_mul_of_integral_traces E⟩

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem DualLatticeMultiple.proof (h : HermitianForm F E W) : DualLatticeMultiple.Statement h := by
  intro D
  obtain ⟨δ, hδ, hdiff⟩ := inverseDifferent_multiple E
  refine ⟨δ * (D.factorial : ℤ), mul_ne_zero hδ (by exact_mod_cast D.factorial_ne_zero),
    fun La hLa => ⟨fun x hx y hy => ?_, fun y hy => ?_⟩⟩
  · have hi : IsIntegral ℤ (Algebra.trace ℚ E (h.toSesq x y)) :=
      Algebra.isIntegral_trace ((mem_integralClosure_iff ℤ E).mp (hLa.integral x hx y hy))
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨n, by rw [← hn]; simp⟩
  ·
    have hdual : δ • y ∈ dualLattice h La := by
      intro x hx
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
      refine (mem_integralClosure_iff ℤ E).mpr (hdiff _ fun a => ?_)
      obtain ⟨n, hn⟩ := hy _ (hLa.isLattice.smul_mem a x hx)
      exact ⟨n, by rw [← hn, LinearMap.map_smul, smul_eq_mul]⟩

    have hm := AddSubgroup.nsmul_relIndex_mem La hdual
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le
    have : (D.factorial : ℤ) • (δ • y) ∈ La := by
      rw [hc, natCast_zsmul, mul_comm, mul_nsmul]
      rw [smul_comm]
      exact AddSubgroup.nsmul_mem _ hm _
    rwa [smul_smul, mul_comm] at this

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
