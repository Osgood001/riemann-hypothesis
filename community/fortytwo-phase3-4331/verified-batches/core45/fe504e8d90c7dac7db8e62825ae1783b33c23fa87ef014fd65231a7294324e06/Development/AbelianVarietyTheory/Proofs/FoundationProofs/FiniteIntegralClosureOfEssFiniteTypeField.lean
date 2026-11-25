import Mathlib

namespace GlobalTheory

open Polynomial

theorem finiteDimensional_algebraicClosure_of_essFiniteType (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Algebra.EssFiniteType K L] : FiniteDimensional K (algebraicClosure K L) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  let E := algebraicClosure K L
  let P := Algebra.adjoin K (Set.range ((↑) : s → L))
  let F := IntermediateField.adjoin K (Set.range ((↑) : s → L))
  haveI : Algebra.IsAlgebraic F L := hs.isAlgebraic_field
  haveI : Algebra.EssFiniteType F L := .of_comp K F L
  haveI : Module.Finite F L := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let b := Module.Basis.ofVectorSpace K E
  have hE : AlgebraicIndependent E ((↑) : s → L) := hs.1.algebraicClosure
  have hP : LinearIndependent P (fun i => (b i : L)) := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have hq : ∀ j, ∃ q : MvPolynomial s K, MvPolynomial.aeval ((↑) : s → L) q = g j := fun j => by
      have : (g j : L) ∈ Algebra.adjoin K (Set.range ((↑) : s → L)) := (g j).2
      rwa [Algebra.adjoin_range_eq_range_aeval] at this
    choose q hq using hq
    have h1 : ∑ j ∈ t, MvPolynomial.map (algebraMap K E) (q j) * MvPolynomial.C (b j) = 0 := by
      apply algebraicIndependent_iff.mp hE
      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, MvPolynomial.aeval_map_algebraMap, hq, MvPolynomial.aeval_C]
      rfl
    have h2 : q i = 0 := by
      ext m
      have h3 := congrArg (MvPolynomial.coeff m) h1
      simp only [MvPolynomial.coeff_sum, mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_map, MvPolynomial.coeff_zero, mul_comm (b _), ← Algebra.smul_def] at h3
      exact linearIndependent_iff'.mp b.linearIndependent t (fun j => (q j).coeff m) h3 i hi
    apply Subtype.ext
    rw [← hq, h2, map_zero]
    rfl
  have hF : LinearIndependent F (fun i => (b i : L)) := by
    open IntermediateField.algebraAdjoinAdjoin in
    exact (LinearIndependent.iff_fractionRing P F).mp hP
  haveI := hF.finite
  exact Module.Finite.of_basis b

end GlobalTheory
