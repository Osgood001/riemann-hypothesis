module
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.QuadraticPrimitiveClassBound

@[expose] public section

open NumberField
namespace NumberField.SqrtNeg163

/-- An integral generator is a root of X²−X+41, of discriminant −163. -/
abbrev K := QuadraticAlgebra ℚ ((-41 : ℤ) : ℚ) ((1 : ℤ) : ℚ)

instance : Fact (¬ IsSquare (QuadraticAlgebra.discr ((-41 : ℤ) : ℚ) ((1 : ℤ) : ℚ))) := by
  refine ⟨fun ⟨z, hz⟩ => ?_⟩
  norm_num [QuadraticAlgebra.discr_def] at hz
  nlinarith [sq_nonneg z]

instance : NumberField K := NumberField.of_module_finite ℚ _

theorem discr_K : discr K = -163 := by
  have h : Int.IsFundamentalDiscr (QuadraticAlgebra.discr (-41 : ℤ) 1) := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    norm_num [QuadraticAlgebra.discr_def, ← Int.squarefree_natAbs]
    exact (by norm_num : Nat.Prime 163).squarefree
  let e := QuadraticAlgebra.Int.algEquivIntegralClosure h
  let B := QuadraticAlgebra.basis (-41 : ℤ) 1
  rw [← discr_eq_discr _ (B.map e.toLinearEquiv)]
  change Algebra.discr ℤ (e ∘ B) = _
  rw [← Algebra.discr_eq_discr_of_algEquiv]
  exact (Algebra.discr_quadraticAlgebra (a := (-41 : ℤ)) (b := 1)).trans
    (by norm_num [QuadraticAlgebra.discr_def])

/-- The class group of the actual imaginary quadratic field ℚ(√−163) is trivial. -/
theorem classNumber_eq_one : classNumber K = 1 :=
  GlobalTheory.QuadraticZeta.classNumber_eq_one_of_heegner_discr K
    (QuadraticAlgebra.finrank_eq_two _ _) (by rw [discr_K]; decide)

end NumberField.SqrtNeg163
