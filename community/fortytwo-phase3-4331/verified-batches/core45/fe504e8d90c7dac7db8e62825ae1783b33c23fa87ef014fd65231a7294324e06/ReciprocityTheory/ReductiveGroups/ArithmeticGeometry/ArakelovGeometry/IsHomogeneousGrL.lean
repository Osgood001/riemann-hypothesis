import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsPrimeFiltrationOfIsMultiHomogIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def lexDeg (a : K → ℕ) : Lex (Fin (Fintype.card K) → ℕ) := toLex (a ∘ (Fintype.equivFin K).symm)

theorem lexDeg_add (a b : K → ℕ) : lexDeg (a + b) = lexDeg a + lexDeg b := rfl

variable (ι) in

abbrev grL : Lex (Fin (Fintype.card K) → ℕ) → Submodule ℤ (MRing ι) :=
  weightedHomogeneousSubmodule ℤ (lexW (ι := ι) (Fintype.equivFin K))

theorem mem_grL_iff (f : MRing ι) (a : K → ℕ) : f ∈ grL ι (lexDeg a) ↔ IsMultiHomog f a := by
  constructor
  · intro h
    have := isMultiHomog_of_mem_lex _ h
    convert this using 1
    funext k
    simp [lexDeg]
  · exact mem_lex_of_isMultiHomog _









theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  rw [← mem_grL_iff] at hf hg ⊢
  rw [lexDeg_add]
  exact SetLike.GradedMul.mul_mem hf hg


end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
