module

public import Lemmata.ProductIdentities.ProdInvZpowMulOfProdZpowEqOne

@[expose] public section

namespace Bl.MovedPointExistence

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem goal1 (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 :=
  Bl.ProductIdentities.goal1 A A' h0 h

end Bl.MovedPointExistence
