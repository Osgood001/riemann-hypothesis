module

public import Lemmata.ProductIdentities.ProdInvZpowMulOfProdZpowEqOne

@[expose] public section

namespace Bl.b110

theorem goal1 {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 :=
  @Bl.ProductIdentities.goal1 n inst inst_1 A A' h0 h

end Bl.b110
