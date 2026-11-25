module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelOfPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSignedTwist

@[expose] public section

open CategoryTheory AlgebraicGeometry Filter Topology Asymptotics
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VolBr

namespace GlobalTheory

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/-- Principalisation implies Hilbert–Samuel even with a signed sublinear moving twist. -/
theorem arithHilbertSamuel_signed_twist_of_principalisation
    (hP : Published.Principalisation)
    {D : ℕ} (hX : IsArithVar p D) (L A : HermLB p) {a : ℝ}
    (hnef : L.IsNef D) (ha : L.IsSelfInter a)
    (z : ℕ → ℤ) (hz : Tendsto (fun n : ℕ => ((z n).natAbs : ℝ) / n) atTop (𝓝 0)) :
    let S := fun n : ℕ => ((L.pow n).tens (zp A (z n))).smallSec
    (∀ᶠ n : ℕ in atTop, (S n).Finite) ∧
      (fun n : ℕ => Real.log ((S n).ncard : ℝ) - a / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
  (arithHilbertSamuel_of_principalisation hP).signed_twist (MixHt.arCalc_of_principalisation hP)
    (HSNef.ampleHS_of_principalisation hP) hX L A hnef ha z hz

/-- The principalisation consequence for finitely many independently moving twists. -/
theorem arithHilbertSamuel_finite_twists_of_principalisation {ι : Type} [Fintype ι]
    (hP : Published.Principalisation)
    {D : ℕ} (hX : IsArithVar p D) (L : HermLB p) (A : ι → HermLB p) {a : ℝ}
    (hnef : L.IsNef D) (ha : L.IsSelfInter a) (z : ℕ → ι → ℤ)
    (hz : ∀ i, Tendsto (fun n : ℕ => ((z n i).natAbs : ℝ) / n) atTop (𝓝 0)) :
    let S := fun n : ℕ => ((L.pow n).tens (comb A (z n))).smallSec
    (∀ᶠ n : ℕ in atTop, (S n).Finite) ∧
      (fun n : ℕ => Real.log ((S n).ncard : ℝ) - a / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
  (arithHilbertSamuel_of_principalisation hP).finite_twists (MixHt.arCalc_of_principalisation hP)
    (HSNef.ampleHS_of_principalisation hP) hX L A hnef ha z hz

end GlobalTheory
