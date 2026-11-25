module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.BilinFormBijectiveOfNondegenerateMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

section
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem holUnif_ex_zero_eq_one : u.ex 0 = 1 :=
  (u.ker 0).2 (zero_mem _)

theorem holUnif_ex_nsmul_eq_pow (z : Fin g → ℂ) (k : ℕ) : u.ex (k • z) = u.ex z ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem holUnif_isZLattice : haveI := u.discrete; IsZLattice ℝ u.Λ := by
  have := u.discrete
  exact ⟨u.full⟩

end

/-- Nondegeneracy is tested only on prime torsion over the complex base. -/
def WeilNondegAtPrimes (P : Out.PolAV (Sp ℂ)) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ x : Out.baseOver _ ⟶ P.A, x ^ p = 1 →
    (∀ y : Out.baseOver _ ⟶ P.A, y ^ p = 1 → Out.WeilIs P.A P.L p x y 1) → x = 1

/-- Only trivial-pair tests at prime torsion levels are needed for lattice perfection. -/
theorem riemannForm_bijective_of_weilNondegAtPrimes (P : Out.PolAV (Sp ℂ))
    (u : HolUnif P.A P.L P.g) (Ef : LinearMap.BilinForm ℤ u.Λ) (hW : WeilNondegAtPrimes P)
    (hE : ∀ p : ℕ, p.Prime → ∀ a b : u.Λ,
      (1 : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / p) →
      Out.WeilIs P.A P.L p (u.ex ((p : ℂ)⁻¹ • (a : Fin P.g → ℂ)))
        (u.ex ((p : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn (1 : ℂˣ))) : Function.Bijective Ef := by
  have := u.discrete
  have := holUnif_isZLattice u
  apply bilinForm_bijective_of_nondegenerate_mod_prime u.Λ Ef
  intro k a hk hdiv
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne_zero

  have hpow : ∀ w : Fin P.g → ℂ, u.ex w ^ k = u.ex ((k : ℂ) • w) := by
    intro w
    rw [← holUnif_ex_nsmul_eq_pow, Nat.cast_smul_eq_nsmul]
  have hx : u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) = 1 := by
    refine hW k hk _ ?_ ?_
    · rw [hpow, smul_smul, mul_inv_cancel₀ hk0, one_smul]
      exact (u.ker _).2 a.2
    · intro y hy
      obtain ⟨w, rfl⟩ := u.ex_onto y
      have hw : (k : ℂ) • w ∈ u.Λ := (u.ker _).1 (by rw [← hpow]; exact hy)
      set b : u.Λ := ⟨(k : ℂ) • w, hw⟩
      have hwb : w = (k : ℂ)⁻¹ • (b : Fin P.g → ℂ) := by
        simp only [b, smul_smul, inv_mul_cancel₀ hk0, one_smul]
      obtain ⟨m, hm⟩ := hdiv b
      have h1 := hE k hk a b (by
        rw [hm]
        push_cast
        rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((k : ℂ) * (m : ℂ)) / (k : ℂ)
            = (-m : ℤ) * (2 * Real.pi * Complex.I) by push_cast; field_simp]
        exact (Complex.exp_int_mul_two_pi_mul_I (-m)).symm)
      have hu : unitOn (1 : ℂˣ) = 1 := map_one _
      rw [hu, ← hwb] at h1
      exact h1
  refine ⟨⟨(k : ℂ)⁻¹ • (a : Fin P.g → ℂ), (u.ker _).1 hx⟩, ?_⟩
  ext1
  simp only [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast, smul_smul,
    mul_inv_cancel₀ hk0, one_smul]


theorem riemannForm_bijective_of_weilNondeg :
    Out.WeilNondegSt → (∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (E : LinearMap.BilinForm ℤ X), (∀ (k : ℕ) (a : X), 0 < k → (∀ b, (k : ℤ) ∣ E a b) → ∃ a', a = (k : ℤ) • a') → Function.Bijective E) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c)) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef) := by
  intro hW _ hE P u Hm χ Ef hc
  exact riemannForm_bijective_of_weilNondegAtPrimes P u Ef
    (fun p hp => hW ℂ P p (by exact_mod_cast hp.ne_zero))
    (fun p hp a b => hE P u Hm χ Ef hc p a b 1 hp.pos)

end GlobalTheory
