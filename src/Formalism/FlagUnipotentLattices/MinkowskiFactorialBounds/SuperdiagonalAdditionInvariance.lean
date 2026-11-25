module

public import Formalism.FlagUnipotentLattices.PairingOrthogonalComplement
public import Mathlib
public import Formalism.SobolevGaussianKernels.StatementEI
public import Formalism.CorankShare.StatementFR

@[expose] public section

namespace Formalism.HermitianLatticeCounting.P.S4aux

open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset

theorem orbit_count_formula : OmCount := by
  intro P Om H hH
  calc (2:ℝ)^Om.card = ∏ p ∈ Om, (2:ℝ) := by simp
    _ ≤ ∏ p ∈ Om, H p := Finset.prod_le_prod₀ (fun _ _ => by norm_num) hH

theorem weighted_cauchy_schwarz : WeightedCS := by
  intro ι _ V _ v W hW
  calc ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ _ := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => (inv_pos.2 (hW i)).le)
        (fun i _ => mul_nonneg (hW i).le (sq_nonneg _)) (fun i _ => ?_)
      have := (hW i).ne'
      apply le_of_eq
      field_simp

theorem fourth_reduction_identity : Step4 := by
  intro P _ _ Om D _ w aN aZ H nn ngen q c κ hw hH hq hnn hN hZ hgen
  let B p := H p ^ c * nn p
  let f p := ((q p : ℝ) ^ κ)⁻¹
  have hB : ∀ p, 0 ≤ B p := fun p => mul_nonneg (pow_nonneg (zero_le_one.trans (hH p)) _) (hnn p)
  have hf : ∀ p, 0 ≤ f p := fun p => by dsimp [f]; positivity
  have bound := defect_mass_le Om D w aN aZ B (fun p => Real.sqrt (f p)) hw hB (fun p _ => Real.sqrt_nonneg _)
    (fun p hp => (hN p hp).trans_eq (by rw [Real.sq_sqrt (hf p)]; unfold B f; ring)) hZ
  have hprod : ∏ p, B p ≤ (∏ p, H p) ^ (2 * c) * ∏ p, ngen p := by
    calc _ ≤ ∏ p, H p ^ c * (H p ^ c * ngen p) := prod_le_prod₀ (fun p _ => hB p)
           (fun p _ => mul_le_mul_of_nonneg_left (hgen p) (pow_nonneg (zero_le_one.trans (hH p)) _))
         _ = _ := by simp only [prod_mul_distrib, prod_pow, two_mul, pow_add]; ring
  exact bound.trans ((mul_le_mul hprod (local_defect_sq_lt_legacy Om q κ (fun p _ => hq p)).le (sq_nonneg _)
    ((prod_nonneg fun p _ => hB p).trans hprod)).trans_eq (by ring))


section unfold
variable {G X : Type} [Group G] [MulAction G X]
open MulAction

end unfold

section dualcap
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

end dualcap

section sametrace
variable {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  (h : V →ₗ[E] V →ₗ⋆[E] E) {r : ℕ} (e : Fin r → V)

end sametrace

namespace Part2

end Part2

section dvrcard
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]

end dvrcard

section count
variable {F : Type} [Field F] [Fintype F]

end count

section inert
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

end inert

section inert2
variable (K : Type) {L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

variable {K}
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

end inert2

section inert3
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)




end inert3

section inert4
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)



end inert4

section unram2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

end unram2

section orth
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

end orth

section unimod
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

end unimod

section unimod2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)



end unimod2

section annih
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

end annih

section stdform
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

end stdform

section hermjac
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]






end hermjac

section hermjacA
variable {E : Type} [CommRing E]

end hermjacA

section hermjacA2
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]

end hermjacA2

section hermjacB
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]


end hermjacB

end Formalism.HermitianLatticeCounting.P.S4aux

namespace Formalism.HermitianLatticeCounting.P

theorem orbit_count_formula : Formalism.HermitianLatticeCounting.S4.OmCount := S4aux.orbit_count_formula
theorem weighted_cauchy_schwarz : Formalism.HermitianLatticeCounting.S4.WeightedCS := S4aux.weighted_cauchy_schwarz
theorem fourth_reduction_identity : Formalism.HermitianLatticeCounting.S4.Step4 := S4aux.fourth_reduction_identity

end Formalism.HermitianLatticeCounting.P
