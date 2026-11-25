module

public import Mathlib
public import Lemmata.OrbitSpans.Basic
public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
public import Formalism.GaloisIrreducibility.NoSolvableTransitive
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRCycleProbSum
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartEqIff
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartSpec
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRLemmaP
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRSquarefreeCount
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRTypeCountExact
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRCycleTypeProb

@[expose] public section

namespace Bl.CyclicComponents

private lemma cyc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hirr : ∀ U : Submodule ℂ V, (∀ g : G, ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (w : V) (hw : w ≠ 0) (S : Submodule ℂ V) (f : Module.End ℂ V)
    (hf : ∀ g : G, f (ρ g w) ∈ S) : ∀ v, f v ∈ S := by
  have hle : Submodule.span ℂ (Set.range fun g => ρ g w) ≤ S.comap f :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hf)
  rw [Bl.OrbitSpans.span_eq_top_of_invariant ρ w hirr hw] at hle
  exact fun _ => hle Submodule.mem_top

private lemma core {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (W : Submodule ℂ V) (P : Module.End ℂ V)
    (hPW : ∀ v, P v ∈ W) (hPfix : ∀ w ∈ W, P w = w)
    (hcomm : ∀ g g' : G, P * ρ g * P * (P * ρ g' * P) = P * ρ g' * P * (P * ρ g * P))
    (hirr : ∀ U : Submodule ℂ V, (∀ g : G, ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤) :
    Module.finrank ℂ W ≤ 1 := by
  by_cases hW : W = ⊥
  · rw [hW]
    simp
  have hB : ∀ g : G, ∀ w ∈ W, P (ρ g w) = (P * ρ g * P) w := by
    intro g w hw
    simp [hPfix w hw]
  have hscal : ∀ h : G, ∃ μ : ℂ, ∀ x ∈ W, (P * ρ h * P) x = μ • x := by
    intro h
    have hBW : ∀ x ∈ W, (P * ρ h * P) x ∈ W := fun x _ => by
      simp only [mul_apply_eq_comp]
      exact hPW _
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((P * ρ h * P).restrict hBW)
    obtain ⟨w, hwv⟩ := hμ.exists_hasEigenvector
    have hw1 := hwv.apply_eq_smul
    have hw2 : (P * ρ h * P) (w : V) = μ • (w : V) := by
      have := congrArg Subtype.val hw1
      simpa [LinearMap.restrict_apply] using this
    have hw0 : (w : V) ≠ 0 := by
      intro h0
      apply hwv.2
      exact Subtype.ext h0
    have key := cyc ρ hirr (w : V) hw0 ((P * ρ h * P).eigenspace μ) P (by
      intro g
      rw [Module.End.mem_eigenspace_iff, hB g w w.2]
      rw [← mul_apply_eq_comp, hcomm h g, mul_apply_eq_comp, hw2, map_smul])
    refine ⟨μ, fun x hx => ?_⟩
    have := Module.End.mem_eigenspace_iff.mp (key x)
    rwa [hPfix x hx] at this
  obtain ⟨w0, hw0W, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have key := cyc ρ hirr w0 hw0 (ℂ ∙ w0) P (by
    intro g
    obtain ⟨μ, hμ⟩ := hscal g
    rw [hB g w0 hw0W, hμ w0 hw0W]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hle : W ≤ ℂ ∙ w0 := by
    intro x hx
    rw [← hPfix x hx]
    exact key x
  calc Module.finrank ℂ W ≤ Module.finrank ℂ (ℂ ∙ w0) := Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hw0

open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility in
theorem goal1 {G : Type} [inst : Group G] [inst_1 : Fintype G] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (J : Subgroup G) (χ : J →* ℂˣ)
    (hcomm : ∀ g g' : G,
      Commute (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ)
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ))
    (hirr : IsIrr ρ) :
    Module.finrank ℂ (eqvSpace ρ (fun u : J => (u : G)) (fun u => (χ u : ℂ))) ≤ 1 := by
  classical
  let P := ρ.asAlgebraHom (twistedIdem J χ)
  have hP : ∀ v, P v = ∑ u : J, ((↑(Nat.card J) : ℂ)⁻¹ * ↑(χ u)⁻¹) • ρ ↑u v := by
    intro v
    dsimp only [P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [twistedIdem.eq_def, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [map_smul, LinearMap.smul_apply, Representation.asAlgebraHom_of]
  have hPW : ∀ v, P v ∈ eqvSpace ρ (fun u : J => u.val) (fun u => (χ u).val) := by
    intro v
    rw [eqvSpace.eq_def]
    show ∀ u : J, ρ ↑u (P v) = (χ u : ℂ) • P v
    intro u0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u0) _ _ (fun u => ?_)
    simp only [Equiv.coe_mulLeft, map_smul, Subgroup.coe_mul, map_mul, mul_apply_eq_comp, smul_smul,
      mul_inv_rev, Units.val_mul]
    congr 1
    linear_combination (-((↑(Nat.card J) : ℂ)⁻¹ * ↑(χ u)⁻¹)) * Units.inv_mul (χ u0)
  have hPfix : ∀ w ∈ eqvSpace ρ (fun u : J => u.val) (fun u => (χ u).val), P w = w := by
    intro w hw
    rw [eqvSpace.eq_def] at hw
    have hw' : ∀ u : J, ρ ↑u w = (χ u : ℂ) • w := hw
    rw [hP]
    simp only [hw', smul_smul, mul_assoc, Units.inv_mul, mul_one]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, mul_inv_cancel₀, one_smul]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcomm2 : ∀ g g' : G, P * ρ g * P * (P * ρ g' * P) = P * ρ g' * P * (P * ρ g * P) := by
    intro g g'
    have := congrArg ρ.asAlgebraHom (hcomm g g').eq
    simpa [map_mul, Representation.asAlgebraHom_of, P] using this
  rw [IsIrr.eq_def] at hirr
  exact core ρ _ P hPW hPfix hcomm2 hirr.2

end Bl.CyclicComponents
