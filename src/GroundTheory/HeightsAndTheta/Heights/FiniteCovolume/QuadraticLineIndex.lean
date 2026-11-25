module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.QuadraticWeightedIndex
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineIndexCoeffs
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedLenSmul
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightPos
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVecAtNeZero
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLenSq

@[expose] public section

open NumberField Module Matrix GroundTheory.Automorphic

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

variable {F E : Type*} [Field F] [Field E] [NumberField E]
  [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A shortest lattice line transfers its actual index and its integral stability
to the group of coefficients, where the minimum is a positive weighted inequality. -/
theorem ShortestVectorIndex.of_weighted_property
    (h : HermitianForm F E W) (v : Basis ι E W) (M : Majorant h v) (La : AddSubgroup W)
    (g : archUnitary h v) (x : W) (hL : IsLattice E La) (hx : x ∈ La) (hx0 : x ≠ 0)
    (hmin : ∀ y ∈ La, y ≠ 0 → M.len (invApply g (vecAt v x)) ≤ M.len (invApply g (vecAt v y)))
    {P : ℕ → Prop} (hp : ∀ c : InfinitePlace E → ℝ, (∀ w, 0 < c w) →
      intSubgroup E ≤ lineCoeffs La x →
      (∀ u : 𝓞 E, ∀ a ∈ lineCoeffs La x, (u : E) * a ∈ lineCoeffs La x) →
      (∀ a ∈ lineCoeffs La x, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2) →
      P ((intSubgroup E).relIndex (lineCoeffs La x))) : P (lineIndex E La x) := by
  let c : InfinitePlace E → ℝ := fun w =>
    (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re
  have hlen (a : E) : M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    rw [WeightedLenSmul.proof h v (LenSq.proof h v) M g x a]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hlen1 : M.len (invApply g (vecAt v x)) ^ 2 = ∑ w, c w := by simpa using hlen 1
  rw [LineIndexCoeffs.proof E W La x hx0]
  apply hp c (WeightPos.proof h v (VecAtNeZero.proof v) M g x hx0)
  · rintro _ ⟨a, rfl⟩
    exact hL.smul_mem a x hx
  · intro u a ha
    change ((u : E) * a) • x ∈ La
    rw [mul_smul]
    exact hL.smul_mem u _ ha
  · intro a ha h0
    rw [← hlen1, ← hlen a]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hmin (a • x) ha (smul_ne_zero h0 hx0)) 2


variable [IsTotallyComplex E]
variable (h : HermitianForm F E W) (v : Basis ι E W) (M : Majorant h v) (La : AddSubgroup W)
  (g : archUnitary h v) (x : W) (hL : IsLattice E La) (hx : x ∈ La) (hx0 : x ≠ 0)
  (hmin : ∀ y ∈ La, y ≠ 0 → M.len (invApply g (vecAt v x)) ≤ M.len (invApply g (vecAt v y)))

include hL hx hx0 hmin in
/-- Every shortest Hermitian lattice line has an index in the stable quadratic
spectrum, not just below its largest element. -/
theorem ShortestVectorIndex.mem_stable_indices (hE : finrank ℚ E = 2) :
    lineIndex E La x ∈ StableQuadraticIndex.indices (NumberField.discr E).natAbs := by
  apply ShortestVectorIndex.of_weighted_property h v M La g x hL hx hx0 hmin
    (P := fun n => n ∈ StableQuadraticIndex.indices (NumberField.discr E).natAbs)
  intro c hc hO hst hm
  apply (imaginary_quadratic_stable_index_spectrum E hE c hc _).mp
  refine ⟨lineCoeffs La x, hO, rfl, hm, ?_⟩
  rintro _ ⟨u, rfl⟩
  exact hst u

include hL hx hx0 hmin in
/-- For the nine displayed discriminant magnitudes every shortest Hermitian line
is primitive. The finite reduction test needs no class-number or PID hypothesis. -/
theorem ShortestVectorIndex.one_of_nine_discriminants (hE : finrank ℚ E = 2)
    (hd : (NumberField.discr E).natAbs ∈ [3, 4, 7, 8, 11, 19, 43, 67, 163]) :
    lineIndex E La x = 1 := by
  have hm := ShortestVectorIndex.mem_stable_indices h v M La g x hL hx hx0 hmin hE
  have hp := (StableQuadraticIndex.mem_indices.mp hm).1
  have hu := Finset.le_sup (f := id) hm
  change lineIndex E La x ≤ StableQuadraticIndex.maximum _ at hu
  have hone := List.mem_map_of_mem (f := StableQuadraticIndex.maximum) hd
  rw [StableQuadraticIndex.nine_maxima, List.mem_replicate] at hone
  omega

end GroundTheory.Heights₂.Heights.FiniteCovolume
