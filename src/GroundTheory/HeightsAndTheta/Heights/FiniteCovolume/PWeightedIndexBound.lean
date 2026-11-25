module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

/-- Transfer any Euclidean packing estimate to the actual weighted coefficient index, before Hadamard. -/
theorem WeightedIndexBound.det_profile (E : Type*) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (h₁ : CoeffLatticeBasis.Statement E) (h₂ : IndexLeDet.Statement E)
    (h₃ : WeightedNormSq.Statement E) (h₄ : WeightedSpaceDim.Statement E)
    (C : ℝ) (hpack : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)]
      (o : Orientation ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (Fin (finrank ℚ E)))
      (b : Fin (finrank ℚ E) → EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (lam : ℝ), 0 < lam →
      (∀ z : Fin (finrank ℚ E) → ℤ, z ≠ 0 → lam ≤ ‖∑ i, (z i : ℝ) • b i‖) →
      lam ^ finrank ℚ E ≤ C * |o.volumeForm b|)
    (h₆ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      VolumeFormIntComb.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E))
    (c : InfinitePlace E → ℝ) (hc : ∀ w, 0 < c w)
    (A : AddSubgroup E) (hOA : intSubgroup E ≤ A) (hFG : A.FG)
    (hmin : ∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2)
    (a : Fin (finrank ℚ E) → 𝓞 E) (ha : LinearIndependent ℚ fun i => (a i : E))
    (o : Orientation ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (Fin (finrank ℚ E))) :
    letI : Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E) := ⟨h₄⟩
    ((intSubgroup E).relIndex A : ℝ) * (Real.sqrt (∑ w, c w)) ^ finrank ℚ E ≤
      C * |o.volumeForm (fun i => weightedEmbed c (a i : E))| := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E) := ⟨h₄⟩
  obtain ⟨e⟩ := h₁ A hOA hFG
  have hmem : ∀ i, (a i : E) ∈ A := fun i => hOA ⟨a i, rfl⟩
  set T : Matrix (Fin (finrank ℚ E)) (Fin (finrank ℚ E)) ℤ := fun i j => e.repr ⟨(a i : E), hmem i⟩ j with hT
  have hcoe : ∀ z : Fin (finrank ℚ E) → ℤ, ((∑ j, z j • e j : A) : E) = ∑ j, z j • (e j : E) := by
    intro z
    change A.subtype _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_zsmul]
    rfl
  have haT : ∀ i, (a i : E) = ∑ j, T i j • (e j : E) := by
    intro i
    rw [← hcoe]
    exact (congrArg Subtype.val (e.sum_repr ⟨(a i : E), hmem i⟩)).symm
  have hidx := h₂ A hOA e a T ha haT

  set Φ := weightedEmbed c with hΦ
  have hc0 : ∀ w, 0 ≤ c w := fun w => (hc w).le
  have hS : 0 < ∑ w, c w := Finset.sum_pos (fun w _ => hc w) Finset.univ_nonempty
  set lam := Real.sqrt (∑ w, c w) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 hS
  set b : Fin (finrank ℚ E) → EuclideanSpace ℝ (InfinitePlace E × Fin 2) := fun i => Φ (e i : E)

  have hmink : lam ^ finrank ℚ E ≤ C * |o.volumeForm b| := by
    refine hpack o b lam hlam0 fun z hz => ?_
    have hsum : ∑ i, (z i : ℝ) • b i = Φ ((∑ i, z i • e i : A) : E) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hcoe, map_sum]
      simp only [map_zsmul, b, Int.cast_smul_eq_zsmul]
    rw [hsum]
    set x : A := ∑ i, z i • e i
    have hx : (x : E) ≠ 0 := by
      intro h0
      have hx0 : x = 0 := Subtype.ext h0
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
      exact hi (Fintype.linearIndependent_iff.1 e.linearIndependent z hx0 i)
    have hq := hmin x x.2 hx
    rw [hlam, ← Real.sqrt_sq (norm_nonneg (Φ x)), h₃ c hc0]
    exact Real.sqrt_le_sqrt hq

  have hab : (fun i => Φ (a i : E)) = fun i => ∑ j, (T i j : ℝ) • b j := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [haT i, map_sum]
    simp only [map_zsmul, b, Int.cast_smul_eq_zsmul]
  have hvol : o.volumeForm (fun i => Φ (a i : E)) = (T.det : ℝ) * o.volumeForm b := by
    rw [hab]; exact h₆ o b T

  change ((intSubgroup E).relIndex A : ℝ) * lam ^ finrank ℚ E ≤ C * |o.volumeForm (fun i => Φ (a i : E))|
  rw [hvol, abs_mul]
  calc
    _ ≤ |(T.det : ℝ)| * lam ^ finrank ℚ E := mul_le_mul_of_nonneg_right hidx (pow_nonneg hlam0.le _)
    _ ≤ |(T.det : ℝ)| * (C * |o.volumeForm b|) := mul_le_mul_of_nonneg_left hmink (abs_nonneg _)
    _ = _ := by ring

theorem WeightedIndexBound.proof (E : Type*) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (h₁ : CoeffLatticeBasis.Statement E) (h₂ : IndexLeDet.Statement E)
    (h₃ : WeightedNormSq.Statement E) (h₄ : WeightedSpaceDim.Statement E)
    (h₅ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      MinkowskiVolumeForm.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E))
    (h₆ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      VolumeFormIntComb.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E)) :
    WeightedIndexBound.Statement E := by
  intro c hc A hOA hFG hmin r ⟨a, ha, hr⟩
  have hd : 0 < Real.sqrt (finrank ℚ E) := Real.sqrt_pos.mpr (by exact_mod_cast (Module.finrank_pos : 0 < finrank ℚ E))
  let C := Real.sqrt (finrank ℚ E) ^ finrank ℚ E
  have hC : 0 ≤ C := pow_nonneg hd.le _
  have : Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E) := ⟨h₄⟩
  let o := (Module.finBasisOfFinrankEq ℝ _ h₄).orientation
  let lam := Real.sqrt (∑ w, c w)
  have hS : 0 < ∑ w, c w := Finset.sum_pos (fun w _ => hc w) Finset.univ_nonempty
  have hlam : 0 < lam := Real.sqrt_pos.mpr hS
  have hr0 : 0 ≤ r := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact (norm_nonneg _).trans (hr (⟨0, Module.finrank_pos⟩ : Fin (finrank ℚ E)) w.embedding)
  have hnorm (i) : ‖weightedEmbed c (a i : E)‖ ≤ r * lam := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr0 hlam.le)).mp
    rw [h₃ c (fun w => (hc w).le), mul_pow, Real.sq_sqrt hS.le, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hr i w.embedding) 2) (hc w).le).trans_eq (mul_comm _ _)
  have hdet := WeightedIndexBound.det_profile E h₁ h₂ h₃ h₄ C (fun o' b lam' hpos hsep => by
    have hb := h₅ o' b lam' hpos hsep
    rw [div_pow, div_le_iff₀ (pow_pos hd _)] at hb
    simpa [C, mul_comm] using hb) h₆ c hc A hOA hFG hmin a ha o
  refine le_of_mul_le_mul_right ?_ (pow_pos hlam (finrank ℚ E))
  calc
    _ ≤ C * |o.volumeForm (fun i => weightedEmbed c (a i : E))| := hdet
    _ ≤ C * ∏ _i : Fin (finrank ℚ E), (r * lam) := mul_le_mul_of_nonneg_left
      ((o.abs_volumeForm_apply_le _).trans (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hnorm i))) hC
    _ = _ := by simp [C, mul_pow]; ring


end GroundTheory.Heights₂.Heights.FiniteCovolume
