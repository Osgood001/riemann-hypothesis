module
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.QuadraticLineIndex

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField NumberField.InfinitePlace GroundTheory.Automorphic Module Matrix

variable {E : Type*} [Field E] [NumberField E] [IsTotallyComplex E] [Algebra.IsQuadraticExtension ℚ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rank_one_shortest_iff (h : HermitianForm ℚ E E) (v : Basis ι E E) (M : Majorant h v)
    (g : archUnitary h v) (A : AddSubgroup E) (c : InfinitePlace E → ℝ) (hc : ∀ w, 0 < c w) :
    (∀ a ∈ A, a ≠ 0 → M.len (invApply g (vecAt v 1)) ≤ M.len (invApply g (vecAt v a))) ↔
      ∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
  let cM : InfinitePlace E → ℝ := fun w =>
    (star (invApply g (vecAt v 1) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v 1) w)).re
  have hpos : ∀ w, 0 < cM w := WeightPos.proof h v (VecAtNeZero.proof v) M g 1 one_ne_zero
  let w : InfinitePlace E := Classical.arbitrary _
  have hd := Algebra.IsQuadraticExtension.finrank_eq_two ℚ E
  rw [weighted_minimum_iff_single_embedding E hd w c (hc w) A,
    ← weighted_minimum_iff_single_embedding E hd w cM (hpos w) A]
  have hlen (a : E) : M.len (invApply g (vecAt v a)) ^ 2 =
      ∑ w, cM w * ‖w.embedding a‖ ^ 2 := by
    simpa [cM, mul_comm] using WeightedLenSmul.proof h v (LenSq.proof h v) M g (1:E) a
  have hone : M.len (invApply g (vecAt v 1)) ^ 2 = ∑ w, cM w := by simpa using hlen 1
  constructor
  · intro hshort a ha hne
    rw [← hone, ← hlen]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hshort a ha hne) 2
  · intro hshort a ha hne
    have hm := hshort a ha hne
    rw [← hone, ← hlen] at hm
    exact le_of_sq_le_sq (by simpa only [sq] using hm) (Real.sqrt_nonneg _)

private theorem fg_of_quadratic_weighted_minimum (A : AddSubgroup E) (c : InfinitePlace E → ℝ)
    (hc : ∀ w, 0 < c w)
    (hmin : ∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2) : A.FG := by
  let w : InfinitePlace E := Classical.arbitrary _
  let f := (w.embedding.toAddMonoidHom.comp A.subtype).toIntLinearMap
  have hinj : Function.Injective f := w.embedding.injective.comp Subtype.val_injective
  have hs := (weighted_minimum_iff_single_embedding E (Algebra.IsQuadraticExtension.finrank_eq_two ℚ E)
    w c (hc w) A).mp hmin
  have : DiscreteTopology f.range := DiscreteTopology.of_forall_le_norm zero_lt_one (by
    rintro ⟨_, a, rfl⟩ hn
    apply hs a a.2
    intro ha
    apply hn
    apply Subtype.ext
    change w.embedding a.val = 0
    rw [ha, map_zero])
  exact (AddGroup.fg_iff_addSubgroup_fg A).mp (Module.Finite.iff_addGroup_fg.mp
    (Module.Finite.equiv (LinearEquiv.ofInjective f hinj).symm))

private theorem lineCoeffs_one {K : Type*} [Field K] (A : AddSubgroup K) : lineCoeffs A (1:K) = A := by
  ext a; change a * 1 ∈ A ↔ a ∈ A; rw [mul_one]

/-- Realize a stable minimum-preserving overgroup as the actual lattice of a
shortest line, of exactly the same index, in any fixed rank-one Hermitian data. -/
theorem rank_one_realizes (h : HermitianForm ℚ E E) (v : Basis ι E E) (M : Majorant h v)
    (g : archUnitary h v) (A : AddSubgroup E) (hO : intSubgroup E ≤ A)
    (hstable : ∀ (a : 𝓞 E) (x : E), x ∈ A → (a:E)*x ∈ A)
    (c : InfinitePlace E → ℝ) (hc : ∀ w, 0 < c w)
    (hmin : ∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2) :
    IsLattice E A ∧ (1:E) ∈ A ∧ lineCoeffs A 1 = A ∧
      lineIndex E A 1 = (intSubgroup E).relIndex A ∧
      ∀ a ∈ A, a ≠ 0 → M.len (invApply g (vecAt v 1)) ≤ M.len (invApply g (vecAt v a)) := by
  have h1 : (1:E) ∈ A := hO ⟨1, (algebraMap (𝓞 E) E).map_one⟩
  refine ⟨⟨hstable, fg_of_quadratic_weighted_minimum A c hc hmin, ?_⟩, h1, lineCoeffs_one A,
    ?_, (rank_one_shortest_iff h v M g A c hc).mpr hmin⟩
  · apply top_unique
    intro y _
    simpa using (Submodule.span E (A : Set E)).smul_mem y (Submodule.subset_span h1)
  · rw [LineIndexCoeffs.proof E E A 1 one_ne_zero, lineCoeffs_one]

/-- Every index allowed by the stable quadratic spectrum occurs in real Hermitian
data, already in rank one and at the shortest vector 1. -/
theorem rank_one_shortest_index_spectrum (h : HermitianForm ℚ E E) (v : Basis ι E E)
    (M : Majorant h v) (g : archUnitary h v) (n : ℕ) :
    (∃ A : AddSubgroup E, IsLattice E A ∧ (1:E) ∈ A ∧ lineIndex E A 1 = n ∧
      ∀ a ∈ A, a ≠ 0 → M.len (invApply g (vecAt v 1)) ≤ M.len (invApply g (vecAt v a))) ↔
      n ∈ StableQuadraticIndex.indices (NumberField.discr E).natAbs := by
  let c : InfinitePlace E → ℝ := fun _ => 1
  have hc (w) : 0 < c w := zero_lt_one
  refine Iff.trans ?_ (imaginary_quadratic_stable_index_spectrum E (Algebra.IsQuadraticExtension.finrank_eq_two ℚ E)
    c hc n)
  constructor
  · rintro ⟨A,hA,h1,hn,hmin⟩
    refine ⟨A,?_,?_,(rank_one_shortest_iff h v M g A c hc).mp hmin,?_⟩
    · rintro _ ⟨u,rfl⟩
      simpa using hA.smul_mem u _ h1
    · rw [LineIndexCoeffs.proof E E A 1 one_ne_zero] at hn
      rwa [lineCoeffs_one] at hn
    · rintro _ ⟨u,rfl⟩ x hx
      exact hA.smul_mem u x hx
  · rintro ⟨A,hO,hn,hmin,hs⟩
    obtain ⟨hA,h1,-,hidx,hshort⟩ := rank_one_realizes h v M g A hO
      (fun u => hs _ ⟨u,rfl⟩) c hc hmin
    exact ⟨A,hA,h1,hidx.trans hn,hshort⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume
