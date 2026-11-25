module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMinkowskiVolumeForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedIndexBound

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module MeasureTheory InfinitePlace
noncomputable section
variable {E : Type*} [Field E] [NumberField E]
/-- The weighted minimum already makes the coefficient group a discrete Euclidean subgroup. -/
theorem fg_of_weighted_minimum {E : Type*} [Field E] [NumberField E]
    (hNorm : WeightedNormSq.Statement E) (c : InfinitePlace E → ℝ) (hc : ∀ w, 0 < c w)
    (A : AddSubgroup E) (hmin : ∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2) :
    A.FG := by
  let f := ((weightedEmbed c).comp A.subtype).toIntLinearMap
  have hpos : 0 < ∑ w, c w := Finset.sum_pos (fun w _ => hc w) Finset.univ_nonempty
  have small (a : A) (ha : ‖f a‖ < Real.sqrt (∑ w, c w)) : a = 0 := by
    by_contra h
    have hb := hmin a a.2 (fun e => h (Subtype.ext e))
    rw [← hNorm c (fun w => (hc w).le)] at hb
    change (∑ w, c w) ≤ ‖f a‖ ^ 2 at hb
    nlinarith [Real.sq_sqrt hpos.le, norm_nonneg (f a)]
  have inj : Function.Injective f := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr
    fun a ha => small a (by simpa [ha] using Real.sqrt_pos.mpr hpos))
  let : DiscreteTopology f.range := discreteTopology_iff_isOpen_singleton_zero.mpr <|
    Metric.isOpen_singleton_iff.mpr ⟨_, Real.sqrt_pos.mpr hpos, by
      rintro ⟨_, a, rfl⟩ ha
      have h := small a (by simpa [dist_zero_right] using ha)
      subst a
      exact Subtype.ext (map_zero f)⟩
  exact (AddGroup.fg_iff_addSubgroup_fg A).mp (Module.Finite.iff_addGroup_fg.mp
    (Module.Finite.equiv (LinearEquiv.ofInjective f inj).symm))

private def pairToMixed (E : Type*) [Field E] [NumberField E] [IsTotallyComplex E] :
    InfinitePlace E × Fin 2 ≃ mixedEmbedding.index E where
  toFun p := Sum.inr (⟨p.1, IsTotallyComplex.isComplex _⟩, p.2)
  invFun
    | .inl w => False.elim ((not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)) w.2)
    | .inr (w, j) => (w, j)
  left_inv _ := rfl
  right_inv
    | .inl w => False.elim ((not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)) w.2)
    | .inr (_, _) => rfl

theorem weightedEmbed_volume_integralBasis [IsTotallyComplex E] {d : ℕ}
    (c : InfinitePlace E → ℝ) (hc : ∀ w, 0 ≤ c w)
    (e : Fin d ≃ InfinitePlace E × Fin 2)
    (f : Fin d ≃ Free.ChooseBasisIndex ℤ (𝓞 E))
    [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = d)]
    (o : Orientation ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (Fin d)) :
    |o.volumeForm (fun i => weightedEmbed c (integralBasis E (f i)))| =
      (∏ w, c w) * (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace E) * Real.sqrt |(discr E : ℝ)| := by
  classical
  let eu := (EuclideanSpace.basisFun (InfinitePlace E × Fin 2) ℝ).reindex e.symm
  let ei := e.trans (pairToMixed E)
  let std := (mixedEmbedding.stdBasis E).reindex ei.symm
  let lat := (mixedEmbedding.latticeBasis E).reindex f.symm
  let w (i : Fin d) := Real.sqrt (c (e i).1)
  have detStd : |std.det (lat : Fin d → _)| = (2 : ℝ)⁻¹ ^ nrComplexPlaces E *
      Real.sqrt |(discr E : ℝ)| := by
    have h := ZSpan.measure_fundamentalDomain lat volume std
    rw [show ZSpan.fundamentalDomain std = ZSpan.fundamentalDomain (mixedEmbedding.stdBasis E) by
           exact ZSpan.fundamentalDomain_reindex _ _,
        show ZSpan.fundamentalDomain lat = ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis E) by
           exact ZSpan.fundamentalDomain_reindex _ _,
        mixedEmbedding.volume_fundamentalDomain_stdBasis, mul_one,
        mixedEmbedding.volume_fundamentalDomain_latticeBasis] at h
    have h' := congrArg ENNReal.toReal h.symm
    simpa [Real.coe_sqrt, Int.norm_eq_abs] using h'
  have hm : eu.toBasis.toMatrix (fun i => weightedEmbed c (integralBasis E (f i))) =
      Matrix.of (fun i j => w i * std.toMatrix lat i j) := by
    ext i j
    simp only [Basis.toMatrix_apply, Matrix.of_apply, eu, OrthonormalBasis.reindex_toBasis,
      Basis.repr_reindex, Finsupp.equivMapDomain_apply, Equiv.symm_symm,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      std, lat, Basis.reindex_apply, mixedEmbedding.latticeBasis_apply]
    generalize h : e i = p
    rcases p with ⟨u, a⟩
    fin_cases a <;> simp [weightedEmbed, ei, pairToMixed, w, h]
  have hw : (∏ i, w i) = ∏ u, c u := by
    calc ∏ i, w i = ∏ p : InfinitePlace E × Fin 2, Real.sqrt (c p.1) := e.prod_comp (fun p => Real.sqrt (c p.1))
      _ = _ := by simp [Fintype.prod_prod_type, Real.sq_sqrt, hc]
  have hm' := congrArg Matrix.det hm
  rw [Matrix.det_mul_column, hw] at hm'
  rw [o.volumeForm_robust' eu, Basis.det_apply, hm', abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => hc i)]
  rw [← Basis.det_apply, detStd, mul_assoc]
  congr 3
  exact Fintype.card_congr (Equiv.subtypeUnivEquiv (IsTotallyComplex.isComplex (K := E)))

open Finset
private theorem prod_le_mean_pow {ι : Type*} [Fintype ι] [Nonempty ι] (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) : ∏ i, c i ≤ ((∑ i, c i) / Fintype.card ι) ^ Fintype.card ι := by
  classical
  have h0 : 0 ≤ ∏ i, c i := prod_nonneg fun i _ => hc i
  have h := Real.geom_mean_le_arith_mean univ (fun _ : ι => 1) c (fun _ _ => zero_le_one)
    (by simp [Fintype.card_pos]) (fun i _ => hc i)
  simp only [Real.rpow_one, sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul] at h
  exact (Real.rpow_inv_natCast_pow h0 Fintype.card_ne_zero).symm.le.trans
    (pow_le_pow_left₀ (Real.rpow_nonneg h0 _) h _)

private theorem discriminant_bound_of_weighted {ι : Type*} [Fintype ι] [Nonempty ι] (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) (I S : ℝ) (hS : 0 ≤ S)
    (h : I * (Real.pi * ∑ i, c i) ^ Fintype.card ι ≤
      (Fintype.card ι + 1).factorial * (∏ i, c i) * S) :
    I ≤ (((Fintype.card ι + 1).factorial : ℝ) /
      (Real.pi * Fintype.card ι) ^ Fintype.card ι) * S := by
  let m := Fintype.card ι
  have hsum : 0 < ∑ i, c i := Finset.sum_pos (fun i _ => hc i) univ_nonempty
  have hm : 0 < (m : ℝ) := by exact_mod_cast Fintype.card_pos
  have hB := prod_le_mean_pow c (fun i => (hc i).le)
  change (∏ i, c i) ≤ ((∑ i, c i) / m) ^ m at hB
  change I * (Real.pi * ∑ i, c i) ^ m ≤ (m + 1).factorial * (∏ i, c i) * S at h
  change I ≤ (((m + 1).factorial : ℝ) / (Real.pi * m) ^ m) * S
  rw [← mul_le_mul_iff_left₀ (show 0 < (Real.pi * ∑ i, c i) ^ m by positivity)]
  apply h.trans
  calc _ ≤ (m + 1).factorial * (((∑ i, c i) / m) ^ m) * S := by gcongr
       _ = _ := by
         rw [div_pow, mul_pow, mul_pow]
         field_simp

/-- Field-only upper bound for the index of a shortest line in a CM lattice. -/
def discriminantIndexBound (E : Type*) [Field E] [NumberField E] : ℝ :=
  let m := Fintype.card (InfinitePlace E)
  if m = 1 then Real.sqrt (|(discr E : ℝ)| / 3)
  else ((m + 1).factorial : ℝ) / (Real.pi * m) ^ m * Real.sqrt |(discr E : ℝ)|

/-- Transfer a packing coefficient to the integral basis with its exact weighted covolume. -/
private theorem discriminant_profile (E : Type*) [Field E] [NumberField E] [IsTotallyComplex E]
    (h₁ : CoeffLatticeBasis.Statement E) (h₂ : IndexLeDet.Statement E)
    (h₃ : WeightedNormSq.Statement E) (h₄ : WeightedSpaceDim.Statement E)
    (h₆ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      VolumeFormIntComb.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E))
    (c : InfinitePlace E → ℝ) (hc : ∀ w, 0 < c w)
    (A : AddSubgroup E) (hOA : intSubgroup E ≤ A)
    (hmin : ∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2)
    (C : ℝ) (hpack : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)]
      (o' : Orientation ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (Fin (finrank ℚ E)))
      (b : Fin (finrank ℚ E) → EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (lam : ℝ), 0 < lam →
      (∀ z : Fin (finrank ℚ E) → ℤ, z ≠ 0 → lam ≤ ‖∑ i, (z i : ℝ) • b i‖) →
      lam ^ finrank ℚ E ≤ C * |o'.volumeForm b|) :
    let m := Fintype.card (InfinitePlace E)
    ((intSubgroup E).relIndex A : ℝ) * (∑ w, c w) ^ m ≤
      C * ((∏ w, c w) * (2 : ℝ)⁻¹ ^ m * Real.sqrt |(discr E : ℝ)|) := by
  classical
  let m := Fintype.card (InfinitePlace E)
  have hd : finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E := h₄
  have : Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E) := ⟨hd⟩
  have hdim : finrank ℚ E = 2 * m := by simpa [m, Fintype.card_prod, Nat.mul_comm] using hd.symm
  let f := (finBasis ℚ E).indexEquiv (integralBasis E)
  let e : Fin (finrank ℚ E) ≃ InfinitePlace E × Fin 2 := Fintype.equivOfCardEq (by simpa using hd.symm)
  let o := (finBasisOfFinrankEq ℝ _ hd).orientation
  let a : Fin (finrank ℚ E) → 𝓞 E := fun i => RingOfIntegers.basis E (f i)
  have hco (i) : (a i : E) = integralBasis E (f i) := by rw [integralBasis_apply]
  have ha : LinearIndependent ℚ (fun i => (a i : E)) := by
    simp_rw [hco]; exact (integralBasis E).linearIndependent.comp _ f.injective
  have hFG := fg_of_weighted_minimum h₃ c hc A hmin
  have hh := WeightedIndexBound.det_profile E h₁ h₂ h₃ h₄ _ hpack h₆ c hc A hOA hFG hmin a ha o
  simp_rw [hco] at hh
  rw [weightedEmbed_volume_integralBasis c (fun w => (hc w).le) e f o, hdim, pow_mul,
    Real.sq_sqrt (Finset.sum_nonneg fun w _ => (hc w).le)] at hh
  exact hh

/-- The archimedean weights give a stronger index estimate before taking their arithmetic mean. -/
theorem WeightedIndexBound.discriminant_weights (E : Type*) [Field E] [NumberField E] [IsTotallyComplex E]
    (h₁ : CoeffLatticeBasis.Statement E) (h₂ : IndexLeDet.Statement E)
    (h₃ : WeightedNormSq.Statement E) (h₄ : WeightedSpaceDim.Statement E)
    (h₆ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      VolumeFormIntComb.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E))
    (c : InfinitePlace E → ℝ) (hc : ∀ w, 0 < c w)
    (A : AddSubgroup E) (hOA : intSubgroup E ≤ A)
    (hmin : ∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2) :
    let m := Fintype.card (InfinitePlace E)
    ((intSubgroup E).relIndex A : ℝ) * (Real.pi * ∑ w, c w) ^ m ≤
      (m + 1).factorial * (∏ w, c w) * Real.sqrt |(discr E : ℝ)| := by
  classical
  let m := Fintype.card (InfinitePlace E)
  have hd : finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E := h₄
  have : Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E) := ⟨hd⟩
  have hdim : finrank ℚ E = 2 * m := by simpa [m, Fintype.card_prod, Nat.mul_comm] using hd.symm
  have hpack (o' : Orientation ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (Fin (finrank ℚ E)))
      (b : Fin (finrank ℚ E) → EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (lam : ℝ) (hlam : 0 < lam)
      (hm : ∀ z : Fin (finrank ℚ E) → ℤ, z ≠ 0 → lam ≤ ‖∑ i, (z i : ℝ) • b i‖) :
      lam ^ finrank ℚ E ≤ (2 ^ m * ((m+1).factorial : ℝ) / Real.pi ^ m) * |o'.volumeForm b| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
    exact MinkowskiVolumeForm.blichfeldt_even _ _ m hdim o' b lam hlam hm
  have hh := discriminant_profile E h₁ h₂ h₃ h₄ h₆ c hc A hOA hmin _ (fun {_} => hpack)
  dsimp only at hh
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hh
  change ((intSubgroup E).relIndex A : ℝ) * (Real.pi * ∑ w, c w) ^ m ≤
    (m + 1).factorial * (∏ w, c w) * Real.sqrt |(discr E : ℝ)|
  rw [mul_pow]
  calc _ = _ := (by ring : _ = ((intSubgroup E).relIndex A : ℝ) * (∑ w, c w) ^ m * Real.pi ^ m)
       _ ≤ _ := hh
       _ = _ := by rw [inv_pow]; field_simp; simp only [m]; ring

/-- The weighted shortest-vector coefficient index is bounded by the field discriminant
alone; the positive archimedean weights cancel by the arithmetic-geometric mean. -/
theorem WeightedIndexBound.discriminant (E : Type*) [Field E] [NumberField E] [IsTotallyComplex E]
    (h₁ : CoeffLatticeBasis.Statement E) (h₂ : IndexLeDet.Statement E)
    (h₃ : WeightedNormSq.Statement E) (h₄ : WeightedSpaceDim.Statement E)
    (h₆ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      VolumeFormIntComb.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E))
    (c : InfinitePlace E → ℝ) (hc : ∀ w, 0 < c w)
    (A : AddSubgroup E) (hOA : intSubgroup E ≤ A)
    (hmin : ∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2) :
    ((intSubgroup E).relIndex A : ℝ) ≤ discriminantIndexBound E := by
  classical
  unfold discriminantIndexBound
  dsimp only
  split_ifs with hm
  · have hd : finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E := h₄
    have : Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E) := ⟨hd⟩
    have hd₂ : finrank ℚ E = 2 := by simpa [Fintype.card_prod, hm] using hd.symm
    have hbound := discriminant_profile E h₁ h₂ h₃ h₄ h₆ c hc A hOA hmin (2 / Real.sqrt 3)
      (fun {_} o b lam hlam hsep => by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
        rw [show lam ^ finrank ℚ E = lam ^ 2 by rw [hd₂]]
        exact MinkowskiVolumeForm.planar _ _ hd₂ o b lam hlam hsep)
    have hmean := prod_le_mean_pow c (fun w => (hc w).le)
    simp only [hm, pow_one, Nat.cast_one, div_one] at hbound hmean
    have hsum : 0 < ∑ w, c w := sum_pos (fun w _ => hc w) univ_nonempty
    rw [Real.sqrt_div (abs_nonneg _), le_div_iff₀ (by positivity)]
    apply (le_of_mul_le_mul_right _ hsum)
    field_simp at hbound
    nlinarith [mul_le_mul_of_nonneg_right hmean (Real.sqrt_nonneg |(discr E : ℝ)|)]
  · exact discriminant_bound_of_weighted c hc _ _ (Real.sqrt_nonneg _)
      (WeightedIndexBound.discriminant_weights E h₁ h₂ h₃ h₄ h₆ c hc A hOA hmin)

end
end GroundTheory.Heights₂.Heights.FiniteCovolume
