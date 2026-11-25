import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsAtlas
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt

namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M

section SlopeTestRemainingChoices

variable {n : ℕ}

theorem eval_bind_one {m : ℕ} (y : Fin m → ℂ) {τ : Type} (g : τ → MvPolynomial (Fin m) ℂ)
    (φ : MvPolynomial τ ℂ) : eval y (bind₁ g φ) = eval (fun q => eval y (g q)) φ := by
  induction φ using MvPolynomial.induction_on
  · simp
  · simp [*]
  · simp [*]

end SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem AlgRes.isOpen_nonvan {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (i : Fin R.n) (g : MvPolynomial (Fin (R.amb i)) ℂ) :
    IsOpen {y | y ∈ R.src i ∧ eval (R.coord i y) g ≠ 0} := by
  have hc : Continuous fun y : R.src i => R.coord i y := (R.isEmbedding i).continuous
  have ho : IsOpen ((fun y : R.src i => R.coord i y) ⁻¹' {v | eval v g ≠ 0}) :=
    (isOpen_ne_fun (MvPolynomial.continuous_eval g) continuous_const).preimage hc
  have h2 := (R.isOpen_alt_bis i).isOpenMap_subtype_val _ ho
  convert h2 using 1
  ext y
  simp [and_comm]

structure LocalBoundaryChart {n : ℕ} (I B : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ) where
  r : Fin e → MvPolynomial (Fin n) ℂ
  J : Finset (Fin e)
  h : MvPolynomial (Fin n) ℂ
  span_eq : Ideal.span (Set.range fun l => algebraMap _ (locRing I p) (r l)) =
    Ideal.map (algebraMap _ (locRing I p)) (ptIdeal p)
  eval_h : eval p h ≠ 0
  mem_bd : h * ∏ l ∈ J, r l ∈ B

theorem AlgRes.localBoundary_volume_zero {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P ⊤ e) (B : ∀ i, Ideal (MvPolynomial (Fin (R.amb i)) ℂ))
    (hz : ∀ i, ∀ x ∈ R.src i, (∀ g ∈ B i, eval (R.coord i x) g = 0) ↔
      (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D)
    (charts : ∀ i x, x ∈ R.src i → LocalBoundaryChart (R.ideal i) (B i) (R.coord i x) e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A) (j : Fin A.n) :
    MeasureTheory.volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      {x | ∃ i, x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D}) = 0 := by
  classical
  have hset : (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      {x | ∃ i, x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D} =
      ⋃ i, ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
        {x | x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D}) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, i, h2⟩; exact ⟨i, h1, h2⟩
    · rintro ⟨i, h1, h2⟩; exact ⟨h1, i, h2⟩
  have hyp : ∀ l : Fin e, MeasureTheory.volume {w : Fin e → ℂ | w l = 0} = 0 := by
    intro l
    have : {w : Fin e → ℂ | w l = 0} =
        Set.univ.pi (Function.update (fun _ => (Set.univ : Set ℂ)) l {0}) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
      constructor
      · intro hw k
        by_cases hk : k = l
        · subst hk; simp [hw]
        · simp [Function.update_of_ne hk]
      · intro hw; simpa using hw l
    rw [this, MeasureTheory.volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  rw [hset]
  refine MeasureTheory.measure_iUnion_null fun i => ?_
  apply MeasureTheory.measure_null_of_locally_null
  rintro y0 ⟨hy0t, hy0s, -⟩
  obtain ⟨ψ, hψc, hxψ, hψs, hψe⟩ := hA.2 i _ hy0s (charts i _ hy0s).r (charts i _ hy0s).span_eq
    _ (R.isOpen_nonvan i (charts i _ hy0s).h) ⟨hy0s, (charts i _ hy0s).eval_h⟩
  set d := charts i _ hy0s with hd
  have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target ψ.open_source
  refine ⟨_, inter_mem_nhdsWithin _ (hU.mem_nhds ⟨hy0t, hxψ⟩), ?_⟩
  have hN : MeasureTheory.volume ((ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) ∩
      {w : Fin e → ℂ | ∏ l ∈ d.J, w l = 0}) = 0 := by
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_iUnion_null hyp)
    rintro w ⟨-, hw⟩
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.1 hw
    exact Set.mem_iUnion.2 ⟨l, hl⟩
  have hg : DifferentiableOn ℝ ((A.chart j) ∘ ψ.symm)
      ((ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) ∩ {w : Fin e → ℂ | ∏ l ∈ d.J, w l = 0}) :=
    fun w hw => (((hψc j).2 w hw.1).differentiableAt.restrictScalars ℝ).differentiableWithinAt
  refine MeasureTheory.measure_mono_null ?_
    (MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ hg hN)
  rintro y ⟨⟨hyt, hys, hyD⟩, -, hyψ⟩
  refine ⟨ψ ((A.chart j).symm y), ⟨⟨ψ.map_source hyψ, ?_⟩, ?_⟩, ?_⟩
  · rw [Set.mem_preimage, ψ.left_inv hyψ]; exact (A.chart j).map_target hyt
  · have hbd := (hz i _ hys).2 hyD _ d.mem_bd
    rw [map_mul, map_prod] at hbd
    have h0 := (mul_eq_zero.1 hbd).resolve_left (hψs hyψ).1.2
    simp only [Set.mem_ofPred_eq, hψe _ hyψ]
    exact h0
  · simp only [Function.comp_apply, ψ.left_inv hyψ, (A.chart j).right_inv hyt]

end ReciprocityTheory.AnForm.R
