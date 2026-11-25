import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
structure ProjectionResolution (P J : Ideal (MRing ι)) (e : ℕ) where

  homog : IsMultiHomogIdeal J

  nondeg : ¬ J ≤ P

  X : Type
  [top : TopologicalSpace X]
  [compact : CompactSpace X]
  [t2 : T2Space X]

  A : FinHolAtlas e X

  U : X → Set X
  isOpen_U : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x

  lift : X → X → (Σ k, ι k) → ℂ
  holo : ∀ x p, A.HoloOn (U x) (fun y => lift x y p)
  mem : ∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P

  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)

  surj : ∀ z ∈ mcPts P, z ∉ mcPts J → ∃ x, SameOrbit (lift x x) z

  inj : ∀ x x', lift x x ∉ mcPts J → SameOrbit (lift x x) (lift x' x') → x = x'

  immersion : ∀ x, lift x x ∉ mcPts J → ∀ p : (k : K) → ι k, (∀ k, lift x x ⟨k, p k⟩ ≠ 0) →
    ∀ j, x ∈ (A.chart j).source →
      (fderiv ℂ (fun y => affCoord p (lift x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

  null : ∀ j, MeasureTheory.volume
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | lift x x ∈ mcPts J}) = 0

attribute [instance] ProjectionResolution.top ProjectionResolution.compact ProjectionResolution.t2

def projectionPotential {P J : Ideal (MRing ι)} {e : ℕ} (R : ProjectionResolution P J e) (L : HermLine ι) : LocPot R.X where
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  φ x y := Real.log (L.h (R.lift x y))

def ProjectionBridgeStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ)
    (R : ProjectionResolution P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    ptsIntegralAt P Ψ (pot L) (logNorm A s) =
      mInt R.A (fun j => projectionPotential R (L j)) (fun x => logNorm A s (R.lift x x))


variable {P J : Ideal (MRing ι)} {e : ℕ}
theorem continuousOn_projectionLift (R : ProjectionResolution P J e) (x : R.X) (p : Σ k, ι k) :
    ContinuousOn (fun z => R.lift x z p) (R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := R.A.cover z
  have ha : AnalyticAt ℂ ((fun w => R.lift x w p) ∘ (R.A.chart j).symm) (R.A.chart j z) :=
    R.holo x p j _ ⟨(R.A.chart j).map_source hj, by
      simp only [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact hz⟩
  have hc : ContinuousAt (((fun w => R.lift x w p) ∘ (R.A.chart j).symm) ∘ (R.A.chart j)) z :=
    ha.continuousAt.comp ((R.A.chart j).continuousAt hj)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with w hw
  simp only [Function.comp_apply, (R.A.chart j).left_inv hw]

private theorem smoothOn_potOf_of_isSmoothHerm (R : ProjectionResolution P J e) {L : HermLine ι} (hL : IsSmoothHerm L)
    (x : R.X) : R.A.SmoothOn ((projectionPotential R L).U x) ((projectionPotential R L).φ x) := by
  intro j
  have hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => R.lift x ((R.A.chart j).symm w))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
    refine contDiffOn_pi.mpr fun p => ?_
    exact ((R.holo x p j).contDiffOn ((R.A.chart j).isOpen_inter_preimage_symm
      (R.isOpen_U x)).uniqueDiffOn).restrict_scalars ℝ
  have hcomp := (hL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L.h _).comp hlift (fun w hw => (R.mem x _ hw.2).1)
  exact hcomp.log fun w hw => (L.pos _ (R.mem x _ hw.2).1).ne'

private theorem exists_holo_re_eq_potOf_sub_on_overlap (R : ProjectionResolution P J e) (L : HermLine ι) (x x' y : R.X)
    (hy : y ∈ R.U x ∩ R.U x') : ∃ W : Set R.X, IsOpen W ∧ y ∈ W ∧ ∃ G : R.X → ℂ,
      R.A.HoloOn W G ∧ ∀ z ∈ W ∩ R.U x ∩ R.U x',
        (projectionPotential R L).φ x z - (projectionPotential R L).φ x' z = (G z).re := by
  classical
  obtain ⟨c, hc, hxy⟩ := R.compat x x' y hy
  choose i hi using (R.mem x' y hy.2).1
  have hVo : IsOpen (R.U x ∩ R.U x') := (R.isOpen_U x).inter (R.isOpen_U x')
  have hcx : ∀ p, ContinuousOn (fun z => R.lift x z p) (R.U x ∩ R.U x') := fun p =>
    (continuousOn_projectionLift R x p).mono Set.inter_subset_left
  have hcx' : ∀ p, ContinuousOn (fun z => R.lift x' z p) (R.U x ∩ R.U x') := fun p =>
    (continuousOn_projectionLift R x' p).mono Set.inter_subset_right
  let r : K → R.X → ℂ := fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ / c k
  let D : K → Set R.X := fun k => (R.U x ∩ R.U x') ∩ (fun z => R.lift x' z ⟨k, i k⟩) ⁻¹' {0}ᶜ
  have hD : ∀ k, IsOpen (D k) := fun k => (hcx' _).isOpen_inter_preimage hVo isOpen_compl_singleton
  have hr : ∀ k, ContinuousOn (r k) (D k) := fun k =>
    (((hcx _).mono Set.inter_subset_left).div ((hcx' _).mono Set.inter_subset_left)
      (fun z hz => hz.2)).div_const _
  let W : Set R.X := (R.U x ∩ R.U x') ∩ ⋂ k, (D k ∩ r k ⁻¹' Complex.slitPlane)
  have hW : IsOpen W :=
    hVo.inter (isOpen_iInter_of_finite fun k =>
      (hr k).isOpen_inter_preimage (hD k) Complex.isOpen_slitPlane)
  have hlk : ∀ k, R.lift x y ⟨k, i k⟩ = c k * R.lift x' y ⟨k, i k⟩ := fun k => congrFun hxy _
  have hyW : y ∈ W := by
    refine ⟨hy, Set.mem_iInter.mpr fun k => ⟨⟨hy, hi k⟩, ?_⟩⟩
    have : r k y = 1 := by
      simp only [r, hlk k]
      field_simp [hi k, hc k]
    simp only [Set.mem_preimage, this]
    exact Complex.one_mem_slitPlane
  refine ⟨W, hW, hyW, fun z => ∑ k, (L.a k : ℂ) * (Complex.log (r k z) + (Real.log ‖c k‖ : ℂ)),
    ?_, ?_⟩
  · intro j w hw
    have hzV : (R.A.chart j).symm w ∈ R.U x ∩ R.U x' := hw.2.1
    have hzk := fun k => Set.mem_iInter.mp hw.2.2 k
    have ha : ∀ p, AnalyticAt ℂ (fun w => R.lift x ((R.A.chart j).symm w) p) w := fun p =>
      R.holo x p j w ⟨hw.1, hzV.1⟩
    have ha' : ∀ p, AnalyticAt ℂ (fun w => R.lift x' ((R.A.chart j).symm w) p) w := fun p =>
      R.holo x' p j w ⟨hw.1, hzV.2⟩
    have hrk : ∀ k, AnalyticAt ℂ (fun w => r k ((R.A.chart j).symm w)) w := fun k =>
      ((ha _).div (ha' _) (hzk k).1.2).div analyticAt_const (hc k)
    show AnalyticAt ℂ (fun w => ∑ k, (L.a k : ℂ) *
      (Complex.log (r k ((R.A.chart j).symm w)) + (Real.log ‖c k‖ : ℂ))) w
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ) Finset.univ fun k _ => ?_
    exact analyticAt_const.mul (((hrk k).clog (hzk k).2).add analyticAt_const)
  · rintro z ⟨⟨hzW, hzx⟩, hzx'⟩
    obtain ⟨c', hc', hz⟩ := R.compat x x' z ⟨hzx, hzx'⟩
    have hzk := fun k => Set.mem_iInter.mp hzW.2 k
    have h2 := L.pos _ (R.mem x' z hzx').1
    have hsm := L.smul c' (R.lift x' z) hc'
    rw [← hz] at hsm
    have hrz : ∀ k, r k z = c' k / c k := by
      intro k
      have hne : R.lift x' z ⟨k, i k⟩ ≠ 0 := (hzk k).1.2
      simp only [r, congrFun hz ⟨k, i k⟩]
      field_simp [hne, hc k]
    have hP : ∀ k ∈ Finset.univ, ‖c' k‖ ^ L.a k ≠ 0 := fun k _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))
    simp only [projectionPotential]
    rw [hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hP) h2.ne', add_sub_cancel_right,
      Real.log_prod hP, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrz k, Real.log_zpow]
    simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_re,
      Complex.log_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_mul, sub_zero,
      norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k)) (norm_ne_zero_iff.mpr (hc k))]
    ring

theorem isPotential_projectionPotential (R : ProjectionResolution P J e) {L : HermLine ι} (hL : IsSmoothHerm L) :
    IsPotential R.A (projectionPotential R L) :=
  ⟨smoothOn_potOf_of_isSmoothHerm R hL, fun x x' y hy => exists_holo_re_eq_potOf_sub_on_overlap R L x x' y hy⟩


end ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

def brQ (R : ProjectionResolution P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    Fin e → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

def brBad (R : ProjectionResolution P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def brW (R : ProjectionResolution P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

variable (R : ProjectionResolution P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem brGood : ∀ x ∉ brBad R Ψ, ∀ j, x ∈ (R.A.chart j).source →
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr ⟨j, hj, h⟩)

theorem notMemB_of_notMem_brBad {x : R.X} (hx : x ∉ brBad R Ψ) : R.lift x x ∉ mcPts J := fun h => hx (Or.inl (Or.inl h))

theorem projection_zero_ne_of_notMem_bridgeBadSet {x : R.X} (hx : x ∉ brBad R Ψ) :
    Ψ (segre (R.lift x x)) 0 ≠ 0 := fun h => hx (Or.inl (Or.inr h))

theorem brW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : R.X}
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) : brW R Ψ x ∈ fibre P Ψ (brQ R Ψ x) := by
  classical
  have hz0 : R.lift x x ∈ mcPts P := R.mem x x (R.mem_U x)
  let k0 : K := hK.some
  let cc : K → ℂ := fun k => if k = k0 then (Ψ (segre (R.lift x x)) 0)⁻¹ else 1
  have hcc : ∀ k, cc k ≠ 0 := by
    intro k
    simp only [cc]
    split_ifs
    · exact inv_ne_zero h0
    · exact one_ne_zero
  have horb : SameOrbit (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) (R.lift x x) := ⟨cc, hcc, rfl⟩
  have hprod : ∏ k, cc k = (Ψ (segre (R.lift x x)) 0)⁻¹ := by simp [cc]
  have hseg : segre (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) = brW R Ψ x := by
    rw [segre_smul, hprod]
    rfl
  refine ⟨fun p => cc p.1 * R.lift x x p, mem_mcPts_of_sameOrbit hPh horb hz0, hseg, ?_⟩
  show Ψ ((Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)) = Fin.cons 1 (brQ R Ψ x)
  rw [map_smul]
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [inv_mul_cancel₀ h0]
  · simp [brQ, div_eq_inv_mul]

theorem brW_injOn : Set.InjOn (brW R Ψ) {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0} := by
  intro x hx x' hx' h
  have hz' := (R.mem x' x' (R.mem_U x')).1
  apply R.inj x x' hx.1
  apply sameOrbit_of_segre hz' (Ψ (segre (R.lift x x)) 0 * (Ψ (segre (R.lift x' x')) 0)⁻¹)
    (mul_ne_zero hx.2 (inv_ne_zero hx'.2))
  have h' : (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) =
      (Ψ (segre (R.lift x' x')) 0)⁻¹ • segre (R.lift x' x') := h
  rw [mul_smul, ← h', smul_smul, mul_inv_cancel₀ hx.2, one_smul]

theorem brFib_finite (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} \ brBad R Ψ).Finite := by
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  refine Set.Finite.of_injOn (f := brW R Ψ) (t := fibre P Ψ y) ?_ ?_ (fibreFinite K ι P e Ψ hP hΨ y)
  · intro x hx
    have h0 := projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2
    have hq : brQ R Ψ x = y := hx.1
    rw [← hq]
    exact brW_mem_fibre R Ψ hP.1 hPh h0
  · intro x hx x' hx' h
    exact brW_injOn R Ψ ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩
      ⟨notMemB_of_notMem_brBad R Ψ hx'.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx'.2⟩ h

theorem exists_of_mem_fibre {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y)
    (hy : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ brQ R Ψ x = y ∧ brW R Ψ x = w := by
  obtain ⟨z, hz, hzw, hΨw⟩ := hw
  have hzJ : z ∉ mcPts J := by
    intro hzJ
    refine hy ⟨z, hz, hzJ, ?_⟩
    rw [hzw]
    exact hΨw
  obtain ⟨x, hx⟩ := R.surj z hz hzJ
  obtain ⟨cc, hcc, hlift⟩ := hx
  have hμ : ∏ k, cc k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hcc k
  have hseg : segre (R.lift x x) = (∏ k, cc k) • w := by
    rw [hlift, segre_smul, hzw]
  have hΨl : Ψ (segre (R.lift x x)) = (∏ k, cc k) • Fin.cons 1 y := by
    rw [hseg, map_smul, hΨw]
  have h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, cc k := by
    rw [hΨl]
    simp
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hzJ
    refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (cc k)⁻¹, fun k => inv_ne_zero (hcc k), ?_⟩ h
    funext p
    rw [hlift]
    exact (inv_mul_cancel_left₀ (hcc p.1) (z p)).symm
  · rw [h0]
    exact hμ
  · funext i
    simp only [brQ, hΨl]
    simp [hμ]
  · show (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) = w
    rw [h0, hseg, smul_smul, inv_mul_cancel₀ hμ, one_smul]

end ReciprocityTheory.ChartRestriction.G.Geo
