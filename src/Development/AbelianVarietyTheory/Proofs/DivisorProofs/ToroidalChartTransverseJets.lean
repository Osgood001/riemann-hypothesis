module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CoeffEqZeroOfMemSpanPow

@[expose] public section
namespace GlobalTheory.RigChart

open MvPowerSeries TrivSqZeroExt

/-- The dual-number point with specified coefficients and tangent coordinates. -/
noncomputable def chartJet {K k σ : Type} [Field K] [Field k] [Fintype σ]
    (e : K →+* k) (a : σ → k) : MvPowerSeries σ K →+* DualNumber k where
  toFun r := ⟨e (constantCoeff r), ∑ i, a i * e (constantCoeff (pderiv i r))⟩
  map_zero' := by ext <;> simp
  map_one' := by
    apply TrivSqZeroExt.ext
    · change e (constantCoeff (1 : MvPowerSeries σ K)) = 1
      simp
    · change (∑ i, a i * e (constantCoeff (pderiv i 1))) = 0
      simp
  map_add' r s := by
    apply TrivSqZeroExt.ext
    · change e (constantCoeff (r + s)) = e (constantCoeff r) + e (constantCoeff s)
      simp
    · change (∑ i, a i * e (constantCoeff (pderiv i (r + s)))) =
        (∑ i, a i * e (constantCoeff (pderiv i r))) +
        (∑ i, a i * e (constantCoeff (pderiv i s)))
      simp [mul_add, Finset.sum_add_distrib]
  map_mul' r s := by
    apply TrivSqZeroExt.ext
    · change e (constantCoeff (r * s)) = e (constantCoeff r) * e (constantCoeff s)
      simp
    · change (∑ i, a i * e (constantCoeff (pderiv i (r * s)))) =
        e (constantCoeff r) * (∑ i, a i * e (constantCoeff (pderiv i s))) +
        (∑ i, a i * e (constantCoeff (pderiv i r))) * e (constantCoeff s)
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)

@[simp] theorem chartJet_C {K k σ : Type} [Field K] [Field k] [Fintype σ]
    (e : K →+* k) (a : σ → k) (c : K) :
    chartJet e a (C c) = TrivSqZeroExt.inl (e c) := by
  apply TrivSqZeroExt.ext
  · change e (constantCoeff (C c : MvPowerSeries σ K)) = e c
    simp
  · change (∑ i, a i * e (constantCoeff (pderiv i (C c)))) = 0
    simp

@[simp] theorem chartJet_X {K k σ : Type} [Field K] [Field k] [Fintype σ]
    (e : K →+* k) (a : σ → k) (j : σ) :
    chartJet e a (X j) = TrivSqZeroExt.inr (a j) := by
  classical
  ext
  · change e (constantCoeff (X j : MvPowerSeries σ K)) = 0
    simp
  · change (∑ i, a i * e (constantCoeff (pderiv i (X j)))) = a j
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [pderiv_X_of_ne (Ne.symm hi)]
    · simp

private theorem chart_fst_eq {K k σ : Type} [Field K] [Field k]
    (ρ : MvPowerSeries σ K →+* DualNumber k)
    (hρ : ∀ r ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K), (ρ r).fst = 0) (r : MvPowerSeries σ K) :
    (ρ r).fst = (ρ (C (constantCoeff r))).fst := by
  have hz : r - C (constantCoeff r) ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K) := by
    change ¬ IsUnit _
    rw [isUnit_iff_constantCoeff]
    simp
  simpa [sub_eq_zero] using hρ _ hz

private theorem chart_hom_ext {K k σ : Type} [Field K] [Field k] [Fintype σ]
    {ρ τ : MvPowerSeries σ K →+* DualNumber k}
    (hρ : ∀ r ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K), (ρ r).fst = 0)
    (hτ : ∀ r ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K), (τ r).fst = 0)
    (hC : ∀ c, ρ (C c) = τ (C c)) (hX : ∀ i, ρ (X i) = τ (X i)) : ρ = τ := by
  classical
  apply RingHom.ext
  intro r
  have hspan : r - C (constantCoeff r) ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) := by
    convert SocleDet.mem_span_X_of_coeff Finset.univ (r - C (constantCoeff r)) ?_ using 1
    · simp [Set.image_univ]
    · intro d hd
      have hz : d = 0 := Finsupp.ext fun i => hd i (Finset.mem_univ _)
      simp [hz]
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hspan
  have hsum : r = (∑ i, b i * X i) + C (constantCoeff r) := by
    rw [hb, sub_add_cancel]
  nth_rw 1 [hsum]
  conv_rhs => rw [hsum]
  simp only [map_add, map_sum, hC]
  apply congrArg (fun t => t + τ (C (constantCoeff r)))
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_mul, hX]
  have hfst : (ρ (b i)).fst = (τ (b i)).fst := by
    rw [chart_fst_eq ρ hρ, chart_fst_eq τ hτ, hC]
  have hx0 : (τ (X i)).fst = 0 := by
    rw [chart_fst_eq τ hτ]
    simp
  ext <;> simp [hfst, hx0]

/-- Every dual-number point above the closed chart point is the explicit jet of
its ordinary tangent vector. The coefficient-field map has no nilpotent part
when the chart coefficient field is algebraic over the rationals. -/
theorem chart_hom_eq_jet {K k σ : Type} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    [Field k] [Fintype σ] (ρ : MvPowerSeries σ K →+* DualNumber k)
    (hρ : ∀ r ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K), (ρ r).fst = 0) :
    ρ = chartJet ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (ρ.comp C))
      (fun i => (ρ (X i)).snd) := by
  let φ := ρ.comp (C : K →+* MvPowerSeries σ K)
  let e := (TrivSqZeroExt.fstHom k k k).toRingHom.comp φ
  let : Algebra ℚ (DualNumber k) := (φ.comp (algebraMap ℚ K)).toAlgebra
  have : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  have he := Algebra.FormallyUnramified.ext' (R := ℚ) (A := K) (B := DualNumber k)
    (TrivSqZeroExt.fstHom k k k).toRingHom ⟨2, TrivSqZeroExt.kerIdeal_sq k k⟩ φ.toRatAlgHom
    ((algebraMap k (DualNumber k)).comp e).toRatAlgHom (fun a => by simp [e, TrivSqZeroExt.algebraMap_eq_inl])
  apply chart_hom_ext hρ
  · intro r hr
    change e (constantCoeff r) = 0
    have hr' : ¬ IsUnit r := hr
    simpa [isUnit_iff_constantCoeff] using hr'
  · intro c
    rw [chartJet_C]
    exact DFunLike.congr_fun he c
  · intro i
    rw [chartJet_X]
    apply TrivSqZeroExt.ext
    · rw [chart_fst_eq ρ hρ]
      simp
    · rfl


open GlobalTheory.Toroidal MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Out

/-- Prescribe the transverse tangent and kill every boundary parameter. -/
noncomputable def transverseJet {K k : Type} [Field K] [Field k] {m d : ℕ}
    (e : K →+* k) (b : Fin d → k) : ChartRing K m d →+* DualNumber k :=
  chartJet e (Sum.elim (fun _ : Fin m => 0) b)

@[simp] theorem transverseJet_bdParam {K k : Type} [Field K] [Field k] {m d : ℕ}
    (e : K →+* k) (b : Fin d → k) (i : Fin m) :
    transverseJet e b (bdParam K m d i) = 0 := by
  simp [transverseJet]

@[simp] theorem transverseJet_X_inr {K k : Type} [Field K] [Field k] {m d : ℕ}
    (e : K →+* k) (b : Fin d → k) (j : Fin d) :
    transverseJet (m := m) e b (X (Sum.inr j)) = TrivSqZeroExt.inr (b j) := by
  simp [transverseJet]

private theorem transverseJet_closed {K k : Type} [Field K] [Field k] {m d : ℕ}
    (e : K →+* k) (b : Fin d → k) (r : ChartRing K m d) (hr : r ∈ IsLocalRing.maximalIdeal _) :
    (transverseJet e b r).fst = 0 := by
  change e (constantCoeff r) = 0
  have hr' : ¬ IsUnit r := hr
  simpa [isUnit_iff_constantCoeff] using hr'

/-- The only question left for rigidity of a mixed chart over an algebraic coefficient
field is whether any nonzero transverse tangent makes its full Mumford data constant.
Vanishing of all boundary parameters is automatic for the test family. -/
theorem isRigid_iff_transverse_jets {K : Type} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    {m d : ℕ} (Q : DegPre (ChartRing K m d)) (gam : Fin m → LinearMap.BilinForm ℤ Q.X) :
    IsRigid Q (bdParam K m d) gam ↔
      ∀ (k : Type) [Field k] (e : K →+* k) (b : Fin d → k) (a : Fin m → k),
        IsConstAlong Q (bdParam K m d) gam (transverseJet e b) a → b = 0 := by
  constructor
  · intro h k _ e b a hc
    have hzero := h k (transverseJet e b) a (transverseJet_closed e b)
      (transverseJet_bdParam e b) hc
    funext j
    simpa using hzero (X (Sum.inr j))
  · intro h k _ ρ a hρ hbd hc r
    let e := (TrivSqZeroExt.fstHom k k k).toRingHom.comp (ρ.comp C)
    let b : Fin d → k := fun j => (ρ (X (Sum.inr j))).snd
    have hv : (fun i : Fin m ⊕ Fin d => (ρ (X i)).snd) = Sum.elim (fun _ => 0) b := by
      funext i
      rcases i with i | j
      · simp only [Sum.elim_inl, hbd i, TrivSqZeroExt.snd_zero]
      · rfl
    have hjet : ρ = transverseJet e b := by
      simpa only [transverseJet, ← hv] using chart_hom_eq_jet ρ hρ
    rw [hjet] at hc ⊢
    rw [h k e b a hc]
    change (∑ i : Fin m ⊕ Fin d, Sum.elim (fun _ => 0) (0 : Fin d → k) i *
      e (constantCoeff (pderiv i r))) = 0
    exact Finset.sum_eq_zero fun i _ => by cases i <;> simp

end GlobalTheory.RigChart
