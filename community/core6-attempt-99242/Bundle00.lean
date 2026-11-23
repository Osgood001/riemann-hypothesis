import Mathlib
universe u v
noncomputable section
section
noncomputable def UpperTheory.Reformulated.B.ClosedUnitBallSubring.ballRing :
    (K : Type) → [inst : NormedField K] → [IsUltrametricDist K] → Subring K :=
  fun K _ _ =>
    { carrier := {x : K | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : K)‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans $ max_le ha' hb'
      zero_mem' := by
        show ‖(0 : K)‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rw [norm_neg]
        exact ha' }
end
section
namespace Bl.FirstLemmaM

noncomputable def goal1 (K : Type*) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans $ max_le ha hb
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

end Bl.FirstLemmaM
end
section
open PowerSeries



namespace Formalism.ELL

def WFixed {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R) : Prop :=
  constantCoeff w = 0 ∧
  w = X ^ 3 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2
      + C W.a₆ * w ^ 3

def WSeriesUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R), ∃! w : PowerSeries R, WFixed W w


section Points

variable {K : Type u} [Field K] {σ : Type}

def xOf (w : PowerSeries K) (s : MvPowerSeries σ K) : FractionRing $ MvPowerSeries σ K :=
  algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) s /
    algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) (w.subst s)

def yOf (w : PowerSeries K) (s : MvPowerSeries σ K) : FractionRing $ MvPowerSeries σ K :=
  -1 / algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) (w.subst s)

end Points

def WPoint : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∀ (σ : Type) [Finite σ] (s : MvPowerSeries σ K), MvPowerSeries.constantCoeff s = 0 → s ≠ 0 →
      (W.map $ algebraMap K $ FractionRing $ MvPowerSeries σ K).toAffine.Nonsingular
        (xOf w s) (yOf w s)


end Formalism.ELL
end
section
open MvPowerSeries (coeff constantCoeff)
open PowerSeries



namespace Formalism.ELL

def WEqAt {R : Type u} [CommRing R] (W : WeierstrassCurve R) {σ : Type}
    (s v : MvPowerSeries σ R) : Prop :=
  v = s ^ 3 + W.a₁ • (s * v) + W.a₂ • (s ^ 2 * v) + W.a₃ • v ^ 2 + W.a₄ • (s * v ^ 2)
      + W.a₆ • v ^ 3

def WSubstUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R), WFixed W w →
    ∀ (σ : Type) [Finite σ] (s : MvPowerSeries σ R), constantCoeff s = 0 →
      WEqAt W s (w.subst s) ∧
      ∀ v : MvPowerSeries σ R, constantCoeff v = 0 → WEqAt W s v → v = w.subst s

def ChordAt {K : Type u} [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) {σ : Type}
    (s t r : MvPowerSeries σ K) : Prop :=
  let W' := (W.map $ algebraMap K $ FractionRing $ MvPowerSeries σ K).toAffine
  let ℓ := (yOf w s - yOf w t) / (xOf w s - xOf w t)
  xOf w r = W'.addX (xOf w s) (xOf w t) ℓ ∧ yOf w r = W'.addY (xOf w s) (xOf w t) (yOf w s) ℓ

def WChordSeries : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∃ F₂ : MvPowerSeries (Fin 2) K,
      (∀ d, coeff d F₂ ∈ Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) ∧
      constantCoeff F₂ = 0 ∧
      coeff (Finsupp.single 0 1) F₂ = 1 ∧ coeff (Finsupp.single 1 1) F₂ = 1 ∧
      ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F₂

def WChordSubst : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∀ F₂ : MvPowerSeries (Fin 2) K, constantCoeff F₂ = 0 →
      ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F₂ →
      ∀ (σ : Type) [Finite σ] (s t : MvPowerSeries σ K),
        constantCoeff s = 0 → constantCoeff t = 0 → s ≠ 0 → t ≠ 0 →
        xOf w s ≠ xOf w t → ChordAt W w s t (MvPowerSeries.subst ![s, t] F₂)

end Formalism.ELL
end
section
open PowerSeries



namespace Formalism.ELL

def wU {K : Type u} [Field K] (w : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => coeff (n + 3) w

def invSer {K : Type u} [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) : PowerSeries K :=
  X * (-1 + C W.a₁ * X + C W.a₃ * w)⁻¹

abbrev coeffRing {K : Type u} [Field K] (W : WeierstrassCurve K) : Subalgebra ℤ K :=
  Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)

def CubeTwo : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    WFixed W w → MvPowerSeries.constantCoeff F = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F →
    let a : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
    let b : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
    ∃ c : MvPowerSeries (Fin 2) K, (∀ d, MvPowerSeries.coeff d c ∈ coeffRing W) ∧
      MvPowerSeries.constantCoeff c = -1 ∧
      b ^ 2 * ((wU w).subst a)⁻¹ - a ^ 2 * ((wU w).subst b)⁻¹
        = c * F * MvPowerSeries.subst ![a, (invSer W w).subst b] F

def CubeThree : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    WFixed W w → MvPowerSeries.constantCoeff F = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F →
    let t : Fin 3 → MvPowerSeries (Fin 3) K := fun i => MvPowerSeries.X i
    let row : Fin 3 → Fin 3 → MvPowerSeries (Fin 3) K := fun i =>
      ![t i ^ 3, t i * ((wU w).subst (t i))⁻¹, -((wU w).subst (t i))⁻¹]
    ∃ e : MvPowerSeries (Fin 3) K, (∀ d, MvPowerSeries.coeff d e ∈ coeffRing W) ∧
      MvPowerSeries.constantCoeff e = -1 ∧
      (Matrix.of row).det
        = e * MvPowerSeries.subst ![MvPowerSeries.subst ![t 0, t 1] F, t 2] F
            * (t 0 - t 1) * (t 0 - t 2) * (t 1 - t 2)

end Formalism.ELL
end
section
open PowerSeries



namespace Formalism.ELL

namespace WeierstrassCoordinateSubstitution

variable {K : Type u} [Field K]

theorem exists_unit_factor {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w) :
    ∃ u, w = X ^ 3 * u ∧ constantCoeff u = 1 := by
  obtain ⟨h0, heq⟩ := hw
  have hX : (X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero
  obtain ⟨v, rfl⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hv : v = X ^ 2 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * X * v ^ 2
      + C W.a₄ * X ^ 2 * v ^ 2 + C W.a₆ * X ^ 2 * v ^ 3 := by
    apply mul_left_cancel₀ hX
    linear_combination heq
  obtain ⟨v₂, rfl⟩ := PowerSeries.X_dvd_iff.mpr $ by simpa using congrArg constantCoeff hv
  have hv₂ : v₂ = X + C W.a₁ * X * v₂ + C W.a₂ * X ^ 2 * v₂ + C W.a₃ * X ^ 2 * v₂ ^ 2
      + C W.a₄ * X ^ 3 * v₂ ^ 2 + C W.a₆ * X ^ 4 * v₂ ^ 3 := by
    apply mul_left_cancel₀ hX
    linear_combination hv
  have hv₂0 : constantCoeff v₂ = 0 := by simpa using congrArg constantCoeff hv₂
  obtain ⟨u, rfl⟩ := PowerSeries.X_dvd_iff.mpr hv₂0
  have hu : u = 1 + C W.a₁ * X * u + C W.a₂ * X ^ 2 * u + C W.a₃ * X ^ 3 * u ^ 2
      + C W.a₄ * X ^ 4 * u ^ 2 + C W.a₆ * X ^ 6 * u ^ 3 := by
    apply mul_left_cancel₀ hX
    linear_combination hv₂
  refine ⟨u, by ring, ?_⟩
  simpa using congrArg constantCoeff hu

theorem subst_w {u w : PowerSeries K} (hwu : w = X ^ 3 * u) {σ : Type}
    (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) :
    w.subst s = s ^ 3 * u.subst s := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero hs
  rw [hwu, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

theorem isUnit_subst {u : PowerSeries K} (hu : constantCoeff u = 1) {σ : Type}
    (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) :
    IsUnit $ u.subst s := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero hs
  obtain ⟨u', hu'⟩ := PowerSeries.X_dvd_iff.mpr $ show constantCoeff (u - 1) = 0 by simp [hu]
  have h1 : u = 1 + X * u' := by rw [← hu']
                                 ring
  rw [MvPowerSeries.isUnit_iff_constantCoeff, h1, ← PowerSeries.coe_substAlgHom ha, map_add,
    map_one, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]
  simp [hs]

theorem xOf_eq {u w : PowerSeries K} (hwu : w = X ^ 3 * u) (hu : constantCoeff u = 1)
    {σ : Type} (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) (hne : s ≠ 0) :
    xOf w s = (algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K)
      $ s ^ 2 * u.subst s)⁻¹ := by
  have hinj := IsFractionRing.injective (MvPowerSeries σ K) $ FractionRing $ MvPowerSeries σ K
  rw [xOf, subst_w hwu s hs, map_mul, map_mul, map_pow, map_pow]
  field_simp

theorem xOf_ne_of_hom {u w : PowerSeries K} (hwu : w = X ^ 3 * u) (hu : constantCoeff u = 1)
    {σ : Type} (φ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (s t : MvPowerSeries σ K)
    (hs0 : MvPowerSeries.constantCoeff s = 0) (ht0 : MvPowerSeries.constantCoeff t = 0)
    (hs : s ≠ 0) (ht : t ≠ 0) (hφs : φ s = 0) (hφt : φ t ≠ 0) : xOf w s ≠ xOf w t := by
  intro h
  rw [xOf_eq hwu hu s hs0 hs, xOf_eq hwu hu t ht0 ht, inv_inj] at h
  have h3 := congrArg φ $ IsFractionRing.injective (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) h
  rw [map_mul, map_mul, map_pow, map_pow, hφs] at h3
  apply mul_ne_zero (pow_ne_zero _ hφt) ((isUnit_subst hu t ht0).map φ).ne_zero
  rw [← h3]
  simp

theorem eq_of_xy {u w : PowerSeries K} (hwu : w = X ^ 3 * u) (hu : constantCoeff u = 1)
    {σ : Type} (A B : MvPowerSeries σ K) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hx : xOf w A = xOf w B)
    (hy : yOf w A = yOf w B) : A = B := by
  have hinj := IsFractionRing.injective (MvPowerSeries σ K) $ FractionRing $ MvPowerSeries σ K
  have key : ∀ s,
      xOf w s = -(algebraMap _ (FractionRing $ MvPowerSeries σ K) s) * yOf w s := by
    intro s
    simp only [xOf, yOf]
    ring
  have zero_of : ∀ s : MvPowerSeries σ K, MvPowerSeries.constantCoeff s = 0 →
      yOf w s = 0 → s = 0 := by
    intro s hs hys
    simp only [yOf, div_eq_zero_iff, neg_eq_zero, one_ne_zero, false_or] at hys
    have h1 : w.subst s = 0 := (map_eq_zero_iff _ hinj).mp hys
    rw [subst_w hwu s hs] at h1
    exact (pow_eq_zero_iff $ by norm_num).mp
      $ (mul_eq_zero.mp h1).resolve_right (isUnit_subst hu s hs).ne_zero
  by_cases hy0 : yOf w A = 0
  rw [zero_of A hA hy0, zero_of B hB (by rw [← hy]; exact hy0)]
  have hyB : yOf w B ≠ 0 := by rw [← hy]
                               exact hy0
  rw [key A, key B, hy] at hx
  exact hinj $ neg_inj.mp $ mul_right_cancel₀ hyB hx

theorem some_congr {L : Type u} [Field L] {W' : WeierstrassCurve.Affine L} {x y x' y' : L}
    {h : W'.Nonsingular x y} (hx : x = x') (hy : y = y') :
    ∃ h', WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx
  subst hy
  exact ⟨h, rfl⟩

end WeierstrassCoordinateSubstitution

end Formalism.ELL

namespace Formalism.ELL

namespace WeierstrassCoordinateSubstitution

variable {K : Type u} [Field K]

theorem chord_add {W : WeierstrassCurve K} {w : PowerSeries K} {σ : Type}
    [DecidableEq $ FractionRing $ MvPowerSeries σ K] (s t r : MvPowerSeries σ K)
    (hs : (W.map $ algebraMap K $ FractionRing $ MvPowerSeries σ K).toAffine.Nonsingular
      (xOf w s) $ yOf w s)
    (ht : (W.map $ algebraMap K $ FractionRing $ MvPowerSeries σ K).toAffine.Nonsingular
      (xOf w t) $ yOf w t)
    (hne : xOf w s ≠ xOf w t) (hch : ChordAt W w s t r) :
    ∃ h : (W.map $ algebraMap K $ FractionRing $ MvPowerSeries σ K).toAffine.Nonsingular
      (xOf w r) $ yOf w r,
      WeierstrassCurve.Affine.Point.some _ _ hs + WeierstrassCurve.Affine.Point.some _ _ ht =
        WeierstrassCurve.Affine.Point.some _ _ h := by
  obtain ⟨hx, hy⟩ := hch
  rw [WeierstrassCurve.Affine.Point.add_some fun h => hne h.1]
  refine some_congr ?_ ?_
  rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
  exact hx.symm
  rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
  exact hy.symm

theorem X_ne_zero' {σ : Type} (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ K) ≠ 0 := by
  intro h
  have h1 := congrArg (MvPowerSeries.coeff $ Finsupp.single i 1) h
  simp at h1

private theorem subst_subst_pair' {τ υ : Type} (F : MvPowerSeries (Fin 2) K)
    (a b : MvPowerSeries τ K) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (v : τ → MvPowerSeries υ K)
    (hv : MvPowerSeries.HasSubst v) :
    MvPowerSeries.subst v (F.subst ![a, b]) =
      F.subst ![MvPowerSeries.subst v a, MvPowerSeries.subst v b] := by
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [ha, hb]) hv]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem subst_X_X_ne_zero (F : MvPowerSeries (Fin 2) K)
    (hF1 : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1) (i j : Fin 3)
    (v : Fin 3 → MvPowerSeries (Fin 2) K) (hv0 : ∀ k, MvPowerSeries.constantCoeff (v k) = 0)
    (hi : v i = MvPowerSeries.X 0) (hj : v j = MvPowerSeries.X 1) :
    F.subst ![(MvPowerSeries.X i : MvPowerSeries (Fin 3) K), MvPowerSeries.X j] ≠ 0 := by
  intro h
  have hv := MvPowerSeries.hasSubst_of_constantCoeff_zero hv0
  have h1 := congrArg (MvPowerSeries.subst v) h
  rw [subst_subst_pair' F _ _ (by simp) (by simp) v hv, MvPowerSeries.subst_X hv,
    MvPowerSeries.subst_X hv, hi, hj] at h1
  have h0 : MvPowerSeries.subst v (0 : MvPowerSeries (Fin 3) K) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hv, map_zero]
  have e : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X := by
    funext k
    fin_cases k <;> rfl
  rw [h0, e, MvPowerSeries.subst_self, id_eq] at h1
  rw [h1] at hF1
  simp at hF1

theorem assoc_of (hS : WChordSubst.{u}) (hP : WPoint.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hw : WFixed W w) {u : PowerSeries K} (hwu : w = X ^ 3 * u)
    (hu : constantCoeff u = 1) (F : MvPowerSeries (Fin 2) K)
    (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F) :
    F.subst ![F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1],
        MvPowerSeries.X 2] =
      F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K),
        F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]] := by
  classical
  have cX : ∀ i : Fin 3,
      MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => by simp
  have nX : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ≠ 0 :=
    fun i => X_ne_zero' i
  have cSub : ∀ a b : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (F.subst ![a, b]) = 0 := by
    intro a b ha hb
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [ha, hb])
      (fun i => by fin_cases i <;> simp [ha, hb]) hF0
  have ne_of : ∀ (v : Fin 3 → MvPowerSeries (Fin 3) K),
      (∀ i, MvPowerSeries.constantCoeff (v i) = 0) →
      ∀ s t : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff s = 0 →
      MvPowerSeries.constantCoeff t = 0 → s ≠ 0 → t ≠ 0 → MvPowerSeries.subst v s = 0 →
      MvPowerSeries.subst v t ≠ 0 → xOf w s ≠ xOf w t := by
    intro v hv s t hs0 ht0 hs ht h1 h2
    apply xOf_ne_of_hom hwu hu (MvPowerSeries.substAlgHom $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv) s t hs0 ht0 hs ht
      (by rw [MvPowerSeries.coe_substAlgHom]; exact h1)
    rwa [MvPowerSeries.coe_substAlgHom]
  have g01 := subst_X_X_ne_zero F hF1 0 1 ![MvPowerSeries.X 0, MvPowerSeries.X 1, 0]
      (fun k => by fin_cases k <;> simp) rfl rfl
  have g12 := subst_X_X_ne_zero F hF1 1 2 ![0, MvPowerSeries.X 0, MvPowerSeries.X 1]
      (fun k => by fin_cases k <;> simp) rfl rfl
  have c01 := cSub _ _ (cX 0) $ cX 1
  have c12 := cSub _ _ (cX 1) $ cX 2
  have hv1 : ∀ i, MvPowerSeries.constantCoeff
      ((![0, MvPowerSeries.X 1, MvPowerSeries.X 2] : Fin 3 → MvPowerSeries (Fin 3) K) i) = 0 :=
    fun i => by fin_cases i <;> simp
  have hv2 : ∀ i, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 3) K) i) = 0 :=
    fun i => by fin_cases i <;> simp
  have hv3 : ∀ i, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0, 0, MvPowerSeries.X 2] : Fin 3 → MvPowerSeries (Fin 3) K) i) = 0 :=
    fun i => by fin_cases i <;> simp
  have ne1 : xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠ xOf w (MvPowerSeries.X 1) := by
    refine ne_of _ hv1 _ _ (cX 0) (cX 1) (nX 0) (nX 1) ?_ ?_
    rw [MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv1]
    rfl
    rw [MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv1]
    exact nX 1
  have ne2 : xOf w (F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]) ≠
      xOf w (MvPowerSeries.X 2) := by
    refine Ne.symm $ ne_of _ hv2 _ _ (cX 2) c01 (nX 2) g01 ?_ ?_
    rw [MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv2]
    rfl
    rw [subst_subst_pair' F _ _ (cX 0) (cX 1) _ $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv2,
      MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv2,
      MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv2]
    exact g01
  have ne3 : xOf w (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ≠ xOf w (MvPowerSeries.X 2) := by
    refine ne_of _ hv3 _ _ (cX 1) (cX 2) (nX 1) (nX 2) ?_ ?_
    rw [MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv3]
    rfl
    rw [MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv3]
    exact nX 2
  have ne4 : xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠
      xOf w (F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]) := by
    refine ne_of _ hv1 _ _ (cX 0) c12 (nX 0) g12 ?_ ?_
    rw [MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv1]
    rfl
    rw [subst_subst_pair' F _ _ (cX 1) (cX 2) _ $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv1,
      MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv1,
      MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero hv1]
    exact g12
  have p0 := hP K W w hw (Fin 3) _ (cX 0) $ nX 0
  have p1 := hP K W w hw (Fin 3) _ (cX 1) $ nX 1
  have p2 := hP K W w hw (Fin 3) _ (cX 2) $ nX 2
  have p01 := hP K W w hw (Fin 3) _ c01 g01
  have p12 := hP K W w hw (Fin 3) _ c12 g12
  obtain ⟨h01, e1⟩ := chord_add _ _ _ p0 p1 ne1 $ hS K W w hw F hF0 hch (Fin 3) _ _ (cX 0) (cX 1) (nX 0) (nX 1) ne1
  obtain ⟨hL, e2⟩ := chord_add _ _ _ p01 p2 ne2 $ hS K W w hw F hF0 hch (Fin 3) _ _ c01 (cX 2) g01 (nX 2) ne2
  obtain ⟨h12, e3⟩ := chord_add _ _ _ p1 p2 ne3 $ hS K W w hw F hF0 hch (Fin 3) _ _ (cX 1) (cX 2) (nX 1) (nX 2) ne3
  obtain ⟨hR, e4⟩ := chord_add _ _ _ p0 p12 ne4 $ hS K W w hw F hF0 hch (Fin 3) _ _ (cX 0) c12 (nX 0) g12 ne4
  have key := e2.symm.trans (((congrArg (· + _) e1).symm.trans
    ((add_assoc _ _ _).trans (congrArg (_ + ·) e3))).trans e4)
  simp [WeierstrassCurve.Affine.Point.some.injEq] at key
  exact eq_of_xy hwu hu _ _ (cSub _ _ c01 $ cX 2) (cSub _ _ (cX 0) c12) key.1 key.2

end WeierstrassCoordinateSubstitution


end Formalism.ELL
end
section
open PowerSeries



namespace Formalism.ELL
namespace WeierstrassChordSeries

section Alg
variable {R : Type*} [CommRing R]

def G (a1 a2 a3 a4 a6 z v : R) : R :=
  z ^ 3 + a1 * (z * v) + a2 * (z ^ 2 * v) + a3 * v ^ 2 + a4 * (z * v ^ 2) + a6 * v ^ 3 - v

def c3 (a2 a4 a6 l : R) : R := 1 + a2 * l + a4 * l ^ 2 + a6 * l ^ 3
def c2 (a1 a2 a3 a4 a6 l n : R) : R :=
  a1 * l + a2 * n + a3 * l ^ 2 + 2 * a4 * l * n + 3 * a6 * l ^ 2 * n
def c1 (a1 a3 a4 a6 l n : R) : R :=
  a1 * n + 2 * a3 * l * n + a4 * n ^ 2 + 3 * a6 * l * n ^ 2 - l
def c0 (a3 a6 n : R) : R := a3 * n ^ 2 + a6 * n ^ 3 - n

lemma G_line (a1 a2 a3 a4 a6 l n z : R) :
    G a1 a2 a3 a4 a6 z (l * z + n) = c3 a2 a4 a6 l * z ^ 3 + c2 a1 a2 a3 a4 a6 l n * z ^ 2
      + c1 a1 a3 a4 a6 l n * z + c0 a3 a6 n := by
  unfold G c3 c2 c1 c0
  ring

lemma vieta [IsDomain R] {a1 a2 a3 a4 a6 l n z1 z2 z3 : R} (hz : z1 ≠ z2)
    (h1 : G a1 a2 a3 a4 a6 z1 (l * z1 + n) = 0) (h2 : G a1 a2 a3 a4 a6 z2 (l * z2 + n) = 0)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0) :
    G a1 a2 a3 a4 a6 z3 (l * z3 + n) = 0 ∧
      c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0 ∧
      c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0 := by
  have k1 := h1
  have k2 := h2
  rw [G_line] at k1 k2
  have k : (z1 - z2) * (c3 a2 a4 a6 l * (z1 ^ 2 + z1 * z2 + z2 ^ 2)
      + c2 a1 a2 a3 a4 a6 l n * (z1 + z2) + c1 a1 a3 a4 a6 l n) = 0 := by
    linear_combination k1 - k2
  have e2 : c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0 := by
    linear_combination (z1 + z2) * he1 - (mul_eq_zero.mp k).resolve_left (sub_ne_zero.mpr hz)
  have e3 : c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0 := by
    linear_combination k1 - z1 ^ 2 * he1 + z1 * e2
  refine ⟨?_, e2, e3⟩
  rw [G_line]
  linear_combination z3 ^ 2 * he1 - z3 * e2 + e3

lemma G_inv [IsDomain R] {a1 a2 a3 a4 a6 z v f u d : R} (hf : f * d = z) (hu : u * d = v)
    (hd : d = -1 + a1 * z + a3 * v) (hd0 : d ≠ 0) (hG : G a1 a2 a3 a4 a6 z v = 0) :
    G a1 a2 a3 a4 a6 f u = 0 := by
  subst hf hu
  exact (mul_eq_zero.mp $ by
      unfold G at hG ⊢
      linear_combination hG - u * d * (d - 1) * hd).resolve_left $ pow_ne_zero 3 hd0

lemma G_zero (a1 a2 a3 a4 a6 z : R) : G a1 a2 a3 a4 a6 z 0 = z ^ 3 := by
  unfold G
  ring

section maps
variable {R' : Type*} [CommRing R'] (φ : R →+* R')
lemma map_lineCoeffCubic (a2 a4 a6 l : R) : φ (c3 a2 a4 a6 l) = c3 (φ a2) (φ a4) (φ a6) (φ l) := by
  simp [c3]
lemma map_lineCoeffQuadratic (a1 a2 a3 a4 a6 l n : R) :
    φ (c2 a1 a2 a3 a4 a6 l n) = c2 (φ a1) (φ a2) (φ a3) (φ a4) (φ a6) (φ l) (φ n) := by
  simp [c2, map_ofNat φ 2, map_ofNat φ 3]
lemma map_lineCoeffLinear (a1 a3 a4 a6 l n : R) :
    φ (c1 a1 a3 a4 a6 l n) = c1 (φ a1) (φ a3) (φ a4) (φ a6) (φ l) (φ n) := by
  simp [c1, map_ofNat φ 2, map_ofNat φ 3]
lemma map_lineCoeffConst (a3 a6 n : R) : φ (c0 a3 a6 n) = c0 (φ a3) (φ a6) (φ n) := by
  simp [c0]
end maps

section mem
variable (T : Subring R)
lemma two_mem : (2 : R) ∈ T := by
  rw [← one_add_one_eq_two]
  exact T.add_mem T.one_mem T.one_mem
lemma three_mem : (3 : R) ∈ T := by
  rw [show (3 : R) = 2 + 1 by norm_num]
  exact T.add_mem (two_mem T) T.one_mem
lemma lineCoeffCubic_mem {a2 a4 a6 l : R} (h2 : a2 ∈ T) (h4 : a4 ∈ T) (h6 : a6 ∈ T) (hl : l ∈ T) :
    c3 a2 a4 a6 l ∈ T := by
  unfold c3
  exact T.add_mem (T.add_mem (T.add_mem T.one_mem $ T.mul_mem h2 hl) $ T.mul_mem h4 $ T.pow_mem hl 2)
    $ T.mul_mem h6 $ T.pow_mem hl 3
lemma lineCoeffQuadratic_mem {a1 a2 a3 a4 a6 l n : R} (h1 : a1 ∈ T) (h2 : a2 ∈ T) (h3 : a3 ∈ T) (h4 : a4 ∈ T)
    (h6 : a6 ∈ T) (hl : l ∈ T) (hn : n ∈ T) : c2 a1 a2 a3 a4 a6 l n ∈ T := by
  unfold c2
  exact T.add_mem (T.add_mem (T.add_mem (T.add_mem (T.mul_mem h1 hl) $ T.mul_mem h2 hn)
    $ T.mul_mem h3 $ T.pow_mem hl 2) $ T.mul_mem (T.mul_mem (T.mul_mem (two_mem T) h4) hl) hn)
    $ T.mul_mem (T.mul_mem (T.mul_mem (three_mem T) h6) $ T.pow_mem hl 2) hn
end mem

end Alg

section Fld
variable {F : Type*} [Field F]

lemma chord_field (a1 a2 a3 a4 a6 z1 z2 z3 v1 v2 v3 l n f u D : F)
    (hv1 : v1 = l * z1 + n) (hv2 : v2 = l * z2 + n) (hv3 : v3 = l * z3 + n)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0)
    (he2 : c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0)
    (he3 : c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0)
    (hc3 : c3 a2 a4 a6 l ≠ 0) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0) (hn : n ≠ 0)
    (hz : z1 ≠ z2) (hD : D = -1 + a1 * z3 + a3 * v3) (hD0 : D ≠ 0) (hf : f * D = z3)
    (hu : u * D = v3) :
    f / u = ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2 ∧
    -1 / u = -((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2) *
        ((((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2) - z1 / v1)
        + -1 / v1) - a1 * (((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2) - a3 := by
  simp [c3, c2, c1, c0] at he1 he2 he3 hc3
  have hu' := (eq_div_iff hD0).mpr hu
  have hxd : z1 / v1 - z2 / v2 = n * (z1 - z2) / (v1 * v2) := by
    rw [div_sub_div _ _ h1 h2]
    congr 1
    rw [hv1, hv2]
    ring
  have hyd : -1 / v1 - -1 / v2 = l * (z1 - z2) / (v1 * v2) := by
    rw [div_sub_div _ _ h1 h2]
    congr 1
    rw [hv1, hv2]
    ring
  have hl : (-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2) = l / n := by
    rw [hxd, hyd]
    first
      | rw [div_div_div_cancel_right₀ $ mul_ne_zero h1 h2, mul_div_mul_right _ _ $ sub_ne_zero.mpr hz]
      | (field_simp; done)
      | (field_simp
         ring)
  have hG' : n ^ 2 * (z3 * v1 * v2 + z1 * v2 * v3 + z2 * v1 * v3) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * (v1 * v2 * v3) = 0 := by
    rw [hv1, hv2, hv3]
    exact by
        have hc : (1 + a2 * l + a4 * l ^ 2 + a6 * l ^ 3) * (n ^ 2 * (z3 * (l * z1 + n) * (l * z2 + n) + z1 * (l * z2 + n) * (l * z3 + n) + z2 * (l * z1 + n) * (l * z3 + n)) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * ((l * z1 + n) * (l * z2 + n) * (l * z3 + n))) = 0 := by
          linear_combination (n ^ 2 * (n ^ 2 - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * l)) * he1 + (l * n * (2 * n ^ 2 - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * l)) * he2 + (l ^ 2 * (3 * n ^ 2 - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * l)) * he3
        exact (mul_eq_zero.mp hc).resolve_left hc3
  have hsum : z3 / v3 = (l / n) ^ 2 + a1 * (l / n) - a2 - z1 / v1 - z2 / v2 := by
    rw [← sub_eq_zero]
    have e : z3 / v3 - ((l / n) ^ 2 + a1 * (l / n) - a2 - z1 / v1 - z2 / v2)
        = (n ^ 2 * (z3 * v1 * v2 + z1 * v2 * v3 + z2 * v1 * v3) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * (v1 * v2 * v3)) / (n ^ 2 * (v1 * v2 * v3)) := by
      field_simp
      ring
    rw [e, hG', zero_div]
  have hx3 : f / u = z3 / v3 := by
    rw [(eq_div_iff hD0).mpr hf, hu']
    first
      | exact div_div_div_cancel_right₀ hD0 _ _
      | (field_simp; done)
      | (field_simp
         ring)
  constructor
  rw [hl, hx3]
  exact hsum
  rw [hl, ← hsum, hu']
  field_simp
  subst hD hv1 hv2 hv3
  ring

end Fld

section Wser
variable {K : Type u} [Field K] (W : WeierstrassCurve K)

def fw (v : PowerSeries K) : PowerSeries K :=
  X ^ 3 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * X * v ^ 2
    + C W.a₆ * v ^ 3

lemma fw_cong {n : ℕ} {v v' : PowerSeries K} (h : X ^ n ∣ v - v') (hv : X ∣ v) (hv' : X ∣ v') :
    X ^ (n + 1) ∣ fw W v - fw W v' := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, rfl⟩ := hv
  obtain ⟨b', rfl⟩ := hv'
  use C W.a₁ * a + C W.a₂ * X * a + C W.a₃ * a * (b + b') + C W.a₄ * X * a * (b + b')
    + C W.a₆ * X * a * (b ^ 2 + b * b' + b' ^ 2)
  unfold fw
  linear_combination (X * (C W.a₁ + C W.a₂ * X + C W.a₃ * (b + b') + C W.a₄ * X * (b + b')
    + C W.a₆ * X * (b ^ 2 + b * b' + b' ^ 2))) * ha

lemma fw_X_dvd {v : PowerSeries K} (hv : X ∣ v) : X ∣ fw W v := by
  obtain ⟨b, rfl⟩ := hv
  use X ^ 2 + C W.a₁ * X * b + C W.a₂ * X ^ 2 * b + C W.a₃ * X * b ^ 2 + C W.a₄ * X ^ 2 * b ^ 2
    + C W.a₆ * X ^ 2 * b ^ 3
  unfold fw
  ring
def it : ℕ → PowerSeries K
  | 0 => 0
  | k + 1 => fw W $ it k

variable {W}

lemma it_spec {w : PowerSeries K} (hw : WFixed W w) :
    ∀ k, X ^ k ∣ w - it W k ∧ X ∣ it W k := by
  have hfix : fw W w = w := hw.2.symm
  intro k
  induction k with
  | zero => exact ⟨by simp, by simp [it]⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    have e : w - it W (k + 1) = fw W w - fw W (it W k) := by
      rw [hfix]
      rfl
    rw [e]
    exact fw_cong W h1 (PowerSeries.X_dvd_iff.mpr hw.1) h2
    exact fw_X_dvd W h2

lemma it_mem (S : Subalgebra ℤ K) (hS : ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K) ⊆ S) :
    ∀ k, it W k ∈ (PowerSeries.map $ algebraMap S K).range := by
  have hX : (X : PowerSeries K) ∈ (PowerSeries.map $ algebraMap S K).range :=
    RingHom.mem_range.mpr ⟨X, PowerSeries.map_X _⟩
  have hC : ∀ a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K),
      (C a : PowerSeries K) ∈ (PowerSeries.map $ algebraMap S K).range := fun a ha =>
    RingHom.mem_range.mpr ⟨C ⟨a, hS ha⟩, by rw [PowerSeries.map_C]; rfl⟩
  intro k
  induction k with
  | zero => exact zero_mem _
  | succ k ih =>
    show fw W (it W k) ∈ _
    unfold fw
    exact add_mem (add_mem (add_mem (add_mem (add_mem (pow_mem hX 3) $ mul_mem (mul_mem (hC W.a₁ $ by simp) hX) ih)
      $ mul_mem (mul_mem (hC W.a₂ $ by simp) $ pow_mem hX 2) ih) $ mul_mem (hC W.a₃ $ by simp) $ pow_mem ih 2)
      $ mul_mem (mul_mem (hC W.a₄ $ by simp) hX) $ pow_mem ih 2) $ mul_mem (hC W.a₆ $ by simp) $ pow_mem ih 3

lemma w_coeff_mem {w : PowerSeries K} (hw : WFixed W w) (m : ℕ) :
    coeff m w ∈ Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K) := by
  have h := (it_spec hw $ m + 1).1
  rw [PowerSeries.X_pow_dvd_iff] at h
  have hm := h m $ Nat.lt_succ_self m
  rw [map_sub, sub_eq_zero] at hm
  rw [hm]
  obtain ⟨p, hp⟩ := RingHom.mem_range.mp $ it_mem
    (Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) Algebra.subset_adjoin $ m + 1
  rw [← hp, PowerSeries.coeff_map]
  exact (coeff m p).2

lemma w_low {w : PowerSeries K} (hw : WFixed W w) :
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1 := by
  have hfix : fw W w = w := hw.2.symm
  have hXw : X ∣ w := PowerSeries.X_dvd_iff.mpr hw.1
  have h0 : fw W 0 = X ^ 3 := by simp [fw]
  have step : ∀ n, X ^ n ∣ w → X ^ (n + 1) ∣ w - X ^ 3 := fun n hn => by
    have := fw_cong W (n := n) (v := w) (v' := 0) (by simpa using hn) hXw $ dvd_zero _
    rwa [hfix, h0] at this
  have lift : ∀ n ≤ 3, X ^ n ∣ w - X ^ 3 → X ^ n ∣ w := fun n hn h => by
    have := dvd_add h $ pow_dvd_pow (X : PowerSeries K) hn
    simpa using this
  have h4 := step 3 $ lift 3 le_rfl $ step 2 $ lift 2 (by norm_num) $ step 1 $ by simpa using hXw
  rw [PowerSeries.X_pow_dvd_iff] at h4
  have c : ∀ i < 4, coeff i w = if i = 3 then 1 else 0 := fun i hi => by
    have := h4 i hi
    rwa [map_sub, PowerSeries.coeff_X_pow, sub_eq_zero] at this
  exact ⟨by simpa using c 0 $ by norm_num, by simpa using c 1 $ by norm_num,
    by simpa using c 2 $ by norm_num, by simpa using c 3 $ by norm_num⟩

end Wser

section Mser
variable {K : Type u} [Field K]

lemma eq_single_iff (e : Fin 2 →₀ ℕ) :
    (e = Finsupp.single 1 (e 1) ↔ e 0 = 0) ∧ (e = Finsupp.single 0 (e 0) ↔ e 1 = 0) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  rw [h]
  simp
  ext j
  fin_cases j <;> simp [h]
  rw [h]
  simp
  ext j
  fin_cases j <;> simp [h]

def lam (w : PowerSeries K) : MvPowerSeries (Fin 2) K := fun e => coeff (e 0 + e 1 + 1) w

lemma coeff_lam (w : PowerSeries K) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (lam w) = coeff (e 0 + e 1 + 1) w := rfl

def Wi (w : PowerSeries K) (i : Fin 2) : MvPowerSeries (Fin 2) K := w.subst (MvPowerSeries.X i)

lemma coeff_Wi (w : PowerSeries K) (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (Wi w i) = if e = Finsupp.single i (e i) then coeff (e i) w else 0 := by
  have ha : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := by
    first
      | exact PowerSeries.HasSubst.of_constantCoeff_zero $ by simp
      | exact PowerSeries.HasSubst.X i
      | exact PowerSeries.HasSubst.X'
  rw [Wi, PowerSeries.coeff_subst ha]
  first
    | simp only [MvPowerSeries.coeff_X_pow]
    | simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial]
  split_ifs with h
  rw [finsum_eq_single _ $ e i]
  rw [if_pos h, smul_eq_mul, mul_one]
  intro d hd
  rw [if_neg, smul_zero]
  intro h'
  apply hd
  rw [h']
  simp
  have hz : ∀ d, (coeff d w • if e = Finsupp.single i d then (1 : K) else 0) = 0 := by
    intro d
    rw [if_neg, smul_zero]
    intro h'
    apply h
    rw [h']
    simp
  simp only [hz, finsum_zero]

private theorem coeff_mul_X_fin_two (φ : MvPowerSeries (Fin 2) K) (j : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (φ * MvPowerSeries.X j) =
      if Finsupp.single j 1 ≤ e then MvPowerSeries.coeff (e - Finsupp.single j 1) φ else 0 := by
  rw [show (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.monomial (Finsupp.single j 1) 1 from rfl, MvPowerSeries.coeff_mul_monomial]
  try simp [mul_one]

private theorem single_one_le_iff_ne_zero (j : Fin 2) (e : Fin 2 →₀ ℕ) : Finsupp.single j 1 ≤ e ↔ e j ≠ 0 := by
  first
    | (rw [Finsupp.single_le_iff]
       exact Nat.one_le_iff_ne_zero)
    | (rw [Finsupp.le_def]
       constructor
       intro h
       simp at this
       omega
       intro h k
       by_cases hk : j = k
       subst hk
       simp
       omega
       simp [Finsupp.single_apply, hk])

lemma lam_mul (w : PowerSeries K) :
    (MvPowerSeries.X 1 - MvPowerSeries.X 0) * lam w = Wi w 1 - Wi w 0 := by
  have key : ∀ a b, a = b → coeff a w = coeff b w := fun a b h => h ▸ rfl
  ext e
  rw [sub_mul, map_sub, map_sub, mul_comm $ MvPowerSeries.X 1, mul_comm $ MvPowerSeries.X 0, coeff_mul_X_fin_two,
    coeff_mul_X_fin_two, coeff_Wi, coeff_Wi, coeff_lam, coeff_lam]
  simp only [(eq_single_iff e).1, (eq_single_iff e).2, single_one_le_iff_ne_zero]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0 <;>
    simp [h0, h1] <;>
    first
      | (apply key; omega)
      | (rw [sub_eq_zero]; apply key; omega)
      | (rw [neg_inj]; apply key; omega)
      | (apply Eq.symm; apply key; omega)

local notation "L" i => MvPowerSeries.coeff $ Finsupp.single i 1
local notation "cc" => MvPowerSeries.constantCoeff

lemma L_mul (φ ψ : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    (L i) (φ * ψ) = cc φ * (L i) ψ + (L i) φ * cc ψ := by
  first
    | (rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
       simp [Finset.Nat.sum_antidiagonal_succ, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
       try ring
       done)
    | (rw [MvPowerSeries.coeff_mul, Finset.sum_eq_add (0, Finsupp.single i 1) (Finsupp.single i 1, 0)]
       simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
       try ring
       simp
       rintro ⟨a, b⟩ hab hne
       rw [Finset.mem_antidiagonal] at hab
       exfalso
       by_cases ha : a i = 0
       apply hne.1
       have a0 : a = 0 := by
         ext j
         by_cases hij : i = j
         subst hij
         simp [ha]
         simp [Finsupp.single_apply, hij] at this
         simp
         omega
       subst a0
       simp at hab
       rw [hab]
       apply hne.2
       have b0 : b = 0 := by
         ext j
         by_cases hij : i = j
         subst hij
         simp at this
         simp
         omega
         simp [Finsupp.single_apply, hij] at this
         simp
         omega
       subst b0
       simp at hab
       rw [hab]
       intro h
       exfalso
       apply h
       simp [Finset.mem_antidiagonal]
       intro h
       exfalso
       apply h
       simp [Finset.mem_antidiagonal]
       done)

lemma L_C (a : K) (i : Fin 2) : (L i) (MvPowerSeries.C a : MvPowerSeries (Fin 2) K) = 0 := by
  simp [MvPowerSeries.coeff_C]

lemma L_X (i j : Fin 2) : (L i) (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = if i = j then 1 else 0 := by
  rw [MvPowerSeries.coeff_X]
  by_cases h : i = j
  subst h
  simp
  have h' : Finsupp.single i 1 ≠ Finsupp.single j 1 := fun e => h $ Finsupp.single_left_injective one_ne_zero e
  rw [if_neg h', if_neg h]

lemma mul_vanishing_order_two {φ : MvPowerSeries (Fin 2) K} (h0 : cc φ = 0) (h1 : ∀ i, (L i) φ = 0)
    (ψ : MvPowerSeries (Fin 2) K) : cc (φ * ψ) = 0 ∧ ∀ i, (L i) (φ * ψ) = 0 := by
  constructor
  rw [map_mul, h0, zero_mul]
  exact fun i => by rw [L_mul, h0, h1 i]
                    ring
variable (W : WeierstrassCurve K) (w : PowerSeries K)

def nu : MvPowerSeries (Fin 2) K := Wi w 0 - lam w * MvPowerSeries.X 0

abbrev ca (a : K) : MvPowerSeries (Fin 2) K := MvPowerSeries.C a

def C3 : MvPowerSeries (Fin 2) K := c3 (ca W.a₂) (ca W.a₄) (ca W.a₆) $ lam w
def C2 : MvPowerSeries (Fin 2) K :=
  c2 (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) (lam w) $ nu w

def z3 : MvPowerSeries (Fin 2) K :=
  -MvPowerSeries.X 0 - MvPowerSeries.X 1 - C2 W w * (C3 W w)⁻¹
def w3 : MvPowerSeries (Fin 2) K := lam w * z3 W w + nu w
def dd : MvPowerSeries (Fin 2) K := -1 + ca W.a₁ * z3 W w + ca W.a₃ * w3 W w

def F2 : MvPowerSeries (Fin 2) K := z3 W w * (dd W w)⁻¹
def wF : MvPowerSeries (Fin 2) K := w3 W w * (dd W w)⁻¹

variable {W w}

lemma Wi_cc (hw : WFixed W w) (i : Fin 2) : cc (Wi w i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Wi]
  simp [(w_low hw).1]

lemma Wi_L (hw : WFixed W w) (i j : Fin 2) : (L j) (Wi w i) = 0 := by
  rw [coeff_Wi]
  by_cases h : j = i
  subst h
  simp [(w_low hw).2.1]
  simp [h]

lemma lam_cc (hw : WFixed W w) : cc (lam w) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lam]
  simp [(w_low hw).2.1]

lemma lam_L (hw : WFixed W w) (i : Fin 2) : (L i) (lam w) = 0 := by
  have h : (Finsupp.single i 1) 0 + (Finsupp.single i 1) 1 = 1 := by
    fin_cases i <;> simp
  rw [coeff_lam, h]
  exact (w_low hw).2.2.1

lemma nu_cc (hw : WFixed W w) : cc (nu w) = 0 := by
  simp [nu, Wi_cc hw, lam_cc hw]

lemma nu_L (hw : WFixed W w) (i : Fin 2) : (L i) (nu w) = 0 := by
  rw [nu, map_sub, L_mul, Wi_L hw, lam_cc hw, lam_L hw]
  simp

lemma nu_ne (hw : WFixed W w) : nu w ≠ 0 := by
  intro h
  have := congrArg (MvPowerSeries.coeff $ Finsupp.single 0 2 + Finsupp.single 1 1) h
  rw [nu, map_sub, coeff_mul_X_fin_two, coeff_Wi, coeff_lam] at this
  first
    | simp [(eq_single_iff _).2, single_one_le_iff_ne_zero] at this
    | skip
  simp [(w_low hw).2.2.2] at this

lemma constantCoeff_chordCoeffCubic (hw : WFixed W w) : cc (C3 W w) = 1 := by
  simp [C3, c3, lam_cc hw]

lemma constantCoeff_chordCoeffQuadratic (hw : WFixed W w) : cc (C2 W w) = 0 := by
  simp [C2, c2, lam_cc hw, nu_cc hw]

private theorem cc_L_mul_eq_zero_of_vanishing {φ : MvPowerSeries (Fin 2) K} (h0 : cc φ = 0) (h1 : ∀ i, (L i) φ = 0)
    (ψ : MvPowerSeries (Fin 2) K) : cc (ψ * φ) = 0 ∧ ∀ i, (L i) (ψ * φ) = 0 := by
  rw [mul_comm]
  exact mul_vanishing_order_two h0 h1 ψ

lemma linearCoeff_chordCoeffQuadratic (hw : WFixed W w) (i : Fin 2) : (L i) (C2 W w) = 0 := by
  have hs0 := lam_cc hw
  have hs1 := lam_L hw
  have hss := mul_vanishing_order_two hs0 hs1 $ lam w
  rw [C2, c2, pow_two]
  simp [map_add, (cc_L_mul_eq_zero_of_vanishing hs0 hs1 _).2 i, (cc_L_mul_eq_zero_of_vanishing (nu_cc hw) (nu_L hw) _).2 i,
    (cc_L_mul_eq_zero_of_vanishing hss.1 hss.2 _).2 i, add_zero]

lemma constantCoeff_thirdParam (hw : WFixed W w) : cc (z3 W w) = 0 := by
  simp [z3, constantCoeff_chordCoeffQuadratic hw]

lemma linearCoeff_thirdParam (hw : WFixed W w) (i : Fin 2) : (L i) (z3 W w) = -1 := by
  rw [z3, map_sub, map_sub, map_neg, L_mul, constantCoeff_chordCoeffQuadratic hw,
    linearCoeff_chordCoeffQuadratic hw, L_X, L_X]
  fin_cases i <;> simp

lemma constantCoeff_thirdValue (hw : WFixed W w) : cc (w3 W w) = 0 := by
  simp [w3, constantCoeff_thirdParam hw, nu_cc hw]

lemma dd_cc (hw : WFixed W w) : cc (dd W w) = -1 := by
  simp [dd, constantCoeff_thirdParam hw, constantCoeff_thirdValue hw]

lemma constantCoeff_formalSum (hw : WFixed W w) : cc (F2 W w) = 0 := by
  simp [F2, constantCoeff_thirdParam hw]

lemma linearCoeff_formalSum (hw : WFixed W w) (i : Fin 2) : (L i) (F2 W w) = 1 := by
  rw [F2, L_mul, constantCoeff_thirdParam hw, linearCoeff_thirdParam hw,
    MvPowerSeries.constantCoeff_inv, dd_cc hw]
  norm_num

lemma wF_cc (hw : WFixed W w) : cc (wF W w) = 0 := by
  simp [wF, constantCoeff_thirdValue hw]

abbrev Sadj (W : WeierstrassCurve K) : Subalgebra ℤ K :=
  Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)

def T (W : WeierstrassCurve K) : Subring $ MvPowerSeries (Fin 2) K :=
  (MvPowerSeries.map $ algebraMap (Sadj W) K).range

lemma mem_T {φ : MvPowerSeries (Fin 2) K} : φ ∈ T W ↔ ∀ e, MvPowerSeries.coeff e φ ∈ Sadj W := by
  constructor
  intro hφ e
  obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hφ
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff e p).2
  intro h
  refine RingHom.mem_range.mpr ⟨fun e => ⟨MvPowerSeries.coeff e φ, h e⟩, ?_⟩
  ext e
  first
    | rfl
    | simp [MvPowerSeries.coeff_map]

lemma inv_mem_integralSeries {φ : MvPowerSeries (Fin 2) K} (h : φ ∈ T W) (h0 : cc φ ≠ 0)
    (hi : (cc φ)⁻¹ ∈ Sadj W) : φ⁻¹ ∈ T W := by
  classical
  rw [mem_T] at h ⊢
  have step : ∀ n, (∀ m, m < n → MvPowerSeries.coeff m φ⁻¹ ∈ Sadj W) →
      MvPowerSeries.coeff n φ⁻¹ ∈ Sadj W := by
    intro n ih
    rw [MvPowerSeries.coeff_inv]
    split_ifs with hn
    exact hi
    refine mul_mem (neg_mem hi) $ sum_mem fun x _ => ?_
    split_ifs with hx
    exact mul_mem (h _) $ ih _ hx
    exact zero_mem _
  intro n
  first
    | exact (wellFounded_lt (α := Fin 2 →₀ ℕ)).induction n step
    | exact WellFoundedLT.induction n step
    | exact (wellFounded_lt (α := Fin 2 →₀ ℕ)).induction (C := fun n => MvPowerSeries.coeff n φ⁻¹ ∈ Sadj W) n step

lemma X_mem_T (i : Fin 2) : (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ∈ T W := by
  rw [mem_T]
  intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  exact one_mem _
  exact zero_mem _

lemma constSeries_mem_integralSeries {a : K} (ha : a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) : ca a ∈ T W := by
  rw [mem_T]
  intro e
  first
    | rw [MvPowerSeries.coeff_C]
    | rw [ca, MvPowerSeries.coeff_C]
  split_ifs
  exact Algebra.subset_adjoin ha
  exact zero_mem _

lemma slope_mem_integralSeries (hw : WFixed W w) : lam w ∈ T W := by
  rw [mem_T]
  intro e
  rw [coeff_lam]
  exact w_coeff_mem hw _

lemma wVar_mem_integralSeries (hw : WFixed W w) (i : Fin 2) : Wi w i ∈ T W := by
  rw [mem_T]
  intro e
  rw [coeff_Wi]
  split_ifs
  exact w_coeff_mem hw _
  exact zero_mem _

lemma intercept_mem_integralSeries (hw : WFixed W w) : nu w ∈ T W := by
  exact sub_mem (wVar_mem_integralSeries hw 0) $ mul_mem (slope_mem_integralSeries hw) $ X_mem_T 0

lemma formalSum_mem_integralSeries (hw : WFixed W w) : F2 W w ∈ T W := by
  have h1 : ca W.a₁ ∈ T W := constSeries_mem_integralSeries $ by simp
  have h2 : ca W.a₂ ∈ T W := constSeries_mem_integralSeries $ by simp
  have h3 : ca W.a₃ ∈ T W := constSeries_mem_integralSeries $ by simp
  have h4 : ca W.a₄ ∈ T W := constSeries_mem_integralSeries $ by simp
  have h6 : ca W.a₆ ∈ T W := constSeries_mem_integralSeries $ by simp
  have hl := slope_mem_integralSeries hw
  have hn := intercept_mem_integralSeries hw
  have hz3 : z3 W w ∈ T W :=
    (T W).sub_mem ((T W).sub_mem ((T W).neg_mem $ X_mem_T 0) $ X_mem_T 1) $ (T W).mul_mem (lineCoeffQuadratic_mem _ h1 h2 h3 h4 h6 hl hn) $ inv_mem_integralSeries (lineCoeffCubic_mem _ h2 h4 h6 hl) (by rw [constantCoeff_chordCoeffCubic hw]; exact one_ne_zero) (by rw [constantCoeff_chordCoeffCubic hw, inv_one]; exact Subalgebra.one_mem _)
  have hdd : dd W w ∈ T W :=
    (T W).add_mem ((T W).add_mem ((T W).neg_mem (T W).one_mem) $ (T W).mul_mem h1 hz3)
      $ (T W).mul_mem h3 $ (T W).add_mem ((T W).mul_mem hl hz3) hn
  exact (T W).mul_mem hz3 $ inv_mem_integralSeries hdd (by rw [dd_cc hw]; exact neg_ne_zero.mpr one_ne_zero) (by rw [dd_cc hw, inv_neg, inv_one]; exact Subalgebra.neg_mem _ $ Subalgebra.one_mem _)

lemma weq_iff (W : WeierstrassCurve K) (s v : MvPowerSeries (Fin 2) K) :
    WEqAt W s v ↔ G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) s v = 0 := by
  unfold Formalism.ELL.WEqAt G
  first
    | (simp [MvPowerSeries.smul_eq_C_mul]
       rw [sub_eq_zero, eq_comm])
    | (simp [Algebra.smul_def, MvPowerSeries.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
       rw [sub_eq_zero, eq_comm])

lemma X_ne : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ MvPowerSeries.X 1 := by
  intro h
  have := congrArg (MvPowerSeries.coeff $ Finsupp.single 0 1) h
  rw [MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl, if_neg] at this
  exact one_ne_zero this
  intro h'
  apply absurd $ Finsupp.single_left_injective one_ne_zero h'
  decide
lemma ne_zero_of_L {φ : MvPowerSeries (Fin 2) K} {i : Fin 2} (h : (L i) φ ≠ 0) : φ ≠ 0 := by
  rintro rfl
  exact h $ map_zero _

lemma v_ne_of_G (W : WeierstrassCurve K) {z v : MvPowerSeries (Fin 2) K} (hz : z ≠ 0)
    (hG : G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) z v = 0) : v ≠ 0 := by
  rintro rfl
  rw [G_zero] at hG
  first
    | exact hz $ pow_eq_zero_iff (by norm_num) |>.mp hG
    | exact hz $ pow_eq_zero hG

lemma chord (hU : WSubstUnique.{u}) (hw : WFixed W w) :
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) (F2 W w) := by
  haveI hdom : IsDomain (MvPowerSeries (Fin 2) K) := by
    first
      | infer_instance
      | exact NoZeroDivisors.to_isDomain _
  have hι : Function.Injective (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) := IsFractionRing.injective _ _
  have hCa : ∀ a, (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (MvPowerSeries.C a) = algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) a := fun a => by
    first
      | rfl
      | (rw [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))]; rfl)
      | simp [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))]
  have hE : ∀ s, MvPowerSeries.constantCoeff s = 0 →
      G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄)
        (ca W.a₆) s (w.subst s) = 0 :=
    fun s hs => (weq_iff W s _).mp (hU K W w hw (Fin 2) s hs).1
  have hG0 := hE (MvPowerSeries.X 0) (by simp)
  have hG1 := hE (MvPowerSeries.X 1) (by simp)
  have hv0 : lam w * MvPowerSeries.X 0 + nu w = Wi w 0 := by
    rw [nu]
    ring
  have hv1 : lam w * MvPowerSeries.X 1 + nu w = Wi w 1 := by
    rw [nu]
    linear_combination lam_mul w
  have hc0 : MvPowerSeries.constantCoeff (C3 W w) ≠ 0 := by
    rw [constantCoeff_chordCoeffCubic hw]
    exact one_ne_zero
  have he1 : C3 W w * (MvPowerSeries.X 0 + MvPowerSeries.X 1 + Formalism.ELL.WeierstrassChordSeries.z3 W w)
      + C2 W w = 0 := by
    rw [Formalism.ELL.WeierstrassChordSeries.z3]
    linear_combination (-C2 W w) * MvPowerSeries.mul_inv_cancel _ hc0
  obtain ⟨hG3, he2, he3⟩ := vieta (a1 := ca W.a₁) (a2 := ca W.a₂)
    (a3 := ca W.a₃) (a4 := ca W.a₄) (a6 := ca W.a₆) (l := lam w)
    (n := nu w) (z1 := MvPowerSeries.X 0) (z2 := MvPowerSeries.X 1) (z3 := Formalism.ELL.WeierstrassChordSeries.z3 W w)
    X_ne (by rw [hv0]; exact hG0) (by rw [hv1]; exact hG1) he1
  have hD0' : MvPowerSeries.constantCoeff (dd W w) ≠ 0 := by
    rw [dd_cc hw]
    norm_num
  have hD0 : dd W w ≠ 0 := fun h => hD0' (by rw [h, map_zero])
  have hfD : F2 W w * dd W w = Formalism.ELL.WeierstrassChordSeries.z3 W w := by
    rw [F2, mul_assoc, MvPowerSeries.inv_mul_cancel _ hD0', mul_one]
  have huD : wF W w * dd W w = w3 W w := by
    rw [wF, mul_assoc, MvPowerSeries.inv_mul_cancel _ hD0', mul_one]
  have hinv := G_inv (a1 := ca W.a₁) (a2 := ca W.a₂)
    (a3 := ca W.a₃) (a4 := ca W.a₄) (a6 := ca W.a₆)
    (z := Formalism.ELL.WeierstrassChordSeries.z3 W w) (v := w3 W w) (d := dd W w) hfD huD rfl hD0 hG3
  have hc : C3 W w ≠ 0 := fun h => hc0 (by rw [h, map_zero])
  have key := chord_field (F := FractionRing (MvPowerSeries (Fin 2) K)) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₁) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₂)
    (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₃) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₄) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₆)
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (MvPowerSeries.X 0)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (MvPowerSeries.X 1)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (Formalism.ELL.WeierstrassChordSeries.z3 W w))
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (Wi w 0)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (Wi w 1)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (w3 W w))
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (lam w)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (nu w)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (F2 W w)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (wF W w))
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (dd W w))
    (by rw [← hv0, map_add, map_mul]) (by rw [← hv1, map_add, map_mul]) (by rw [w3, map_add, map_mul])
    (by
      have := congrArg (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) he1
      simpa [C3, C2, map_lineCoeffCubic, map_lineCoeffQuadratic, hCa,
        ca] using this)
    (by
      have := congrArg (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) he2
      simpa [map_lineCoeffCubic, map_lineCoeffLinear, hCa, ca] using this)
    (by
      have := congrArg (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) he3
      simpa [map_lineCoeffCubic, map_lineCoeffConst, hCa, ca] using this)
    (by
      have := (map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hc
      simpa [C3, map_lineCoeffCubic, hCa, ca] using this)
    ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr (v_ne_of_G W (ne_zero_of_L (i := 0) (by rw [L_X]; simp)) hG0)) ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr (v_ne_of_G W (ne_zero_of_L (i := 1) (by rw [L_X]; simp)) hG1))
    ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr (v_ne_of_G W (ne_zero_of_L (i := 0) (by rw [linearCoeff_thirdParam hw]; norm_num)) hG3)) ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr (nu_ne hw))
    (hι.ne X_ne)
    (by
      rw [dd]
      simp [hCa, ca])
    ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hD0)
    (by rw [← map_mul, hfD]) (by rw [← map_mul, huD])
  obtain ⟨hx, hy⟩ := key
  unfold Formalism.ELL.ChordAt Formalism.ELL.xOf Formalism.ELL.yOf
  rw [← (hU K W w hw (Fin 2) (F2 W w) (constantCoeff_formalSum hw)).2 _ (wF_cc hw) ((weq_iff W _ _).mpr hinv)]
  first
    | exact ⟨hx, hy⟩
    | (refine ⟨?_, ?_⟩
       convert hx using 1
       convert hy using 1
       simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
         WeierstrassCurve.Affine.negAddY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
       rfl)

end Mser

end WeierstrassChordSeries

open WeierstrassChordSeries in
theorem wChordSeries_of (hU : WSubstUnique.{u}) : WChordSeries.{u} := by
  intro K _ W w hw
  exact ⟨Formalism.ELL.WeierstrassChordSeries.F2 W w, Formalism.ELL.WeierstrassChordSeries.mem_T.mp $ Formalism.ELL.WeierstrassChordSeries.formalSum_mem_integralSeries hw, Formalism.ELL.WeierstrassChordSeries.constantCoeff_formalSum hw,
    Formalism.ELL.WeierstrassChordSeries.linearCoeff_formalSum hw 0, Formalism.ELL.WeierstrassChordSeries.linearCoeff_formalSum hw 1, Formalism.ELL.WeierstrassChordSeries.chord hU hw⟩
end Formalism.ELL
end
section
open PowerSeries



namespace Formalism.ELL

namespace WeierstrassPointSeriesTail

def wTail {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R) : PowerSeries R :=
  C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2 + C W.a₆ * w ^ 3

theorem wTail_dvd {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (k : ℕ) (hk : 1 ≤ k) (h : (X : PowerSeries R) ^ k ∣ w) :
    (X : PowerSeries R) ^ (k + 1) ∣ wTail W w := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨u, rfl⟩ := h
  use C W.a₁ * u + C W.a₂ * X * u + C W.a₃ * X ^ j * u ^ 2 + C W.a₄ * X ^ (j + 1) * u ^ 2 +
    C W.a₆ * X ^ (2 * j + 1) * u ^ 3
  unfold wTail
  ring

theorem factor {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (hw : WFixed W w) : ∃ e, w = X ^ 3 * (1 + X * e) := by
  have hsplit : w = X ^ 3 + wTail W w := by
    unfold wTail
    conv_lhs => rw [hw.2]
    ring
  obtain ⟨e, he⟩ := wTail_dvd W w 3 (by norm_num) $ by
      rw [hsplit]
      exact dvd_add dvd_rfl $ wTail_dvd W w 2 (by norm_num) $ by
          rw [hsplit]
          exact dvd_add (pow_dvd_pow X $ by norm_num) $ wTail_dvd W w 1 le_rfl $ by
              rw [pow_one, PowerSeries.X_dvd_iff]
              exact hw.1
  use e
  rw [hsplit, he]
  ring
end WeierstrassPointSeriesTail

open WeierstrassPointSeriesTail in
theorem wSeriesNonsingularPoint_holds : WPoint := by
  intro K _ W w hw σ _ s hs0 hs
  have : IsDomain $ MvPowerSeries σ K := NoZeroDivisors.to_isDomain _
  have hsub := PowerSeries.HasSubst.of_constantCoeff_zero hs0
  have hE : w.subst s = s ^ 3 + MvPowerSeries.C W.a₁ * s * w.subst s +
      MvPowerSeries.C W.a₂ * s ^ 2 * w.subst s + MvPowerSeries.C W.a₃ * (w.subst s) ^ 2 +
      MvPowerSeries.C W.a₄ * s * (w.subst s) ^ 2 + MvPowerSeries.C W.a₆ * (w.subst s) ^ 3 := by
    conv_lhs => rw [hw.2]
    simp only [PowerSeries.subst_add hsub, PowerSeries.subst_mul hsub, PowerSeries.subst_pow hsub,
      PowerSeries.subst_X hsub, PowerSeries.subst_C]
  obtain ⟨e, he⟩ := factor W w hw
  have hfac : w.subst s = s ^ 3 * (1 + s * e.subst s) := by
    rw [← PowerSeries.coe_substAlgHom hsub, he]
    simp [PowerSeries.substAlgHom_X]
  have hwc : MvPowerSeries.constantCoeff (w.subst s) = 0 := by
    rw [hfac]
    simp [hs0]
  have hinj := IsFractionRing.injective (MvPowerSeries σ K) $ FractionRing $ MvPowerSeries σ K
  have hV : algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) (w.subst s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr $ by
        rw [hfac]
        refine mul_ne_zero (pow_ne_zero 3 hs) fun h0 => ?_
        have := congrArg MvPowerSeries.constantCoeff h0
        simp [hs0] at this
  have hC : ∀ a, algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K)
      (MvPowerSeries.C a) = algebraMap K (FractionRing $ MvPowerSeries σ K) a := fun a =>
    (IsScalarTower.algebraMap_apply K (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) a).symm
  have hE' := congrArg (algebraMap (MvPowerSeries σ K) $ FractionRing $ MvPowerSeries σ K) hE
  simp only [map_add, map_mul, map_pow, hC] at hE'
  have hx : xOf w s * algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) (w.subst s) =
      algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) s := by
    simp only [xOf]
    exact div_mul_cancel₀ _ hV
  have hy : yOf w s * algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) (w.subst s) =
      -1 := by
    simp only [yOf]
    rw [div_mul_cancel₀ _ hV]
  set Z := algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) s
  set V := algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) $ w.subst s
  set x := xOf w s
  set y := yOf w s
  set A₁ := algebraMap K (FractionRing $ MvPowerSeries σ K) W.a₁
  set A₂ := algebraMap K (FractionRing $ MvPowerSeries σ K) W.a₂
  set A₃ := algebraMap K (FractionRing $ MvPowerSeries σ K) W.a₃
  set A₄ := algebraMap K (FractionRing $ MvPowerSeries σ K) W.a₄
  set A₆ := algebraMap K (FractionRing $ MvPowerSeries σ K) W.a₆
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  constructor
  apply mul_left_cancel₀ $ pow_ne_zero 3 hV
  linear_combination hE' + (V * (y * V - 1) + A₁ * V * Z + A₃ * V ^ 2) * hy +
    (A₁ * V * (y * V) - ((x * V) ^ 2 + (x * V) * Z + Z ^ 2) - A₂ * V * (x * V + Z) - A₄ * V ^ 2) * hx
  by_contra hcon
  push Not at hcon
  obtain ⟨hP, hQ⟩ := hcon
  have hD0 : (1 - MvPowerSeries.C W.a₁ * s - 2 * MvPowerSeries.C W.a₃ * w.subst s -
      MvPowerSeries.C W.a₂ * s ^ 2 - 2 * MvPowerSeries.C W.a₄ * s * w.subst s -
      3 * MvPowerSeries.C W.a₆ * (w.subst s) ^ 2 : MvPowerSeries σ K) ≠ 0 := by
    intro h0
    have := congrArg MvPowerSeries.constantCoeff h0
    simp [hs0, hwc] at this
  apply hD0
  apply hinj
  rw [map_zero]
  apply (mul_eq_zero.mp _).resolve_right hV
  simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, hC]
  linear_combination V ^ 2 * hQ - Z * V ^ 2 * hP + 3 * hE' + (-2 * V + Z * A₁ * V) * hy +
    (-A₁ * V - 3 * Z * (x * V + Z) - 2 * A₂ * Z * V) * hx

end Formalism.ELL
end
section
open PowerSeries



namespace Formalism.ELL

namespace WeierstrassSeriesLimit

section Series

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

def T (v : PowerSeries R) : PowerSeries R :=
  X ^ 3 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * X * v ^ 2
      + C W.a₆ * v ^ 3

def E (a b : PowerSeries R) : PowerSeries R :=
  C W.a₁ * X + C W.a₂ * X ^ 2 + C W.a₃ * (a + b) + C W.a₄ * X * (a + b)
    + C W.a₆ * (a ^ 2 + a * b + b ^ 2)

theorem T_sub (a b : PowerSeries R) : T W a - T W b = (a - b) * E W a b := by
  simp [T, E]
  ring

theorem X_dvd_E {a b : PowerSeries R} (ha : X ∣ a) (hb : X ∣ b) : X ∣ E W a b := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  use C W.a₁ + C W.a₂ * X + C W.a₃ * (a' + b') + C W.a₄ * X * (a' + b')
    + C W.a₆ * X * (a' ^ 2 + a' * b' + b' ^ 2)
  simp [E]
  ring

theorem X_dvd_wMap {a : PowerSeries R} (ha : X ∣ a) : X ∣ T W a := by
  obtain ⟨a', rfl⟩ := ha
  use X ^ 2 + C W.a₁ * X * a' + C W.a₂ * X ^ 2 * a' + C W.a₃ * X * a' ^ 2
    + C W.a₄ * X ^ 2 * a' ^ 2 + C W.a₆ * X ^ 2 * a' ^ 3
  simp [T]
  ring

theorem contract {k : ℕ} {a b : PowerSeries R} (ha : X ∣ a) (hb : X ∣ b) (h : X ^ k ∣ a - b) :
    X ^ (k + 1) ∣ T W a - T W b := by
  rw [T_sub, pow_succ]
  exact mul_dvd_mul h $ X_dvd_E W ha hb

omit W in
theorem eq_zero_of_forall_X_pow_dvd {d : PowerSeries R} (h : ∀ k, X ^ k ∣ d) : d = 0 := by
  ext n
  simpa using (X_pow_dvd_iff.mp $ h $ n + 1) n $ Nat.lt_succ_self n

def seq : ℕ → PowerSeries R
  | 0 => 0
  | k + 1 => T W $ seq k

theorem X_dvd_seq (k : ℕ) : X ∣ seq W k := by
  induction k with
  | zero => show X ∣ (0 : PowerSeries R); exact dvd_zero _
  | succ k ih => show X ∣ T W (seq W k); exact X_dvd_wMap W ih

theorem seq_step (k : ℕ) : X ^ k ∣ seq W (k + 1) - seq W k := by
  induction k with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    exact contract W (X_dvd_seq W _) (X_dvd_seq W _) ih

theorem seq_far (j i : ℕ) : X ^ j ∣ seq W (j + i) - seq W j := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : j + (i + 1) = j + i + 1 := by omega
    rw [e, show seq W (j + i + 1) - seq W j
      = (seq W (j + i + 1) - seq W (j + i)) + (seq W (j + i) - seq W j) by ring]
    exact dvd_add ((pow_dvd_pow X $ Nat.le_add_right j i).trans $ seq_step W $ j + i) ih

def lim : PowerSeries R := PowerSeries.mk fun n => coeff n $ seq W $ n + 1

theorem lim_approx (k : ℕ) : X ^ k ∣ lim W - seq W k := by
  rw [X_pow_dvd_iff]
  intro m hm
  obtain ⟨i, rfl⟩ : ∃ i, k = m + 1 + i := ⟨k - (m + 1), by omega⟩
  have h := X_pow_dvd_iff.mp (seq_far W (m + 1) i) m $ Nat.lt_succ_self m
  simp [map_sub, lim, coeff_mk] at h ⊢
  linear_combination -h

theorem lim_fixed : WFixed W $ lim W := by
  have h1 := lim_approx W 1
  rw [pow_one] at h1
  have hX : X ∣ lim W := by
    have := dvd_add h1 $ X_dvd_seq W 1
    rwa [sub_add_cancel] at this
  use X_dvd_iff.mp hX
  show lim W = T W (lim W)
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_X_pow_dvd
  intro k
  have h3 :=
    contract W (X_dvd_seq W k) hX
      (by rw [← neg_sub]; exact dvd_neg.mpr $ lim_approx W k)
  have e : lim W - T W (lim W)
      = (lim W - seq W (k + 1)) + (T W (seq W k) - T W (lim W)) := by
    rw [show seq W (k + 1) = T W (seq W k) from rfl]
    ring
  rw [e]
  exact (pow_dvd_pow X $ Nat.le_succ k).trans $ dvd_add (lim_approx W $ k + 1) h3

theorem fixed_unique {w w' : PowerSeries R} (hw : WFixed W w) (hw' : WFixed W w') : w = w' := by
  exact sub_eq_zero.mp $ eq_zero_of_forall_X_pow_dvd (by
      intro k
      induction k with
      | zero => rw [pow_zero]; exact one_dvd _
      | succ k ih =>
        have h := contract W (X_dvd_iff.mpr hw.1) (X_dvd_iff.mpr hw'.1) ih
        rwa [show T W w = w from hw.2.symm, show T W w' = w' from hw'.2.symm] at h)


end Series

section Subst

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem mv_eq_zero {σ : Type*} {d e : MvPowerSeries σ R}
    (he : MvPowerSeries.constantCoeff e = 0) (h : d = d * e) : d = 0 := by
  have hc : IsUnit $ MvPowerSeries.constantCoeff $ 1 - e := by
    rw [map_sub, map_one, he, sub_zero]
    exact isUnit_one
  have h0 : d * (1 - e) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  exact (MvPowerSeries.isUnit_iff_constantCoeff.mpr hc).mul_left_eq_zero.mp h0

private theorem hasSubst_of_constantCoeff_eq_zero_elliptic_torsion {σ : Type} {s : MvPowerSeries σ R}
    (hs : MvPowerSeries.constantCoeff s = 0) : PowerSeries.HasSubst s :=
  PowerSeries.HasSubst.of_constantCoeff_zero hs

private theorem substAlgHom_apply' {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s)
    (f : PowerSeries R) : PowerSeries.substAlgHom ha f = f.subst s :=
  congrFun (PowerSeries.coe_substAlgHom ha) f

private theorem substAlgHom_X' {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s) :
    PowerSeries.substAlgHom ha (X : PowerSeries R) = s := by
  rw [substAlgHom_apply']
  exact PowerSeries.subst_X ha

private theorem powerSeries_smul_eq_C_mul (r : R) (f : PowerSeries R) : r • f = C r * f :=
  PowerSeries.smul_eq_C_mul f r

private theorem substAlgHom_C {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s)
    (r : R) : PowerSeries.substAlgHom ha (C r) = algebraMap R (MvPowerSeries σ R) r := by
  rw [show (C r : PowerSeries R) = r • (1 : PowerSeries R) by rw [powerSeries_smul_eq_C_mul, mul_one],
    map_smul, map_one, Algebra.smul_def, mul_one]

private theorem constantCoeff_subst_eq_zero_elliptic_torsion {w : PowerSeries R} (hw0 : constantCoeff w = 0)
    {σ : Type} (s : MvPowerSeries σ R) (hs : MvPowerSeries.constantCoeff s = 0) :
    MvPowerSeries.constantCoeff (w.subst s) = 0 := by
  have ha := hasSubst_of_constantCoeff_eq_zero_elliptic_torsion hs
  obtain ⟨w₁, hw₁⟩ := X_dvd_iff.mpr hw0
  rw [← substAlgHom_apply' ha, hw₁, map_mul, substAlgHom_X' ha, map_mul, hs, zero_mul]

theorem subst_eq {w : PowerSeries R} (hw : WFixed W w) {σ : Type} (s : MvPowerSeries σ R)
    (hs : MvPowerSeries.constantCoeff s = 0) : WEqAt W s $ w.subst s := by
  have ha := hasSubst_of_constantCoeff_eq_zero_elliptic_torsion hs
  have e := congrArg (PowerSeries.substAlgHom ha) hw.2
  simp [map_add, map_mul, map_pow, substAlgHom_C ha, substAlgHom_X' ha] at e
  rw [substAlgHom_apply' ha] at e
  unfold Formalism.ELL.WEqAt
  simp [Algebra.smul_def]
  linear_combination e

end Subst

end WeierstrassSeriesLimit

open WeierstrassSeriesLimit in
theorem wSeriesExistsUnique_holds : WSeriesUnique.{u} := by
  intro R _ W
  exact ⟨Formalism.ELL.WeierstrassSeriesLimit.lim W, Formalism.ELL.WeierstrassSeriesLimit.lim_fixed W,
    fun w hw => Formalism.ELL.WeierstrassSeriesLimit.fixed_unique W hw $ Formalism.ELL.WeierstrassSeriesLimit.lim_fixed W⟩

open WeierstrassSeriesLimit in

open WeierstrassSeriesLimit in
theorem wSeriesSubstUnique_holds : WSubstUnique.{u} := by
  intro R _ W w hw σ _ s hs
  refine ⟨Formalism.ELL.WeierstrassSeriesLimit.subst_eq W hw s hs, fun v hv hvE => ?_⟩
  have hu := Formalism.ELL.WeierstrassSeriesLimit.subst_eq W hw s hs
  unfold WEqAt at hu hvE
  simp [Algebra.smul_def] at hu hvE
  have key : v - w.subst s = (v - w.subst s) *
      (algebraMap R (MvPowerSeries σ R) W.a₁ * s + algebraMap R (MvPowerSeries σ R) W.a₂ * s ^ 2
        + algebraMap R (MvPowerSeries σ R) W.a₃ * (v + w.subst s)
        + algebraMap R (MvPowerSeries σ R) W.a₄ * s * (v + w.subst s)
        + algebraMap R (MvPowerSeries σ R) W.a₆ * (v ^ 2 + v * w.subst s + w.subst s ^ 2)) := by
    linear_combination hvE - hu
  refine sub_eq_zero.mp $ Formalism.ELL.WeierstrassSeriesLimit.mv_eq_zero ?_ key
  simp [hs, hv, _root_.Formalism.ELL.WeierstrassSeriesLimit.constantCoeff_subst_eq_zero_elliptic_torsion hw.1 s hs]

end Formalism.ELL
end
section
open PowerSeries



namespace Formalism.ELL.WeierstrassSubstitution

theorem mvsubst_psubst {K : Type u} [Field K] {τ σ : Type} (w : PowerSeries K)
    (a : MvPowerSeries τ K) (ha : MvPowerSeries.constantCoeff a = 0)
    (b : τ → MvPowerSeries σ K) (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (w.subst a) = w.subst (MvPowerSeries.subst b a) := by
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha) hb]

theorem eq_inv_of_map {L F : Type*} [CommRing L] [Field F] (f : L →+* F) {a b : L}
    (h : a * b = 1) : f b = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_right $ by rw [← map_mul, h, map_one]

theorem eq_zero_of_weq {K : Type u} [Field K] {W : WeierstrassCurve K} {σ : Type}
    {s : MvPowerSeries σ K} (h : Formalism.ELL.WEqAt W s 0) : s = 0 := by
  unfold Formalism.ELL.WEqAt at h
  simp [mul_zero, smul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h.symm

theorem ne_zero_of_weq {K : Type u} [Field K] {W : WeierstrassCurve K} {σ : Type}
    {s v : MvPowerSeries σ K} (h : Formalism.ELL.WEqAt W s v) (hs : s ≠ 0) : v ≠ 0 := by
  rintro rfl
  exact hs $ eq_zero_of_weq h

end Formalism.ELL.WeierstrassSubstitution

open Formalism.ELL.WeierstrassSubstitution in
theorem Formalism.ELL.wChordSubst_of (hU : Formalism.ELL.WSubstUnique.{u}) : Formalism.ELL.WChordSubst.{u} := by
  intro K _ W w hw F₂ hF0 hch σ _ s t hs ht hs0 ht0 hxst
  classical

  have chord_forms : ∀ (L : Type u) [Field L] (V : WeierstrassCurve.Affine L)
      (x0 x1 w0 w1 D PX : L), w0 ≠ 0 → w1 ≠ 0 → D = x0 * w1 - x1 * w0 → D ≠ 0 →
      PX = (w0 - w1) ^ 2 * w0 * w1 + V.a₁ * (w0 - w1) * D * w0 * w1
        - V.a₂ * D ^ 2 * w0 * w1 - x0 * D ^ 2 * w1 - x1 * D ^ 2 * w0 →
      V.addX (x0 / w0) (x1 / w1) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
          PX / (D ^ 2 * w0 * w1) ∧
      V.addY (x0 / w0) (x1 / w1) (-1 / w0) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
          (-((w0 - w1) * (PX - x0 * D ^ 2 * w1)) + D ^ 3 * w1 - V.a₁ * D * PX
            - V.a₃ * D ^ 3 * w0 * w1) / (D ^ 3 * w0 * w1) := by
    intro L _ V x0 x1 w0 w1 D PX h0 h1 hD hd hPX
    have hl : (-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1) = (w0 - w1) / D := by
      rw [hD]
      rw [hD] at hd
      field_simp
      ring
    have hX : V.addX (x0 / w0) (x1 / w1) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
        PX / (D ^ 2 * w0 * w1) := by
      rw [hl, hPX]
      simp only [WeierstrassCurve.Affine.addX]
      field_simp
    use hX
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY]
    rw [hX, hl]
    field_simp
    ring
  have hv : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hs, ht]
  set φ := MvPowerSeries.substAlgHom (R := K) hv with hφ
  have φe : ∀ g, φ g = MvPowerSeries.subst ![s, t] g := fun g => by
    rw [hφ, MvPowerSeries.coe_substAlgHom]
  have φX0 : φ (MvPowerSeries.X 0) = s := by rw [φe, MvPowerSeries.subst_X hv]
                                             rfl
  have φX1 : φ (MvPowerSeries.X 1) = t := by rw [φe, MvPowerSeries.subst_X hv]
                                             rfl
  have φw : ∀ g, MvPowerSeries.constantCoeff g = 0 →
      φ (w.subst g) = w.subst (φ g) := fun g hg => by
    rw [φe, φe, mvsubst_psubst w g hg _ hv]
  have φw0 : φ (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) = w.subst s := by
    rw [φw _ $ MvPowerSeries.constantCoeff_X 0, φX0]
  have φw1 : φ (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = w.subst t := by
    rw [φw _ $ MvPowerSeries.constantCoeff_X 1, φX1]
  have φwF : φ (w.subst F₂) = w.subst (φ F₂) := φw F₂ hF0
  have injA := IsFractionRing.injective (MvPowerSeries (Fin 2) K)
    $ FractionRing $ MvPowerSeries (Fin 2) K
  have injB := IsFractionRing.injective (MvPowerSeries σ K) $ FractionRing $ MvPowerSeries σ K

  have ws0 : w.subst s ≠ 0 := ne_zero_of_weq (hU K W w hw σ s hs).1 hs0
  have wt0 : w.subst t ≠ 0 := ne_zero_of_weq (hU K W w hw σ t ht).1 ht0
  have dB : s * w.subst t - t * w.subst s ≠ 0 := by
    intro h
    apply hxst
    unfold Formalism.ELL.xOf
    rw [div_eq_div_iff ((map_ne_zero_iff _ injB).2 ws0) $ (map_ne_zero_iff _ injB).2 wt0,
      ← map_mul, ← map_mul]
    congr 1
    linear_combination h
  have w00 : w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    ws0 $ by rw [← φw0, h, map_zero]
  have w10 : w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    wt0 $ by rw [← φw1, h, map_zero]
  have φD : φ (MvPowerSeries.X 0 * w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) -
      MvPowerSeries.X 1 * w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) =
      s * w.subst t - t * w.subst s := by
    simp only [map_sub, map_mul, φX0, φX1, φw0, φw1]
  have dA : MvPowerSeries.X 0 * w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) -
      MvPowerSeries.X 1 * w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    dB $ by rw [← φD, h, map_zero]
  unfold Formalism.ELL.ChordAt at hch ⊢
  simp only at hch ⊢
  unfold Formalism.ELL.xOf Formalism.ELL.yOf at hch ⊢
  rw [(chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injA).2 w00)
      ((map_ne_zero_iff _ injA).2 w10) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injA).2 dA) rfl).1,
    (chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injA).2 w00)
      ((map_ne_zero_iff _ injA).2 w10) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injA).2 dA) rfl).2] at hch
  rw [(chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injB).2 ws0)
      ((map_ne_zero_iff _ injB).2 wt0) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injB).2 dB) rfl).1,
    (chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injB).2 ws0)
      ((map_ne_zero_iff _ injB).2 wt0) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injB).2 dB) rfl).2]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃] at hch ⊢
  simp only [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K)
    $ FractionRing $ MvPowerSeries (Fin 2) K] at hch
  simp only [IsScalarTower.algebraMap_apply K (MvPowerSeries σ K)
    $ FractionRing $ MvPowerSeries σ K]
  have iw0 := (map_ne_zero_iff _ injA).2 w00
  have iw1 := (map_ne_zero_iff _ injA).2 w10
  have idA : algebraMap (MvPowerSeries (Fin 2) K) (FractionRing $ MvPowerSeries (Fin 2) K) (MvPowerSeries.X 0) *
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing $ MvPowerSeries (Fin 2) K)
        (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) -
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing $ MvPowerSeries (Fin 2) K) (MvPowerSeries.X 1) *
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing $ MvPowerSeries (Fin 2) K)
        (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact (map_ne_zero_iff _ injA).2 dA
  have jw0 := (map_ne_zero_iff _ injB).2 ws0
  have jw1 := (map_ne_zero_iff _ injB).2 wt0
  have jdB : algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) s *
      algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) (w.subst t) -
      algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) t *
      algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) (w.subst s) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact (map_ne_zero_iff _ injB).2 dB
  obtain ⟨hx, hy⟩ := hch
  rw [← φe F₂]
  by_cases hwF : w.subst F₂ = 0
  ·
    have hF : F₂ = 0 := eq_zero_of_weq $ hwF ▸ (hU K W w hw (Fin 2) F₂ hF0).1
    have hr : w.subst (φ F₂) = 0 := by
      rw [hF, map_zero]
      exact ((hU K W w hw σ 0 $ map_zero _).2 0 (map_zero _)
        (by unfold Formalism.ELL.WEqAt; simp)).symm
    rw [hwF, map_zero, div_zero, eq_comm, div_eq_zero_iff] at hx hy
    have hx' := hx.resolve_right $ by simp [iw0, iw1, idA]
    have hy' := hy.resolve_right $ by simp [iw0, iw1, idA]
    simp only [← map_mul, ← map_sub, ← map_add, ← map_pow, ← map_neg] at hx' hy'
    rw [map_eq_zero_iff _ injA] at hx' hy'
    have hxB := congrArg φ hx'
    have hyB := congrArg φ hy'
    simp only [map_mul, map_sub, map_add, map_pow, map_neg, map_zero, AlgHom.commutes,
      φX0, φX1, φw0, φw1] at hxB hyB
    have hxF := congrArg (algebraMap (MvPowerSeries σ K) $ FractionRing $ MvPowerSeries σ K) hxB
    have hyF := congrArg (algebraMap (MvPowerSeries σ K) $ FractionRing $ MvPowerSeries σ K) hyB
    simp only [map_mul, map_sub, map_add, map_pow, map_neg, map_zero] at hxF hyF
    rw [hr, map_zero, div_zero, div_zero]
    constructor
    rw [hxF, zero_div]
    rw [hyF, zero_div]
  have iwF := (map_ne_zero_iff _ injA).2 hwF
  rw [div_eq_div_iff iwF $ by simp [iw0, iw1, idA]] at hx
  rw [div_eq_div_iff iwF $ by simp [iw0, iw1, idA], neg_one_mul] at hy
  simp only [← map_mul, ← map_sub, ← map_add, ← map_pow, ← map_neg] at hx hy
  rw [injA.eq_iff] at hx hy
  have hxB := congrArg φ hx
  have hyB := congrArg φ hy
  simp only [map_mul, map_sub, map_add, map_pow, map_neg, AlgHom.commutes,
    φX0, φX1, φw0, φw1, φwF] at hxB hyB
  have hxF := congrArg (algebraMap (MvPowerSeries σ K) $ FractionRing $ MvPowerSeries σ K) hxB
  have hyF := congrArg (algebraMap (MvPowerSeries σ K) $ FractionRing $ MvPowerSeries σ K) hyB
  simp only [map_mul, map_sub, map_add, map_pow, map_neg] at hxF hyF

  have jwr : algebraMap (MvPowerSeries σ K) (FractionRing $ MvPowerSeries σ K) (w.subst (φ F₂)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero, neg_eq_zero] at hyF
    revert hyF
    simp [jw0, jw1, jdB]
  constructor
  rw [div_eq_div_iff jwr $ by simp [jw0, jw1, jdB]]
  linear_combination hxF
  rw [div_eq_div_iff jwr $ by simp [jw0, jw1, jdB], neg_one_mul]
  linear_combination hyF
end
section
open Finset (sum_add_distrib sum_congr)
open MvPowerSeries

namespace Formalism.G.LogCR

variable {R : Type*} [CommRing R] {σ τ : Type*}

def Agree (N : ℕ) (f g : MvPowerSeries σ R) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < N → coeff d f = coeff d g

theorem Agree.mono {N M : ℕ} {f g : MvPowerSeries σ R} (h : Agree N f g) (hMN : M ≤ N) :
    Agree M f g := fun d hd => h d $ lt_of_lt_of_le hd hMN

theorem Agree.pderiv {N : ℕ} {f g : MvPowerSeries σ R} (h : Agree (N + 1) f g) (i : σ) :
    Agree N (MvPowerSeries.pderiv i f) $ MvPowerSeries.pderiv i g := by
  classical
  intro d hd
  rw [coeff_pderiv, coeff_pderiv, h (d + Finsupp.single i 1) ?_]
  rw [map_add, Finsupp.degree_single]
  omega

theorem Agree.mul {N : ℕ} {x x' y y' : MvPowerSeries σ R} (hx : Agree N x x')
    (hy : Agree N y y') : Agree N (x * y) $ x' * y' := by
  classical
  intro d hd
  rw [coeff_mul, coeff_mul]
  refine sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = d := by simpa using hp
  rw [hx p.1 $ lt_of_le_of_lt (Finsupp.degree_mono $ hp' ▸ le_self_add) hd,
    hy p.2 $ lt_of_le_of_lt (Finsupp.degree_mono $ hp' ▸ le_add_self) hd]

theorem agree_iff [Finite σ] {N : ℕ} {f g : MvPowerSeries σ R} :
    Agree N f g ↔ truncTotal N f = truncTotal N g := by
  constructor
  intro h
  ext d
  rw [coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite]
  split_ifs with hd
  exact h d hd
  rfl
  intro h d hd
  have := congrArg (fun p => p.coeff d) h
  rwa [coeff_truncTotal _ hd, coeff_truncTotal _ hd] at this

theorem agree_truncTotal [Finite σ] (N : ℕ) (f : MvPowerSeries σ R) :
    Agree N f (truncTotal N f : MvPowerSeries σ R) := by
  intro d hd
  rw [MvPolynomial.coeff_coe, coeff_truncTotal _ hd]

theorem Agree.subst [Finite σ] [Finite τ] {N : ℕ} {f f' : MvPowerSeries σ R}
    {a a' : σ → MvPowerSeries τ R} (ha : ∀ j, constantCoeff (a j) = 0)
    (ha' : ∀ j, constantCoeff (a' j) = 0) (hf : Agree N f f') (haa : ∀ j, Agree N (a j) $ a' j) :
    Agree N (f.subst a) $ f'.subst a' := by
  rw [agree_iff, truncTotal_subst ha, truncTotal_subst ha', agree_iff.mp hf]
  have : (fun i => ((a i).truncTotal N : MvPowerSeries τ R)) =
      fun i => ((a' i).truncTotal N : MvPowerSeries τ R) := by
    funext i
    rw [agree_iff.mp $ haa i]
  rw [this]

theorem pderiv_aeval [Fintype σ] (p : MvPolynomial σ R) (A : σ → MvPowerSeries τ R) (i : τ) :
    MvPowerSeries.pderiv i (MvPolynomial.aeval A p) =
      ∑ j, MvPolynomial.aeval A (MvPolynomial.pderiv j p) * MvPowerSeries.pderiv i (A j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, add_mul, sum_add_distrib]
  | mul_X p j hp =>
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add, map_mul,
      MvPolynomial.aeval_X, add_mul, sum_add_distrib]
    rw [Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul, add_comm]
    congr 1
    rw [Finset.mul_sum]
    exact sum_congr rfl fun k _ => by ring
    simp [Pi.single_apply, apply_ite $ MvPolynomial.aeval A, mul_ite, ite_mul]

theorem pderiv_subst [Fintype σ] [Finite τ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ j, constantCoeff (a j) = 0) (f : MvPowerSeries σ R) (i : τ) :
    MvPowerSeries.pderiv i (f.subst a) =
      ∑ j, (MvPowerSeries.pderiv j f).subst a * MvPowerSeries.pderiv i (a j) := by
  classical
  ext d
  set N := d.degree + 2 with hN
  set P : MvPolynomial σ R := truncTotal N f with hP
  set A : σ → MvPowerSeries τ R := fun j => (truncTotal N (a j) : MvPowerSeries τ R) with hA
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => by
    have := agree_truncTotal N (a j) 0 $ by simp [hN]
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, ha j] at this
    exact this.symm
  have hfP := agree_truncTotal N f
  have haA : ∀ j, Agree N (a j) $ A j := fun j => agree_truncTotal N $ a j
  have h2 : ∀ j, Agree (d.degree + 1)
      ((MvPowerSeries.pderiv j f).subst a * MvPowerSeries.pderiv i (a j))
      $ (MvPowerSeries.pderiv j (P : MvPowerSeries σ R)).subst A *
        MvPowerSeries.pderiv i (A j) := fun j =>
    Agree.mul (Agree.subst ha hA0 (hfP.pderiv j) fun k => (haA k).mono $ by omega)
      $ (haA j).pderiv i
  have key : MvPowerSeries.pderiv i ((P : MvPowerSeries σ R).subst A) =
      ∑ j, (MvPowerSeries.pderiv j (P : MvPowerSeries σ R)).subst A *
        MvPowerSeries.pderiv i (A j) := by
    rw [subst_coe, pderiv_aeval]
    refine sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.pderiv_coe P, subst_coe]
  rw [((Agree.subst ha hA0 hfP haA).pderiv i) d $ by omega, key, map_sum, map_sum]
  exact sum_congr rfl fun j _ => (h2 j d $ by omega).symm

theorem pderiv_psubst [Finite τ] {a : MvPowerSeries τ R} (ha : constantCoeff a = 0)
    (f : PowerSeries R) (i : τ) :
    MvPowerSeries.pderiv i (f.subst a) =
      (PowerSeries.derivative f).subst a * MvPowerSeries.pderiv i a := by
  have := pderiv_subst (σ := Unit) (a := fun _ => a) (fun _ => ha) f i
  simpa [PowerSeries.subst_def, PowerSeries.derivative] using this

end Formalism.G.LogCR
end
section
open PowerSeries


namespace Formalism.G

section Hom

variable {R : Type u} [CommRing R]

abbrev atX (f : PowerSeries R) : MvPowerSeries (Fin 2) R := f.subst (MvPowerSeries.X (0 : Fin 2))

abbrev atY (f : PowerSeries R) : MvPowerSeries (Fin 2) R := f.subst (MvPowerSeries.X (1 : Fin 2))

def IsHom (F G : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ f.subst F.toPowerSeries = G.toPowerSeries.subst ![atX f, atY f]

def IsLog (F : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ coeff 1 f = 1 ∧ f.subst F.toPowerSeries = atX f + atY f

end Hom




def LogDeterminesLaw : Prop :=
  ∀ (R : Type u) [CommRing R] (F G : FormalGroup R) (f : PowerSeries R),
    IsLog F f → IsLog G f → F = G



section FunEq

variable {K : Type u} [NormedField K]

def IntegralPS (f : PowerSeries K) : Prop := ∀ n : ℕ, ‖coeff n f‖ ≤ 1

def IntegralMv {ι : Type v} (F : MvPowerSeries ι K) : Prop :=
  ∀ d : ι →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ 1

def DivBy (x : K) (f : PowerSeries K) : Prop := ∀ n : ℕ, ‖coeff n f‖ ≤ ‖x‖

def IsFrobLift (p q : ℕ) (σ : K →+* K) : Prop := ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ q‖ ≤ ‖(p : K)‖

def IsFunEqType (p q : ℕ) (σ : K →+* K) (f : PowerSeries K) : Prop :=
  IntegralPS $ f - (p : K)⁻¹ • (PowerSeries.map σ f).subst ((PowerSeries.X : PowerSeries K) ^ q)

def IsFunEqTypeMv {ι : Type v} (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K) (φ : MvPowerSeries ι K) :
    Prop :=
  IntegralMv $ φ - (p : K)⁻¹ • MvPowerSeries.expand q hq (MvPowerSeries.map σ φ)

end FunEq

def unitBall (K : Type u) [NormedField K] [IsUltrametricDist K] : Subring K := by
  first | exact @Bl.FirstLemmaM.goal1 K ‹_› ‹_› | exact @Bl.FirstLemmaM.goal1 K ‹_› | exact @Bl.FirstLemmaM.goal1 K | exact @Bl.FirstLemmaM.goal1

def FunctionalEquationSetting (K : Type u) [NormedField K] (p q : ℕ) (σ : K →+* K) : Prop :=
  p.Prime ∧ (∃ h : ℕ, 0 < h ∧ q = p ^ h) ∧ ‖(p : K)‖ < 1 ∧ IsFrobLift p q σ



def FunEqHom : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (σ : K →+* K),
    FunctionalEquationSetting K p q σ →
    ∀ f g : PowerSeries K, constantCoeff f = 0 → coeff 1 f = 1 → IsFunEqType p q σ f →
      constantCoeff g = 0 → IsFunEqType p q σ g →
      ∃ h : PowerSeries K, constantCoeff h = 0 ∧ IntegralPS h ∧ f.subst h = g

def FunEqSubst : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ f : PowerSeries K, constantCoeff f = 0 → IsFunEqType p q σ f →
    ∀ (ι : Type v) (α : MvPowerSeries ι K), MvPowerSeries.constantCoeff α = 0 → IntegralMv α →
      IsFunEqTypeMv p q hq σ (f.subst α)





def ltLog (p : ℕ) [Fact p.Prime] : PowerSeries ℚ_[p] :=
  PowerSeries.mk fun n => by
    classical exact if ∃ k : ℕ, p ^ k = n then ((n : ℚ_[p]))⁻¹ else 0

def LubinTateExample : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∃ F : FormalGroup ℤ_[p], IsLog (F.map PadicInt.Coe.ringHom) (ltLog p) ∧
      ∃ e : PowerSeries ℤ_[p], IsHom F F e ∧ coeff 1 e = (p : ℤ_[p]) ∧
        ∀ n : ℕ, (p : ℤ_[p]) ∣ coeff n (e - PowerSeries.X ^ p)

abbrev gauss {K : Type u} [NormedField K] {ι : Type v} (c : ℝ) (F : MvPowerSeries ι K) : ℝ :=
  MvPowerSeries.gaussNorm (fun a : K => ‖a‖) (fun _ : ι => c) F

abbrev HasGauss {K : Type u} [NormedField K] {ι : Type v} (c : ℝ) (F : MvPowerSeries ι K) : Prop :=
  MvPowerSeries.HasGaussNorm (fun a : K => ‖a‖) (fun _ : ι => c) F



def iterPderiv {K : Type u} [CommRing K] {r : ℕ} (α : Fin r → ℕ) :
    Module.End K $ MvPowerSeries (Fin r) K :=
  ((List.finRange r).map fun i => ((MvPowerSeries.pderiv i).toLinearMap) ^ (α i)).prod



end Formalism.G
end
section
open PowerSeries
namespace Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G

section Formal

variable {K : Type u} [Field K]

theorem subst_XX (G : MvPowerSeries (Fin 2) K) :
    G.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] = G := by
  have : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X := by
    funext i
    fin_cases i <;> rfl
  rw [this, MvPowerSeries.subst_self]
  rfl

theorem hasSubst2 {s t : MvPowerSeries (Fin 2) K} (hs : MvPowerSeries.constantCoeff s = 0)
    (ht : MvPowerSeries.constantCoeff t = 0) : MvPowerSeries.HasSubst ![s, t] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hs, ht])

theorem cc_subst2 {G s t : MvPowerSeries (Fin 2) K} (hG : MvPowerSeries.constantCoeff G = 0)
    (hs : MvPowerSeries.constantCoeff s = 0) (ht : MvPowerSeries.constantCoeff t = 0) :
    MvPowerSeries.constantCoeff (G.subst ![s, t]) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst2 hs ht)
    (by intro i; fin_cases i <;> simp [hs, ht]) hG

theorem cc_wsubst {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w) {σ : Type}
    {s : MvPowerSeries σ K} (hs : MvPowerSeries.constantCoeff s = 0) :
    MvPowerSeries.constantCoeff (w.subst s) = 0 := by
  obtain ⟨u0, hwu, _⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  rw [WeierstrassCoordinateSubstitution.subst_w hwu s hs, map_mul, map_pow, hs]
  simp

theorem fg_ne_zero (F : FormalGroup K) : F.toPowerSeries ≠ 0 := by
  intro h
  have := F.lin_coeff_X; rw [h] at this; simp at this

theorem x_X0_ne_formal_group {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w)
    (F : FormalGroup K) :
    xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ xOf w F.toPowerSeries := by
  obtain ⟨u0, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  have hφ : MvPowerSeries.HasSubst
      ![(0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] := hasSubst2 (by simp) $ by simp
  refine WeierstrassCoordinateSubstitution.xOf_ne_of_hom hwu hu (MvPowerSeries.substAlgHom hφ) _ _ (by simp)
    F.zero_constantCoeff (WeierstrassCoordinateSubstitution.X_ne_zero' 0) (fg_ne_zero F) ?_ ?_
  rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hφ]
  rfl
  rw [MvPowerSeries.coe_substAlgHom,
    F.zero_add $ PowerSeries.HasSubst.of_constantCoeff_zero $ by simp]
  exact WeierstrassCoordinateSubstitution.X_ne_zero' 1

theorem x_X0_ne_x_X1 {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w) :
    xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ xOf w (MvPowerSeries.X 1) := by
  obtain ⟨u0, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  have hφ : MvPowerSeries.HasSubst
      ![(0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] := hasSubst2 (by simp) $ by simp
  refine WeierstrassCoordinateSubstitution.xOf_ne_of_hom hwu hu (MvPowerSeries.substAlgHom hφ) _ _ (by simp)
    (by simp) (WeierstrassCoordinateSubstitution.X_ne_zero' 0) (WeierstrassCoordinateSubstitution.X_ne_zero' 1) ?_ ?_
  rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hφ]
  rfl
  rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hφ]
  exact WeierstrassCoordinateSubstitution.X_ne_zero' 1

theorem weq_C {W : WeierstrassCurve K} {σ : Type} {s v : MvPowerSeries σ K} (h : WEqAt W s v) :
    v = s ^ 3 + MvPowerSeries.C W.a₁ * (s * v) + MvPowerSeries.C W.a₂ * (s ^ 2 * v)
      + MvPowerSeries.C W.a₃ * v ^ 2 + MvPowerSeries.C W.a₄ * (s * v ^ 2)
      + MvPowerSeries.C W.a₆ * v ^ 3 := by
  unfold WEqAt at h
  simpa [MvPowerSeries.smul_eq_C_mul] using h

theorem weq_of_C {W : WeierstrassCurve K} {σ : Type} {s v : MvPowerSeries σ K}
    (h : v = s ^ 3 + MvPowerSeries.C W.a₁ * (s * v) + MvPowerSeries.C W.a₂ * (s ^ 2 * v)
      + MvPowerSeries.C W.a₃ * v ^ 2 + MvPowerSeries.C W.a₄ * (s * v ^ 2)
      + MvPowerSeries.C W.a₆ * v ^ 3) : WEqAt W s v := by
  unfold WEqAt
  simpa [MvPowerSeries.smul_eq_C_mul] using h

theorem inv_formal (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hw : WFixed W w) (F : FormalGroup K)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries)
    (ψ : MvPowerSeries (Fin 2) K)
    (hψ : (1 - MvPowerSeries.C W.a₁ * MvPowerSeries.X 0 - MvPowerSeries.C W.a₃ *
      w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) * ψ = 1) :
    F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      -MvPowerSeries.X 0 * ψ] = 0 := by
  classical
  obtain ⟨u0, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set z1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hz1
  set G := F.toPowerSeries with hG
  set w0 := w.subst z0 with hw0
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have c1 : MvPowerSeries.constantCoeff z1 = 0 := by simp [hz1]
  have n0 : z0 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 0
  have cw0 : MvPowerSeries.constantCoeff w0 = 0 := cc_wsubst hw c0
  have cG : MvPowerSeries.constantCoeff G = 0 := F.zero_constantCoeff
  set E := 1 - MvPowerSeries.C W.a₁ * z0 - MvPowerSeries.C W.a₃ * w0 with hE
  have nE := left_ne_zero_of_mul_eq_one hψ
  have nψ : ψ ≠ 0 := right_ne_zero_of_mul_eq_one hψ
  set J := -z0 * ψ with hJ
  have cJ : MvPowerSeries.constantCoeff J = 0 := by simp [hJ, c0]
  have nJ : J ≠ 0 := by
    rw [hJ, neg_mul, neg_ne_zero]
    exact mul_ne_zero n0 nψ
  have hwJ : w.subst J = -w0 * ψ := by
    obtain ⟨_, huniq⟩ := hU K W w hw (Fin 2) J cJ
    refine (huniq _ (by simp [cw0]) $ weq_of_C ?_).symm
    have key : E ^ 3 * ((-w0 * ψ) - (J ^ 3 + MvPowerSeries.C W.a₁ * (J * (-w0 * ψ))
        + MvPowerSeries.C W.a₂ * (J ^ 2 * (-w0 * ψ)) + MvPowerSeries.C W.a₃ * (-w0 * ψ) ^ 2
        + MvPowerSeries.C W.a₄ * (J * (-w0 * ψ) ^ 2) + MvPowerSeries.C W.a₆ * (-w0 * ψ) ^ 3)) = 0 := by
      rw [hJ]
      linear_combination ((z0 ^ 3 + MvPowerSeries.C W.a₂ * (z0 ^ 2 * w0)
          + MvPowerSeries.C W.a₄ * (z0 * w0 ^ 2) + MvPowerSeries.C W.a₆ * w0 ^ 3)
          * ((E * ψ) ^ 2 + E * ψ + 1)
        - (MvPowerSeries.C W.a₁ * (z0 * w0) + MvPowerSeries.C W.a₃ * w0 ^ 2) * E * (E * ψ + 1)
        - w0 * E ^ 2) * hψ - weq_C (hU K W w hw (Fin 2) z0 c0).1 - (1 + E) * w0 * hE
    exact sub_eq_zero.mp $ (mul_eq_zero.mp key).resolve_left $ pow_ne_zero 3 nE
  set j := algebraMap (MvPowerSeries (Fin 2) K) (FractionRing $ MvPowerSeries (Fin 2) K) with hj
  have jne : ∀ {x}, x ≠ 0 → j x ≠ 0 := fun hx h => hx $ (IsFractionRing.injective _ _) $ by rw [h, map_zero]
  have nw0 : w0 ≠ 0 := WeierstrassSubstitution.ne_zero_of_weq (hU K W w hw (Fin 2) z0 c0).1 n0
  have hjC : ∀ a : K, algebraMap K (FractionRing $ MvPowerSeries (Fin 2) K) a =
      j (MvPowerSeries.C a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply K $ MvPowerSeries (Fin 2) K, MvPowerSeries.algebraMap_apply]
    rfl
  have hjψ : j ψ = (j E)⁻¹ := WeierstrassSubstitution.eq_inv_of_map j hψ
  have hjE : j E = 1 - j (MvPowerSeries.C W.a₁) * j z0 - j (MvPowerSeries.C W.a₃) * j w0 := by
    rw [hE]
    simp [map_sub, map_one, map_mul]
  have hxJ : xOf w J = xOf w z0 := by
    unfold xOf
    rw [hwJ, hJ, map_mul, map_mul, map_neg, map_neg, neg_mul, neg_mul, neg_div_neg_eq,
      mul_div_mul_right _ _ $ jne nψ]
  have p0 := wSeriesNonsingularPoint_holds K W w hw (Fin 2) z0 c0 n0
  have p1 := wSeriesNonsingularPoint_holds K W w hw (Fin 2) z1 c1 $ WeierstrassCoordinateSubstitution.X_ne_zero' 1
  have pJ := wSeriesNonsingularPoint_holds K W w hw (Fin 2) J cJ nJ
  have hPJ : WeierstrassCurve.Affine.Point.some _ _ pJ = -WeierstrassCurve.Affine.Point.some _ _ p0 := by
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hxJ, (by
        unfold yOf xOf
        rw [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, hjC, hjC,
          hwJ, map_mul, map_neg, hjψ]
        have h1 := jne nw0
        have h2 := jne nE
        rw [hjE] at h2 ⊢
        simp [← hj, ← hw0]
        field_simp)⟩
  obtain ⟨pG, eG⟩ := WeierstrassCoordinateSubstitution.chord_add z0 z1 G p0 p1 (x_X0_ne_x_X1 hw) hch
  have xGJ : xOf w G ≠ xOf w J := by rw [hxJ]
                                     exact (x_X0_ne_formal_group hw F).symm
  obtain ⟨pH, eH⟩ := WeierstrassCoordinateSubstitution.chord_add G J _ pG pJ xGJ $ hS K W w hw G cG hch (Fin 2) G J cG cJ (fg_ne_zero F) nJ xGJ
  have hH : WeierstrassCurve.Affine.Point.some _ _ pH = WeierstrassCurve.Affine.Point.some _ _ p1 := by
    rw [← eH, hPJ, ← eG]
    abel
  obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj hH
  have hHz1 := WeierstrassCoordinateSubstitution.eq_of_xy hwu hu _ _ (cc_subst2 cG cG cJ) c1 hx hy

  have hφ : MvPowerSeries.HasSubst ![z0, (0 : MvPowerSeries (Fin 2) K)] := hasSubst2 c0 $ by simp
  have hφz0 : MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] z0 = z0 := by
    rw [hz0, MvPowerSeries.subst_X hφ]
    rfl
  have hφw0 : MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] w0 = w0 := by
    rw [hw0, WeierstrassSubstitution.mvsubst_psubst w z0 c0 _ hφ, hφz0]
  have hφE : MvPowerSeries.substAlgHom hφ E = E := by
    rw [hE, map_sub, map_sub, map_one, map_mul, map_mul, MvPowerSeries.coe_substAlgHom, hφz0,
      hφw0]
    simp
  have hφψ : MvPowerSeries.substAlgHom hφ ψ = ψ := by
    have h := congrArg (MvPowerSeries.substAlgHom hφ) hψ
    rw [map_mul, map_one, hφE, ← hψ] at h
    exact mul_left_cancel₀ nE h
  have hφJ : MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] J = J := by
    rw [← MvPowerSeries.coe_substAlgHom hφ, hJ, map_mul, map_neg, hφψ,
      MvPowerSeries.coe_substAlgHom, hφz0]
  have e := congrArg (MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)]) hHz1
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst2 cG cJ) hφ, hz1, MvPowerSeries.subst_X hφ] at e
  have e2 : (fun i => MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] $ ![G, J] i) =
      ![z0, J] := by
    funext i
    fin_cases i
    simp [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact F.add_zero $ PowerSeries.HasSubst.of_constantCoeff_zero c0
    simpa using hφJ
  rw [e2] at e
  simpa using e

end Formal
end Formalism.ELL.FormalGroupPointsHom
end
section
open MvPowerSeries

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

theorem hs2 {σ : Type*} {u v : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (hv : constantCoeff v = 0) : MvPowerSeries.HasSubst ![u, v] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hu, hv]

theorem hs3 {σ : Type*} {u v w : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (hv : constantCoeff v = 0) (hw : constantCoeff w = 0) : MvPowerSeries.HasSubst ![u, v, w] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hu, hv, hw]

theorem subst2_subst {σ τ : Type*} (Φ : MvPowerSeries (Fin 2) R) {u v : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) {b : σ → MvPowerSeries τ R}
    (hb : MvPowerSeries.HasSubst b) :
    (Φ.subst ![u, v]).subst b = Φ.subst ![u.subst b, v.subst b] := by
  rw [MvPowerSeries.subst_comp_subst_apply (hs2 hu hv) hb]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem psubst_subst {σ τ : Type*} (φ : PowerSeries R) {u : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (φ.subst u).subst b = φ.subst (u.subst b) := by
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hu) hb]

theorem constantCoeff_subst_of_zero {σ τ : Type*} [Finite σ] [Finite τ]
    (Φ : MvPowerSeries σ R) {b : σ → MvPowerSeries τ R} (hb : ∀ i, constantCoeff (b i) = 0) :
    constantCoeff (Φ.subst b) = constantCoeff Φ := by
  rw [MvPowerSeries.constantCoeff_subst $ MvPowerSeries.hasSubst_of_constantCoeff_zero hb, finsum_eq_single _ 0]
  simp
  intro d hd
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hd $ Finsupp.ext h
  have h0 : constantCoeff (d.prod fun s e => b s ^ e) = 0 := by
    rw [Finsupp.prod, map_prod]
    apply Finset.prod_eq_zero $ Finsupp.mem_support_iff.mpr hi
    rw [map_pow, hb i, zero_pow hi]
  rw [h0, smul_zero]

theorem isUnit_natCast_succ [Algebra ℚ R] (n : ℕ) : IsUnit $ (n : R) + 1 := by
  have h : ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) := by simp
  rw [h]
  exact IsUnit.map _ $ isUnit_iff_ne_zero.2 $ by positivity

variable (F : FormalGroup R)

def omegaF : PowerSeries R :=
  MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0]
    $ MvPowerSeries.pderiv 1 F.toPowerSeries

theorem constantCoeff_omega : PowerSeries.constantCoeff (omegaF F) = 1 := by
  have := constantCoeff_subst_of_zero (MvPowerSeries.pderiv 1 F.toPowerSeries)
    (b := ![(PowerSeries.X : PowerSeries R), 0]) fun i => by fin_cases i <;> simp [PowerSeries.X]
  rw [omegaF, PowerSeries.constantCoeff, this, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simpa using F.lin_coeff_Y

theorem hb0 : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries R), 0] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [PowerSeries.X]

theorem hX0 : constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = 0 := by
  simp
theorem hX1 : constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = 0 := by
  simp

theorem eval_zero_subst_law (φ : PowerSeries R) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] (φ.subst F.toPowerSeries) = φ := by
  rw [psubst_subst φ F.zero_constantCoeff hb0]
  have : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] F.toPowerSeries =
      PowerSeries.X := F.Xzero_eq_X
  rw [this, PowerSeries.X_subst]

theorem evalYZero_atY (φ : PowerSeries R) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] (atY φ) =
      PowerSeries.C (PowerSeries.constantCoeff φ) := by
  rw [atY, psubst_subst φ hX1 hb0, subst_X hb0]
  simp [PowerSeries.subst_zero_eq_C_constantCoeff]
  rfl

theorem pderiv_log {g : PowerSeries R} (hg : IsLog F g) :
    (PowerSeries.derivative g).subst F.toPowerSeries * MvPowerSeries.pderiv 1 F.toPowerSeries =
      atY (PowerSeries.derivative g) := by
  have := congrArg (MvPowerSeries.pderiv 1) hg.2.2
  rw [pderiv_psubst F.zero_constantCoeff, map_add, atX, atY, pderiv_psubst hX0,
    pderiv_psubst hX1] at this
  simpa [pderiv_X_of_ne $ show (0 : Fin 2) ≠ 1 by decide] using this

theorem derivative_log_mul_omega {g : PowerSeries R} (hg : IsLog F g) :
    PowerSeries.derivative g * omegaF F = 1 := by
  have := congrArg (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0]) $ pderiv_log F hg
  rw [subst_mul hb0, eval_zero_subst_law, evalYZero_atY] at this
  rw [omegaF, this]
  have h1 : PowerSeries.constantCoeff (PowerSeries.derivative g) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, hg.2.1]
    simp
  rw [h1, map_one]

theorem log_unique [Algebra ℚ R] {f g : PowerSeries R} (hf : IsLog F f) (hg : IsLog F g) :
    f = g := by
  ext n
  cases n with
  | zero => simpa using hf.1.trans hg.1.symm
  | succ n =>
    have := congrArg (PowerSeries.coeff n) $ by
        have hu := PowerSeries.mul_invOfUnit (omegaF F) 1 $ by simp [constantCoeff_omega]
        calc PowerSeries.derivative f
            = PowerSeries.derivative f * omegaF F * PowerSeries.invOfUnit (omegaF F) 1 := by
              rw [mul_assoc, hu, mul_one]
          _ = PowerSeries.derivative g * omegaF F * PowerSeries.invOfUnit (omegaF F) 1 := by
              rw [derivative_log_mul_omega F hf, derivative_log_mul_omega F hg]
          _ = PowerSeries.derivative g := by rw [mul_assoc, hu, mul_one]
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at this
    apply (isUnit_natCast_succ (R := R) n).mul_left_cancel
    rw [mul_comm, this, mul_comm]
end Formalism.G.LogP

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

theorem subst_zero' {σ τ : Type*} {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (0 : MvPowerSeries σ R).subst b = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom hb, map_zero]

theorem subst_XX (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = Φ := by
  have h : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = MvPowerSeries.X := by
    funext i
    fin_cases i <;> rfl
  rw [h, MvPowerSeries.subst_self, id]

theorem omega_subst {σ : Type*} {u : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (F : FormalGroup R) :
    (omegaF F).subst u = (MvPowerSeries.pderiv 1 F.toPowerSeries).subst ![u, 0] := by
  have hu' : MvPowerSeries.HasSubst fun _ : Unit => u :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hu
  unfold omegaF
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hb0 hu']
  congr 1
  funext i
  fin_cases i
  exact MvPowerSeries.subst_X hu' ()
  exact subst_zero' hu'

variable (F : FormalGroup R)

theorem omega_key :
    (omegaF F).subst F.toPowerSeries =
      MvPowerSeries.pderiv 1 F.toPowerSeries * atY (omegaF F) := by
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hY : ∀ i, constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) = 0 := fun i => by
    simp
  have hG : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 1]) = 0 := by
    rw [constantCoeff_subst_of_zero _ fun i => by fin_cases i <;> simp, hFc]
  have hH : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 2]) = 0 := by
    rw [constantCoeff_subst_of_zero _ fun i => by fin_cases i <;> simp, hFc]
  have dG : MvPowerSeries.pderiv 2 (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 1]) = 0 := by
    rw [pderiv_subst fun i => by fin_cases i <;> simp]
    simp [Fin.sum_univ_two, pderiv_X_of_ne $ show (0 : Fin 3) ≠ 2 by decide,
      pderiv_X_of_ne $ show (1 : Fin 3) ≠ 2 by decide]
  have dH : MvPowerSeries.pderiv 2 (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 2]) = (MvPowerSeries.pderiv 1 F.toPowerSeries).subst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 2] := by
    rw [pderiv_subst fun i => by fin_cases i <;> simp]
    simp [Fin.sum_univ_two, pderiv_X_of_ne $ show (1 : Fin 3) ≠ 2 by decide]
  have E := congrArg (MvPowerSeries.pderiv 2) F.assoc
  rw [pderiv_subst fun i => by fin_cases i <;> simp [hG],
    pderiv_subst fun i => by fin_cases i <;> simp [hH]] at E
  simp [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, dG, dH, pderiv_X_self,
    pderiv_X_of_ne $ show (0 : Fin 3) ≠ 2 by decide, mul_zero, zero_add, mul_one] at E
  have hc3 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1, 0] :=
    hs3 (by simp) (by simp) $ by simp
  have E' := congrArg (MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1, 0]) E
  rw [subst_mul hc3, subst2_subst _ hG (hY 2) hc3, subst2_subst _ (hY 0) hH hc3,
    subst2_subst _ (hY 1) (hY 2) hc3, subst2_subst _ (hY 0) (hY 1) hc3,
    subst2_subst _ (hY 1) (hY 2) hc3] at E'
  simp [subst_X hc3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at E'
  rw [subst_XX, F.add_zero $ PowerSeries.HasSubst.of_constantCoeff_zero hX1, subst_XX] at E'
  rwa [omega_subst hFc, atY, omega_subst hX1]

end Formalism.G.LogP

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

theorem psubst_one {σ : Type*} {a : MvPowerSeries σ R} (ha : PowerSeries.HasSubst a) :
    (1 : PowerSeries R).subst a = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_one]

theorem subst_X0_zero_eq_rescale (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = rescale ![1, 0] Φ := by
  rw [MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  fin_cases s <;> simp

theorem eq_zero_of_pderiv_one [Algebra ℚ R] {h : MvPowerSeries (Fin 2) R}
    (hD : MvPowerSeries.pderiv 1 h = 0)
    (h0 : h.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0) : h = 0 := by
  rw [subst_X0_zero_eq_rescale] at h0
  ext n
  rw [map_zero]
  by_cases hn : n 1 = 0
  have h1 := congrArg (MvPowerSeries.coeff n) h0
  rw [MvPowerSeries.coeff_rescale, map_zero] at h1
  have hprod : (n.prod fun s m => (![1, 0] : Fin 2 → R) s ^ m) = 1 := by
    rw [Finsupp.prod]
    apply Finset.prod_eq_one
    intro s hs
    fin_cases s
    simp
    exact absurd hn $ Finsupp.mem_support_iff.mp hs
  rwa [hprod, one_mul] at h1
  have hm : n = (n - Finsupp.single 1 1) + Finsupp.single 1 1 := by
    ext i
    fin_cases i <;> simp <;> omega
  have h1 := congrArg (MvPowerSeries.coeff $ n - Finsupp.single 1 1) hD
  rw [MvPowerSeries.coeff_pderiv, map_zero, ← hm] at h1
  exact ((isUnit_natCast_succ _).mul_left_eq_zero).mp h1

variable (F : FormalGroup R)

def lam : PowerSeries R := PowerSeries.invOfUnit (omegaF F) 1

theorem omega_mul_lam : omegaF F * lam F = 1 := by
  apply PowerSeries.mul_invOfUnit _ _
  rw [constantCoeff_omega, Units.val_one]
variable [Algebra ℚ R]

def logF : PowerSeries R :=
  PowerSeries.mk fun n => if n = 0 then 0 else
    algebraMap ℚ R (1 / (n : ℚ)) * PowerSeries.coeff (n - 1) (lam F)

theorem derivative_logF : PowerSeries.derivative (logF F) = lam F := by
  ext n
  rw [PowerSeries.coeff_derivative]
  unfold logF
  rw [PowerSeries.coeff_mk, if_neg $ Nat.succ_ne_zero n, Nat.add_sub_cancel, mul_comm, ← mul_assoc]
  have h : ((n : R) + 1) * algebraMap ℚ R (1 / ((n + 1 : ℕ) : ℚ)) = 1 := by
    rw [show ((n : R) + 1) = algebraMap ℚ R ((n + 1 : ℕ) : ℚ) by simp, ← map_mul,
      mul_one_div_cancel $ by positivity, map_one]
  rw [h, one_mul]

theorem logF_isLog : IsLog F $ logF F := by
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hFs : PowerSeries.HasSubst F.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero hFc
  have hX1s : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hX1
  have hc0 : PowerSeries.constantCoeff (logF F) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, logF, PowerSeries.coeff_mk, if_pos rfl]
  refine ⟨hc0, ?_, ?_⟩
  rw [logF, PowerSeries.coeff_mk, if_neg one_ne_zero, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, lam, PowerSeries.constantCoeff_invOfUnit]
  simp
  have hω := omega_mul_lam F
  have hF1 : (lam F).subst F.toPowerSeries * (omegaF F).subst F.toPowerSeries = 1 := by
    rw [← PowerSeries.subst_mul hFs, mul_comm, hω, psubst_one hFs]
  have hY1 : atY (lam F) * atY (omegaF F) = 1 := by
    rw [atY, atY, ← PowerSeries.subst_mul hX1s, mul_comm, hω, psubst_one hX1s]
  have hk := omega_key F
  have hD : MvPowerSeries.pderiv 1
      ((logF F).subst F.toPowerSeries - atX (logF F) - atY (logF F)) = 0 := by
    rw [map_sub, map_sub, pderiv_psubst hFc, atX, atY, pderiv_psubst hX0, pderiv_psubst hX1,
      derivative_logF, pderiv_X_self, pderiv_X_of_ne $ show (0 : Fin 2) ≠ 1 by decide]
    linear_combination (-((lam F).subst F.toPowerSeries *
      MvPowerSeries.pderiv 1 F.toPowerSeries)) * hY1 + atY (lam F) * hF1 -
      (lam F).subst F.toPowerSeries * atY (lam F) * hk
  have hc2 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] := hs2 (by simp) $ by simp
  have := eq_zero_of_pderiv_one hD $ by
      rw [subst_sub hc2, subst_sub hc2, atX, atY, psubst_subst _ hFc hc2, psubst_subst _ hX0 hc2,
        psubst_subst _ hX1 hc2, F.add_zero $ PowerSeries.HasSubst.of_constantCoeff_zero hX0,
        subst_X hc2, subst_X hc2]
      simp [PowerSeries.subst_zero_of_constantCoeff_zero hc0]
  rwa [sub_sub, sub_eq_zero] at this

end Formalism.G.LogP

namespace Formalism.G.LogP

variable {R : Type*} [CommRing R]

theorem psubst_injective {f : PowerSeries R} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : PowerSeries.coeff 1 f = 1) {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (h : f.subst a = f.subst b) : a = b := by
  have : Invertible $ PowerSeries.coeff 1 f := hf1 ▸ invertibleOne
  have inv : ∀ c : MvPowerSeries σ R, constantCoeff c = 0 → f.substInv.subst (f.subst c) = c := by
    intro c hc
    have hcs := PowerSeries.HasSubst.of_constantCoeff_zero hc
    rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hf0) hcs, PowerSeries.subst_substInv_left f hf0,
      PowerSeries.subst_X hcs]
  rw [← inv a ha, h, inv b hb]

end Formalism.G.LogP
end
section
open MvPowerSeries (constantCoeff pderiv)
namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type*} [CommRing K]

def ccd (i : Fin 2) (H : MvPowerSeries (Fin 2) K) : K :=
  constantCoeff $ pderiv i H

def Q (H : MvPowerSeries (Fin 2) K) : K :=
  constantCoeff $ pderiv 1 $ pderiv 0 H













theorem hv {x y : MvPowerSeries (Fin 2) K} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    ∀ j, constantCoeff (![x, y] j) = 0 := by
  intro j
  fin_cases j <;> simp [hx, hy]

theorem ccd_F (F : MvPowerSeries (Fin 2) K) {x y : MvPowerSeries (Fin 2) K}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (i : Fin 2) :
    ccd i (F.subst ![x, y]) = ccd 0 F * ccd i x + ccd 1 F * ccd i y := by
  unfold ccd
  rw [pderiv_subst $ hv hx hy, map_sum, Fin.sum_univ_two]
  simp [map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ $ hv hx hy, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]


theorem ccd_single (F : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    ccd i F = MvPowerSeries.coeff (Finsupp.single i 1) F := by
  unfold ccd
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp


end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem hb : ∀ j, constantCoeff
    ((![PowerSeries.X, (0 : PowerSeries K)] : Fin 2 → PowerSeries K) j) = 0 := by
  intro j
  fin_cases j
  exact MvPowerSeries.constantCoeff_X _
  simp







end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL

open Formalism.G Formalism.ELL.FormalGroupQuadraticJets Formalism.G.LogCR


end Formalism.ELL
end
section
open PowerSeries



namespace Formalism.ELL
namespace CubeTwoAlt

open WeierstrassChordSeries

variable {K : Type u} [Field K]

local notation "cc" => MvPowerSeries.constantCoeff

theorem coeff_subst_X0_zero (H : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (he : e 1 = 0) :
    MvPowerSeries.coeff e (H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0]) =
      MvPowerSeries.coeff e H := by
  classical
  have hprod : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s n => (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] s) ^ n)
        = MvPowerSeries.X 0 ^ d 0 * 0 ^ d 1 := by
    intro d
    rw [Finsupp.prod_fintype _ _ fun i => pow_zero _, Fin.prod_univ_two]
    simp
  rw [MvPowerSeries.coeff_subst $ FormalGroupPointsHom.hasSubst2 (by simp) $ by simp, finsum_eq_single _ e]
  rw [hprod, he, pow_zero, mul_one, MvPowerSeries.coeff_X_pow]
  have : e = Finsupp.single 0 (e 0) := ((eq_single_iff e).2).mpr he
  rw [if_pos this, smul_eq_mul, mul_one]
  intro d hd
  rw [hprod]
  rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
  rw [h1, pow_zero, mul_one, MvPowerSeries.coeff_X_pow, if_neg, smul_zero]
  intro h
  apply hd
  rw [((eq_single_iff d).2).mpr h1]
  exact h.symm
  rw [zero_pow h1.ne', mul_zero, map_zero, smul_zero]

theorem X_one_dvd_of_subst_X_zero_eq_zero (H : MvPowerSeries (Fin 2) K)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] = 0) :
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ H := by
  rw [MvPowerSeries.X_dvd_iff]
  intro m hm
  rw [← coeff_subst_X0_zero H m hm, h, map_zero]

theorem vec_mem {W : WeierstrassCurve K} {x y : MvPowerSeries (Fin 2) K} (hx : x ∈ T W)
    (hy : y ∈ T W) : ∀ i, ![x, y] i ∈ T W := by
  intro i
  fin_cases i
  exact hx
  exact hy

theorem subst_mem_T_of_mem {W : WeierstrassCurve K} {f : MvPowerSeries (Fin 2) K} (hf : f ∈ T W)
    {a : Fin 2 → MvPowerSeries (Fin 2) K} (ha : ∀ i, a i ∈ T W) (h0 : ∀ i, cc (a i) = 0) :
    f.subst a ∈ T W := by
  obtain ⟨fS, rfl⟩ := hf
  choose aS haS using fun i => ha i
  have hinj : Function.Injective $ algebraMap (Sadj W) K := fun x y h => Subtype.ext h
  have hS : MvPowerSeries.HasSubst aS := MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    apply hinj
    rw [map_zero]
    have := congrArg MvPowerSeries.constantCoeff $ haS i
    rwa [MvPowerSeries.constantCoeff_map, h0 i] at this
  use fS.subst aS
  rw [MvPowerSeries.map_subst hS]
  congr 1
  funext i
  exact haS i

theorem div_diag {W : WeierstrassCurve K} (H : MvPowerSeries (Fin 2) K) (hT : H ∈ T W)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] = 0) :
    ∃ Q ∈ T W, H = (MvPowerSeries.X 1 - MvPowerSeries.X 0) * Q := by
  have c0 : cc (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hτ : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 + MvPowerSeries.X 0] := FormalGroupPointsHom.hasSubst2 c0 (by simp)
  have hτ' : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 - MvPowerSeries.X 0] := FormalGroupPointsHom.hasSubst2 c0 (by simp)
  have hε : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] :=
    FormalGroupPointsHom.hasSubst2 c0 (by simp)
  obtain ⟨H', hH'⟩ : ∃ H', H' = H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 + MvPowerSeries.X 0] := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ := X_one_dvd_of_subst_X_zero_eq_zero H' (by
      rw [hH', MvPowerSeries.subst_comp_subst_apply hτ hε]
      have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0]
          $ ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1 + MvPowerSeries.X 0] i)
          = ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] := by
        funext i
        fin_cases i
        simp [MvPowerSeries.subst_X hε]
        simp [MvPowerSeries.subst_add hε, MvPowerSeries.subst_X hε]
      rw [this]
      exact h)
  have hback : H'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 - MvPowerSeries.X 0] = H := by
    rw [hH', MvPowerSeries.subst_comp_subst_apply hτ hτ']
    have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        MvPowerSeries.X 1 - MvPowerSeries.X 0]
        $ ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1 + MvPowerSeries.X 0] i)
        = ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] := by
      funext i
      fin_cases i
      simp [MvPowerSeries.subst_X hτ']
      simp [MvPowerSeries.subst_add hτ', MvPowerSeries.subst_X hτ']
    rw [this]
    exact FormalGroupPointsHom.subst_XX H
  refine ⟨Q'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 - MvPowerSeries.X 0], ?_, ?_⟩
  have hH'T : H' ∈ T W := by
    rw [hH']
    exact subst_mem_T_of_mem hT (vec_mem (X_mem_T 0) ((T W).add_mem (X_mem_T 1) (X_mem_T 0)))
      $ FormalGroupQuadraticJets.hv c0 (by simp)
  exact subst_mem_T_of_mem (by
      rw [mem_T]
      intro e
      have := congrArg (MvPowerSeries.coeff (e + Finsupp.single 1 1)) hQ'
      rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, if_pos le_add_self,
        add_tsub_cancel_right, one_mul] at this
      rw [← this]
      exact mem_T.mp hH'T _) (vec_mem (X_mem_T 0) ((T W).sub_mem (X_mem_T 1) (X_mem_T 0)))
    (FormalGroupQuadraticJets.hv c0 (by simp))
  conv_lhs => rw [← hback]
  rw [hQ', MvPowerSeries.subst_mul hτ', MvPowerSeries.subst_X hτ']
  simp

variable {W : WeierstrassCurve K} {w : PowerSeries K}

theorem w_eq_X_cube_mul_unit (hw : WFixed W w) : w = X ^ 3 * wU w := by
  obtain ⟨l0, l1, l2, _⟩ := w_low hw
  ext n
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  rw [wU, PowerSeries.coeff_mk, Nat.sub_add_cancel h]
  interval_cases n <;> assumption

theorem wU_cc (hw : WFixed W w) : PowerSeries.constantCoeff (wU w) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, wU, PowerSeries.coeff_mk]
  exact (w_low hw).2.2.2

theorem subst_wU_X_mem_T_of_wFixed (hw : WFixed W w) (i : Fin 2) :
    (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ∈ T W := by
  classical
  rw [mem_T]
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  rw [wU, PowerSeries.coeff_mk]
  exact w_coeff_mem hw _
  exact Subalgebra.zero_mem _

theorem U_cc (hw : WFixed W w) (i : Fin 2) :
    cc ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)) = 1 := by
  classical
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst_single]
  simp [wU, (w_low hw).2.2.2]

theorem Wi_eq (hw : WFixed W w) (i : Fin 2) :
    Wi w i = MvPowerSeries.X i ^ 3 * (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
  WeierstrassCoordinateSubstitution.subst_w (w_eq_X_cube_mul_unit hw) _ $ by simp

def dI (W : WeierstrassCurve K) (w : PowerSeries K) (i : Fin 2) : MvPowerSeries (Fin 2) K :=
  -1 + ca W.a₁ * MvPowerSeries.X i + ca W.a₃ * Wi w i

theorem dI_cc (hw : WFixed W w) (i : Fin 2) : cc (dI W w i) = -1 := by
  simp [dI, Wi_cc hw]

theorem dI_mem_T_of_wFixed (hw : WFixed W w) (i : Fin 2) : dI W w i ∈ T W :=
  (T W).add_mem ((T W).add_mem ((T W).neg_mem (T W).one_mem)
    $ (T W).mul_mem (constSeries_mem_integralSeries $ by simp) $ X_mem_T i) $ (T W).mul_mem (constSeries_mem_integralSeries $ by simp) $ wVar_mem_integralSeries hw i

theorem invSer_subst (hw : WFixed W w) (i : Fin 2) :
    (invSer W w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X i * (dI W w i)⁻¹ := by
  have ha : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X i
  have hφc : PowerSeries.constantCoeff (-1 + C W.a₁ * X + C W.a₃ * w : PowerSeries K) ≠ 0 := by
    simp [hw.1]
  have e := congrArg (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K))
    $ PowerSeries.mul_inv_cancel _ hφc
  have hs : (-1 + C W.a₁ * X + C W.a₃ * w : PowerSeries K).subst
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = dI W w i := by
    rw [← PowerSeries.coe_substAlgHom ha]
    simp [map_add, map_neg, map_one, map_mul]
    rw [PowerSeries.coe_substAlgHom ha, PowerSeries.subst_C, PowerSeries.subst_C,
      PowerSeries.subst_X ha]
    rfl
  have h1 : (1 : PowerSeries K).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 1 := by
    rw [← PowerSeries.coe_substAlgHom ha, map_one]
  rw [PowerSeries.subst_mul ha, hs, h1] at e
  have hinv : (-1 + C W.a₁ * X + C W.a₃ * w : PowerSeries K)⁻¹.subst
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = (dI W w i)⁻¹ :=
    (MvPowerSeries.eq_inv_iff_mul_eq_one (by rw [dI_cc hw]; exact neg_ne_zero.mpr one_ne_zero)).mpr
      (by rw [mul_comm]; exact e)
  rw [invSer, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, hinv]

theorem ib_cc (hw : WFixed W w) :
    cc ((invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = 0 := by
  rw [invSer_subst hw]
  simp

theorem inverseSeries_subst_X1_mem (hw : WFixed W w) :
    (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∈ T W := by
  rw [invSer_subst hw]
  exact (T W).mul_mem (X_mem_T 1) $ inv_mem_integralSeries (dI_mem_T_of_wFixed hw 1)
    (by rw [dI_cc hw]; exact neg_ne_zero.mpr one_ne_zero)
    (by rw [dI_cc hw, inv_neg, inv_one]; exact Subalgebra.neg_mem _ $ Subalgebra.one_mem _)

theorem chord_series_eq_F2 (hw : WFixed W w) {F : MvPowerSeries (Fin 2) K} (hF0 : cc F = 0)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F) : F = WeierstrassChordSeries.F2 W w := by
  have h2 := chord wSeriesSubstUnique_holds.{u} hw
  dsimp [ChordAt] at hch h2
  exact WeierstrassCoordinateSubstitution.eq_of_xy (w_eq_X_cube_mul_unit hw) (wU_cc hw) F (WeierstrassChordSeries.F2 W w) hF0 (constantCoeff_formalSum hw)
    (hch.1.trans h2.1.symm) $ hch.2.trans h2.2.symm

theorem Fp_diag (hw : WFixed W w) :
    ((WeierstrassChordSeries.F2 W w).subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)]).subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] = 0 := by
  have hU := wSeriesSubstUnique_holds.{u}
  have hS := wChordSubst_of hU
  let FG : FormalGroup K := ⟨WeierstrassChordSeries.F2 W w, constantCoeff_formalSum hw, linearCoeff_formalSum hw 0, linearCoeff_formalSum hw 1,
    WeierstrassCoordinateSubstitution.assoc_of hS wSeriesNonsingularPoint_holds hw (w_eq_X_cube_mul_unit hw) (wU_cc hw) (WeierstrassChordSeries.F2 W w) (constantCoeff_formalSum hw) (linearCoeff_formalSum hw 0)
      $ chord hU hw⟩
  have hdA : dI W w 0 * (dI W w 0)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [dI_cc hw]; exact neg_ne_zero.mpr one_ne_zero)
  have hψ : (1 - MvPowerSeries.C W.a₁ * MvPowerSeries.X 0 - MvPowerSeries.C W.a₃ *
      w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) * (-(dI W w 0)⁻¹) = 1 := by
    simp only [dI, Wi] at hdA ⊢
    linear_combination hdA
  have hd : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 0] := FormalGroupPointsHom.hasSubst2 (by simp) $ by simp
  rw [MvPowerSeries.subst_comp_subst_apply (FormalGroupPointsHom.hasSubst2 (by simp) $ ib_cc hw) hd]
  have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 0] $ ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] i) =
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), -MvPowerSeries.X 0 * -(dI W w 0)⁻¹] := by
    funext i
    fin_cases i
    simp [MvPowerSeries.subst_X hd]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [WeierstrassSubstitution.mvsubst_psubst _ _ (by simp) _ hd, MvPowerSeries.subst_X hd]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [invSer_subst hw 0]
    ring
  rw [this]
  exact FormalGroupPointsHom.inv_formal hU hS hw FG (chord hU hw) _ hψ

end CubeTwoAlt
end Formalism.ELL

namespace Formalism.ELL
namespace CubeTwoAlt

open WeierstrassChordSeries

variable {K : Type u} [Field K] {W : WeierstrassCurve K} {w : PowerSeries K}

local notation "cc" => MvPowerSeries.constantCoeff

theorem chord_subst_inverse_mem (hw : WFixed W w) :
    (WeierstrassChordSeries.F2 W w).subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] ∈ T W :=
  subst_mem_T_of_mem (formalSum_mem_integralSeries hw) (vec_mem (X_mem_T 0) $ inverseSeries_subst_X1_mem hw)
    $ FormalGroupQuadraticJets.hv (by simp) $ ib_cc hw

theorem Fp_lin (hw : WFixed W w) :
    MvPowerSeries.coeff (Finsupp.single 1 1) ((WeierstrassChordSeries.F2 W w).subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)]) = -1 := by
  have h := FormalGroupQuadraticJets.ccd_F (WeierstrassChordSeries.F2 W w) (x := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
    (by simp) (ib_cc hw) 1
  simp [FormalGroupQuadraticJets.ccd_single] at h
  rw [h, linearCoeff_formalSum hw 0, linearCoeff_formalSum hw 1, invSer_subst hw 1, WeierstrassChordSeries.L_mul]
  simp [WeierstrassChordSeries.L_X, MvPowerSeries.constantCoeff_inv, dI_cc hw]

theorem C3_mem_T_of_wFixed (hw : WFixed W w) : C3 W w ∈ T W :=
  lineCoeffCubic_mem _ (constSeries_mem_integralSeries $ by simp) (constSeries_mem_integralSeries $ by simp) (constSeries_mem_integralSeries $ by simp) $ slope_mem_integralSeries hw

theorem dd_mem_T_of_wFixed (hw : WFixed W w) : dd W w ∈ T W := by
  have h1 : ca W.a₁ ∈ T W := constSeries_mem_integralSeries $ by simp
  have h2 : ca W.a₂ ∈ T W := constSeries_mem_integralSeries $ by simp
  have h3 : ca W.a₃ ∈ T W := constSeries_mem_integralSeries $ by simp
  have h4 : ca W.a₄ ∈ T W := constSeries_mem_integralSeries $ by simp
  have h6 : ca W.a₆ ∈ T W := constSeries_mem_integralSeries $ by simp
  have hl := slope_mem_integralSeries hw
  have hn := intercept_mem_integralSeries hw
  have hz3 : z3 W w ∈ T W :=
    (T W).sub_mem ((T W).sub_mem ((T W).neg_mem $ X_mem_T 0) $ X_mem_T 1) $ (T W).mul_mem (lineCoeffQuadratic_mem _ h1 h2 h3 h4 h6 hl hn) $ inv_mem_integralSeries (lineCoeffCubic_mem _ h2 h4 h6 hl) (by rw [constantCoeff_chordCoeffCubic hw]; exact one_ne_zero) (by rw [constantCoeff_chordCoeffCubic hw, inv_one]; exact Subalgebra.one_mem _)
  exact (T W).add_mem ((T W).add_mem ((T W).neg_mem (T W).one_mem) $ (T W).mul_mem h1 hz3)
      $ (T W).mul_mem h3 $ (T W).add_mem ((T W).mul_mem hl hz3) hn

theorem main (hw : WFixed W w) :
    ∃ c : MvPowerSeries (Fin 2) K, c ∈ T W ∧ cc c = -1 ∧
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2 *
          ((wU w).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))⁻¹
        - (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2 *
          ((wU w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K))⁻¹
        = c * WeierstrassChordSeries.F2 W w * MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
            (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] (WeierstrassChordSeries.F2 W w) := by
  have : IsDomain $ MvPowerSeries (Fin 2) K := NoZeroDivisors.to_isDomain _
  have hU := wSeriesSubstUnique_holds.{u}
  obtain ⟨Q, hQT, hQ⟩ := div_diag _ (chord_subst_inverse_mem hw) $ Fp_diag hw
  have hQc : cc Q = -1 := by
    have h := Fp_lin hw
    rw [hQ, WeierstrassChordSeries.L_mul] at h
    simpa [WeierstrassChordSeries.L_X] using h

  have hUs := fun s hs => hU K W w hw (Fin 2) s hs
  have h0 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 0) $ by simp).1
  have h1 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 1) $ by simp).1
  have hW0 : Wi w 0 = lam w * MvPowerSeries.X 0 + nu w := by unfold nu
                                                             ring
  have hW1 : Wi w 1 = lam w * MvPowerSeries.X 1 + nu w := by
    have := lam_mul w
    unfold nu; linear_combination -this
  change WeierstrassChordSeries.G _ _ _ _ _ _ (Wi w 0) = 0 at h0
  change WeierstrassChordSeries.G _ _ _ _ _ _ (Wi w 1) = 0 at h1
  have hinv := MvPowerSeries.mul_inv_cancel _ (by rw [constantCoeff_chordCoeffCubic hw]; exact one_ne_zero)
  have he1 : c3 (ca W.a₂) (ca W.a₄) (ca W.a₆) (lam w) *
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + z3 W w) +
      c2 (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) (lam w) (nu w) = 0 := by
    change C3 W w * _ + C2 W w = 0
    rw [z3]
    linear_combination (-C2 W w) * hinv
  rw [hW0] at h0
  rw [hW1] at h1
  obtain ⟨-, -, he3⟩ := vieta X_ne h0 h1 he1
  change C3 W w * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * z3 W w)
    + c0 (ca W.a₃) (ca W.a₆) (nu w) = 0 at he3
  simp [c0] at he3
  obtain ⟨Ua, hUa⟩ : ∃ U, U = (wU w).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) :=
    ⟨_, rfl⟩
  obtain ⟨Ub, hUb⟩ : ∃ U, U = (wU w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E,
      E = 1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2 := ⟨_, rfl⟩
  have hUac := hUa ▸ U_cc hw 0
  have hUbc := hUb ▸ U_cc hw 1
  have hEc : cc E = 1 := by rw [hE]
                            simp [nu_cc hw]
  have hIa := MvPowerSeries.mul_inv_cancel _ (by rw [hUac]; exact one_ne_zero)
  have hIb := MvPowerSeries.mul_inv_cancel _ (by rw [hUbc]; exact one_ne_zero)
  have hIe := MvPowerSeries.mul_inv_cancel _ (by rw [hEc]; exact one_ne_zero)
  have hIq := MvPowerSeries.mul_inv_cancel _ (by rw [hQc]; exact neg_ne_zero.mpr one_ne_zero)
  have hWa := hUa ▸ Wi_eq hw 0
  have hWb := hUb ▸ Wi_eq hw 1
  have hlam := lam_mul w
  have hν2 : (MvPowerSeries.X 1 - MvPowerSeries.X 0) * nu w =
      MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ 3 * Ua
        - MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 3 * Ub := by
    unfold nu
    linear_combination (-MvPowerSeries.X 0) * hlam + MvPowerSeries.X 1 * hWa
      - MvPowerSeries.X 0 * hWb
  have key0 : MvPowerSeries.X 0 * MvPowerSeries.X 1 *
      ((MvPowerSeries.X 1 - MvPowerSeries.X 0) * C3 W w * z3 W w
        + (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * Ua * Ub * E) = 0 := by
    rw [hE]
    linear_combination (MvPowerSeries.X 1 - MvPowerSeries.X 0) * he3
      + (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 1 ^ 2 * Ub
        * (1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2)) * hIa
      - (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ 2 * Ua
        * (1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2)) * hIb
      + (1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2) * hν2
  have key1 := (mul_eq_zero.mp key0).resolve_left
    $ mul_ne_zero (WeierstrassCoordinateSubstitution.X_ne_zero' 0) $ WeierstrassCoordinateSubstitution.X_ne_zero' 1
  have hdc : cc (dd W w) ≠ 0 := by rw [dd_cc hw]
                                   exact neg_ne_zero.mpr one_ne_zero
  have hF : WeierstrassChordSeries.F2 W w * dd W w = z3 W w := by
    rw [WeierstrassChordSeries.F2, mul_assoc, mul_comm _ $ dd W w, MvPowerSeries.mul_inv_cancel _ hdc, mul_one]
  rw [← hF] at key1
  refine ⟨-(C3 W w * dd W w * Ua⁻¹ * Ub⁻¹ * E⁻¹ * Q⁻¹), ?_, ?_, ?_⟩
  have hUaT : Ua⁻¹ ∈ T W := inv_mem_integralSeries (hUa ▸ subst_wU_X_mem_T_of_wFixed hw 0) (by rw [hUac]; exact one_ne_zero)
    (by rw [hUac, inv_one]; exact Subalgebra.one_mem _)
  have hUbT := inv_mem_integralSeries (hUb ▸ subst_wU_X_mem_T_of_wFixed hw 1) (by rw [hUbc]; exact one_ne_zero)
    (by rw [hUbc, inv_one]; exact Subalgebra.one_mem _)
  have hET : E ∈ T W := by
    rw [hE]
    exact (T W).sub_mem ((T W).sub_mem (T W).one_mem
      $ (T W).mul_mem (constSeries_mem_integralSeries $ by simp) $ intercept_mem_integralSeries hw)
      $ (T W).mul_mem (constSeries_mem_integralSeries $ by simp) $ (T W).pow_mem (intercept_mem_integralSeries hw) 2
  have hEiT := inv_mem_integralSeries hET (by rw [hEc]; exact one_ne_zero)
    (by rw [hEc, inv_one]; exact Subalgebra.one_mem _)
  have hQiT := inv_mem_integralSeries hQT (by rw [hQc]; exact neg_ne_zero.mpr one_ne_zero)
    (by rw [hQc, inv_neg, inv_one]; exact Subalgebra.neg_mem _ $ Subalgebra.one_mem _)
  exact (T W).neg_mem $ (T W).mul_mem ((T W).mul_mem ((T W).mul_mem ((T W).mul_mem
    ((T W).mul_mem (C3_mem_T_of_wFixed hw) $ dd_mem_T_of_wFixed hw) hUaT) hUbT) hEiT) hQiT
  simp [MvPowerSeries.constantCoeff_inv, constantCoeff_chordCoeffCubic hw, dd_cc hw, hUac, hUbc, hEc, hQc]
  rw [hQ, ← hUa, ← hUb]
  linear_combination (Ua⁻¹ * Ub⁻¹ * E⁻¹ * Q⁻¹ * Q) * key1
    - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * (Ub * Ub⁻¹) * (E * E⁻¹)
      * (Q * Q⁻¹) * hIa
    - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * (E * E⁻¹) * (Q * Q⁻¹) * hIb
    - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * (Q * Q⁻¹) * hIe
    - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * hIq

end CubeTwoAlt

theorem cube_two : Formalism.ELL.CubeTwo.{u} := by
  intro K _ W w F hw hF0 hch
  have hF := CubeTwoAlt.chord_series_eq_F2 hw hF0 hch
  subst hF
  obtain ⟨c, hcT, hcc, hc⟩ := CubeTwoAlt.main hw
  exact ⟨c, fun d => WeierstrassChordSeries.mem_T.mp hcT d, hcc, hc⟩

end Formalism.ELL
end
section
namespace Formalism.ELL









theorem wSeriesUnique : WSeriesUnique.{u} := wSeriesExistsUnique_holds
theorem wSubstUnique : WSubstUnique.{u} := wSeriesSubstUnique_holds



theorem cubeTwo : CubeTwo.{u} := cube_two

end Formalism.ELL
end
section
open scoped BigOperators


namespace Formalism.DworkPowerSeriesWeights

variable {K : Type u} [NormedField K] {ι : Type v}

def Integral (f : MvPowerSeries ι K) : Prop :=
  ∀ n : ι →₀ ℕ, ‖MvPowerSeries.coeff n f‖ ≤ 1

def mvExp [CharZero K] (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  PowerSeries.subst f $ PowerSeries.exp K

end Formalism.DworkPowerSeriesWeights
end
section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def wZeta (L : PeriodPair) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)

def wFactor (l z : ℂ) : ℂ := (1 - z / l) * Complex.exp (z / l + z ^ 2 / (2 * l ^ 2))

def wSigma (L : PeriodPair) (z : ℂ) : ℂ := z * ∏' l : L.lattice, wFactor (l : ℂ) z

def wEta (L : PeriodPair) : ℂ →ₗ[ℝ] ℂ :=
  L.basis.constr ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)]

def area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|

def s2 (L : PeriodPair) : ℂ :=
  (wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁) / (L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁)

def sgStar (L : PeriodPair) (z : ℂ) : ℂ := wSigma L z * Complex.exp (-(s2 L) * z ^ 2 / 2)

def herm (L : PeriodPair) (z w : ℂ) : ℂ := z * conj w / (area L : ℂ)

def opU (L : PeriodPair) (x : ℂ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F (z + x) * Complex.exp (-(Real.pi : ℂ) * herm L z x - (Real.pi : ℂ) * herm L x x / 2)

open Classical in

def semiChar (L : PeriodPair) (ω : ℂ) : ℂ := if ω / 2 ∈ L.lattice then 1 else -1

def th0 (L : PeriodPair) (t : ℂ) (z : ℂ) : ℂ := opU L t (sgStar L) z / opU L t (sgStar L) 0

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def ZetaSummable : Prop :=
  ∀ (L : PeriodPair) (z : ℂ),
    Summable fun l : L.lattice => 1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2

def ZetaHasDeriv : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → HasDerivAt (wZeta L) (-(L.weierstrassP z)) z

def ZetaOdd : Prop := ∀ (L : PeriodPair) (z : ℂ), wZeta L (-z) = -wZeta L z


def ZetaQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice → z ∉ L.lattice → wZeta L (z + ω) = wZeta L z + wEta L ω

def SigmaSummable : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), Summable fun l : L.lattice => ‖wFactor (l : ℂ) z - 1‖

def SigmaProdLU : Prop :=
  ∀ L : PeriodPair, HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z)
    (fun z => ∏' l : L.lattice, wFactor (l : ℂ) z) Set.univ

def SigmaEntire : Prop := ∀ L : PeriodPair, Differentiable ℂ $ wSigma L

def SigmaOdd : Prop := ∀ (L : PeriodPair) (z : ℂ), wSigma L (-z) = -wSigma L z

def SigmaZero : Prop := ∀ (L : PeriodPair) (z : ℂ), wSigma L z = 0 ↔ z ∈ L.lattice

def SigmaSimple : Prop :=
  ∀ L : PeriodPair, deriv (wSigma L) 0 = 1 ∧ ∀ z ∈ L.lattice, deriv (wSigma L) z ≠ 0

def SigmaLogDeriv : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → HasDerivAt (wSigma L) (wZeta L z * wSigma L z) z

def SigmaLogDeriv2 : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice →
    wSigma L z * iteratedDeriv 2 (wSigma L) z - deriv (wSigma L) z ^ 2
      = -(L.weierstrassP z) * wSigma L z ^ 2

def SigmaQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice →
    wSigma L (z + ω) = semiChar L ω * Complex.exp (wEta L ω * (z + ω / 2)) * wSigma L z

def EtaEisenstein : Prop :=
  ∀ L : PeriodPair,
    wEta L L.ω₁ = L.ω₁ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 ∧
    wEta L L.ω₂ = L.ω₂ * ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2

def Legendre : Prop :=
  ∀ L : PeriodPair,
    wEta L L.ω₁ * L.ω₂ - wEta L L.ω₂ * L.ω₁
      = (if 0 < (L.ω₂ / L.ω₁).im then 1 else -1) * (2 * (Real.pi : ℂ) * Complex.I)

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F


def AreaPos : Prop := ∀ L : PeriodPair, 0 < area L


def EtaSplit : Prop :=
  ∀ (L : PeriodPair) (x : ℂ), wEta L x = s2 L * x + ((Real.pi : ℂ) / (area L : ℂ)) * conj x

def QuasiPeriodConstUnique : Prop :=
  ∀ (L : PeriodPair) (s : ℂ),
    (∀ ω ∈ L.lattice, wEta L ω = s * ω + ((Real.pi : ℂ) / (area L : ℂ)) * conj ω) → s = s2 L





def SgStarQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice →
    sgStar L (z + ω) = semiChar L ω
      * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * sgStar L z


def SgStarBasic : Prop :=
  ∀ L : PeriodPair, Differentiable ℂ (sgStar L) ∧ (∀ z, sgStar L (-z) = -sgStar L z) ∧
    (∀ z, sgStar L z = 0 ↔ z ∈ L.lattice) ∧
    deriv (sgStar L) 0 = 1 ∧ iteratedDeriv 3 (sgStar L) 0 = -3 * s2 L








def ThetaZeroLogDerivative : Prop :=
  ∀ (L : PeriodPair) (ω₀ z : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → z + ω₀ / 2 ∉ L.lattice →
    HasDerivAt (th0 L $ ω₀ / 2)
      ((wZeta L (z + ω₀ / 2) - wZeta L (ω₀ / 2) - s2 L * z) * th0 L (ω₀ / 2) z) z

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def IsPeriodic (L : PeriodPair) (f : ℂ → ℂ) : Prop := ∀ ω ∈ L.lattice, ∀ z, f (z + ω) = f z

def EllipticEntire : Prop :=
  ∀ (L : PeriodPair) (f : ℂ → ℂ), Differentiable ℂ f → IsPeriodic L f → ∀ z, f z = f 0

def EllipticNoPole : Prop :=
  ∀ (L : PeriodPair) (f : ℂ → ℂ), (∀ z, MeromorphicAt f z) → IsPeriodic L f →
    (∀ z, 0 ≤ meromorphicOrderAt f z) → ∃ c : ℂ, ∀ z, ContinuousAt f z → f z = c

def EllipticOnePole : Prop :=
  ∀ (L : PeriodPair) (f : ℂ → ℂ) (p : ℂ), (∀ z, MeromorphicAt f z) → IsPeriodic L f →
    (∀ z, z - p ∉ L.lattice → 0 ≤ meromorphicOrderAt f z) → -1 ≤ meromorphicOrderAt f p →
    ∃ c : ℂ, ∀ z, ContinuousAt f z → f z = c

def SigmaOrder : Prop :=
  ∀ (L : PeriodPair) (a b z : ℂ), a ≠ 0 →
    meromorphicOrderAt (fun w => wSigma L $ a * w + b) z
      = (by classical exact if a * z + b ∈ L.lattice then 1 else 0)

def SigmaAdd : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice →
    wSigma L (z + w) * wSigma L (z - w)
      = -(wSigma L z ^ 2 * wSigma L w ^ 2 * (L.weierstrassP z - L.weierstrassP w))

def SgStarAdd : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice →
    sgStar L (z + w) * sgStar L (z - w)
      = -(sgStar L z ^ 2 * sgStar L w ^ 2 * (L.weierstrassP z - L.weierstrassP w))

def PInjective : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice →
    (L.weierstrassP z = L.weierstrassP w ↔ z - w ∈ L.lattice ∨ z + w ∈ L.lattice)

def PDerivZero : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → (L.derivWeierstrassP z = 0 ↔ 2 * z ∈ L.lattice)

def SigmaDouble : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice →
    wSigma L (2 * z) = -(L.derivWeierstrassP z) * wSigma L z ^ 4





def ThetaLine : Prop :=
  ∀ (L : PeriodPair) (F : ℂ → ℂ), Differentiable ℂ F →
    (∀ ω ∈ L.lattice, ∀ z, semiChar L ω * opU L ω F z = F z) → ∃ c : ℂ, ∀ z, F z = c * sgStar L z

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc

def LatticeOnly : Prop :=
  ∀ L L' : PeriodPair, L.lattice = L'.lattice →
    wZeta L = wZeta L' ∧ wSigma L = wSigma L' ∧ wEta L = wEta L' ∧ area L = area L' ∧ s2 L = s2 L' ∧
    sgStar L = sgStar L' ∧ L.weierstrassP = L'.weierstrassP ∧ L.g₂ = L'.g₂ ∧ L.g₃ = L'.g₃

def Homogeneity : Prop :=
  ∀ (L : PeriodPair) (c : ℂ) (hc : c ≠ 0),
    (∀ z, z ∈ (scalePair L c hc).lattice ↔ c⁻¹ * z ∈ L.lattice) ∧
    (∀ z, wZeta (scalePair L c hc) (c * z) = c⁻¹ * wZeta L z) ∧
    (∀ z, wSigma (scalePair L c hc) (c * z) = c * wSigma L z) ∧
    (∀ z, (scalePair L c hc).weierstrassP (c * z) = (c ^ 2)⁻¹ * L.weierstrassP z) ∧
    (∀ z, wEta (scalePair L c hc) (c * z) = c⁻¹ * wEta L z) ∧
    area (scalePair L c hc) = ‖c‖ ^ 2 * area L ∧
    s2 (scalePair L c hc) = (c ^ 2)⁻¹ * s2 L ∧
    (∀ z, sgStar (scalePair L c hc) (c * z) = c * sgStar L z) ∧
    (∀ t z, th0 (scalePair L c hc) (c * t) (c * z) = th0 L t z) ∧
    (scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ ∧ (scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃

def MulStable (L : PeriodPair) (α : ℂ) : Prop := ∀ ω ∈ L.lattice, α * ω ∈ L.lattice

def IsKerReps (L : PeriodPair) (α : ℂ) (S : Finset ℂ) : Prop :=
  (∀ P ∈ S, α * P ∈ L.lattice ∧ P ∉ L.lattice) ∧
  (∀ P ∈ S, ∀ Q ∈ S, P - Q ∈ L.lattice → P = Q) ∧
  (∀ z, α * z ∈ L.lattice → z ∉ L.lattice → ∃ P ∈ S, z - P ∈ L.lattice)

def KerRepsExist : Prop :=
  ∀ (L : PeriodPair) (α : ℂ), α ≠ 0 → MulStable L α → ∃ S : Finset ℂ, IsKerReps L α S

def KerRepsCard : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ((S.card : ℝ) + 1) = Complex.normSq α

def MulStableIntegral : Prop :=
  ∀ (L : PeriodPair) (α : ℂ), MulStable L α →
    ∃ t n : ℤ, α + conj α = (t : ℂ) ∧ α * conj α = (n : ℂ) ∧ α ^ 2 - (t : ℂ) * α + (n : ℂ) = 0

def IsogenyP : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∀ z, α * z ∉ L.lattice →
      α ^ 2 * L.weierstrassP (α * z)
        = L.weierstrassP z + ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)

def IsogenySigma : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∀ z, z ∉ L.lattice →
      sgStar L (α * z) ^ 2
        = α ^ 2 * sgStar L z ^ (2 * (S.card + 1)) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP P)

def QuasiPeriodConstIsogeny : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    (α ^ 2 - (Complex.normSq α : ℂ)) * s2 L = ∑ P ∈ S, L.weierstrassP P

def HalfShift : Prop :=
  ∀ (L : PeriodPair) (t z : ℂ), t ∉ L.lattice → 2 * t ∈ L.lattice → z ∉ L.lattice → z + t ∉ L.lattice →
    (L.weierstrassP (z + t) - L.weierstrassP t) * (L.weierstrassP z - L.weierstrassP t)
      = 3 * L.weierstrassP t ^ 2 - L.g₂ / 4

def PSecond : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice →
    HasDerivAt L.derivWeierstrassP (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z

def TranslateProduct : Prop :=
  ∀ (L : PeriodPair) (P Q z : ℂ), Q ∉ L.lattice → z + P ∉ L.lattice →
    opU L (P + Q) (sgStar L) z * opU L (P - Q) (sgStar L) z
      = opU L Q (sgStar L) 0 ^ 2 * (L.weierstrassP Q - L.weierstrassP (z + P))
        * opU L P (sgStar L) z ^ 2

end Formalism.L2.Th1.F
end
section
open Filter Topology

namespace Formalism.L2.Th1.F
namespace AnalyticIdentityTheoremsZetaFacts

lemma term_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) + 1 / l + s / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hd : ‖l‖ / 2 ≤ ‖s - l‖ := by
    have h1 := norm_sub_norm_le l s
    rw [norm_sub_rev] at h1
    linarith
  have hdpos : 0 < ‖s - l‖ := by linarith
  have hl := norm_pos_iff.mp hl0
  have hsl := norm_pos_iff.mp hdpos
  have key : 1 / (s - l) + 1 / l + s / l ^ 2 = s ^ 2 / (l ^ 2 * (s - l)) := by
    field_simp
    ring
  rw [key, norm_div, norm_mul, norm_pow, norm_pow,
    show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hl0.le, Real.rpow_natCast]
  calc ‖s‖ ^ 2 / (‖l‖ ^ 2 * ‖s - l‖) ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by
        apply div_le_div₀ (by positivity) _ $ mul_pos (pow_pos hl0 2) $ half_pos hl0
        exact mul_le_mul_of_nonneg_left hd $ by positivity
        exact pow_le_pow_left₀ (norm_nonneg s) hs.le 2
    _ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ := by
        field_simp

def zetaExcept (L : PeriodPair) (l₀ z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l.1 = l₀ then 0 else (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)

lemma hasSumLU_zetaExcept (L : PeriodPair) (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦
        if l.1 = l₀ then 0 else (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2))
      (zetaExcept L l₀) := by
  have hs3 :=
    ZLattice.summable_norm_rpow L.lattice (-3) (by rw [L.finrank_lattice]; norm_num)
  refine L.hasSumLocallyUniformly_aux _ (fun r l => 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun r _ => hs3.mul_left $ 2 * r ^ 2) fun r hr => ?_
  filter_upwards [Filter.eventually_ge_atTop $ 2 * r] with R hR x hx l hl
  split_ifs
  rw [norm_zero]
  positivity
  exact term_bound r hr x hx l (by rw [hl]; exact hR)


lemma hasSumLU_wZeta (L : PeriodPair) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
      $ wZeta L := by
  have hs3 :=
    ZLattice.summable_norm_rpow L.lattice (-3) (by rw [L.finrank_lattice]; norm_num)
  refine L.hasSumLocallyUniformly_aux _ (fun r l => 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun r _ => hs3.mul_left $ 2 * r ^ 2) fun r hr => ?_
  filter_upwards [Filter.eventually_ge_atTop $ 2 * r] with R hR x hx l hl
  apply term_bound r hr x hx l
  rwa [hl]
private lemma differentiableOn_of_hasSumLocallyUniformlyOn' {ι : Type*} {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (h : HasSumLocallyUniformlyOn F g U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U) :
    DifferentiableOn ℂ g U := by
  exact h.differentiableOn
    (Filter.Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hF i) hU

private lemma hasDerivAt_inv_sub_add_inv_add_div_sq (l z : ℂ) (h : z - l ≠ 0) :
    HasDerivAt (fun z ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  have e : (fun w => 1 / (w - l) + 1 / l + w / l ^ 2) =
      fun w => (w - l)⁻¹ + 1 / l + w / l ^ 2 := by
    funext w
    rw [one_div]
  rw [e]
  apply ((((hasDerivAt_inv h).comp z $ (hasDerivAt_id' z).sub_const l).add_const $ 1 / l).add $ (hasDerivAt_id' z).div_const $ l ^ 2).congr_deriv
  ring
lemma differentiableOn_zetaExcept (L : PeriodPair) (l₀ : ℂ) :
    DifferentiableOn ℂ (zetaExcept L l₀) (L.lattice \ {l₀})ᶜ := by
  refine differentiableOn_of_hasSumLocallyUniformlyOn' (hasSumLU_zetaExcept L l₀).hasSumLocallyUniformlyOn (fun l => ?_)
    L.isOpen_compl_lattice_diff
  by_cases h : (l : ℂ) = l₀
  simp only [h, ↓reduceIte]
  exact differentiableOn_const 0
  simp only [h, ↓reduceIte]
  intro z hz
  exact (hasDerivAt_inv_sub_add_inv_add_div_sq l z $ by
      intro e
      apply hz
      rw [sub_eq_zero.mp e]
      exact ⟨l.2, h⟩).differentiableAt.differentiableWithinAt

lemma zetaExcept_zero_add (L : PeriodPair) (z : ℂ) : zetaExcept L 0 z + 1 / z = wZeta L z := by
  refine (((hasSumLU_zetaExcept L 0).hasSum (x := z)).add $ hasSum_ite_eq (0 : L.lattice) $ 1 / z).unique ?_
  convert ((hasSumLU_wZeta L).hasSum (x := z)) using 1
  funext l
  by_cases hl : l = 0
  subst hl
  simp
  have hl' : (l : ℂ) ≠ 0 := by
    intro h
    apply hl
    exact Subtype.ext h
  simp [hl, hl']

lemma zetaExcept_zero_zero (L : PeriodPair) : zetaExcept L 0 0 = 0 := by
  have h : ∀ l, (if (l : ℂ) = 0 then 0 else
      (1 / (0 - (l : ℂ)) + 1 / (l : ℂ) + 0 / (l : ℂ) ^ 2)) = 0 := by
    intro l
    split_ifs
    rfl
    rw [zero_sub, zero_div, add_zero, one_div_neg_eq_neg_one_div, neg_add_cancel]
  simp [zetaExcept, h, tsum_zero]

lemma hasDerivAt_term (l z : ℂ) (h : z - l ≠ 0) :
    HasDerivAt (fun z ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  exact hasDerivAt_inv_sub_add_inv_add_div_sq l z h

private lemma hasSum_deriv_of_hasSumLocallyUniformlyOn {ι : Type*} {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (h : HasSumLocallyUniformlyOn F g U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) : HasSum (fun i => deriv (F i) z) $ deriv g z := by
  have hd := h.deriv
    (Filter.Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hF i) hU
  exact HasSumLocallyUniformlyOn.hasSum (by
      refine hd.congr fun s x hx => ?_
      have he : (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, F i := by
        funext y
        simp [Finset.sum_apply]
      simp [Function.comp_apply]
      rw [he, deriv_sum fun i _ => (hF i).differentiableAt $ hU.mem_nhds hx]) hz

lemma eqOn_deriv_wZeta (L : PeriodPair) :
    Set.EqOn (deriv $ wZeta L) (fun z ↦ -(L.weierstrassP z)) (L.lattice : Set ℂ)ᶜ := by
  intro z hz
  have hs := hasSum_deriv_of_hasSumLocallyUniformlyOn (hasSumLU_wZeta L).hasSumLocallyUniformlyOn (by
      intro l w hw
      exact (hasDerivAt_term l w $ by
          intro e
          apply hw
          rw [sub_eq_zero.mp e]
          exact l.2).differentiableAt.differentiableWithinAt) (L.isClosed_lattice.isOpen_compl) hz
  have hder : (fun l : L.lattice =>
      deriv (fun w : ℂ => 1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) z) =
      fun l : L.lattice => -(1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) := by
    funext l
    have hzl : z - l ≠ 0 := by
      intro e
      apply hz
      rw [sub_eq_zero.mp e]
      exact l.2
    exact (hasDerivAt_term l z hzl).deriv
  rw [hder] at hs
  exact hs.unique (L.hasSum_weierstrassP z).neg

lemma differentiableOn_wZeta (L : PeriodPair) :
    DifferentiableOn ℂ (wZeta L) (L.lattice : Set ℂ)ᶜ := by
  refine differentiableOn_of_hasSumLocallyUniformlyOn' (hasSumLU_wZeta L).hasSumLocallyUniformlyOn (fun l => ?_)
    L.isClosed_lattice.isOpen_compl
  intro w hw
  exact (hasDerivAt_term l w $ by
      intro e
      apply hw
      rw [sub_eq_zero.mp e]
      exact l.2).differentiableAt.differentiableWithinAt

end AnalyticIdentityTheoremsZetaFacts

open AnalyticIdentityTheoremsZetaFacts

theorem zeta_summable : ZetaSummable := by
  intro L z
  exact (hasSumLU_wZeta L).hasSum.summable

theorem zeta_has_deriv : ZetaHasDeriv := by
  intro L z hz
  have := ((differentiableOn_wZeta L).differentiableAt $ (L.isClosed_lattice.isOpen_compl).mem_nhds hz).hasDerivAt
  rwa [eqOn_deriv_wZeta L hz] at this

theorem zeta_odd : ZetaOdd := by
  intro L z
  unfold wZeta
  rw [← (Equiv.neg L.lattice).tsum_eq, ← tsum_neg]
  refine tsum_congr fun l => ?_
  simp only [Equiv.neg_apply, Submodule.coe_neg]
  have h1 : -z - -(l : ℂ) = -(z - l) := by ring
  rw [h1, neg_sq, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div, neg_div]
  ring


end Formalism.L2.Th1.F
end
section
open Set (mem_univ univ)
open Filter Topology

namespace Formalism.L2.Th1.F

theorem elliptic_entire_const : EllipticEntire := by
  intro L f hf hper z
  have key : ∀ x, ∃ ω ∈ L.lattice, ‖x - ω‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ := by
    intro x
    have hx := L.basis.sum_repr x
    rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at hx
    use (⌊L.basis.repr x 0⌋ : ℂ) * L.ω₁ + (⌊L.basis.repr x 1⌋ : ℂ) * L.ω₂, PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩
    generalize L.basis.repr x 0 = a at hx ⊢
    generalize L.basis.repr x 1 = b at hx ⊢
    subst hx
    have e : a • L.ω₁ + b • L.ω₂ - ((⌊a⌋ : ℂ) * L.ω₁ + (⌊b⌋ : ℂ) * L.ω₂)
        = ((Int.fract a : ℝ) : ℂ) * L.ω₁ + ((Int.fract b : ℝ) : ℂ) * L.ω₂ := by
      simp only [Complex.real_smul, Int.fract]
      push_cast; ring
    rw [e]
    have hfr : ∀ r v, ‖((Int.fract r : ℝ) : ℂ) * v‖ ≤ ‖v‖ := by
      intro r v
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg $ Int.fract_nonneg _]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    exact (norm_add_le _ _).trans $ add_le_add (hfr a _) $ hfr b _
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) $ ‖L.ω₁‖ + ‖L.ω₂‖).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  exact hf.apply_eq_apply_of_bounded (by
      rw [isBounded_iff_forall_norm_le]
      use C
      rintro _ ⟨x, rfl⟩
      obtain ⟨ω, hω, hxω⟩ := key x
      have : f x = f (x - ω) := by
        have := hper ω hω $ x - ω
        rwa [sub_add_cancel] at this
      rw [this]
      apply hC _
      simpa using hxω) z 0

namespace Elliptic

lemma eq_of_eventuallyEq_nhdsNE {g₁ g₂ : ℂ → ℂ} {z : ℂ} (h₁ : ContinuousAt g₁ z)
    (h₂ : ContinuousAt g₂ z) (h : g₁ =ᶠ[𝓝[≠] z] g₂) : g₁ z = g₂ z :=
  tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    $ (h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm

lemma tendsto_add_nhdsNE (z ω : ℂ) : Tendsto (fun w => w + ω) (𝓝[≠] z) (𝓝[≠] (z + ω)) := by
  rw [tendsto_nhdsWithin_iff]
  use ((continuous_add_const ω).tendsto z).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact fun h => hw $ add_right_cancel h

end Elliptic

theorem elliptic_no_pole_const : EllipticNoPole := by
  intro L f hmer hper hord
  have hM : MeromorphicOn f univ := fun z _ => hmer z
  set g := toMeromorphicNFOn f univ with hg_def
  have heq : ∀ z, g =ᶠ[𝓝[≠] z] f := fun z =>
    hM.toMeromorphicNFOn_eq_self_on_nhdsNE $ mem_univ z
  have han : ∀ z, AnalyticAt ℂ g z := fun z => by
    rw [← (meromorphicNFOn_toMeromorphicNFOn f univ $ mem_univ z).meromorphicOrderAt_nonneg_iff_analyticAt, meromorphicOrderAt_congr $ heq z]
    exact hord z
  have hcont : ∀ z, ContinuousAt g z := fun z => (han z).continuousAt
  have hdiff : Differentiable ℂ g := fun z => (han z).differentiableAt
  have hpg : IsPeriodic L g := by
    intro ω hω z
    have hc1 : ContinuousAt (fun w => g $ w + ω) z :=
      show ContinuousAt (g ∘ fun w => w + ω) z from
        (hcont $ z + ω).comp_of_eq (continuous_add_const ω).continuousAt rfl
    have h2 : (fun w => g $ w + ω) =ᶠ[𝓝[≠] z] g := by
      filter_upwards [(Elliptic.tendsto_add_nhdsNE z ω).eventually $ heq $ z + ω, heq z] with w hw1 hw2
      rw [hw1, hper ω hω w, hw2]
    exact Elliptic.eq_of_eventuallyEq_nhdsNE hc1 (hcont z) h2
  refine ⟨g 0, fun z hz => ?_⟩
  rw [← elliptic_entire_const L g hdiff hpg z]
  exact Elliptic.eq_of_eventuallyEq_nhdsNE hz (hcont z) (heq z).symm

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate Topology
open Filter

namespace Formalism.L2.Th1.F

namespace EtaEis

lemma tsum_int_telescope (a : ℤ → ℂ) (hs : Summable fun m => a m - a (m + 1))
    (h1 : Tendsto (fun N : ℕ => a (N : ℤ)) atTop $ 𝓝 0)
    (h2 : Tendsto (fun N : ℕ => a $ -(N : ℤ)) atTop $ 𝓝 0) :
    ∑' m : ℤ, (a m - a (m + 1)) = 0 := by
  have hH : HasSum (fun N : ℕ => (a (N : ℤ) - a ((N : ℤ) + 1))
      + (a (-((N : ℤ) + 1)) - a (-((N : ℤ) + 1) + 1))) (∑' m : ℤ, (a m - a (m + 1))) := by
    exact hs.hasSum.nat_add_neg_add_one
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((a (i : ℤ) - a ((i : ℤ) + 1))
      + (a (-((i : ℤ) + 1)) - a (-((i : ℤ) + 1) + 1))) = a (-(N : ℤ)) - a (N : ℤ) := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have e1 : -((k : ℤ) + 1) + 1 = -(k : ℤ) := by ring
      rw [e1]
      push_cast
      ring
  have hlim := (h2.sub h1).congr fun N => (hpart N).symm
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hH.tendsto_sum_nat hlim

lemma tendsto_one_div_linear (c w : ℂ) (hw : w ≠ 0) :
    Tendsto (fun N : ℕ => 1 / (c + (N : ℂ) * w)) atTop $ 𝓝 0 := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹) atTop $ 𝓝 0 := by
    first
    | exact RCLike.tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)
    | (have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_nhds_zero_nat
       simpa using h)
    | (rw [Metric.tendsto_atTop]
       intro ε hε
       obtain ⟨K, hK⟩ := exists_nat_gt $ 1 / ε
       refine ⟨K, fun n hn => ?_⟩
       have hKpos : (0 : ℝ) < 1 / ε := by positivity
       have hn' : (1 / ε : ℝ) < n := lt_of_lt_of_le hK $ by exact_mod_cast hn
       have hnpos : (0 : ℝ) < n := lt_trans hKpos hn'
       have hnorm : ‖((n : ℂ))⁻¹‖ = ((n : ℝ))⁻¹ := by simp
       rw [dist_zero_right, hnorm, inv_eq_one_div, div_lt_iff₀ hnpos]
       rw [div_lt_iff₀ hε] at hn'
       linarith)
  have h2 : Tendsto (fun N : ℕ => c * ((N : ℂ))⁻¹ + w) atTop $ 𝓝 $ c * 0 + w :=
    (hinv.const_mul c).add_const w
  rw [mul_zero, zero_add] at h2
  have h3 : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * (c * ((N : ℂ))⁻¹ + w)⁻¹) atTop $ 𝓝 $ 0 * w⁻¹ :=
    hinv.mul $ h2.inv₀ hw
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr $ by omega
  rw [one_div, ← mul_inv]
  congr 1
  linear_combination c * mul_inv_cancel₀ hN0

def tm (l x : ℂ) : ℂ := 1 / (x - l) + 1 / l + x / l ^ 2

private theorem summable_inv_sq_nat_mul_add (c w : ℂ) (hw : w ≠ 0) :
    Summable fun N : ℕ => 1 / ((N : ℂ) * w + c) ^ 2 := by
  have hw' := norm_pos_iff.mpr hw
  obtain ⟨K, hK⟩ := exists_nat_gt $ 2 * ‖c‖ / ‖w‖
  have hg : Summable fun N : ℕ => 4 / ‖w‖ ^ 2 * (1 / ((N + K : ℕ) : ℝ) ^ 2) := by
    have h0 : Summable fun N : ℕ => 1 / (N : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
    exact ((summable_nat_add_iff K).mpr h0).mul_left _
  refine (summable_nat_add_iff K).mp
    $ Summable.of_norm $ hg.of_nonneg_of_le (fun _ => norm_nonneg _) fun N => ?_
  have hMK : K ≤ N + K := Nat.le_add_left K N
  generalize N + K = M at hMK ⊢
  have h2 : 2 * ‖c‖ < (M : ℝ) * ‖w‖ := by
    exact (div_lt_iff₀ hw').mp $ lt_of_lt_of_le hK $ by exact_mod_cast hMK
  have h4 : ‖(M : ℂ) * w‖ ≤ ‖(M : ℂ) * w + c‖ + ‖c‖ := by
    calc ‖(M : ℂ) * w‖ = ‖((M : ℂ) * w + c) - c‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖(M : ℂ) * w + c‖ + ‖c‖ := norm_sub_le _ _
  simp at h4
  have h3 : (M : ℝ) * ‖w‖ / 2 ≤ ‖(M : ℂ) * w + c‖ := by linarith [norm_nonneg c]
  have h5 : 0 < (M : ℝ) * ‖w‖ / 2 := by linarith [norm_nonneg c]
  rw [norm_div, norm_one, norm_pow]
  calc 1 / ‖(M : ℂ) * w + c‖ ^ 2 ≤ 1 / ((M : ℝ) * ‖w‖ / 2) ^ 2 :=
        one_div_le_one_div_of_le (pow_pos h5 2) (by rw [sq, sq]; exact mul_le_mul h3 h3 h5.le $ norm_nonneg _)
    _ = 4 / ‖w‖ ^ 2 * (1 / (M : ℝ) ^ 2) := by ring

lemma summable_inv_sq (u v : ℂ) (hu : u ≠ 0) (n : ℤ) :
    Summable fun m : ℤ => 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by
  exact summable_int_iff_summable_nat_and_neg.mpr ⟨by
      refine (summable_inv_sq_nat_mul_add ((n : ℂ) * v) u hu).congr fun N => ?_
      simp [Int.cast_natCast], by
      refine (summable_inv_sq_nat_mul_add ((n : ℂ) * v) (-u) $ neg_ne_zero.mpr hu).congr fun N => ?_
      rw [Int.cast_neg, Int.cast_natCast, neg_mul, mul_neg]⟩

private theorem tm_half_sub_tm_neg_half (u l : ℂ) :
    tm l (u / 2) - tm l (-(u / 2))
      = 1 / (u / 2 - l) - 1 / (u / 2 - (l + u)) + u * (1 / l ^ 2) := by
  unfold tm
  rw [show -(u / 2) - l = u / 2 - (l + u) by ring]
  ring

private theorem tsum_zeta_half_diff_eq_mul_tsum_inv_sq (u v : ℂ) (hu : u ≠ 0) (n : ℤ)
    (hfib : Summable fun m : ℤ => tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2))) :
    ∑' m : ℤ, (tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2)))
      = u * ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by
  have hq := summable_inv_sq u v hu n
  have hsplit : ∀ m : ℤ, tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2))
      = (1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
          - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v)))
        + u * (1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) := by
    intro m
    rw [tm_half_sub_tm_neg_half, Int.cast_add, Int.cast_one,
      show ((m : ℂ) + 1) * u + (n : ℂ) * v = (m : ℂ) * u + (n : ℂ) * v + u by ring]
  have htel : Summable fun m : ℤ => 1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
      - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v)) := by
    refine (hfib.sub $ hq.mul_left u).congr fun m => ?_
    rw [hsplit m]
    ring
  have ht :=
    tsum_int_telescope (fun k : ℤ => 1 / (u / 2 - ((k : ℂ) * u + (n : ℂ) * v))) htel (by
        refine (tendsto_one_div_linear (u / 2 - (n : ℂ) * v) (-u) $ neg_ne_zero.mpr hu).congr
          fun N => ?_
        push_cast
        congr 1; ring) (by
        refine (tendsto_one_div_linear (u / 2 - (n : ℂ) * v) u hu).congr fun N => ?_
        push_cast
        congr 1; ring)
  rw [tsum_congr hsplit, htel.tsum_add $ hq.mul_left u, ht, zero_add, tsum_mul_left]

lemma core (u v : ℂ) (hu : u ≠ 0)
    (hS : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) x) :
    (∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2))
      - ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2))
      = u * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by
  have hsum : Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2)
      - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2)) := (hS _).sub $ hS _
  have hfib : ∀ n : ℤ, Summable fun m : ℤ => tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2)) := by
    exact hsum.prod_factor
  have h2 : ∑' p : ℤ × ℤ, (tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2)
          - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2)))
      = ∑' n : ℤ, ∑' m : ℤ, (tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
          - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2))) := by
    exact hsum.tsum_prod' hfib
  rw [((hS _).tsum_sub $ hS _).symm, h2, ← tsum_mul_left]
  exact tsum_congr fun n => tsum_zeta_half_diff_eq_mul_tsum_inv_sq u v hu n $ hfib n

end EtaEis

open EtaEis in
theorem etaEisenstein_of (hs : ZetaSummable) (ho : ZetaOdd) : EtaEisenstein := by
  intro L
  have hu1 : L.ω₁ ≠ 0 := by
    intro h
    exact L.ω₁_div_two_notMem_lattice (by rw [h]; simp)
  have hu2 : L.ω₂ ≠ 0 := by
    intro h
    exact L.ω₂_div_two_notMem_lattice (by rw [h]; simp)

  have hS2 : ∀ x, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * L.ω₂ + (p.1 : ℂ) * L.ω₁) x := by
    intro x
    refine ((L.latticeEquivProd.symm.toEquiv.summable_iff).mpr $ hs L x).congr fun p => ?_
    simp [Function.comp, LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, tm, add_comm]
  have hZ2 : ∀ x, wZeta L x = ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * L.ω₂ + (p.1 : ℂ) * L.ω₁) x := by
    intro x
    rw [wZeta, ← L.latticeEquivProd.symm.toEquiv.tsum_eq]
    refine tsum_congr fun p => ?_
    simp [LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, tm, add_comm]
  have hS1 : ∀ x, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * L.ω₁ + (p.1 : ℂ) * L.ω₂) x := by
    intro x
    refine (((Equiv.prodComm ℤ ℤ).summable_iff).mpr $ hS2 x).congr fun p => ?_
    simp [Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]
  have hZ1 : ∀ x, wZeta L x = ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * L.ω₁ + (p.1 : ℂ) * L.ω₂) x := by
    intro x
    rw [hZ2, ← (Equiv.prodComm ℤ ℤ).tsum_eq]
    refine tsum_congr fun p => ?_
    simp [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]
  have hE1 : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by
    have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0
    simpa [wEta] using this
  constructor
  rw [hE1, ← core L.ω₁ L.ω₂ hu1 hS1, ← hZ1, ← hZ1, ho]
  ring
  have h := core L.ω₂ L.ω₁ hu2 hS2
  rw [← hZ2, ← hZ2, ho] at h
  trans 2 * wZeta L (L.ω₂ / 2)
  have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
  simpa [wEta] using this
  calc 2 * wZeta L (L.ω₂ / 2) = wZeta L (L.ω₂ / 2) - -wZeta L (L.ω₂ / 2) := by ring
    _ = _ := h
    _ = _ := by
      congr 1
      refine tsum_congr fun m => tsum_congr fun n => ?_
      rw [add_comm]

end Formalism.L2.Th1.F
end
section
open Filter Topology

namespace Formalism.L2.Th1.F
namespace IsogenyPAux

lemma P_local (L : PeriodPair) (ω : ℂ) (hω : ω ∈ L.lattice) (w : ℂ) :
    L.weierstrassP w = L.weierstrassPExcept 0 (w - ω) + 1 / (w - ω) ^ 2 := by
  have h1 := L.weierstrassPExcept_add (0 : L.lattice) $ w - ω
  have h2 := L.weierstrassP_sub_coe w ⟨ω, hω⟩
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h1 h2
  rw [← h2, ← h1]

lemma analyticAt_P (L : PeriodPair) (a b z : ℂ) (hz : a * z + b ∉ L.lattice) :
    AnalyticAt ℂ (fun w => L.weierstrassP $ a * w + b) z :=
  AnalyticAt.fun_comp (f := fun w => a * w + b) (g := L.weierstrassP)
    (L.analyticOnNhd_weierstrassP _ hz) $ by fun_prop

lemma analyticAt_PExcept (L : PeriodPair) (a z : ℂ) :
    AnalyticAt ℂ (fun w => L.weierstrassPExcept 0 $ a * (w - z)) z := by
  refine AnalyticAt.fun_comp (f := fun w => a * (w - z)) (g := L.weierstrassPExcept 0) ?_
    $ by fun_prop
  simpa using L.analyticAt_weierstrassPExcept 0

lemma eventually_notMem (L : PeriodPair) (α z : ℂ) (hα : α ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, α * w ∉ L.lattice := by
  filter_upwards [(((continuous_const.mul continuous_id).tendsto z).eventually $ L.compl_lattice_sdiff_singleton_mem_nhds $ α * z).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hne hmem
  refine hw ⟨hmem, ?_⟩
  simpa [hα] using hne

lemma ext_at (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hst : MulStable L α)
    (h1 : ∀ P ∈ T, α * P ∈ L.lattice)
    (h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q)
    (z₀ P' : ℂ) (hP' : P' ∈ T) (hz : z₀ + P' ∈ L.lattice) :
    AnalyticAt ℂ (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) z₀ ∧
    (fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P)) =ᶠ[𝓝[≠] z₀]
      fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P) := by
  constructor
  refine ((analyticAt_const.mul $ analyticAt_PExcept L α z₀).sub $ analyticAt_PExcept L 1 z₀).sub ?_
  refine Finset.analyticAt_fun_sum _ fun P hP => analyticAt_P L 1 P z₀ ?_
  intro hmem
  rw [one_mul] at hmem
  refine (Finset.mem_erase.1 hP).1 $ h2 P (Finset.mem_erase.1 hP).2 P' hP' ?_
  have := L.lattice.sub_mem hmem hz
  simpa using this
  have hαz : α * z₀ ∈ L.lattice := by
    have := L.lattice.sub_mem (hst _ hz) $ h1 P' hP'
    have e : α * (z₀ + P') - α * P' = α * z₀ := by ring
    rwa [e] at this
  filter_upwards [self_mem_nhdsWithin] with w hne
  rw [← Finset.add_sum_erase T _ hP', P_local L (α * z₀) hαz $ α * w,
    P_local L (z₀ + P') hz $ w + P']
  have e1 : α * w - α * z₀ = α * (w - z₀) := by ring
  have e2 : w + P' - (z₀ + P') = w - z₀ := by ring
  rw [e1, e2]
  simp [one_mul]
  field_simp
  ring

end IsogenyPAux

open IsogenyPAux

theorem isogenyWeierstrassP_of_ellipticNoPole (hN : EllipticNoPole) : IsogenyP := by
  intro L α S hα hst hS z hz
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have h0S : (0 : ℂ) ∉ S := fun h => (hS1 0 h).2 L.lattice.zero_mem
  set T : Finset ℂ := insert 0 S with hT
  have h1 : ∀ P ∈ T, α * P ∈ L.lattice := by
    intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    simp
    exact (hS1 P hP).1
  have h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q := by
    intro P hP Q hQ hPQ
    rcases Finset.mem_insert.1 hP with rfl | hP <;> rcases Finset.mem_insert.1 hQ with rfl | hQ
    rfl
    exact absurd (by simpa using hPQ) (hS1 Q hQ).2
    exact absurd (by simpa using hPQ) (hS1 P hP).2
    exact hS2 P hP Q hQ hPQ
  have h3 : ∀ z₀, α * z₀ ∈ L.lattice → ∃ P ∈ T, z₀ + P ∈ L.lattice := by
    intro z₀ hz₀
    by_cases hm : z₀ ∈ L.lattice
    exact ⟨0, Finset.mem_insert_self _ _, by simpa using hm⟩
    obtain ⟨P, hP, hPz⟩ := hS3 (-z₀) (by simpa using L.lattice.neg_mem hz₀)
      (fun h => hm $ by simpa using L.lattice.neg_mem h)
    use P, Finset.mem_insert_of_mem hP
    have := L.lattice.neg_mem hPz
    have e : -(-z₀ - P) = z₀ + P := by ring
    rwa [e] at this
  set f : ℂ → ℂ := fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P) with hf

  have han : ∀ z₀, α * z₀ ∉ L.lattice → AnalyticAt ℂ f z₀ := by
    intro z₀ hz₀
    have a1 : AnalyticAt ℂ (fun w => L.weierstrassP $ α * w) z₀ := by
      simpa using analyticAt_P L α 0 z₀ $ by simpa using hz₀
    refine (analyticAt_const.mul a1).sub $ Finset.analyticAt_fun_sum _ fun P hP => ?_
    have := analyticAt_P L 1 P z₀ $ by
      intro hmem
      rw [one_mul] at hmem
      apply hz₀
      have := L.lattice.sub_mem (hst _ hmem) $ h1 P hP
      have e : α * (z₀ + P) - α * P = α * z₀ := by ring
      rwa [e] at this
    simpa using this
  have hext : ∀ z₀, ∃ g, AnalyticAt ℂ g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
    intro z₀
    by_cases hz₀ : α * z₀ ∈ L.lattice
    obtain ⟨P', hP', hzP⟩ := h3 z₀ hz₀
    exact ⟨_, ext_at L α T hα hst h1 h2 z₀ P' hP' hzP⟩
    exact ⟨f, han z₀ hz₀, EventuallyEq.rfl⟩
  have hmer : ∀ z, MeromorphicAt f z := by
    intro z
    obtain ⟨g, hg, hfg⟩ := hext z
    exact hg.meromorphicAt.congr hfg.symm
  obtain ⟨c, hc⟩ := hN L f hmer (by
      intro ω hω w
      simp [hf]
      have e1 : α * (w + ω) = α * w + α * ω := by ring
      rw [e1, L.weierstrassP_add_coe (α * w) ⟨α * ω, hst ω hω⟩]
      congr 1
      refine Finset.sum_congr rfl fun P _ => ?_
      have e2 : w + ω + P = w + P + ω := by ring
      rw [e2, L.weierstrassP_add_coe (w + P) ⟨ω, hω⟩]) fun z => (hmer z).meromorphicOrderAt_nonneg_iff.2 $ hext z

  have hc0 : c = -∑ P ∈ S, L.weierstrassP P := by
    obtain ⟨ha, he⟩ := ext_at L α T hα hst h1 h2 0 0 (Finset.mem_insert_self _ _) $ by simp
    have hev : (fun _ => c) =ᶠ[𝓝[≠] 0] f := by
      filter_upwards [eventually_notMem L α 0 hα] with w hw
      exact (hc w (han w hw).continuousAt).symm
    have := Elliptic.eq_of_eventuallyEq_nhdsNE continuousAt_const ha.continuousAt $ hev.trans he
    rw [this, hT, Finset.erase_insert h0S]
    simp
  have hfz := hc z (han z hz).continuousAt
  rw [hc0] at hfz
  simp [hf, hT, Finset.sum_insert h0S, add_zero] at hfz
  rw [Finset.sum_sub_distrib]
  linear_combination hfz


end Formalism.L2.Th1.F
end
section
open Complex (exp exp_add exp_ne_zero normSq)
open Finset (induction_on prod_congr prod_const prod_empty prod_insert prod_mul_distrib sum_eq_single)
open Real (pi)
open Filter Topology
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F
namespace IsogenySigmaQuotient

variable (L : PeriodPair)

open Classical in

def ind (x : ℂ) : WithTop ℤ := if x ∈ L.lattice then 1 else 0

lemma ind_of_mem {x : ℂ} (h : x ∈ L.lattice) : ind L x = 1 := by
  simp [ind, h]

lemma ind_of_notMem {x : ℂ} (h : x ∉ L.lattice) : ind L x = 0 := by
  simp [ind, h]



private lemma meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (h : g x ≠ 0) :
    meromorphicOrderAt g x = 0 := by
  have := (meromorphicOrderAt_eq_int_iff (n := 0) hg.meromorphicAt).2 ⟨g, hg, h, by simp⟩
  simpa using this

lemma sg_order (hord : SigmaOrder) (he : SigmaEntire) (a b z : ℂ) (ha : a ≠ 0) :
    meromorphicOrderAt (fun w => sgStar L $ a * w + b) z = ind L (a * z + b) := by
  have hA : AnalyticAt ℂ (fun w => wSigma L $ a * w + b) z := by
    have hd := he L
    exact (by fun_prop : Differentiable ℂ fun w => wSigma L $ a * w + b).analyticAt z
  have hE :=
    (by fun_prop : Differentiable ℂ fun w => exp $ -(s2 L) * (a * w + b) ^ 2 / 2).analyticAt z
  have hf : (fun w => sgStar L $ a * w + b) =
      (fun w => wSigma L $ a * w + b) * fun w => exp $ -(s2 L) * (a * w + b) ^ 2 / 2 := by
    funext w
    rfl
  rw [hf, meromorphicOrderAt_mul hA.meromorphicAt hE.meromorphicAt, hord L a b z ha,
    meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hE $ exp_ne_zero _, add_zero]
  rfl

variable (α : ℂ) (S : Finset ℂ)

def num (z : ℂ) : ℂ := sgStar L (α * z) ^ 2

def fac (P z : ℂ) : ℂ := (-(sgStar L P ^ 2)⁻¹) * (sgStar L (z + P) * sgStar L (z - P))

def den (z : ℂ) : ℂ := α ^ 2 * sgStar L z ^ 2 * ∏ P ∈ S, fac L P z

def mlt (ω z : ℂ) : ℂ := exp $ (pi : ℂ) * herm L z ω + (pi : ℂ) * herm L ω ω / 2

lemma semiChar_sq (ω : ℂ) : semiChar L ω ^ 2 = 1 := by
  unfold semiChar
  split_ifs <;> norm_num

lemma sg_sq_add (hq : SgStarQuasi) (ω z : ℂ) (hω : ω ∈ L.lattice) :
    sgStar L (z + ω) ^ 2 = mlt L ω z ^ 2 * sgStar L z ^ 2 := by
  rw [hq L ω z hω]
  simp [mlt]
  linear_combination (exp ((pi : ℂ) * herm L z ω + (pi : ℂ) * herm L ω ω / 2) ^ 2 *
    sgStar L z ^ 2) * semiChar_sq L ω

lemma fac_add (hq : SgStarQuasi) (P ω z : ℂ) (hω : ω ∈ L.lattice) :
    fac L P (z + ω) = mlt L ω z ^ 2 * fac L P z := by
  have e1 : z + ω + P = z + P + ω := by ring
  have e2 : z + ω - P = z - P + ω := by ring
  have hE : exp ((pi : ℂ) * herm L (z + P) ω + (pi : ℂ) * herm L ω ω / 2) *
      exp ((pi : ℂ) * herm L (z - P) ω + (pi : ℂ) * herm L ω ω / 2) =
      exp ((pi : ℂ) * herm L z ω + (pi : ℂ) * herm L ω ω / 2) ^ 2 := by
    rw [sq, ← exp_add, ← exp_add]
    congr 1; simp only [herm]; ring
  simp only [fac, mlt]
  rw [e1, e2, hq L ω (z + P) hω, hq L ω (z - P) hω]
  linear_combination (-(sgStar L P ^ 2)⁻¹ * sgStar L (z + P) * sgStar L (z - P) * semiChar L ω ^ 2) * hE +
    (-(sgStar L P ^ 2)⁻¹ * sgStar L (z + P) * sgStar L (z - P) *
      exp ((pi : ℂ) * herm L z ω + (pi : ℂ) * herm L ω ω / 2) ^ 2) * semiChar_sq L ω

lemma den_add (hq : SgStarQuasi) (ω z : ℂ) (hω : ω ∈ L.lattice) :
    den L α S (z + ω) = (mlt L ω z ^ 2) ^ (S.card + 1) * den L α S z := by
  simp [den]
  rw [sg_sq_add L hq ω z hω, prod_congr rfl fun P _ => fac_add L hq P ω z hω,
    prod_mul_distrib, prod_const]
  ring

lemma herm_mul (z ω : ℂ) : herm L (α * z) (α * ω) = (normSq α : ℂ) * herm L z ω := by
  simp [herm, map_mul]
  rw [← Complex.mul_conj]; ring

lemma num_add (hq : SgStarQuasi) (hst : MulStable L α) (hc : (S.card : ℝ) + 1 = normSq α)
    (ω z : ℂ) (hω : ω ∈ L.lattice) :
    num L α (z + ω) = (mlt L ω z ^ 2) ^ (S.card + 1) * num L α z := by
  simp [num]
  rw [mul_add, sg_sq_add L hq (α * ω) (α * z) $ hst ω hω]
  congr 1
  have hN : (normSq α : ℂ) = ((S.card + 1 : ℕ) : ℂ) := by
    rw [← hc]
    push_cast; ring
  have key : ∀ x y, exp ((pi : ℂ) * (((S.card + 1 : ℕ) : ℂ) * x) +
      (pi : ℂ) * (((S.card + 1 : ℕ) : ℂ) * y) / 2) =
      exp ((pi : ℂ) * x + (pi : ℂ) * y / 2) ^ (S.card + 1) := by
    intro x y
    rw [← Complex.exp_nat_mul]; congr 1; ring
  simp [mlt]
  rw [herm_mul L α z ω, herm_mul L α ω ω, hN, key]
  ring

lemma sg_add_order (hord : SigmaOrder) (he : SigmaEntire) (P z : ℂ) :
    meromorphicOrderAt (fun w : ℂ => sgStar L $ w + P) z = ind L (z + P) := by
  have := sg_order L hord he 1 P z one_ne_zero
  simp [one_mul] at this
  exact this

lemma sg_sub_order (hord : SigmaOrder) (he : SigmaEntire) (P z : ℂ) :
    meromorphicOrderAt (fun w : ℂ => sgStar L $ w - P) z = ind L (z - P) := by
  have := sg_order L hord he 1 (-P) z one_ne_zero
  simp [one_mul, ← sub_eq_add_neg] at this
  exact this

lemma sg_add_analyticAt (hb : SgStarBasic) (P z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => sgStar L $ w + P) z := by
  have hd := (hb L).1
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => sgStar L $ w + P).analyticAt z

lemma sg_sub_analyticAt (hb : SgStarBasic) (P z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => sgStar L $ w - P) z := by
  have hd := (hb L).1
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => sgStar L $ w - P).analyticAt z

lemma fac_analyticAt (hb : SgStarBasic) (P z : ℂ) : AnalyticAt ℂ (fac L P) z := by
  have hd := (hb L).1
  exact (show Differentiable ℂ (fun w => fac L P w) by simp [fac]; fun_prop).analyticAt z

lemma fac_order (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (P z : ℂ)
    (hP : P ∉ L.lattice) :
    meromorphicOrderAt (fac L P) z = ind L (z + P) + ind L (z - P) := by
  have hs : sgStar L P ≠ 0 := fun h => hP $ ((hb L).2.2.1 P).1 h
  have h1 := sg_add_analyticAt L hb P z
  have h2 := sg_sub_analyticAt L hb P z
  have h12 : AnalyticAt ℂ ((fun w => sgStar L $ w + P) * fun w => sgStar L $ w - P) z := h1.mul h2
  have e : fac L P = (fun _ : ℂ => -(sgStar L P ^ 2)⁻¹) *
      ((fun w => sgStar L $ w + P) * fun w => sgStar L $ w - P) := by
    funext w
    rfl
  rw [e, meromorphicOrderAt_mul analyticAt_const.meromorphicAt h12.meromorphicAt,
    meromorphicOrderAt_mul h1.meromorphicAt h2.meromorphicAt,
    meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero analyticAt_const $ by simp [hs], sg_add_order L hord he P z, sg_sub_order L hord he P z, zero_add]

lemma sg_id_order (hord : SigmaOrder) (he : SigmaEntire) (z : ℂ) :
    meromorphicOrderAt (sgStar L) z = ind L z := by
  have := sg_order L hord he 1 0 z one_ne_zero
  simp [one_mul, add_zero] at this
  exact this

lemma num_analyticAt (hb : SgStarBasic) (z : ℂ) : AnalyticAt ℂ (num L α) z := by
  have hd := (hb L).1
  exact (show Differentiable ℂ (fun w => num L α w) by simp [num]; fun_prop).analyticAt z

private lemma analyticAt_prod_fac (hb : SgStarBasic) (T : Finset ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w => ∏ P ∈ T, fac L P w) z := by
  refine induction_on T ?_ ?_
  simp [prod_empty]
  exact analyticAt_const
  intro a T ha ih
  have e : (fun w => ∏ P ∈ insert a T, fac L P w) = fun w => fac L a w * ∏ P ∈ T, fac L P w := by
    funext w
    rw [prod_insert ha]
  rw [e]
  exact (fac_analyticAt L hb a z).mul ih

lemma den_analyticAt (hb : SgStarBasic) (z : ℂ) : AnalyticAt ℂ (den L α S) z := by
  have hd := (hb L).1
  have h1 :=
    (by fun_prop : Differentiable ℂ fun w => α ^ 2 * sgStar L w ^ 2).analyticAt z
  exact h1.mul $ analyticAt_prod_fac L hb S z

private lemma add_self_eq_two_mul_extended_int (x : WithTop ℤ) : x + x = 2 * x := by
  cases x with
  | top => first | rfl | decide | simp
  | coe a =>
    rw [← WithTop.coe_add, show (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_mul,
      two_mul]

lemma num_order (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0) (z : ℂ) :
    meromorphicOrderAt (num L α) z = 2 * ind L (α * z) := by
  have hd := (hb L).1
  have hg :=
    (by fun_prop : Differentiable ℂ fun w => sgStar L $ α * w).analyticAt z
  have e : num L α = (fun w => sgStar L $ α * w) * (fun w => sgStar L $ α * w) := by
    funext w
    exact sq _
  rw [e, meromorphicOrderAt_mul hg.meromorphicAt hg.meromorphicAt]
  have := sg_order L hord he α 0 z hα
  simp [add_zero] at this
  rw [this, add_self_eq_two_mul_extended_int]

private lemma meromorphicOrderAt_prod_fac (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic)
    (T : Finset ℂ) (hT : ∀ P ∈ T, P ∉ L.lattice) (z : ℂ) :
    meromorphicOrderAt (fun w => ∏ P ∈ T, fac L P w) z = ∑ P ∈ T, (ind L (z + P) + ind L (z - P)) := by
  revert hT
  refine induction_on T ?_ ?_
  intro _
  simp [prod_empty, Finset.sum_empty]
  exact meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero analyticAt_const one_ne_zero
  intro a T ha ih hT
  have e : (fun w => ∏ P ∈ insert a T, fac L P w) = (fac L a) * fun w => ∏ P ∈ T, fac L P w := by
    funext w
    rw [prod_insert ha]; rfl
  rw [e, meromorphicOrderAt_mul (fac_analyticAt L hb a z).meromorphicAt
    (analyticAt_prod_fac L hb T z).meromorphicAt,
    fac_order L hord he hb a z $ hT a $ Finset.mem_insert_self a T,
    ih fun P hP => hT P $ Finset.mem_insert_of_mem hP, Finset.sum_insert ha]

lemma den_order (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0)
    (hS : ∀ P ∈ S, P ∉ L.lattice) (z : ℂ) :
    meromorphicOrderAt (den L α S) z
      = 2 * ind L z + ∑ P ∈ S, (ind L (z + P) + ind L (z - P)) := by
  have hd := (hb L).1
  have h1 : AnalyticAt ℂ (fun _ : ℂ => α ^ 2) z := analyticAt_const
  have h2 : AnalyticAt ℂ (fun w => sgStar L w ^ 2) z :=
    (by fun_prop : Differentiable ℂ fun w => sgStar L w ^ 2).analyticAt z
  have e : den L α S = ((fun _ : ℂ => α ^ 2) * fun w => sgStar L w ^ 2) * fun w => ∏ P ∈ S, fac L P w := by
    funext w
    rfl
  have hs : (fun w => sgStar L w ^ 2) = sgStar L * sgStar L := by
    funext w
    exact sq _
  have hm := (hd.analyticAt z).meromorphicAt
  rw [e, meromorphicOrderAt_mul (h1.mul h2).meromorphicAt (analyticAt_prod_fac L hb S z).meromorphicAt,
    meromorphicOrderAt_mul h1.meromorphicAt h2.meromorphicAt, meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero h1 $ pow_ne_zero 2 hα,
    meromorphicOrderAt_prod_fac L hord he hb S hS z, zero_add, hs, meromorphicOrderAt_mul hm hm,
    sg_id_order L hord he z, add_self_eq_two_mul_extended_int]

lemma count_sub (hS : IsKerReps L α S) (z : ℂ) (h1 : α * z ∈ L.lattice) (h2 : z ∉ L.lattice) :
    ∑ P ∈ S, ind L (z - P) = 1 := by
  obtain ⟨P0, hP0, hz⟩ := hS.2.2 z h1 h2
  rw [sum_eq_single P0]
  exact ind_of_mem L hz
  intro b hb hne
  apply ind_of_notMem L
  intro hb'
  apply hne
  apply hS.2.1 b hb P0 hP0
  have e : b - P0 = (z - P0) - (z - b) := by ring
  rw [e]
  exact L.lattice.sub_mem hz hb'
  intro h
  exact absurd hP0 h

lemma count_add (hS : IsKerReps L α S) (z : ℂ) (h1 : α * z ∈ L.lattice) (h2 : z ∉ L.lattice) :
    ∑ P ∈ S, ind L (z + P) = 1 := by
  obtain ⟨P0, hP0, hz⟩ := hS.2.2 (-z) (by rw [mul_neg]; exact L.lattice.neg_mem h1) fun h => h2 $ by simpa using L.lattice.neg_mem h
  have hz' : z + P0 ∈ L.lattice := by
    have := L.lattice.neg_mem hz
    convert this using 1
    ring
  rw [sum_eq_single P0]
  exact ind_of_mem L hz'
  intro b hb hne
  apply ind_of_notMem L
  intro hb'
  apply hne
  apply hS.2.1 b hb P0 hP0
  have e : b - P0 = (z + b) - (z + P0) := by ring
  rw [e]
  exact L.lattice.sub_mem hb' hz'
  intro h
  exact absurd hP0 h

lemma den_order_two (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0)
    (hS : IsKerReps L α S) (z : ℂ) (h1 : α * z ∈ L.lattice) :
    meromorphicOrderAt (den L α S) z = 2 := by
  rw [den_order L α S hord he hb hα (fun P hP => (hS.1 P hP).2) z]
  by_cases hz : z ∈ L.lattice
  rw [ind_of_mem L hz]
  have h0 : ∀ P ∈ S, ind L (z + P) + ind L (z - P) = 0 := by
    intro P hP
    have hPL := (hS.1 P hP).2
    rw [ind_of_notMem L fun h => hPL $ by simpa using L.lattice.sub_mem h hz,
      ind_of_notMem L fun h => hPL $ by simpa using L.lattice.sub_mem hz h]
    simp
  rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
  rfl
  rw [ind_of_notMem L hz, Finset.sum_add_distrib, count_add L α S hS z h1 hz, count_sub L α S hS z h1 hz]
  rfl

lemma mem_of_den_eq_zero (hb : SgStarBasic) (hα : α ≠ 0) (hst : MulStable L α)
    (hS : IsKerReps L α S) (z : ℂ) (h : den L α S z = 0) : α * z ∈ L.lattice := by
  have hz := (hb L).2.2.1
  unfold den at h
  rcases mul_eq_zero.1 h with h | h
  rcases mul_eq_zero.1 h with h | h
  exact absurd ((pow_eq_zero_iff two_ne_zero).1 h) hα
  exact hst z $ (hz z).1 $ (pow_eq_zero_iff two_ne_zero).1 h
  obtain ⟨P, hP, h⟩ := Finset.prod_eq_zero_iff.1 h
  have hPL := hS.1 P hP
  have hs : sgStar L P ≠ 0 := fun h0 => hPL.2 $ (hz P).1 h0
  unfold fac at h
  rcases mul_eq_zero.1 h with h | h
  exfalso
  simp [hs] at h
  rcases mul_eq_zero.1 h with h | h
  have h3 := hst _ $ (hz _).1 h
  have e : α * z = α * (z + P) - α * P := by ring
  rw [e]
  exact L.lattice.sub_mem h3 hPL.1
  have h3 := hst _ $ (hz _).1 h
  have e : α * z = α * (z - P) + α * P := by ring
  rw [e]
  exact L.lattice.add_mem h3 hPL.1

lemma quot_order (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0)
    (hst : MulStable L α) (hS : IsKerReps L α S) (z : ℂ) :
    0 ≤ meromorphicOrderAt (fun w => num L α w / den L α S w) z := by
  have hden := den_analyticAt L α S hb z
  have e : (fun w => num L α w / den L α S w) = num L α * (den L α S)⁻¹ := by
    funext w
    exact div_eq_mul_inv _ _
  rw [e, meromorphicOrderAt_mul (num_analyticAt L α hb z).meromorphicAt hden.meromorphicAt.inv, meromorphicOrderAt_inv,
    num_order L α hord he hb hα z]
  by_cases h : α * z ∈ L.lattice
  rw [den_order_two L α S hord he hb hα hS z h, ind_of_mem L h]
  decide
  rw [meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hden fun h0 => h $ mem_of_den_eq_zero L α S hb hα hst hS z h0, ind_of_notMem L h]
  decide

lemma quot_periodic (hq : SgStarQuasi) (hst : MulStable L α)
    (hc : (S.card : ℝ) + 1 = normSq α) :
    IsPeriodic L fun w => num L α w / den L α S w := by
  intro ω hω z
  show num L α (z + ω) / den L α S (z + ω) = num L α z / den L α S z
  rw [num_add L α S hq hst hc ω z hω, den_add L α S hq ω z hω]
  exact mul_div_mul_left _ _ $ pow_ne_zero _ $ pow_ne_zero _ (by simp only [mlt]; exact exp_ne_zero _)

lemma exists_const (hN : EllipticNoPole) (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic)
    (hq : SgStarQuasi) (hα : α ≠ 0) (hst : MulStable L α) (hS : IsKerReps L α S)
    (hc : (S.card : ℝ) + 1 = normSq α) :
    ∃ c : ℂ, ∀ z, num L α z = c * den L α S z := by
  obtain ⟨c, hc'⟩ := hN L _ (fun z => (num_analyticAt L α hb z).meromorphicAt.div (den_analyticAt L α S hb z).meromorphicAt) (quot_periodic L α S hq hst hc) $ quot_order L α S hord he hb hα hst hS
  refine ⟨c, fun z => ?_⟩
  by_cases h0 : den L α S z = 0
  rw [h0, mul_zero]
  simp [num, ((hb L).2.2.1 _).2 $ mem_of_den_eq_zero L α S hb hα hst hS z h0]
  have hcont : ContinuousAt (fun w => num L α w / den L α S w) z :=
    (num_analyticAt L α hb z).continuousAt.div (den_analyticAt L α S hb z).continuousAt h0
  exact (div_eq_iff h0).1 $ hc' z hcont

lemma sg_eq_mul_dslope (hb : SgStarBasic) (z : ℂ) : sgStar L z = z * dslope (sgStar L) 0 z := by
  have h := sub_smul_dslope (sgStar L) 0 z
  simp [sub_zero, smul_eq_mul] at h
  rw [h, ((hb L).2.2.1 0).2 L.lattice.zero_mem, sub_zero]

lemma fac_zero (hb : SgStarBasic) (P : ℂ) (hP : P ∉ L.lattice) : fac L P 0 = 1 := by
  simp [fac, zero_add, zero_sub, (hb L).2.1]
  trans (sgStar L P ^ 2)⁻¹ * sgStar L P ^ 2
  ring
  rw [inv_mul_cancel₀ $ pow_ne_zero 2 fun h0 => hP $ ((hb L).2.2.1 P).1 h0]

lemma const_eq_one (hb : SgStarBasic) (hα : α ≠ 0) (hS : ∀ P ∈ S, P ∉ L.lattice) (c : ℂ)
    (h : ∀ z, num L α z = c * den L α S z) : c = 1 := by
  have hdc := continuousAt_dslope_same.2 $ (hb L).1 0
  have hd0 : dslope (sgStar L) 0 0 = 1 := by rw [dslope_same]
                                             exact (hb L).2.2.2.1
  have g1c : ContinuousAt (fun w => dslope (sgStar L) 0 (α * w) ^ 2) 0 := by
    have h1 : ContinuousAt (fun w => dslope (sgStar L) 0 $ α * w) 0 :=
      ContinuousAt.comp_of_eq hdc (by fun_prop) $ by simp
    exact h1.pow 2
  have hprod : ContinuousAt (fun w => ∏ P ∈ S, fac L P w) 0 := (analyticAt_prod_fac L hb S 0).continuousAt
  have g2c : ContinuousAt (fun w => c * dslope (sgStar L) 0 w ^ 2 * ∏ P ∈ S, fac L P w) 0 :=
    (continuousAt_const.mul $ hdc.pow 2).mul hprod
  have heq : (fun w => dslope (sgStar L) 0 (α * w) ^ 2) =ᶠ[𝓝[≠] 0]
      fun w => c * dslope (sgStar L) 0 w ^ 2 * ∏ P ∈ S, fac L P w := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : w ≠ 0 := hw
    have hh := h w
    simp only [num, den] at hh
    rw [sg_eq_mul_dslope L hb $ α * w, sg_eq_mul_dslope L hb w] at hh
    have hne : α ^ 2 * w ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hα) $ pow_ne_zero 2 hw'
    apply mul_left_cancel₀ hne
    linear_combination hh
  have key := tendsto_nhds_unique (g1c.tendsto.mono_left nhdsWithin_le_nhds)
    $ (g2c.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
  simp only [mul_zero, hd0, one_pow, mul_one] at key
  rw [prod_congr rfl fun P hP => fac_zero L hb P $ hS P hP, Finset.prod_const_one, mul_one] at key
  exact key.symm

lemma fac_eq (hb : SgStarBasic) (hsa : SgStarAdd) (P z : ℂ) (hP : P ∉ L.lattice)
    (hz : z ∉ L.lattice) :
    fac L P z = sgStar L z ^ 2 * (L.weierstrassP z - L.weierstrassP P) := by
  simp [fac]
  rw [hsa L z P hz hP]
  have := inv_mul_cancel₀ $ pow_ne_zero 2 fun h0 => hP $ ((hb L).2.2.1 P).1 h0
  linear_combination (sgStar L z ^ 2 * (L.weierstrassP z - L.weierstrassP P)) * this

end IsogenySigmaQuotient

open IsogenySigmaQuotient in
theorem isogenySigma_of (hN : EllipticNoPole) (hord : SigmaOrder) (hsa : SgStarAdd)
    (hq : SgStarQuasi) (hb : SgStarBasic) (hcard : KerRepsCard) (he : SigmaEntire) :
    IsogenySigma := by
  intro L α S hα hst hS z hz
  have hc := hcard L α S hα hst hS
  have hS' : ∀ P ∈ S, P ∉ L.lattice := fun P hP => (hS.1 P hP).2
  obtain ⟨c, hc'⟩ := exists_const L α S hN hord he hb hq hα hst hS hc
  have h1 := const_eq_one L α S hb hα hS' c hc'
  subst h1
  have h := hc' z
  simp [num, den, one_mul] at h
  rw [h, prod_congr rfl fun P hP => fac_eq L hb hsa P z (hS' P hP) hz, prod_mul_distrib,
    prod_const]
  ring

end Formalism.L2.Th1.F
end
section
open UpperHalfPlane hiding I
open EisensteinSeries Complex SummationFilter ModularGroup
open scoped Real

namespace Formalism.L2.Th1.F.LegendreModelEllipticTorsion

lemma e2Summand_succ (z : ℍ) (a : ℕ) : e2Summand ((a : ℤ) + 1) z =
    -4 * π ^ 2 * ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ ((a + 1) * n : ℕ) := by
  have hw : 0 < (((a : ℂ) + 1) * (z : ℂ)).im := by
    have e : (((a : ℂ) + 1) * (z : ℂ)).im = ((a : ℝ) + 1) * (z : ℂ).im := by
      simp [Complex.mul_im]
    rw [e]
    exact mul_pos (by positivity) z.im_pos
  have H := EisensteinSeries.qExpansion_identity_pnat (k := 1) le_rfl ⟨((a : ℂ) + 1) * (z : ℂ), hw⟩
  have hc : ((⟨((a : ℂ) + 1) * (z : ℂ), hw⟩ : ℍ) : ℂ) = ((a : ℂ) + 1) * (z : ℂ) := rfl
  rw [hc] at H
  unfold EisensteinSeries.e2Summand
  have e1 : ∀ n : ℤ, eisSummand 2 ![(a : ℤ) + 1, n] z
      = 1 / (((a : ℂ) + 1) * (z : ℂ) + n) ^ (1 + 1) := by
    intro n
    simp [eisSummand, zpow_neg]
  have hq : ∀ n : ℕ+, cexp (2 * π * I * (((a : ℂ) + 1) * (z : ℂ))) ^ (n : ℕ)
      = cexp (2 * π * I * z) ^ ((a + 1) * (n : ℕ)) := by
    intro n
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [e1]
  rw [H]
  simp only [hq, pow_one]
  set S := ∑' n : ℕ+, ((n : ℕ) : ℂ) * cexp (2 * π * I * z) ^ ((a + 1) * (n : ℕ))
  simp only [Nat.factorial, Nat.cast_one, div_one, Nat.mul_one, Nat.succ_eq_add_one, zero_add]
  linear_combination (4 * (π : ℂ) ^ 2 * S) * Complex.I_sq

lemma summable_e2Summand_succ (z : ℍ) : Summable fun a : ℕ => e2Summand ((a : ℤ) + 1) z := by
  set r := cexp (2 * π * I * (z : ℂ)) with hr
  set ρ := ‖r‖ with hρdef
  have hρ : ρ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hsum :=
    summable_pow_mul_geometric_of_norm_lt_one 1 $ by rwa [Real.norm_of_nonneg hρ0]
  have hsumP : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) := by
    have := hsum.comp_injective PNat.coe_injective
    simp [pow_one] at this
    exact this
  set C := ∑' n : ℕ+, ((n : ℕ) : ℝ) * ρ ^ (n : ℕ)
  have hpt : ∀ (a : ℕ) (n : ℕ+), ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖
      ≤ ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) * ρ ^ a := by
    intro a n
    rw [norm_mul, norm_pow, Complex.norm_natCast, mul_assoc, ← pow_add]
    apply mul_le_mul_of_nonneg_left _ $ Nat.cast_nonneg _
    apply pow_le_pow_of_le_one hρ0 hρ.le
    have := n.pos
    nlinarith
  have hb : ∀ a : ℕ, ‖e2Summand ((a : ℤ) + 1) z‖ ≤ 4 * π ^ 2 * C * ρ ^ a := by
    intro a
    rw [e2Summand_succ, norm_mul]
    have h4 : ‖(-4 * (π : ℂ) ^ 2)‖ = 4 * π ^ 2 := by
      rw [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    rw [h4, mul_assoc $ 4 * π ^ 2]
    apply mul_le_mul_of_nonneg_left _ $ by positivity
    have hs : Summable fun n : ℕ+ => ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hpt a) $ hsumP.mul_right _
    calc ‖∑' n : ℕ+, ((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖
        ≤ ∑' n : ℕ+, ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ+, ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) * ρ ^ a :=
          Summable.tsum_le_tsum (hpt a) hs $ hsumP.mul_right _
      _ = C * ρ ^ a := tsum_mul_right
  exact Summable.of_norm_bounded (g := fun a : ℕ => 4 * π ^ 2 * C * ρ ^ a)
    ((summable_geometric_of_lt_one hρ0 hρ).mul_left _) hb

lemma summable_e2Summand (z : ℍ) : Summable fun n : ℤ => e2Summand n z := by
  have h0 : Summable fun n : ℕ => e2Summand (n : ℤ) z := by
    rw [← summable_nat_add_iff 1]
    refine (summable_e2Summand_succ z).congr ?_
    intro a
    push_cast
    rfl
  refine Summable.of_nat_of_neg h0 ?_
  refine h0.congr ?_
  intro n
  exact ((EisensteinSeries.e2Summand_even z) (n : ℤ)).symm

lemma tsum_e2Summand (z : ℍ) : ∑' n : ℤ, e2Summand n z = G2 z := by
  unfold EisensteinSeries.G2
  exact (tsum_eq_of_summable_unconditional $ summable_e2Summand z).symm

private lemma one_div_sq_eq_of_eq_mul (X Y c : ℂ) (h : X = c * Y) :
    1 / X ^ 2 = (c ^ 2)⁻¹ * Y ^ (-2 : ℤ) := by
  subst h
  rw [mul_pow, one_div, mul_inv, zpow_neg]
  norm_cast

lemma sumA (u v : ℂ) (h : 0 < (v / u).im) :
    ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 = (u ^ 2)⁻¹ * G2 ⟨v / u, h⟩ := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  have hc : ((⟨v / u, h⟩ : ℍ) : ℂ) = v / u := rfl
  rw [← tsum_e2Summand, ← tsum_mul_left]
  congr 1
  funext n
  unfold EisensteinSeries.e2Summand
  rw [← tsum_mul_left]
  congr 1
  funext m
  simp only [eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one]
  apply one_div_sq_eq_of_eq_mul
  field_simp
  ring

lemma sumB (u v : ℂ) (h : 0 < (v / u).im) :
    ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 = (v ^ 2)⁻¹ * G2 (S • ⟨v / u, h⟩) := by
  have hv : v ≠ 0 := by
    rintro rfl
    simp at h
  have hw : ((S • (⟨v / u, h⟩ : ℍ) : ℍ) : ℂ) = -(u / v) := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(v / u))⁻¹ = -(u / v)
    rw [inv_neg, inv_div]
  rw [← tsum_e2Summand, ← tsum_mul_left]
  congr 1
  funext m
  have he : e2Summand (-m) (S • (⟨v / u, h⟩ : ℍ)) = e2Summand m (S • (⟨v / u, h⟩ : ℍ)) :=
    EisensteinSeries.e2Summand_even _ m
  rw [← he]
  unfold EisensteinSeries.e2Summand
  rw [← tsum_mul_left]
  congr 1
  funext n
  simp only [eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one, hw]
  apply one_div_sq_eq_of_eq_mul
  field_simp
  push_cast
  ring

lemma key (u v : ℂ) (h : 0 < (v / u).im) :
    (u * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) * v
      - (v * ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) * u = 2 * π * I := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  have hv : v ≠ 0 := by
    rintro rfl
    simp at h
  rw [sumA u v h, sumB u v h]
  have hT := EisensteinSeries.G2_S_transform ⟨v / u, h⟩
  have hc : ((⟨v / u, h⟩ : ℍ) : ℂ) = v / u := rfl
  rw [hc] at hT
  rw [hT]
  field_simp
  ring

end Formalism.L2.Th1.F.LegendreModelEllipticTorsion

namespace Formalism.L2.Th1.F

lemma LegendreModelEllipticTorsion.im_pos_of_not (L : PeriodPair) (h : ¬ 0 < (L.ω₂ / L.ω₁).im) :
    0 < (L.ω₁ / L.ω₂).im := by
  have hind := L.indep
  have ha : L.ω₁ ≠ 0 := by simpa using hind.ne_zero 0
  have hb : L.ω₂ ≠ 0 := by simpa using hind.ne_zero 1
  have hne : (L.ω₂ / L.ω₁).im ≠ 0 := by
    intro him
    have hr : L.ω₂ / L.ω₁ = ((L.ω₂ / L.ω₁).re : ℂ) := Complex.ext (by simp) $ by simp [him]
    have hbr : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁ := by
      rw [← hr]
      field_simp
    have h2 := (LinearIndependent.pair_iff.mp hind) (L.ω₂ / L.ω₁).re (-1) $ by
      rw [Complex.real_smul, Complex.real_smul]
      nth_rewrite 2 [hbr]
      push_cast
      ring
    norm_num at h2
  rw [show L.ω₁ / L.ω₂ = (L.ω₂ / L.ω₁)⁻¹ from (inv_div _ _).symm, Complex.inv_im]
  exact div_pos (neg_pos.mpr $ lt_of_le_of_ne (not_lt.mp h) hne) $ Complex.normSq_pos.mpr $ div_ne_zero hb ha

theorem legendre_of (h : EtaEisenstein) : Legendre := by
  intro L
  obtain ⟨h1, h2⟩ := h L
  rw [h1, h2]
  split_ifs with hp
  rw [one_mul]
  exact LegendreModelEllipticTorsion.key L.ω₁ L.ω₂ hp
  have hp' := LegendreModelEllipticTorsion.im_pos_of_not L hp
  have k := LegendreModelEllipticTorsion.key L.ω₂ L.ω₁ hp'
  have e1 : (∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₂ + (n : ℂ) * L.ω₁) ^ 2)
      = ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 := by
    congr 1
    funext a; congr 1; funext b; ring
  have e2 : (∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₂ + (n : ℂ) * L.ω₁) ^ 2)
      = ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 := by
    congr 1
    funext a; congr 1; funext b; ring
  rw [e1, e2] at k
  linear_combination -k

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate
open Complex (normSq real_smul)
open LinearMap (det range)
open Nat (card card_eq_fintype_card finite_of_card_ne_zero)

namespace Formalism.L2.Th1.F

namespace Ker

theorem matrix_data (L : PeriodPair) (α : ℂ) (h : MulStable L α) :
    ∃ a b c d : ℤ, α * L.ω₁ = a * L.ω₁ + c * L.ω₂ ∧ α * L.ω₂ = b * L.ω₁ + d * L.ω₂ ∧
      (2 * α.re = ((a + d : ℤ) : ℝ)) ∧ normSq α = ((a * d - b * c : ℤ) : ℝ) := by
  obtain ⟨a, c, hac⟩ := PeriodPair.mem_lattice.1 $ h _ L.ω₁_mem_lattice
  obtain ⟨b, d, hbd⟩ := PeriodPair.mem_lattice.1 $ h _ L.ω₂_mem_lattice
  use a, b, c, d, hac.symm, hbd.symm
  have hind := LinearIndependent.pair_iff.1 L.indep
  have hω1 : L.ω₁ ≠ 0 := by
    intro h0
    exact one_ne_zero (hind 1 0 $ by simp [h0]).1
  have hω2 : L.ω₂ ≠ 0 := by
    intro h0
    exact one_ne_zero (hind 0 1 $ by simp [h0]).2
  have e1 : (α - a) * L.ω₁ = c * L.ω₂ := by linear_combination -hac
  have e2 : (α - d) * L.ω₂ = b * L.ω₁ := by linear_combination -hbd
  have hq : α ^ 2 - ((a + d : ℤ) : ℂ) * α + ((a * d - b * c : ℤ) : ℂ) = 0 := by
    have h0 : ((α - a) * (α - d) - b * c) * (L.ω₁ * L.ω₂) = 0 := by
      linear_combination (α - d) * L.ω₂ * e1 + c * L.ω₂ * e2
    rcases mul_eq_zero.1 h0 with h1 | h1
    push_cast
    linear_combination h1
    exact absurd h1 $ mul_ne_zero hω1 hω2
  by_cases him : α.im = 0
  have hαr : α = (α.re : ℂ) := Complex.ext (by simp) $ by simp [him]
  obtain ⟨h1, h2⟩ := hind (α.re - a) (-c) $ by
    rw [real_smul, real_smul]
    rw [hαr] at e1
    push_cast
    linear_combination e1
  obtain ⟨h3, h4⟩ := hind (-b) (α.re - d) $ by
    rw [real_smul, real_smul]
    rw [hαr] at e2
    push_cast
    linear_combination e2
  have ha : (a : ℝ) = α.re := by linarith
  have hd : (d : ℝ) = α.re := by linarith
  have hb : (b : ℝ) = 0 := by linarith
  have hc : (c : ℝ) = 0 := by linarith
  constructor
  push_cast
  linarith
  rw [Complex.normSq_apply, him]
  push_cast
  rw [ha, hd, hb, hc]
  ring
  have hq' : (starRingEnd ℂ α) ^ 2 - ((a + d : ℤ) : ℂ) * starRingEnd ℂ α + ((a * d - b * c : ℤ) : ℂ) = 0 := by
    have := congrArg (starRingEnd ℂ) hq
    simpa using this
  have hne : α - starRingEnd ℂ α ≠ 0 := by
    intro h0
    apply him
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hsum : α + starRingEnd ℂ α = ((a + d : ℤ) : ℂ) := by
    have h0 : (α - starRingEnd ℂ α) * (α + starRingEnd ℂ α - ((a + d : ℤ) : ℂ)) = 0 := by
      linear_combination hq - hq'
    linear_combination (mul_eq_zero.1 h0).resolve_left hne
  have hprod : α * starRingEnd ℂ α = ((a * d - b * c : ℤ) : ℂ) := by
    linear_combination α * hsum - hq
  constructor
  have h2 := Complex.add_conj α
  rw [hsum] at h2
  exact_mod_cast h2.symm
  have h3 := Complex.mul_conj α
  rw [hprod] at h3
  exact_mod_cast h3.symm

def mulEnd (L : PeriodPair) (α : ℂ) (h : MulStable L α) : L.lattice →ₗ[ℤ] L.lattice where
  toFun x := ⟨α * x, h _ x.2⟩
  map_add' x y := by ext; simp [mul_add]
  map_smul' n x := by ext; simp; ring

theorem mulEnd_injective (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (h : MulStable L α) :
    Function.Injective $ mulEnd L α h := by
  intro x y hxy
  have := congrArg Subtype.val hxy
  apply Subtype.ext
  simpa [mulEnd, hα] using this

theorem det_mulEnd (L : PeriodPair) (α : ℂ) (h : MulStable L α) :
    ((det (mulEnd L α h) : ℤ) : ℝ) = normSq α := by
  obtain ⟨a, b, c, d, hac, hbd, -, hn⟩ := matrix_data L α h
  have h0 : mulEnd L α h (L.latticeBasis 0) = a • L.latticeBasis 0 + c • L.latticeBasis 1 := by
    apply Subtype.ext
    simp [mulEnd, L.latticeBasis_zero, L.latticeBasis_one, hac]
  have h1 : mulEnd L α h (L.latticeBasis 1) = b • L.latticeBasis 0 + d • L.latticeBasis 1 := by
    apply Subtype.ext
    simp [mulEnd, L.latticeBasis_zero, L.latticeBasis_one, hbd]
  have key : det (mulEnd L α h) = a * d - b * c := by
    rw [← LinearMap.det_toMatrix L.latticeBasis, Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, h0, h1] <;> ring
  rw [hn, key]

theorem card_quot (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (h : MulStable L α) :
    ((card (L.lattice ⧸ range (mulEnd L α h)) : ℕ) : ℝ) = normSq α := by
  have key : (det (mulEnd L α h)).natAbs =
      card (L.lattice ⧸ range (mulEnd L α h)) := by
    rw [← Submodule.natAbs_det_equiv (range (mulEnd L α h))
      $ LinearEquiv.ofInjective (mulEnd L α h) (mulEnd_injective L α hα h)]
    congr 2
  rw [← key, Nat.cast_natAbs, Int.cast_abs, det_mulEnd, abs_of_nonneg (Complex.normSq_nonneg α)]

theorem mk_eq_iff (L : PeriodPair) (α : ℂ) (h : MulStable L α) (u v : L.lattice) :
    (Submodule.Quotient.mk u : L.lattice ⧸ range (mulEnd L α h)) = Submodule.Quotient.mk v ↔
      ∃ x ∈ L.lattice, (u : ℂ) - v = α * x := by
  rw [Submodule.Quotient.eq]
  constructor
  rintro ⟨x, hx⟩
  use x, x.2
  have := congrArg Subtype.val hx
  simpa [mulEnd] using this.symm
  rintro ⟨x, hx, hxe⟩
  exact ⟨⟨x, hx⟩, Subtype.ext (by simp [mulEnd, hxe])⟩

end Ker

open Ker


theorem kernel_reps_card : KerRepsCard := by
  unfold KerRepsCard
  intro L α S hα h hS
  obtain ⟨h1, h2, h3⟩ := hS
  haveI : Finite (L.lattice ⧸ range (mulEnd L α h)) := by
    apply finite_of_card_ne_zero
    intro h0
    have hc := card_quot L α hα h
    rw [h0] at hc
    exact hα (Complex.normSq_eq_zero.1 (by rw [← hc]; simp))
  have hout : ∀ q : L.lattice ⧸ range (mulEnd L α h), Submodule.Quotient.mk (Quotient.out q) = q :=
    fun q => Quotient.out_eq' q
  have hdiv : ∀ u : ℂ, α * (u / α) = u := fun u => by field_simp
  classical
  haveI := Fintype.ofFinite (L.lattice ⧸ range (mulEnd L α h))
  have hφ0 : ∀ P : S, (Submodule.Quotient.mk (⟨α * P, (h1 P P.2).1⟩ : L.lattice) :
      L.lattice ⧸ range (mulEnd L α h)) ≠ 0 := by
    intro P h0
    rw [← Submodule.Quotient.mk_zero, mk_eq_iff] at h0
    obtain ⟨x, hx, hxe⟩ := h0
    exact (h1 P P.2).2 ((by simpa [hα] using hxe) ▸ hx)
  let φ : S → {q : L.lattice ⧸ range (mulEnd L α h) // ¬ q = 0} :=
    fun P => ⟨Submodule.Quotient.mk (⟨α * P, (h1 P P.2).1⟩ : L.lattice), hφ0 P⟩
  have hinj : Function.Injective φ := by
    intro P P' hPP
    have h6 := congrArg Subtype.val hPP
    simp [φ] at h6
    rw [mk_eq_iff] at h6
    obtain ⟨x, hx, hxe⟩ := h6
    have hxe' : α * (P : ℂ) - α * (P' : ℂ) = α * x := hxe
    have hd : (P : ℂ) - P' = x := mul_left_cancel₀ hα (by rw [mul_sub]; exact hxe')
    exact Subtype.ext (h2 P P.2 P' P'.2 (hd ▸ hx))
  have hsurj : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    have hz1 : α * (((Quotient.out q : L.lattice) : ℂ) / α) ∈ L.lattice := by
      rw [hdiv]
      exact (Quotient.out q).2
    have hz2 : ((Quotient.out q : L.lattice) : ℂ) / α ∉ L.lattice := by
      intro hm
      apply hq
      rw [← hout q, ← Submodule.Quotient.mk_zero, mk_eq_iff]
      exact ⟨_, hm, by rw [hdiv]; simp⟩
    obtain ⟨P, hP, hzP⟩ := h3 _ hz1 hz2
    refine ⟨⟨P, hP⟩, Subtype.ext ?_⟩
    show (Submodule.Quotient.mk (⟨α * P, (h1 P hP).1⟩ : L.lattice) :
      L.lattice ⧸ range (mulEnd L α h)) = q
    conv_rhs => rw [← hout q]
    rw [mk_eq_iff]
    use -(((Quotient.out q : L.lattice) : ℂ) / α - P), neg_mem hzP
    rw [mul_neg, mul_sub, hdiv]
    ring
  have hc1 : card {q : L.lattice ⧸ range (mulEnd L α h) // ¬ q = 0} + 1 =
      card (L.lattice ⧸ range (mulEnd L α h)) := by
    rw [card_eq_fintype_card, card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have := Fintype.card_pos (α := L.lattice ⧸ range (mulEnd L α h))
    omega
  have e2 : card S = S.card := by simp
  rw [← card_quot L α hα h]
  exact_mod_cast (show S.card + 1 = card (L.lattice ⧸ range (mulEnd L α h)) by
    rw [← e2, Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩), hc1])

theorem kernel_reps_exist : KerRepsExist := by
  unfold KerRepsExist
  intro L α hα h
  haveI : Finite (L.lattice ⧸ range (mulEnd L α h)) := by
    apply finite_of_card_ne_zero
    intro h0
    have hc := card_quot L α hα h
    rw [h0] at hc
    exact hα (Complex.normSq_eq_zero.1 (by rw [← hc]; simp))
  have hout : ∀ q : L.lattice ⧸ range (mulEnd L α h), Submodule.Quotient.mk (Quotient.out q) = q :=
    fun q => Quotient.out_eq' q
  have hdiv : ∀ u : ℂ, α * (u / α) = u := fun u => by field_simp
  classical
  haveI := Fintype.ofFinite (L.lattice ⧸ range (mulEnd L α h))
  use (Finset.univ.filter fun q : L.lattice ⧸ range (mulEnd L α h) => q ≠ 0).image
    fun q => ((Quotient.out q : L.lattice) : ℂ) / α
  unfold IsKerReps
  refine ⟨?_, ?_, ?_⟩
  intro P hP
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hP
  simp [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  refine ⟨by rw [hdiv]; exact (Quotient.out q).2, ?_⟩
  intro hm
  apply hq
  rw [← hout q, ← Submodule.Quotient.mk_zero, mk_eq_iff]
  exact ⟨_, hm, by rw [hdiv]; simp⟩
  intro P hP P' hP' hd
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hP
  obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hP'
  have hqq : q = q' := by
    rw [← hout q, ← hout q', mk_eq_iff]
    exact ⟨_, hd, by rw [mul_sub, hdiv, hdiv]⟩
  rw [hqq]
  intro z hz hzn
  have hq0 : (Submodule.Quotient.mk (⟨α * z, hz⟩ : L.lattice) :
      L.lattice ⧸ range (mulEnd L α h)) ≠ 0 := by
    intro h0
    rw [← Submodule.Quotient.mk_zero, mk_eq_iff] at h0
    obtain ⟨x, hx, hxe⟩ := h0
    have hzx : z = x := by simpa [hα] using hxe
    exact hzn (hzx ▸ hx)
  set q : L.lattice ⧸ range (mulEnd L α h) := Submodule.Quotient.mk (⟨α * z, hz⟩ : L.lattice) with hqdef
  refine ⟨((Quotient.out q : L.lattice) : ℂ) / α, Finset.mem_image.2 ⟨q, by simp [hq0], rfl⟩, ?_⟩
  have h5 := hout q
  rw [hqdef, mk_eq_iff] at h5
  obtain ⟨x, hx, hxe⟩ := h5
  have hzx : z - ((Quotient.out q : L.lattice) : ℂ) / α = -x :=
    mul_left_cancel₀ hα (by rw [mul_sub, hdiv]; linear_combination -hxe)
  rw [hzx]
  exact neg_mem hx

end Formalism.L2.Th1.F
end
section
open scoped Topology

namespace Formalism.L2.Th1.F

namespace PDeriv

lemma hasDerivAt_P (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have hd := (L.differentiableOn_weierstrassP.differentiableAt
    $ L.isClosed_lattice.isOpen_compl.mem_nhds hz).hasDerivAt
  rwa [L.deriv_weierstrassP] at hd

lemma eventually_notMem (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, w ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz



end PDeriv

open PDeriv

theorem sigmaDouble_of (h : SigmaAdd) (he : SigmaEntire) (hs : SigmaSimple) : SigmaDouble := by
  intro L z hz
  have h0 : wSigma L 0 = 0 := by simp [wSigma, zero_mul]
  have hd : ∀ x, HasDerivAt (wSigma L) (deriv (wSigma L) x) x := fun x => (he L x).hasDerivAt
  have hF := (HasDerivAt.comp z (hd $ z + z) $ (hasDerivAt_id' z).const_add z).mul
    $ HasDerivAt.comp z (hd $ z - z) $ (hasDerivAt_id' z).const_sub z
  have hG := ((((hd z).mul $ hd z).const_mul $ wSigma L z ^ 2).mul
    $ (hasDerivAt_P L hz).const_sub $ L.weierstrassP z).neg
  have hG' : HasDerivAt (fun w => wSigma L (z + w) * wSigma L (z - w)) _ z :=
    hG.congr_of_eventuallyEq $ (eventually_notMem L hz).mono fun w hw => by
      simp [Pi.neg_apply, Pi.mul_apply]
      rw [h L z w hz hw]
      ring
  have key := hF.unique hG'
  simp [Function.comp_apply, Pi.mul_apply, sub_self, h0, (hs L).1] at key
  rw [two_mul]
  linear_combination -key

theorem pDerivZero_of (h : SigmaDouble) (hz : SigmaZero) : PDerivZero := by
  intro L z hz'
  have hσ : wSigma L z ≠ 0 := fun h0 => hz' $ (hz L z).mp h0
  rw [← hz L $ 2 * z, h L z hz']
  simp [hσ]



end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace PeriodAreaSignLemmas

def det (L : PeriodPair) : ℝ := (conj L.ω₁ * L.ω₂).im

def sgn (L : PeriodPair) : ℤ := if 0 < (L.ω₂ / L.ω₁).im then 1 else -1

lemma det_eq (L : PeriodPair) : det L = L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re := by
  simp [det, Complex.mul_im]
  ring

lemma det_ne_zero (L : PeriodPair) : det L ≠ 0 := by
  intro h
  rw [det_eq] at h
  have key := LinearIndependent.pair_iff.mp L.indep
  have h1 := key L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext
    simp
    linarith
    simp
    ring)
  have h2 := key L.ω₂.re (-L.ω₁.re) (by
    apply Complex.ext
    simp
    ring
    simp
    linarith)
  have h3 : L.ω₁ = 0 := by
    apply Complex.ext
    simpa using h2.2
    simpa using h1.2
  exact one_ne_zero (key 1 0 $ by simp [h3]).1

lemma ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  intro h
  apply det_ne_zero L
  simp [det, h]

lemma div_im (L : PeriodPair) : (L.ω₂ / L.ω₁).im = det L / Complex.normSq L.ω₁ := by
  rw [Complex.div_im, det_eq]
  ring

lemma div_im_pos_iff (L : PeriodPair) : 0 < (L.ω₂ / L.ω₁).im ↔ 0 < det L := by
  rw [div_im, div_pos_iff_of_pos_right $ Complex.normSq_pos.mpr $ ω₁_ne_zero L]

lemma area_eq (L : PeriodPair) : area L = |det L| := rfl

lemma area_pos (L : PeriodPair) : 0 < area L := abs_pos.mpr $ det_ne_zero L

lemma det_eq_sgn_mul (L : PeriodPair) : det L = (sgn L : ℝ) * area L := by
  rw [area_eq, sgn]
  split_ifs with h
  rw [abs_of_pos $ (div_im_pos_iff L).mp h]
  simp
  have : det L < 0 := lt_of_le_of_ne (not_lt.mp fun h' => h $ (div_im_pos_iff L).mpr h')
    (det_ne_zero L)
  rw [abs_of_neg this]
  simp


lemma disc_eq (L : PeriodPair) :
    L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ = -(2 * Complex.I * (det L : ℂ)) := by
  rw [det_eq]
  apply Complex.ext
  simp
  ring
  simp
  ring

lemma disc_ne_zero (L : PeriodPair) : L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ ≠ 0 := by
  rw [disc_eq]
  have : (det L : ℂ) ≠ 0 := by exact_mod_cast det_ne_zero L
  simp [this]

lemma exists_coord (L : PeriodPair) (x : ℂ) : ∃ a b : ℝ, x = (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ := by
  use L.basis.repr x 0, L.basis.repr x 1
  have := L.basis.sum_repr x
  rw [Fin.sum_univ_two] at this
  simpa using this.symm

lemma wEta_coord (L : PeriodPair) (a b : ℝ) :
    wEta L ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) = (a : ℂ) * wEta L L.ω₁ + (b : ℂ) * wEta L L.ω₂ := by
  have : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = a • L.ω₁ + b • L.ω₂ := by simp
  rw [this, map_add, map_smul, map_smul]
  simp

end PeriodAreaSignLemmas

open PeriodAreaSignLemmas

theorem areaPos_thm : AreaPos := fun L => area_pos L

theorem etaSplit_of (h : Legendre) : EtaSplit := by
  intro L x
  have hL := h L
  have hs : ((if 0 < (L.ω₂ / L.ω₁).im then 1 else -1 : ℂ)) = ((sgn L : ℤ) : ℂ) := by
    rw [sgn]
    split_ifs <;> simp
  rw [hs] at hL
  have hA : (area L : ℂ) ≠ 0 := by exact_mod_cast (area_pos L).ne'
  have hD := disc_ne_zero L
  have hDe := disc_eq L
  have hdet : (det L : ℂ) = ((sgn L : ℤ) : ℂ) * (area L : ℂ) := by
    exact_mod_cast det_eq_sgn_mul L
  set D := L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ with hDdef
  have hpi : ((Real.pi : ℂ) / (area L : ℂ)) * D
      = -(((sgn L : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    rw [hDe, hdet]
    field_simp
  have hs2 : s2 L * D = wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁ := by
    rw [s2, ← hDdef]
    field_simp
  have e1 : wEta L L.ω₁ = s2 L * L.ω₁ + ((Real.pi : ℂ) / (area L : ℂ)) * conj L.ω₁ := by
    apply mul_right_cancel₀ hD
    linear_combination (-L.ω₁) * hs2 - (conj L.ω₁) * hpi - (conj L.ω₁) * hL + wEta L L.ω₁ * hDdef
  have e2 : wEta L L.ω₂ = s2 L * L.ω₂ + ((Real.pi : ℂ) / (area L : ℂ)) * conj L.ω₂ := by
    apply mul_right_cancel₀ hD
    linear_combination (-L.ω₂) * hs2 - (conj L.ω₂) * hpi - (conj L.ω₂) * hL + wEta L L.ω₂ * hDdef
  obtain ⟨a, b, rfl⟩ := exists_coord L x
  rw [wEta_coord]
  simp [map_add, map_mul, Complex.conj_ofReal]
  linear_combination (a : ℂ) * e1 + (b : ℂ) * e2

namespace PeriodAreaSignLemmas




end PeriodAreaSignLemmas




end Formalism.L2.Th1.F
end
section
open Complex (exp exp_add exp_nat_mul)
open Filter Topology

namespace Formalism.L2.Th1.F
namespace SigmaAdditionFormula

variable (L : PeriodPair) (w : ℂ)

def additionQuotient (z : ℂ) : ℂ :=
  wSigma L (z + w) * wSigma L (z - w) / wSigma L z ^ 2 + wSigma L w ^ 2 * L.weierstrassP z

def frobeniusStickelbergerDetMulSigmaCube (z : ℂ) : ℂ :=
  wSigma L (z + w) * wSigma L (z - w)
    + wSigma L w ^ 2 * (dslope (wSigma L) 0 z ^ 2 + wSigma L z ^ 2 * L.weierstrassPExcept 0 z)

lemma semiChar_sq (ω : ℂ) : semiChar L ω ^ 2 = 1 := by
  unfold semiChar
  split_ifs <;> norm_num

lemma additionQuotient_periodic (hq : SigmaQuasi) : IsPeriodic L $ additionQuotient L w := by
  intro ω hω z
  have he : exp (wEta L ω * (z + w + ω / 2)) * exp (wEta L ω * (z - w + ω / 2))
      = exp (wEta L ω * (z + ω / 2)) ^ 2 := by
    rw [← exp_add, sq, ← exp_add]
    congr 1
    ring
  unfold additionQuotient
  rw [show z + ω + w = (z + w) + ω by ring, show z + ω - w = (z - w) + ω by ring, hq L ω (z + w) hω, hq L ω (z - w) hω, hq L ω z hω, L.weierstrassP_add_coe z ⟨ω, hω⟩]
  congr 1
  calc _ = (semiChar L ω ^ 2 * (exp (wEta L ω * (z + w + ω / 2))
          * exp (wEta L ω * (z - w + ω / 2)))) * (wSigma L (z + w) * wSigma L (z - w))
          / ((semiChar L ω ^ 2 * exp (wEta L ω * (z + ω / 2)) ^ 2) * wSigma L z ^ 2) := by
        ring
    _ = _ := by rw [semiChar_sq L ω, he, one_mul, mul_div_mul_left _ _ $ pow_ne_zero _ $ Complex.exp_ne_zero _]

lemma analyticAt_dslope (he : SigmaEntire) : AnalyticAt ℂ (dslope (wSigma L) 0) 0 := by
  obtain ⟨p, hp⟩ := (he L).analyticAt 0
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

lemma sigma_zero (hz : SigmaZero) : wSigma L 0 = 0 := (hz L 0).2 L.lattice.zero_mem

lemma dslope_neg (ho : SigmaOdd) (z : ℂ) : dslope (wSigma L) 0 (-z) = dslope (wSigma L) 0 z := by
  rcases eq_or_ne z 0 with rfl | hz0
  rw [neg_zero]
  have h0 : wSigma L 0 = 0 := by
    have := ho L 0
    rw [neg_zero] at this
    linear_combination this / 2
  rw [dslope_of_ne _ $ neg_ne_zero.2 hz0, dslope_of_ne _ hz0, slope_def_field, slope_def_field,
    ho L z, h0, sub_zero, sub_zero, sub_zero, sub_zero, neg_div_neg_eq]

lemma additionNumerator_neg (ho : SigmaOdd) (z : ℂ) : frobeniusStickelbergerDetMulSigmaCube L w (-z) = frobeniusStickelbergerDetMulSigmaCube L w z := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [dslope_neg L ho z, ho L z, L.weierstrassPExcept_neg, neg_zero,
    show -z + w = -(z - w) by ring, show -z - w = -(z + w) by ring, ho L $ z - w, ho L $ z + w]
  ring

lemma twistedGamma_analyticAt_zero (he : SigmaEntire) : AnalyticAt ℂ (frobeniusStickelbergerDetMulSigmaCube L w) 0 := by
  have hσd : Differentiable ℂ $ wSigma L := he L
  have hs : ∀ c : ℂ, AnalyticAt ℂ (fun z => wSigma L $ z + c) 0 := fun c =>
    (hσd.comp $ differentiable_id.add_const c).analyticAt 0
  have hs' : ∀ c : ℂ, AnalyticAt ℂ (fun z => wSigma L $ z - c) 0 := fun c =>
    (hσd.comp $ differentiable_id.sub_const c).analyticAt 0
  have hP :=
    L.analyticOnNhd_weierstrassPExcept 0 0 $ by simp
  have hσ : AnalyticAt ℂ (wSigma L) 0 := hσd.analyticAt 0
  exact ((hs w).mul $ hs' w).add $ analyticAt_const.mul $ ((analyticAt_dslope L he).pow 2).add $ (hσ.pow 2).mul hP

lemma twistedGamma_zero (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) : frobeniusStickelbergerDetMulSigmaCube L w 0 = 0 := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [dslope_same, (hs L).1, sigma_zero L hz, zero_add, zero_sub, ho L w]
  ring

private lemma weierstrassP_eq_except_zero_add_inv_sq (z : ℂ) : L.weierstrassP z = L.weierstrassPExcept 0 z + 1 / z ^ 2 := by
  rw [← L.weierstrassPExcept_add 0 z]
  simp

private lemma eventually_not_mem_lattice_punctured_zero : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  exact Filter.inf_principal_eq_bot.1 $ discreteTopology_subtype_iff.1 (inferInstance : DiscreteTopology L.lattice) 0 L.lattice.zero_mem

lemma additionQuotient_mul_eventuallyEq (hz : SigmaZero) :
    (fun z => additionQuotient L w z * wSigma L z ^ 2) =ᶠ[𝓝[≠] 0] frobeniusStickelbergerDetMulSigmaCube L w := by
  filter_upwards [eventually_not_mem_lattice_punctured_zero L, self_mem_nhdsWithin] with z hzL hz0
  have hσ : wSigma L z ≠ 0 := fun h => hzL $ (hz L z).1 h
  have hd : dslope (wSigma L) 0 z = wSigma L z / z := by
    rw [dslope_of_ne _ hz0, slope_def_field, sigma_zero L hz, sub_zero, sub_zero]
  unfold additionQuotient frobeniusStickelbergerDetMulSigmaCube
  rw [weierstrassP_eq_except_zero_add_inv_sq L z, hd]
  field_simp
  ring

private lemma exists_twistedGamma_eq_sq_mul_analytic (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) :
    ∃ m : ℂ → ℂ, AnalyticAt ℂ m 0 ∧ ∀ y, frobeniusStickelbergerDetMulSigmaCube L w y = y ^ 2 * m y := by

  have hder : deriv (frobeniusStickelbergerDetMulSigmaCube L w) 0 = 0 := by
    have h1 :=
      deriv_comp_neg (f := frobeniusStickelbergerDetMulSigmaCube L w) (x := 0)
    rw [funext $ additionNumerator_neg L w ho, neg_zero] at h1
    linear_combination h1 / 2
  obtain ⟨p, hp⟩ := twistedGamma_analyticAt_zero L w he
  refine ⟨dslope (dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0) 0, ⟨_, hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope⟩, fun y => ?_⟩
  have e1 := sub_smul_dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0 y
  have e2 := sub_smul_dslope (dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0) 0 y
  rw [dslope_same, hder] at e2
  simp [sub_zero, smul_eq_mul, twistedGamma_zero L w ho hz hs] at e1 e2
  rw [← e1, ← e2]
  ring


private lemma meromorphicAt_weierstrassP (z : ℂ) : MeromorphicAt L.weierstrassP z := by
  classical
  obtain ⟨l, hl⟩ : ∃ l : L.lattice, z ∉ (L.lattice : Set ℂ) \ {(l : ℂ)} := by
    by_cases h : z ∈ L.lattice
    exact ⟨⟨z, h⟩, fun h' => h'.2 rfl⟩
    exact ⟨0, fun h' => h h'.1⟩
  rw [funext fun x => (L.weierstrassPExcept_add l x).symm]
  exact (L.analyticOnNhd_weierstrassPExcept l z hl).meromorphicAt.add
    $ (analyticAt_const.meromorphicAt.div ((analyticAt_id.sub analyticAt_const).pow 2).meromorphicAt).sub
      analyticAt_const.meromorphicAt

lemma additionQuotient_meromorphicAt (he : SigmaEntire) (z : ℂ) : MeromorphicAt (additionQuotient L w) z := by
  have hσd : Differentiable ℂ $ wSigma L := he L
  exact ((((hσd.comp $ differentiable_id.add_const w).analyticAt z).mul $ (hσd.comp $ differentiable_id.sub_const w).analyticAt z).meromorphicAt.div ((hσd.analyticAt z).pow 2).meromorphicAt).add
    $ analyticAt_const.meromorphicAt.mul $ meromorphicAt_weierstrassP L z

lemma additionQuotient_analyticAt (he : SigmaEntire) (hz : SigmaZero) (z : ℂ) (hzL : z ∉ L.lattice) :
    AnalyticAt ℂ (additionQuotient L w) z := by
  have hσd : Differentiable ℂ $ wSigma L := he L
  have hσz : wSigma L z ≠ 0 := fun h => hzL $ (hz L z).1 h
  exact ((((hσd.comp $ differentiable_id.add_const w).analyticAt z).mul $ (hσd.comp $ differentiable_id.sub_const w).analyticAt z).div ((hσd.analyticAt z).pow 2) $ pow_ne_zero _ hσz).add $ analyticAt_const.mul $ by
      rw [show L.weierstrassP = fun x => L.weierstrassPExcept 0 x + 1 / x ^ 2 from funext $ weierstrassP_eq_except_zero_add_inv_sq L]
      exact (L.analyticOnNhd_weierstrassPExcept 0 z fun h => hzL h.1).add
        $ analyticAt_const.div (analyticAt_id.pow 2) $ pow_ne_zero _ $ by
            rintro rfl
            exact hzL L.lattice.zero_mem

private lemma exists_analytic_eq_additionQuotient_near_zero (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ additionQuotient L w =ᶠ[𝓝[≠] 0] A := by
  obtain ⟨m, hm, hgm⟩ := exists_twistedGamma_eq_sq_mul_analytic L w he ho hz hs
  have hd := analyticAt_dslope L he
  have hd0 : dslope (wSigma L) 0 0 ≠ 0 := by
    rw [dslope_same, (hs L).1]
    exact one_ne_zero
  have hσ : ∀ y, wSigma L y = y * dslope (wSigma L) 0 y := fun y => by
    have := sub_smul_dslope (wSigma L) 0 y
    simp [sub_zero, smul_eq_mul, sigma_zero L hz] at this
    exact this.symm
  use fun y => m y / dslope (wSigma L) 0 y ^ 2, hm.div (hd.pow 2) $ pow_ne_zero _ hd0
  filter_upwards [additionQuotient_mul_eventuallyEq L w hz, (hd.continuousAt.eventually_ne hd0).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y h1 h2 h3
  rw [hgm, hσ y] at h1
  rw [eq_div_iff $ pow_ne_zero _ h2]
  apply mul_left_cancel₀ $ pow_ne_zero 2 h3
  linear_combination h1


lemma additionQuotient_order (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple)
    (hq : SigmaQuasi) (hord : SigmaOrder) (z : ℂ) : 0 ≤ meromorphicOrderAt (additionQuotient L w) z := by
  by_cases hzL : z ∈ L.lattice
  obtain ⟨A, hA, hfA⟩ := exists_analytic_eq_additionQuotient_near_zero L w he ho hz hs
  have hfun : additionQuotient L w = fun x => additionQuotient L w $ x - z := funext fun x => by
    have := additionQuotient_periodic L w hq (-z) (neg_mem hzL) x
    rw [← sub_eq_add_neg] at this
    exact this.symm
  have ht : Filter.Tendsto (fun x => x - z) (𝓝[≠] z) $ 𝓝[≠] 0 :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_id.sub continuous_const).tendsto' z 0 $ sub_self z).mono_left
        nhdsWithin_le_nhds)
      (Filter.mem_of_superset self_mem_nhdsWithin fun x hx => sub_ne_zero.2 hx)
  have h2 : (fun x => additionQuotient L w $ x - z) =ᶠ[𝓝[≠] z] fun x => A $ x - z := ht.eventually hfA
  rw [hfun, meromorphicOrderAt_congr h2]
  exact (hA.comp_of_eq (analyticAt_id.sub analyticAt_const) $ sub_self z).meromorphicOrderAt_nonneg
  exact (additionQuotient_analyticAt L w he hz z hzL).meromorphicOrderAt_nonneg

end SigmaAdditionFormula

open SigmaAdditionFormula in
theorem sigmaAdd_of (hN : EllipticNoPole) (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero)
    (hs : SigmaSimple) (hq : SigmaQuasi) (hord : SigmaOrder) : SigmaAdd := by
  intro L z w hzL hwL
  obtain ⟨c, hc⟩ := hN L (additionQuotient L w) (additionQuotient_meromorphicAt L w he) (additionQuotient_periodic L w hq)
    $ additionQuotient_order L w he ho hz hs hq hord
  have hfz := hc z (additionQuotient_analyticAt L w he hz z hzL).continuousAt
  have hσz : wSigma L z ≠ 0 := fun h => hzL $ (hz L z).1 h
  rw [← hc w (additionQuotient_analyticAt L w he hz w hwL).continuousAt] at hfz
  unfold additionQuotient at hfz
  rw [sub_self, sigma_zero L hz, mul_zero, zero_div, zero_add] at hfz
  have e : wSigma L (z + w) * wSigma L (z - w) / wSigma L z ^ 2 * wSigma L z ^ 2
      = wSigma L (z + w) * wSigma L (z - w) := div_mul_cancel₀ _ $ pow_ne_zero 2 hσz
  linear_combination (wSigma L z ^ 2) * hfz - e

theorem sgStarAdd_of (h : SigmaAdd) : SgStarAdd := by
  intro L z w hz hw
  unfold sgStar
  have ex : exp (-(s2 L) * (z + w) ^ 2 / 2) * exp (-(s2 L) * (z - w) ^ 2 / 2)
      = exp (-(s2 L) * z ^ 2 / 2) ^ 2 * exp (-(s2 L) * w ^ 2 / 2) ^ 2 := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  calc _ = (wSigma L (z + w) * wSigma L (z - w)) * (exp (-(s2 L) * (z + w) ^ 2 / 2)
          * exp (-(s2 L) * (z - w) ^ 2 / 2)) := by ring
    _ = _ := by
        rw [h L z w hz hw, ex]
        ring

theorem pInjective_of (h : SigmaAdd) (hz : SigmaZero) : PInjective := by
  intro L z w hzL hwL
  have e := h L z w hzL hwL
  have hσz : wSigma L z ≠ 0 := fun h' => hzL $ (hz L z).1 h'
  have hσw : wSigma L w ≠ 0 := fun h' => hwL $ (hz L w).1 h'
  constructor
  intro hP
  rw [hP, sub_self, mul_zero, neg_zero] at e
  rcases mul_eq_zero.1 e with h1 | h1
  exact Or.inr $ (hz L _).1 h1
  exact Or.inl $ (hz L _).1 h1
  intro hor
  have h0 : wSigma L (z + w) * wSigma L (z - w) = 0 := by
    rcases hor with h1 | h1
    rw [(hz L _).2 h1, mul_zero]
    rw [(hz L _).2 h1, zero_mul]
  rw [h0] at e
  have h3 : wSigma L z ^ 2 * wSigma L w ^ 2 * (L.weierstrassP z - L.weierstrassP w) = 0 := by
    linear_combination e
  rcases mul_eq_zero.1 h3 with h1 | h1
  exact absurd h1 $ mul_ne_zero (pow_ne_zero _ hσz) $ pow_ne_zero _ hσw
  exact sub_eq_zero.1 h1

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate
open Filter

namespace Formalism.L2.Th1.F

namespace SigmaBasic

lemma differentiable_wFactor (l : ℂ) : Differentiable ℂ $ wFactor l := by
  unfold wFactor
  fun_prop

lemma wFactor_zero_right (l : ℂ) : wFactor l 0 = 1 := by
  simp [wFactor]

lemma wFactor_neg_neg (l z : ℂ) : wFactor (-l) (-z) = wFactor l z := by
  simp [wFactor, neg_div_neg_eq, neg_sq]

lemma wFactor_eq_zero_iff {l : ℂ} (hl : l ≠ 0) (z : ℂ) : wFactor l z = 0 ↔ z = l := by
  unfold wFactor
  rw [mul_eq_zero, or_iff_left $ Complex.exp_ne_zero _, sub_eq_zero, eq_comm, div_eq_one_iff_eq hl]

lemma wFactor_zero_left (z : ℂ) : wFactor 0 z = 1 := by
  simp [wFactor]

lemma differentiable_tprod (h : SigmaProdLU) (L : PeriodPair) :
    Differentiable ℂ fun z => ∏' l : L.lattice, wFactor (l : ℂ) z := by
  rw [← differentiableOn_univ]
  refine TendstoLocallyUniformlyOn.differentiableOn (h L) ?_ isOpen_univ
  refine Eventually.of_forall fun s => ?_
  refine Differentiable.differentiableOn ?_
  intro x
  exact DifferentiableAt.fun_finset_prod fun l _ => differentiable_wFactor _ x

end SigmaBasic

open SigmaBasic

theorem sigmaEntire_of (h : SigmaProdLU) : SigmaEntire := by
  intro L
  unfold wSigma
  exact differentiable_id.mul $ differentiable_tprod h L

theorem sigma_odd : SigmaOdd := by
  intro L z
  have hP : ∏' l : L.lattice, wFactor (l : ℂ) (-z) = ∏' l : L.lattice, wFactor (l : ℂ) z := by
    rw [← (Equiv.neg L.lattice).tprod_eq fun l : L.lattice => wFactor (l : ℂ) $ -z]
    congr 1
    ext l
    simp [wFactor_neg_neg]
  unfold wSigma
  rw [hP]
  ring

theorem sigmaZero_of (h : SigmaSummable) : SigmaZero := by
  intro L z
  unfold wSigma
  constructor
  intro h0
  rcases mul_eq_zero.mp h0 with hz | hp
  rw [hz]
  exact zero_mem _
  by_contra hz
  have hne : ∀ l : L.lattice, wFactor (l : ℂ) z ≠ 0 := by
    intro l hl
    by_cases hl0 : (l : ℂ) = 0
    rw [hl0, wFactor_zero_left] at hl
    exact one_ne_zero hl
    rw [wFactor_eq_zero_iff hl0] at hl
    apply hz
    rw [hl]
    exact l.2
  have hs : Summable fun l : L.lattice => Complex.log $ wFactor (l : ℂ) z := by
    have := Complex.summable_log_one_add_of_summable $ Summable.of_norm $ h L z
    simpa [add_sub_cancel] using this
  rw [← Complex.cexp_tsum_eq_tprod hne hs] at hp
  exact Complex.exp_ne_zero _ hp
  intro hz
  by_cases hz0 : z = 0
  rw [hz0, zero_mul]
  rw [tprod_of_exists_eq_zero ⟨⟨z, hz⟩, (wFactor_eq_zero_iff hz0 z).mpr rfl⟩, mul_zero]

theorem sigmaDerivZero_of (h : SigmaProdLU) : ∀ L : PeriodPair, deriv (wSigma L) 0 = 1 := by
  intro L
  unfold wSigma
  rw [deriv_fun_mul (by fun_prop) $ differentiable_tprod h L 0]
  simp [wFactor_zero_right]

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate
open Filter

namespace Formalism.L2.Th1.F

namespace SigmaConv

lemma norm_factor_sub_one_le (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) :
    ‖(1 - w) * Complex.exp (w + w ^ 2 / 2) - 1‖ ≤ 2 * ‖w‖ ^ 3 := by
  set f : ℂ → ℂ := fun x => (1 - x) * Complex.exp (x + x ^ 2 / 2) with hf
  have hder : ∀ x : ℂ, HasDerivAt f (-(x ^ 2) * Complex.exp (x + x ^ 2 / 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℂ => x + x ^ 2 / 2) (1 + x) x := by
      apply ((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv
      first | (norm_num; done) | (norm_num; ring) | ring
    apply (((hasDerivAt_id x).const_sub (1 : ℂ)).mul h1.cexp).congr_deriv
    simp [id]
    ring
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) ‖w‖,
      ‖-(x ^ 2) * Complex.exp (x + x ^ 2 / 2)‖ ≤ 2 * ‖w‖ ^ 2 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have hx2 := hx.trans hw
    rw [norm_mul, norm_neg, norm_pow, Complex.norm_exp]
    have h3 : ‖x + x ^ 2 / 2‖ ≤ ‖x‖ + ‖x‖ ^ 2 / 2 := by
      calc ‖x + x ^ 2 / 2‖ ≤ ‖x‖ + ‖x ^ 2 / 2‖ := norm_add_le _ _
        _ = ‖x‖ + ‖x‖ ^ 2 / 2 := by rw [norm_div, norm_pow]
                                    norm_num
    have hre : (x + x ^ 2 / 2).re ≤ 5 / 8 := by
      have := Complex.re_le_norm (x + x ^ 2 / 2)
      nlinarith [norm_nonneg x]
    have he : Real.exp ((x + x ^ 2 / 2).re) ≤ 2 := by
      calc Real.exp ((x + x ^ 2 / 2).re) ≤ Real.exp (5 / 8) := Real.exp_le_exp.mpr hre
        _ ≤ 2 := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          apply Real.exp_le_exp.mpr
          have := Real.log_two_gt_d9
          norm_num at this ⊢
          linarith
    have hx2' : ‖x‖ ^ 2 ≤ ‖w‖ ^ 2 := by gcongr
    calc ‖x‖ ^ 2 * Real.exp ((x + x ^ 2 / 2).re) ≤ ‖w‖ ^ 2 * 2 :=
          mul_le_mul hx2' he (Real.exp_pos _).le (sq_nonneg _)
      _ = 2 * ‖w‖ ^ 2 := by ring
  have key := (convex_closedBall (0 : ℂ) ‖w‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hder x).hasDerivWithinAt) hbound (Metric.mem_closedBall_self (norm_nonneg w)) (by rw [Metric.mem_closedBall, dist_zero_right])
  have f0 : f 0 = 1 := by simp [f]
  rw [f0, sub_zero] at key
  calc ‖f w - 1‖ ≤ 2 * ‖w‖ ^ 2 * ‖w‖ := key
    _ = 2 * ‖w‖ ^ 3 := by ring

lemma wFactor_eq (l z : ℂ) :
    wFactor l z = (1 - z / l) * Complex.exp (z / l + (z / l) ^ 2 / 2) := by
  unfold wFactor
  congr 2
  ring

lemma norm_wFactor_sub_one_le (r : ℝ) (l z : ℂ) (hz : ‖z‖ ≤ r) (hl : 2 * r ≤ ‖l‖) :
    ‖wFactor l z - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hrp : ‖l‖ ^ (-3 : ℝ) = (‖l‖ ^ 3)⁻¹ := by
    rw [Real.rpow_neg $ norm_nonneg _]
    norm_cast
  rcases eq_or_ne l 0 with rfl | hl0
  have h1 : wFactor 0 z = 1 := by simp [wFactor]
  rw [h1, sub_self, norm_zero]
  exact mul_nonneg (mul_nonneg (by norm_num) $ pow_nonneg ((norm_nonneg z).trans hz) 3) $ Real.rpow_nonneg le_rfl _
  calc ‖wFactor l z - 1‖ ≤ 2 * ‖z / l‖ ^ 3 := by
        rw [wFactor_eq]
        exact norm_factor_sub_one_le _ $ by
            rw [norm_div, div_le_iff₀ $ norm_pos_iff.mpr hl0]
            linarith
    _ = 2 * ‖z‖ ^ 3 * (‖l‖ ^ 3)⁻¹ := by rw [norm_div, div_pow]
                                        ring
    _ ≤ 2 * r ^ 3 * (‖l‖ ^ 3)⁻¹ := by gcongr
    _ = 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by rw [hrp]

private lemma summable_norm_lattice_rpow_neg_three (L : PeriodPair) :
    Summable fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ) := by
  have hfin : Module.finrank ℤ L.lattice = 2 := by
    rw [ZLattice.rank ℝ L.lattice, Complex.finrank_real_complex]
  apply ZLattice.summable_norm_rpow L.lattice $ -3
  rw [hfin]
  norm_num
lemma summable_majorant (L : PeriodPair) (r : ℝ) :
    Summable fun l : L.lattice => 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) :=
  (summable_norm_lattice_rpow_neg_three L).mul_left _

lemma eventually_large (L : PeriodPair) (R : ℝ) :
    ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  rcases le_or_gt R 0 with hR | hR
  exact Eventually.of_forall fun l => hR.trans (norm_nonneg _)
  have hε : (0 : ℝ) < R ^ (-3 : ℝ) := Real.rpow_pos_of_pos hR _
  filter_upwards [((summable_norm_lattice_rpow_neg_three L).tendsto_cofinite_zero).eventually (gt_mem_nhds hε), eventually_cofinite_ne 0] with l hl hl0
  by_contra hlt
  push_neg at hlt
  have := Real.rpow_le_rpow_of_nonpos (by
      rw [norm_pos_iff]
      exact fun h => hl0 (Subtype.ext h)) hlt.le (by norm_num : (-3 : ℝ) ≤ 0)
  linarith

lemma continuous_wFactor (l : ℂ) : Continuous $ wFactor l := by
  unfold wFactor
  fun_prop

end SigmaConv

open SigmaConv

theorem sigma_summable : SigmaSummable := by
  intro L z
  refine Summable.of_norm_bounded_eventually (summable_majorant L ‖z‖) ?_
  filter_upwards [eventually_large L $ 2 * ‖z‖] with l hl
  rw [norm_norm]
  exact norm_wFactor_sub_one_le ‖z‖ l z le_rfl hl

theorem sigma_product_locally_uniform : SigmaProdLU := by
  intro L
  have key : HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) => 1 + (wFactor (l : ℂ) z - 1))
      (fun z => ∏' l : L.lattice, (1 + (wFactor (l : ℂ) z - 1))) Set.univ := by
    rw [HasProdLocallyUniformlyOn, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    refine HasProdUniformlyOn.tendstoUniformlyOn $ Summable.hasProdUniformlyOn_one_add (f := fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z - 1)
      hK (summable_majorant L r) ?_ ?_
    filter_upwards [eventually_large L $ 2 * r] with l hl x hx
    exact norm_wFactor_sub_one_le r l x (by simpa using hr hx) hl
    intro l
    exact ((continuous_wFactor _).sub continuous_const).continuousOn
  simpa [add_sub_cancel] using key

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate
open Filter

namespace Formalism.L2.Th1.F

namespace ModifiedSigmaBounds

lemma semiChar_sq (L : PeriodPair) (ω : ℂ) : semiChar L ω * semiChar L ω = 1 := by
  unfold semiChar
  split_ifs <;> norm_num


end ModifiedSigmaBounds

open ModifiedSigmaBounds

theorem sgStarQuasi_of (hq : SigmaQuasi) (he : EtaSplit) : SgStarQuasi := by
  intro L ω z hω
  simp only [sgStar]
  rw [hq L ω z hω, he L ω]
  have key : Complex.exp ((s2 L * ω + ((Real.pi : ℂ) / (area L : ℂ)) * conj ω) * (z + ω / 2))
        * Complex.exp (-(s2 L) * (z + ω) ^ 2 / 2)
      = Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
        * Complex.exp (-(s2 L) * z ^ 2 / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [herm]
    ring
  linear_combination (semiChar L ω * wSigma L z) * key



namespace ModifiedSigmaBounds

open SigmaConv

lemma eventually_small (L : PeriodPair) :
    ∀ᶠ z : ℂ in nhds 0, ∀ l : L.lattice, (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖ := by
  have hlim : Tendsto (fun z : ℂ => 2 * ‖z‖) (nhds 0) $ nhds 0 := by
    have hc : Continuous fun z : ℂ => 2 * ‖z‖ := by fun_prop
    simpa using hc.tendsto 0
  have hfin : {l : L.lattice | ¬ (1 : ℝ) ≤ ‖(l : ℂ)‖}.Finite := eventually_large L 1
  have h1 : ∀ᶠ z : ℂ in nhds 0, ∀ l ∈ {l : L.lattice | ¬ (1 : ℝ) ≤ ‖(l : ℂ)‖},
      (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖ := by
    rw [Filter.eventually_all_finite hfin]
    intro l _
    by_cases hl : (l : ℂ) = 0
    simp [hl]
    filter_upwards [hlim.eventually_le_const $ norm_pos_iff.mpr hl] with z hz _ using hz
  filter_upwards [h1, hlim.eventually_le_const one_pos] with z hz1 hz2 l hl
  by_cases h : 1 ≤ ‖(l : ℂ)‖
  exact hz2.trans h
  exact hz1 l h hl

lemma norm_tprod_sub_one_le (hs : SigmaSummable) (L : PeriodPair) (z : ℂ)
    (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖) :
    ‖∏' l : L.lattice, wFactor (l : ℂ) z - 1‖
      ≤ Real.exp (∑' l : L.lattice, 2 * ‖z‖ ^ 3 * ‖l‖ ^ (-3 : ℝ)) - 1 := by
  have ht :=
    (Tendsto.sub_const (multipliable_one_add_of_summable $ hs L z).hasProd 1).norm
  simp only [add_sub_cancel] at ht
  refine le_of_tendsto ht $ Eventually.of_forall fun t => ?_
  have h1 := t.norm_prod_one_add_sub_one_le fun l : L.lattice => wFactor (l : ℂ) z - 1
  simp only [add_sub_cancel] at h1
  refine h1.trans ?_
  have h2 : ∑ l ∈ t, ‖wFactor (l : ℂ) z - 1‖ ≤ ∑' l : L.lattice, 2 * ‖z‖ ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
    refine (Finset.sum_le_sum fun l _ => ?_).trans
      $ (summable_majorant L ‖z‖).sum_le_tsum t fun l _ => by positivity
    by_cases hl : (l : ℂ) = 0
    simp only [hl, wFactor, div_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero, Complex.exp_zero, mul_one, sub_self, norm_zero]
    positivity
    exact norm_wFactor_sub_one_le ‖z‖ l z le_rfl $ hz l hl
  have := Real.exp_le_exp.mpr h2
  linarith

lemma sigma_sub_id_bound (hs : SigmaSummable) (L : PeriodPair) :
    ∃ K r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → ‖wSigma L z - z‖ ≤ K * ‖z‖ ^ 4 := by
  set C : ℝ := ∑' l : L.lattice, ‖l‖ ^ (-3 : ℝ) with hC
  have hlim : Tendsto (fun z : ℂ => 2 * ‖z‖ ^ 3 * C) (nhds 0) $ nhds 0 := by
    have : Continuous fun z : ℂ => 2 * ‖z‖ ^ 3 * C := by fun_prop
    simpa using this.tendsto 0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp $ (eventually_small L).and $ hlim.eventually_le_const one_pos
  refine ⟨4 * C, r, hr, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hball $ by simpa using hz
  have hb := norm_tprod_sub_one_le hs L z h1
  rw [tsum_mul_left, ← hC] at hb
  have hx0 : 0 ≤ 2 * ‖z‖ ^ 3 * C := by positivity
  have hexp := Real.abs_exp_sub_one_le (x := 2 * ‖z‖ ^ 3 * C) $ by rwa [abs_of_nonneg hx0]
  rw [abs_of_nonneg hx0] at hexp
  have heq : wSigma L z - z = z * (∏' l : L.lattice, wFactor (l : ℂ) z - 1) := by
    simp [wSigma]
    ring
  rw [heq, norm_mul]
  calc ‖z‖ * ‖∏' l : L.lattice, wFactor (l : ℂ) z - 1‖
      ≤ ‖z‖ * (2 * (2 * ‖z‖ ^ 3 * C)) := by
        gcongr
        exact hb.trans $ (le_abs_self _).trans hexp
    _ = 4 * C * ‖z‖ ^ 4 := by ring

lemma iteratedDeriv_eq_zero_of_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f) {K r : ℝ} (hr : 0 < r)
    (hb : ∀ z, ‖z‖ < r → ‖f z‖ ≤ K * ‖z‖ ^ 4) (n : ℕ) (hn : n < 4) : iteratedDeriv n f 0 = 0 := by
  rw [← norm_le_zero_iff]
  have hev : ∀ᶠ R in nhdsWithin (0 : ℝ) $ Set.Ioi 0,
      ‖iteratedDeriv n f 0‖ ≤ n.factorial * K * R ^ (4 - n) := by
    filter_upwards [Ioo_mem_nhdsGT hr] with R hR
    have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR.1
      (c := 0) hf.diffContOnCl (C := K * R ^ 4) fun z hz => by
        have hz' : ‖z‖ = R := by simpa using hz
        have := hb z $ hz' ▸ hR.2
        rwa [hz'] at this
    refine h1.trans $ le_of_eq ?_
    have h2 : R ^ 4 = R ^ (4 - n) * R ^ n := by rw [← pow_add, Nat.sub_add_cancel hn.le]
    have h3 : R ^ n ≠ 0 := pow_ne_zero _ hR.1.ne'
    rw [h2]
    field_simp
  exact ge_of_tendsto (by
      have hc : Continuous fun R : ℝ => n.factorial * K * R ^ (4 - n) := by fun_prop
      have h0 := hc.tendsto 0
      rw [zero_pow $ by omega, mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds) hev

end ModifiedSigmaBounds

open ModifiedSigmaBounds in
theorem sigmaTaylorLow_of (he : SigmaEntire) (hs : SigmaSummable) :
    ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0 := by
  intro L
  obtain ⟨K, r, hr, hb⟩ := sigma_sub_id_bound hs L
  have hd : Differentiable ℂ fun z => wSigma L z - z := (he L).sub differentiable_id
  have key : ∀ n : ℕ, n < 4 → n ≠ 1 → iteratedDeriv n (wSigma L) 0 = 0 := by
    intro n hn hn1
    have h0 := iteratedDeriv_eq_zero_of_bound hd hr hb n hn
    rw [iteratedDeriv_fun_sub ((he L).contDiff.contDiffAt) $ contDiff_fun_id.contDiffAt,
      iteratedDeriv_fun_id_zero, if_neg hn1, sub_zero] at h0
    exact h0
  exact ⟨key 2 (by norm_num) $ by norm_num, key 3 (by norm_num) $ by norm_num⟩

theorem sgStarBasic_of (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (h1 : SigmaSimple)
    (h3 : ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0) :
    SgStarBasic := by
  intro L
  set e : ℂ → ℂ := fun z => Complex.exp (-(s2 L) * z ^ 2 / 2) with he_def
  have hed : Differentiable ℂ e := by
    rw [he_def]
    fun_prop
  have hfun : sgStar L = wSigma L * e := rfl
  have hs0 := (hz L 0).mpr L.lattice.zero_mem
  have he0 : e 0 = 1 := by simp [he_def]
  have hde : deriv e = fun z => -(s2 L) * z * e z := by
    funext z
    have h : HasDerivAt (fun z : ℂ => -(s2 L) * z ^ 2 / 2) (-(s2 L) * (2 * z) / 2) z := by
      have := ((hasDerivAt_pow 2 z).const_mul $ -(s2 L)).div_const 2
      simpa using this
    rw [h.cexp.deriv]
    ring
  have he1 : deriv e 0 = 0 := by rw [hde]
                                 simp
  have he2 : iteratedDeriv 2 e 0 = -(s2 L) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hde]
    have h : HasDerivAt (fun z : ℂ => -(s2 L) * z * e z)
        (-(s2 L) * e 0 + -(s2 L) * 0 * deriv e 0) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).const_mul $ -(s2 L)).fun_mul (hed 0).hasDerivAt
      simpa using this
    rw [h.deriv, he0]
    ring
  refine ⟨(he L).mul hed, ?_, ?_, ?_, ?_⟩
  intro z
  simp [sgStar, ho L z]
  intro z
  simp [sgStar, hz L z, Complex.exp_ne_zero]
  rw [hfun, deriv_mul (he L 0) $ hed 0, (h1 L).1, he0, hs0, he1]
  ring
  rw [hfun, iteratedDeriv_mul (he L).contDiff.contDiffAt hed.contDiff.contDiffAt]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, iteratedDeriv_zero,
    iteratedDeriv_one, hs0, (h1 L).1, (h3 L).1, (h3 L).2, he2]
  norm_num [Nat.choose]

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace SigmaLog

lemma hasDerivAt_wFactor (l z : ℂ) :
    HasDerivAt (wFactor l)
      (-(1 / l) * Complex.exp (z / l + z ^ 2 / (2 * l ^ 2))
        + (1 - z / l) * (Complex.exp (z / l + z ^ 2 / (2 * l ^ 2)) * (1 / l + 2 * z / (2 * l ^ 2)))) z := by
  have h1 : HasDerivAt (fun z : ℂ => 1 - z / l) (-(1 / l)) z := by
    simpa using ((hasDerivAt_id z).div_const l).const_sub 1
  have h2 : HasDerivAt (fun z : ℂ => z / l + z ^ 2 / (2 * l ^ 2)) (1 / l + 2 * z / (2 * l ^ 2)) z := by
    have := ((hasDerivAt_id z).div_const l).fun_add $ (hasDerivAt_pow 2 z).div_const $ 2 * l ^ 2
    simpa using this
  exact h1.mul h2.cexp

lemma differentiable_wFactor (l : ℂ) : Differentiable ℂ $ wFactor l :=
  fun z => (hasDerivAt_wFactor l z).differentiableAt

lemma wFactor_ne_zero {l z : ℂ} (h : z ≠ l) : wFactor l z ≠ 0 := by
  unfold wFactor
  refine mul_ne_zero ?_ $ Complex.exp_ne_zero _
  by_cases hl : l = 0
  simp [hl]
  intro h0
  apply h
  field_simp at h0
  linear_combination -h0

lemma logDeriv_wFactor {l z : ℂ} (h : z ≠ l) :
    logDeriv (wFactor l) z
      = (1 / (z - l) + 1 / l + z / l ^ 2) - (if l = 0 then 1 / z else 0) := by
  rw [logDeriv_apply, (hasDerivAt_wFactor l z).deriv]
  by_cases hl : l = 0
  simp [hl, wFactor]
  have h1 : z - l ≠ 0 := sub_ne_zero.mpr h
  have h2 : 1 - z / l ≠ 0 := by
    intro h0
    apply h
    field_simp at h0
    linear_combination -h0
  rw [if_neg hl, wFactor, sub_zero, div_eq_iff $ mul_ne_zero h2 $ Complex.exp_ne_zero $ z / l + z ^ 2 / (2 * l ^ 2)]
  field_simp
  ring

end SigmaLog

open SigmaLog in
theorem sigmaLogDeriv_of (h1 : SigmaProdLU) (h2 : SigmaSummable) (h3 : ZetaSummable) :
    SigmaLogDeriv := by
  intro L z hz
  have hne : ∀ l : L.lattice, z ≠ (l : ℂ) := fun l h => hz (h ▸ l.2)
  have hz0 : z ≠ 0 := fun h => hz (h ▸ L.lattice.zero_mem)
  set P : ℂ → ℂ := fun z => ∏' l : L.lattice, wFactor (l : ℂ) z with hP

  have hPne : P z ≠ 0 := by
    have := tprod_one_add_ne_zero_of_summable (f := fun l : L.lattice => wFactor (l : ℂ) z - 1)
      (fun l => by simpa using wFactor_ne_zero (hne l)) (h2 L z)
    simpa [hP] using this

  have hPd : DifferentiableOn ℂ P Set.univ := by
    refine (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp (h1 L)).differentiableOn (.of_forall fun s => ?_) isOpen_univ
    exact DifferentiableOn.fun_finsetProd fun i _ => (differentiable_wFactor _).differentiableOn

  have hc : HasSum (fun l : L.lattice => if (l : ℂ) = 0 then 1 / z else 0) (1 / z) := by
    have : (fun l : L.lattice => if (l : ℂ) = 0 then 1 / z else 0)
        = fun l : L.lattice => if l = 0 then 1 / z else 0 := by
      funext l
      simp
    rw [this]
    exact hasSum_ite_eq 0 (1 / z)
  have hs : HasSum (fun l : L.lattice => logDeriv (wFactor (l : ℂ)) z) (wZeta L z - 1 / z) := by
    have := (h3 L z).hasSum.sub hc
    have he : (fun l : L.lattice => logDeriv (wFactor (l : ℂ)) z)
        = fun l : L.lattice => (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
            - (if (l : ℂ) = 0 then 1 / z else 0) := by
      funext l
      exact logDeriv_wFactor (hne l)
    rwa [he]
  have hlog : logDeriv P z = wZeta L z - 1 / z := by
    have := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ z)
      (f := fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z) (fun l => wFactor_ne_zero (hne l))
      (fun l => (differentiable_wFactor _).differentiableOn) hs.summable
      (h1 L).multipliableLocallyUniformlyOn hPne
    rwa [hs.tsum_eq] at this
  have hPderiv : HasDerivAt P ((wZeta L z - 1 / z) * P z) z := by
    have := ((hPd z (Set.mem_univ z)).differentiableAt Filter.univ_mem).hasDerivAt
    rwa [← hlog, logDeriv_apply, div_mul_cancel₀ _ hPne]
  have := (hasDerivAt_id z).mul hPderiv
  have he : wZeta L z * wSigma L z = 1 * P z + id z * ((wZeta L z - 1 / z) * P z) := by
    simp [wSigma, id, hP]
    field_simp
    ring
  rwa [he]

end Formalism.L2.Th1.F
end
section
namespace Formalism.L2.Th1.F

theorem sigmaOrder_of (he : SigmaEntire) (hz : SigmaZero) (hs : SigmaSimple) : SigmaOrder := by
  intro L a b z ha
  classical
  set f : ℂ → ℂ := fun w => wSigma L (a * w + b) with hfdef
  have hfd : Differentiable ℂ f := (he L).comp $ (differentiable_id.const_mul a).add_const b
  have hfa : AnalyticAt ℂ f z := hfd.analyticAt z
  have hder : HasDerivAt f (deriv (wSigma L) (a * z + b) * (a * 1)) z := by
    have h1 : HasDerivAt (fun w : ℂ => a * w + b) (a * 1) z :=
      ((hasDerivAt_id z).const_mul a).add_const b
    exact ((he L) $ a * z + b).hasDerivAt.comp z h1
  rw [hfa.meromorphicOrderAt_eq]
  split_ifs with hmem
  have h0 : f z = 0 := (hz L $ a * z + b).2 hmem
  have hord : analyticOrderAt f z = ((1 : ℕ) : ℕ∞) := by
    rw [hfa.analyticOrderAt_eq_natCast]
    refine ⟨dslope f z, ?_, ?_, ?_⟩
    have hon : DifferentiableOn ℂ (dslope f z) Set.univ :=
      (Complex.differentiableOn_dslope Filter.univ_mem).2 hfd.differentiableOn
    exact (differentiableOn_univ.1 hon).analyticAt z
    rw [dslope_same, hder.deriv]
    apply mul_ne_zero $ (hs L).2 _ hmem
    simpa using ha
    filter_upwards with w
    rw [pow_one, sub_smul_dslope, h0, sub_zero]
  rw [hord]
  rfl
  have hne : f z ≠ 0 := fun h => hmem $ (hz L $ a * z + b).1 h
  rw [analyticOrderAt_eq_zero.2 $ Or.inr hne]
  rfl

end Formalism.L2.Th1.F
end
section
open Complex (exp exp_add exp_zero real_smul)
open Formalism.L2.Th1.F (semiChar wEta wSigma wZeta)
namespace Formalism.L2.Th1.F

namespace PeriodLatticeBasisLemmas

private theorem mem_lattice_iff_exists_int_comb' (L : PeriodPair) {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ = x := by
  exact L.mem_lattice

private theorem periodPair_basis_zero_eq_omega_one (L : PeriodPair) : L.basis 0 = L.ω₁ := by
  exact L.basis_zero

private theorem periodPair_basis_one_eq_omega_two (L : PeriodPair) : L.basis 1 = L.ω₂ := by
  exact L.basis_one

private theorem basis_equivFun_real_comb_periods (L : PeriodPair) (s t : ℝ) :
    L.basis.equivFun ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) = ![s, t] := by
  have e : ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) = L.basis.equivFun.symm ![s, t] := by
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, periodPair_basis_zero_eq_omega_one, periodPair_basis_one_eq_omega_two]
    simp [real_smul]
  rw [e, LinearEquiv.apply_symm_apply]

private theorem lattice_eq_iInter_preimage_int_coords (L : PeriodPair) :
    (L.lattice : Set ℂ) = ⋂ i : Fin 2, (fun x => L.basis.equivFun x i) ⁻¹' Set.range ((↑) : ℤ → ℝ) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
  constructor
  intro hx i
  obtain ⟨m, n, rfl⟩ := (mem_lattice_iff_exists_int_comb' L).mp hx
  have h : L.basis.equivFun ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) = ![(m : ℝ), (n : ℝ)] := by
    exact_mod_cast basis_equivFun_real_comb_periods L m n
  rw [h]
  fin_cases i
  exact ⟨m, rfl⟩
  exact ⟨n, rfl⟩
  intro h
  obtain ⟨m, hm⟩ := h 0
  obtain ⟨n, hn⟩ := h 1
  refine (mem_lattice_iff_exists_int_comb' L).mpr ⟨m, n, ?_⟩
  have hs := L.basis.sum_equivFun x
  rw [Fin.sum_univ_two, periodPair_basis_zero_eq_omega_one, periodPair_basis_one_eq_omega_two, ← hm, ← hn] at hs
  rw [← hs]
  simp [real_smul]

private theorem isClosed_periodPair_lattice (L : PeriodPair) : IsClosed (L.lattice : Set ℂ) := by
  rw [lattice_eq_iInter_preimage_int_coords]
  refine isClosed_iInter fun i => ?_
  exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage $ (continuous_apply i).comp $ LinearMap.continuous_of_finiteDimensional L.basis.equivFun.toLinearMap

lemma isOpen_compl (L : PeriodPair) : IsOpen $ (L.lattice : Set ℂ)ᶜ :=
  (isClosed_periodPair_lattice L).isOpen_compl

lemma isPreconnected_compl (L : PeriodPair) : IsPreconnected $ (L.lattice : Set ℂ)ᶜ := by
  have hc : (L.lattice : Set ℂ).Countable := by
    refine (Set.countable_range fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂).mono ?_
    intro x hx
    obtain ⟨m, n, rfl⟩ := (mem_lattice_iff_exists_int_comb' L).mp hx
    exact ⟨(m, n), rfl⟩
  exact (hc.isPathConnected_compl_of_one_lt_rank $ by
      rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
      norm_num).isConnected.isPreconnected

lemma add_notMem {L : PeriodPair} {ω z : ℂ} (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    z + ω ∉ L.lattice := by
  intro h
  apply hz
  have h2 := L.lattice.sub_mem h hω
  rwa [add_sub_cancel_right] at h2

def QP (L : PeriodPair) (ω c : ℂ) : Prop :=
  ∀ z : ℂ, wSigma L (z + ω) = c * exp (wEta L ω * (z + ω / 2)) * wSigma L z

lemma exists_const (hq : ZetaQuasi) (hl : SigmaLogDeriv) (hz : SigmaZero) (L : PeriodPair) {ω : ℂ}
    (hω : ω ∈ L.lattice) :
    ∃ c : ℂ, ∀ z : ℂ, wSigma L (z + ω) = c * exp (wEta L ω * z) * wSigma L z := by
  by_cases hne : ∃ z₀ : ℂ, z₀ ∉ L.lattice
  swap
  simp [not_exists, not_not] at hne
  refine ⟨0, fun z => ?_⟩
  rw [zero_mul, zero_mul]
  exact (hz L _).mpr (hne _)
  obtain ⟨z₀, hz₀⟩ := hne
  set g : ℂ → ℂ := fun y => wSigma L (y + ω) * exp (-(wEta L ω) * y) /
    wSigma L y with hg
  have H : ∀ y : ℂ, y ∉ L.lattice → HasDerivAt g
      ((((wZeta L (y + ω) * wSigma L (y + ω)) * exp (-(wEta L ω) * y)
        + wSigma L (y + ω) * (exp (-(wEta L ω) * y) * (-(wEta L ω) * 1)))
          * wSigma L y
        - wSigma L (y + ω) * exp (-(wEta L ω) * y)
          * (wZeta L y * wSigma L y))
        / wSigma L y ^ 2) y := by
    intro y hy
    have h1 : HasDerivAt (fun x => wSigma L (x + ω))
        (wZeta L (y + ω) * wSigma L (y + ω)) y := by
      have h' := (hl L (y + ω) (add_notMem hω hy)).comp y ((hasDerivAt_id' y).add_const ω)
      rwa [mul_one] at h'
    have h2 : HasDerivAt (fun x => exp (-(wEta L ω) * x))
        (exp (-(wEta L ω) * y) * (-(wEta L ω) * 1)) y :=
      ((hasDerivAt_id' y).const_mul (-(wEta L ω))).cexp
    exact (h1.mul h2).div (hl L y hy) ((hz L y).not.mpr hy)
  have hconst : ∀ {x y : ℂ}, x ∈ (L.lattice : Set ℂ)ᶜ → y ∈ (L.lattice : Set ℂ)ᶜ → g x = g y :=
    IsOpen.is_const_of_deriv_eq_zero (isOpen_compl L) (isPreconnected_compl L)
    (f := g) (fun y hy => (H y hy).differentiableAt.differentiableWithinAt)
    $ fun y hy => by
      rw [Pi.zero_apply, (H y hy).deriv, hq L ω y hω hy]
      ring
  refine ⟨g z₀, fun z => ?_⟩
  by_cases hzL : z ∈ L.lattice
  rw [(hz L z).mpr hzL, (hz L _).mpr (L.lattice.add_mem hzL hω)]
  simp
  have hs : wSigma L z ≠ 0 := (hz L z).not.mpr hzL
  have h1 : g z * wSigma L z =
      wSigma L (z + ω) * exp (-(wEta L ω) * z) := by
    rw [hg]
    dsimp only
    field_simp
  have he : exp (-(wEta L ω) * z) * exp (wEta L ω * z) = 1 := by
    rw [← exp_add, ← exp_zero]
    congr 1
    ring
  calc wSigma L (z + ω)
      = wSigma L (z + ω) *
          (exp (-(wEta L ω) * z) * exp (wEta L ω * z)) := by
        rw [he, mul_one]
    _ = g z * wSigma L z * exp (wEta L ω * z) := by
        rw [h1]
        ring
    _ = g z₀ * exp (wEta L ω * z) * wSigma L z := by
        rw [hconst hzL hz₀]
        ring

lemma qp_of_half_notMem (hq : ZetaQuasi) (hl : SigmaLogDeriv) (ho : SigmaOdd) (hz : SigmaZero)
    (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) : QP L ω $ -1 := by
  obtain ⟨c, hc⟩ := exists_const hq hl hz L hω
  have key := hc $ -(ω / 2)
  rw [show -(ω / 2) + ω = ω / 2 by ring, ho L] at key
  have hce : c * exp (wEta L ω * -(ω / 2)) = -1 := by
    apply mul_right_cancel₀ $ (hz L _).not.mpr hω2
    linear_combination key
  have hE : exp (wEta L ω * -(ω / 2)) * exp (wEta L ω * (ω / 2)) = 1 := by
    rw [← exp_add, ← exp_zero]
    congr 1
    ring
  unfold QP
  intro z
  rw [hc z, mul_add, exp_add]
  linear_combination (-(exp (wEta L ω * z) * wSigma L z * c)) * hE
    + (exp (wEta L ω * z) * wSigma L z
        * exp (wEta L ω * (ω / 2))) * hce

lemma qp_two_mul (L : PeriodPair) {ω c : ℂ} (h : QP L ω c) (hc : c ^ 2 = 1) : QP L (2 * ω) 1 := by
  unfold QP at h ⊢
  intro z
  rw [two_mul, map_add, show z + (ω + ω) = z + ω + ω by ring, h $ z + ω, h z]
  have hE : exp (wEta L ω * (z + ω + ω / 2)) * exp (wEta L ω * (z + ω / 2))
      = exp ((wEta L ω + wEta L ω) * (z + (ω + ω) / 2)) := by
    rw [← exp_add]
    congr 1
    ring
  linear_combination (exp (wEta L ω * (z + ω + ω / 2))
      * exp (wEta L ω * (z + ω / 2)) * wSigma L z) * hc
    + wSigma L z * hE

lemma semiChar_sq (L : PeriodPair) (ω : ℂ) : semiChar L ω ^ 2 = 1 := by
  unfold semiChar
  split_ifs <;> norm_num

lemma semiChar_ne_zero (L : PeriodPair) (ω : ℂ) : semiChar L ω ≠ 0 := by
  unfold semiChar
  split_ifs <;> norm_num

private theorem linearIndependent_real_periods (L : PeriodPair) : LinearIndependent ℝ ![L.ω₁, L.ω₂] := by
  exact L.indep

lemma coords_half (L : PeriodPair) {a b a' b' : ℤ}
    (h : (a' : ℂ) * L.ω₁ + b' * L.ω₂ = (a * L.ω₁ + b * L.ω₂) / 2) : a = 2 * a' ∧ b = 2 * b' := by
  have h2 : ((2 * a' - a : ℤ) : ℝ) • L.ω₁ + ((2 * b' - b : ℤ) : ℝ) • L.ω₂ = 0 := by
    simp [real_smul]
    push_cast
    linear_combination 2 * h
  obtain ⟨h3, h4⟩ := LinearIndependent.pair_iff.mp (linearIndependent_real_periods L) _ _ h2
  have h5 : 2 * a' - a = 0 := by exact_mod_cast h3
  have h6 : 2 * b' - b = 0 := by exact_mod_cast h4
  constructor <;> omega

private theorem int_comb_periods_mem_lattice (L : PeriodPair) (a b : ℤ) :
    (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ ∈ L.lattice :=
  (mem_lattice_iff_exists_int_comb' L).mpr ⟨a, b, rfl⟩

private theorem semiChar_zero_eq_one (L : PeriodPair) : semiChar L 0 = 1 := by
  unfold semiChar
  rw [if_pos (by rw [zero_div]; exact L.lattice.zero_mem)]

private theorem quasiPeriodic_zero_semiChar_zero (L : PeriodPair) : QP L 0 $ semiChar L 0 := by
  rw [semiChar_zero_eq_one]
  unfold QP
  intro z
  simp

lemma qp_coords (hq : ZetaQuasi) (hl : SigmaLogDeriv) (ho : SigmaOdd) (hz : SigmaZero)
    (L : PeriodPair) : ∀ n : ℕ, ∀ a b : ℤ, a.natAbs + b.natAbs ≤ n →
      QP L (a * L.ω₁ + b * L.ω₂) (semiChar L $ a * L.ω₁ + b * L.ω₂) := by
  intro n
  induction n with
  | zero =>
    intro a b h
    have ha : a = 0 := Int.natAbs_eq_zero.mp $ by omega
    have hb : b = 0 := Int.natAbs_eq_zero.mp $ by omega
    subst ha hb
    simp
    exact quasiPeriodic_zero_semiChar_zero L
  | succ n ih =>
    intro a b h
    by_cases h2 : ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) / 2 ∈ L.lattice
    obtain ⟨a', b', hab⟩ := (mem_lattice_iff_exists_int_comb' L).mp h2
    obtain ⟨rfl, rfl⟩ := coords_half L hab
    have e2 : (2 : ℤ).natAbs = 2 := rfl
    rw [Int.natAbs_mul, Int.natAbs_mul, e2] at h
    have hs1 : semiChar L (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂) = 1 := by
      unfold semiChar
      rw [if_pos h2]
    rw [hs1, show (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂)
        = 2 * ((a' : ℂ) * L.ω₁ + (b' : ℂ) * L.ω₂) by push_cast
                                                     ring]
    exact qp_two_mul L (ih a' b' $ by omega) $ semiChar_sq L _
    have hs1 : semiChar L ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) = -1 := by
      unfold semiChar
      rw [if_neg h2]
    rw [hs1]
    exact qp_of_half_notMem hq hl ho hz L (int_comb_periods_mem_lattice L a b) h2

end PeriodLatticeBasisLemmas

open PeriodLatticeBasisLemmas in

theorem sigmaQuasi_of (hq : ZetaQuasi) (hl : SigmaLogDeriv) (_he : SigmaEntire) (ho : SigmaOdd)
    (hz : SigmaZero) : SigmaQuasi := by
  intro L ω z hω
  obtain ⟨a, b, rfl⟩ := (_root_.Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.mem_lattice_iff_exists_int_comb' L).mp hω
  exact Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.qp_coords hq hl ho hz L _ a b le_rfl z

open PeriodLatticeBasisLemmas in

theorem sigmaSimple_of (hq : SigmaQuasi) (he : SigmaEntire)
    (h0 : ∀ L : PeriodPair, deriv (wSigma L) 0 = 1) : SigmaSimple := by
  intro L
  refine ⟨h0 L, fun z hzL => ?_⟩
  have hd1 : HasDerivAt (fun y => semiChar L z * exp (wEta L z * (y + z / 2))
      * wSigma L y) (deriv (wSigma L) z) 0 := by
    convert (by
        have h' := (he L $ 0 + z).hasDerivAt.comp (0 : ℂ) $ (hasDerivAt_id' (0 : ℂ)).add_const z
        rw [zero_add, mul_one] at h'
        exact h') using 1
    funext y
    exact (hq L z y hzL).symm
  have hσ0 : wSigma L 0 = 0 := by simp [wSigma]
  rw [hd1.unique $ (((((hasDerivAt_id' (0 : ℂ)).add_const $ z / 2).const_mul $ wEta L z).cexp).const_mul $ semiChar L z).mul (he L 0).hasDerivAt, hσ0, h0 L]
  simp [Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.semiChar_ne_zero, Complex.exp_ne_zero]

end Formalism.L2.Th1.F
end
section
open Complex (exp exp_add)
open Filter Topology

namespace Formalism.L2.Th1.F

namespace ThreeTermRelation

lemma le_sub_of_add_le {o : WithTop ℤ} {m k : ℤ} (h : ((k + m : ℤ) : WithTop ℤ) ≤ o) :
    (k : WithTop ℤ) ≤ o - (m : WithTop ℤ) := by
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    have := WithTop.coe_le_coe.1 h
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    apply WithTop.coe_le_coe.2
    omega
lemma semiChar_mul_self (L : PeriodPair) (ω : ℂ) : semiChar L ω * semiChar L ω = 1 := by
  unfold semiChar
  split_ifs <;> norm_num

lemma eq_of_eventuallyEq_punctured {f g : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z)
    (hg : ContinuousAt g z) (h : f =ᶠ[𝓝[≠] z] g) : f z = g z :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    $ (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm

lemma eventually_notMem (L : PeriodPair) (z : ℂ) : ∀ᶠ x in 𝓝[≠] z, x ∉ L.lattice := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    $ L.compl_lattice_sdiff_singleton_mem_nhds z] with x hx0 hx1
  have hx0' := hx0
  simp_all

variable (L : PeriodPair) (b c : ℂ)

def threeTermDet (x : ℂ) : ℂ :=
  (L.weierstrassP b * L.derivWeierstrassP c - L.weierstrassP c * L.derivWeierstrassP b)
    - L.weierstrassP x * (L.derivWeierstrassP c - L.derivWeierstrassP b)
    + L.derivWeierstrassP x * (L.weierstrassP c - L.weierstrassP b)

def nAux (x : ℂ) : ℂ := threeTermDet L b c x * wSigma L x ^ 3

def threeTermDenom (x : ℂ) : ℂ := wSigma L (x + (b + c)) * wSigma L (x + -b) * wSigma L (x + -c)

def threeTermQuotient (x : ℂ) : ℂ := nAux L b c x / threeTermDenom L b c x

def frobeniusStickelbergerDetMulSigmaCube (x : ℂ) : ℂ :=
  (L.weierstrassP b * L.derivWeierstrassP c - L.weierstrassP c * L.derivWeierstrassP b)
      * wSigma L x ^ 3
    - (x * dslope (wSigma L) 0 x ^ 3 + L.weierstrassPExcept 0 x * wSigma L x ^ 3)
      * (L.derivWeierstrassP c - L.derivWeierstrassP b)
    + (-2 * dslope (wSigma L) 0 x ^ 3 + L.derivWeierstrassPExcept 0 x * wSigma L x ^ 3)
      * (L.weierstrassP c - L.weierstrassP b)

lemma sigma_zero (hz : SigmaZero) : wSigma L 0 = 0 := (hz L 0).2 $ zero_mem _

lemma analyticAt_dslope (he : SigmaEntire) : AnalyticAt ℂ (dslope (wSigma L) 0) 0 := by
  obtain ⟨p, hp⟩ := (he L).analyticAt 0
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

lemma wp_congr {x y : ℂ} (h : x + -y ∈ L.lattice) :
    L.weierstrassP x = L.weierstrassP y ∧ L.derivWeierstrassP x = L.derivWeierstrassP y := by
  have e : y + ((⟨x + -y, h⟩ : L.lattice) : ℂ) = x := by
    ring
  have h1 := L.weierstrassP_add_coe y ⟨x + -y, h⟩
  have h2 := L.derivWeierstrassP_add_coe y ⟨x + -y, h⟩
  rw [e] at h1 h2
  constructor
  exact h1
  exact h2
lemma threeTermNum_eq_twistedGamma_of_sigmaZero (hz : SigmaZero) (x : ℂ) (hx : x ≠ 0) : nAux L b c x = frobeniusStickelbergerDetMulSigmaCube L b c x := by
  have hP := L.weierstrassPExcept_def 0 x
  have hP' := L.derivWeierstrassPExcept_def 0 x
  simp [ZeroMemClass.coe_zero] at hP hP'
  unfold nAux threeTermDet frobeniusStickelbergerDetMulSigmaCube
  rw [hP, hP', dslope_of_ne _ hx, slope_def_field, sigma_zero L hz]
  field_simp
  ring

lemma twistedGamma_zero (hz : SigmaZero) (hs : SigmaSimple) :
    frobeniusStickelbergerDetMulSigmaCube L b c 0 = -2 * (L.weierstrassP c - L.weierstrassP b) := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [dslope_same, (hs L).1, sigma_zero L hz]
  ring

lemma twistedGamma_analyticAt_zero (he : SigmaEntire) : AnalyticAt ℂ (frobeniusStickelbergerDetMulSigmaCube L b c) 0 := by
  have h3 := analyticAt_dslope L he
  have h4 := (he L).analyticAt 0
  have h5 := L.analyticAt_weierstrassPExcept 0
  have h6 := L.analyticAt_derivWeierstrassPExcept 0
  unfold frobeniusStickelbergerDetMulSigmaCube
  fun_prop

lemma sig_analyticAt (he : SigmaEntire) (β z : ℂ) : AnalyticAt ℂ (fun w => wSigma L $ w + β) z :=
  ((he L).comp $ differentiable_id.add_const β).analyticAt z

lemma sig_order_mem (hord : SigmaOrder) {β z : ℂ} (h : z + β ∈ L.lattice) :
    meromorphicOrderAt (fun w => wSigma L $ w + β) z = ((1 : ℤ) : WithTop ℤ) := by
  have := hord L 1 β z one_ne_zero
  simp [one_mul] at this
  rw [this, if_pos $ by rwa [one_mul]]
  rfl

lemma sig_order_notMem (hord : SigmaOrder) {β z : ℂ} (h : z + β ∉ L.lattice) :
    meromorphicOrderAt (fun w => wSigma L $ w + β) z = ((0 : ℤ) : WithTop ℤ) := by
  have := hord L 1 β z one_ne_zero
  simp [one_mul] at this
  rw [this, if_neg $ by rwa [one_mul]]
  rfl

lemma sig_eventually_ne (he : SigmaEntire) (hord : SigmaOrder) (β z : ℂ) :
    ∀ᶠ x in 𝓝[≠] z, wSigma L (x + β) ≠ 0 := by
  refine (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (sig_analyticAt L he β z).meromorphicAt).1 ?_
  by_cases h : z + β ∈ L.lattice
  rw [sig_order_mem L hord h]
  exact WithTop.coe_ne_top
  rw [sig_order_notMem L hord h]
  exact WithTop.coe_ne_top

lemma threeTermDenom_eventually_ne (he : SigmaEntire) (hord : SigmaOrder) (z : ℂ) :
    ∀ᶠ x in 𝓝[≠] z, threeTermDenom L b c x ≠ 0 := by
  filter_upwards [sig_eventually_ne L he hord (b + c) z, sig_eventually_ne L he hord (-b) z,
    sig_eventually_ne L he hord (-c) z] with x h1 h2 h3
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

lemma threeTermDenom_analyticAt (he : SigmaEntire) (z : ℂ) : AnalyticAt ℂ (threeTermDenom L b c) z :=
  ((sig_analyticAt L he (b + c) z).mul $ sig_analyticAt L he (-b) z).mul
    $ sig_analyticAt L he (-c) z

lemma threeTermNum_analyticAt (he : SigmaEntire) (z : ℂ) (hzL : z ∉ L.lattice) :
    AnalyticAt ℂ (nAux L b c) z := by
  have h4 := (he L).analyticAt z
  have h5 := L.analyticOnNhd_weierstrassP z hzL
  have h6 := L.analyticOnNhd_derivWeierstrassP z hzL
  unfold nAux threeTermDet
  fun_prop

lemma threeTermNum_meromorphicAt (he : SigmaEntire) (z : ℂ) : MeromorphicAt (nAux L b c) z := by
  have h4 := ((he L).analyticAt z).meromorphicAt
  have h5 := L.meromorphic_weierstrassP z
  have h6 := L.meromorphic_derivWeierstrassP z
  unfold nAux threeTermDet
  fun_prop

lemma threeTermQuotient_meromorphicAt (he : SigmaEntire) (z : ℂ) : MeromorphicAt (threeTermQuotient L b c) z :=
  (threeTermNum_meromorphicAt L b c he z).div (threeTermDenom_analyticAt L b c he z).meromorphicAt

lemma threeTermQuotient_periodic (hq : SigmaQuasi) : IsPeriodic L $ threeTermQuotient L b c := by
  intro ω hω x
  have h1 : wSigma L (x + ω + (b + c))
      = semiChar L ω * exp (wEta L ω * (x + (b + c) + ω / 2)) * wSigma L (x + (b + c)) := by
    rw [← hq L ω (x + (b + c)) hω]
    congr 1; ring
  have h2 : wSigma L (x + ω + -b)
      = semiChar L ω * exp (wEta L ω * (x + -b + ω / 2)) * wSigma L (x + -b) := by
    rw [← hq L ω (x + -b) hω]
    congr 1; ring
  have h3 : wSigma L (x + ω + -c)
      = semiChar L ω * exp (wEta L ω * (x + -c + ω / 2)) * wSigma L (x + -c) := by
    rw [← hq L ω (x + -c) hω]
    congr 1; ring
  have hE : exp (wEta L ω * (x + (b + c) + ω / 2)) * exp (wEta L ω * (x + -b + ω / 2))
        * exp (wEta L ω * (x + -c + ω / 2))
      = exp (wEta L ω * (x + ω / 2)) ^ 3 := by
    rw [← exp_add, ← exp_add, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hχ : semiChar L ω ≠ 0 := fun h => by simpa [h] using semiChar_mul_self L ω
  have hne : semiChar L ω ^ 3 * exp (wEta L ω * (x + ω / 2)) ^ 3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hχ) $ pow_ne_zero _ $ Complex.exp_ne_zero _
  unfold threeTermQuotient nAux threeTermDenom threeTermDet
  rw [hq L ω x hω, h1, h2, h3, L.weierstrassP_add_coe x ⟨ω, hω⟩, L.derivWeierstrassP_add_coe x ⟨ω, hω⟩, ← mul_div_mul_left _ (wSigma L (x + (b + c)) * wSigma L (x + -b) * wSigma L (x + -c)) hne]
  congr 1
  ring
  rw [← hE]
  ring

lemma threeTermQuotient_order_ge (he : SigmaEntire) {z : ℂ} {k m1 m2 m3 : ℤ}
    (h1 : meromorphicOrderAt (fun w => wSigma L $ w + (b + c)) z = (m1 : WithTop ℤ))
    (h2 : meromorphicOrderAt (fun w => wSigma L $ w + -b) z = (m2 : WithTop ℤ))
    (h3 : meromorphicOrderAt (fun w => wSigma L $ w + -c) z = (m3 : WithTop ℤ))
    (hN : ((k + (m1 + m2 + m3) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (nAux L b c) z) :
    (k : WithTop ℤ) ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have hm : meromorphicOrderAt (threeTermDenom L b c) z = ((m1 + m2 + m3 : ℤ) : WithTop ℤ) := by
    have e : threeTermDenom L b c = ((fun w => wSigma L $ w + (b + c)) * (fun w => wSigma L $ w + -b))
        * (fun w => wSigma L $ w + -c) := rfl
    rw [e, meromorphicOrderAt_mul ((sig_analyticAt L he (b + c) z).mul
        $ sig_analyticAt L he (-b) z).meromorphicAt (sig_analyticAt L he (-c) z).meromorphicAt,
      meromorphicOrderAt_mul (sig_analyticAt L he (b + c) z).meromorphicAt
        (sig_analyticAt L he (-b) z).meromorphicAt, h1, h2, h3]
    rfl
  unfold threeTermQuotient
  rw [fun_meromorphicOrderAt_div (threeTermNum_meromorphicAt L b c he z)
    (threeTermDenom_analyticAt L b c he z).meromorphicAt, hm]
  exact le_sub_of_add_le hN

lemma one_le_order {f : ℂ → ℂ} {z : ℂ} (han : AnalyticAt ℂ f z) (h0 : f z = 0) :
    ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f z := by
  rw [han.meromorphicOrderAt_eq]
  refine ENat.monotone_map_iff.mpr Nat.mono_cast
    $ (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 1) han).mpr fun i hi ↦ ?_
  interval_cases i
  simpa using h0

lemma threeTermNum_eq_zero_left {z : ℂ} (h : z + -b ∈ L.lattice) : nAux L b c z = 0 := by
  obtain ⟨h1, h2⟩ := wp_congr L h
  unfold nAux threeTermDet
  rw [h1, h2]
  ring

lemma threeTermNum_eq_zero_right {z : ℂ} (h : z + -c ∈ L.lattice) : nAux L b c z = 0 := by
  obtain ⟨h1, h2⟩ := wp_congr L h
  unfold nAux threeTermDet
  rw [h1, h2]
  ring

lemma threeTermQuotient_order_off (he : SigmaEntire) (hord : SigmaOrder) (hm : b - c ∉ L.lattice) {z : ℂ}
    (hzL : z ∉ L.lattice) {m1 : ℤ}
    (h1 : meromorphicOrderAt (fun w => wSigma L $ w + (b + c)) z = (m1 : WithTop ℤ)) :
    ((-m1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have han := threeTermNum_analyticAt L b c he z hzL
  by_cases hb : z + -b ∈ L.lattice
  have hc : z + -c ∉ L.lattice := fun hc => hm (by
    have := L.lattice.sub_mem hc hb
    convert this using 1
    ring)
  refine threeTermQuotient_order_ge L b c he h1 (sig_order_mem L hord hb) (sig_order_notMem L hord hc) ?_
  have := one_le_order han $ threeTermNum_eq_zero_left L b c hb
  convert this using 2
  ring
  by_cases hc : z + -c ∈ L.lattice
  refine threeTermQuotient_order_ge L b c he h1 (sig_order_notMem L hord hb) (sig_order_mem L hord hc) ?_
  have := one_le_order han $ threeTermNum_eq_zero_right L b c hc
  convert this using 2
  ring
  refine threeTermQuotient_order_ge L b c he h1 (sig_order_notMem L hord hb) (sig_order_notMem L hord hc) ?_
  have := han.meromorphicOrderAt_nonneg
  convert this using 1
  simp

lemma threeTermQuotient_order_zero (he : SigmaEntire) (hz : SigmaZero) (hord : SigmaOrder)
    (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) :
    0 ≤ meromorphicOrderAt (threeTermQuotient L b c) 0 := by
  have hN : 0 ≤ meromorphicOrderAt (nAux L b c) 0 := by
    have : nAux L b c =ᶠ[𝓝[≠] 0] frobeniusStickelbergerDetMulSigmaCube L b c := by
      filter_upwards [self_mem_nhdsWithin] with x hx using threeTermNum_eq_twistedGamma_of_sigmaZero L b c hz x hx
    rw [meromorphicOrderAt_congr this]
    exact (twistedGamma_analyticAt_zero L b c he).meromorphicOrderAt_nonneg
  have := threeTermQuotient_order_ge L b c he (z := 0) (k := 0)
    (sig_order_notMem L hord $ by simpa using hp)
    (sig_order_notMem L hord $ by simpa using hb)
    (sig_order_notMem L hord $ by simpa using hc) $ by simpa using hN
  simpa using this

lemma threeTermQuotient_order_lattice (he : SigmaEntire) (hz : SigmaZero) (hord : SigmaOrder) (hq : SigmaQuasi)
    (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) {z : ℂ}
    (hzL : z ∈ L.lattice) : 0 ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have h := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := 0) (c := z)
    (f := threeTermQuotient L b c)
  have h' : threeTermQuotient L b c ∘ (· + z) = threeTermQuotient L b c := funext fun x => threeTermQuotient_periodic L b c hq z hzL x
  rw [h', zero_add] at h
  rw [← h]
  exact threeTermQuotient_order_zero L b c he hz hord hb hc hp

lemma core (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) {a : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice)
    (hm : b - c ∉ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  obtain ⟨k, hk⟩ := h1 L (threeTermQuotient L b c) (-(b + c)) (threeTermQuotient_meromorphicAt L b c he)
    (threeTermQuotient_periodic L b c hq)
    (fun z hzp => by
      by_cases hzL : z ∈ L.lattice
      exact threeTermQuotient_order_lattice L b c he hz hord hq hb hc hp hzL
      have := threeTermQuotient_order_off L b c he hord hm hzL
        (sig_order_notMem L hord (β := b + c) $ by rwa [sub_neg_eq_add] at hzp)
      simpa using this)
    (by
      have hpL : -(b + c) ∉ L.lattice := fun h => hp $ by simpa using L.lattice.neg_mem h
      have := threeTermQuotient_order_off L b c he hord hm hpL
        $ sig_order_mem L hord (β := b + c) $ by simp
      simpa using this)
  have hev : ∀ z, ∀ᶠ x in 𝓝[≠] z, nAux L b c x = k * threeTermDenom L b c x := by
    intro z
    filter_upwards [eventually_notMem L z, threeTermDenom_eventually_ne L b c he hord z] with x hx1 hx2
    have := hk x ((threeTermNum_analyticAt L b c he x hx1).div (threeTermDenom_analyticAt L b c he x) hx2).continuousAt
    unfold threeTermQuotient at this
    rwa [div_eq_iff hx2] at this
  have hmc : ∀ z, ContinuousAt (fun x => k * threeTermDenom L b c x) z := fun z =>
    continuousAt_const.mul (threeTermDenom_analyticAt L b c he z).continuousAt
  have h0 : frobeniusStickelbergerDetMulSigmaCube L b c 0 = k * threeTermDenom L b c 0 := by
    refine eq_of_eventuallyEq_punctured (g := fun x => k * threeTermDenom L b c x)
      (twistedGamma_analyticAt_zero L b c he).continuousAt (hmc 0) ?_
    filter_upwards [hev 0, self_mem_nhdsWithin] with x hx1 hx2
    rw [← threeTermNum_eq_twistedGamma_of_sigmaZero L b c hz x hx2, hx1]
  have ha' :=
    eq_of_eventuallyEq_punctured (g := fun x => k * threeTermDenom L b c x)
      (threeTermNum_analyticAt L b c he a ha).continuousAt (hmc a) $ hev a
  have h3 := hadd L b c hb hc
  rw [twistedGamma_zero L b c hz hs] at h0
  unfold threeTermDenom at h0 ha'
  unfold nAux at ha'
  rw [zero_add, zero_add, zero_add, ho L b, ho L c] at h0
  have e1 : a + (b + c) = a + b + c := by ring
  have e2 : a + -b = a - b := by ring
  have e3 : wSigma L (a + -c) = -wSigma L (c - a) := by rw [← ho L]
                                                        congr 1; ring
  rw [e1, e2, e3] at ha'
  refine mul_left_cancel₀ (fun h => hp $ (hz L _).1 h) ?_
  linear_combination (wSigma L (b + c) * wSigma L b ^ 3 * wSigma L c ^ 3) * ha'
    + (wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (c - a) * wSigma L b ^ 2 * wSigma L c ^ 2) * h0
    - (2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (c - a)) * h3

lemma trivial_case (hz : SigmaZero) {a : ℂ} (hm : b - c ∈ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  obtain ⟨h1, h2⟩ := wp_congr L (x := b) (y := c) $ by simpa [sub_eq_add_neg] using hm
  rw [(hz L $ b - c).2 hm]
  unfold threeTermDet
  rw [h1, h2]
  ring

lemma step (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) {a : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  by_cases hm : b - c ∈ L.lattice
  exact trivial_case L b c hz hm
  exact core L b c h1 hord hq hz he ho hs hadd ha hb hc hp hm

lemma det_eq (a : ℂ) :
    Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                  1, L.weierstrassP b, L.derivWeierstrassP b;
                  1, L.weierstrassP c, L.derivWeierstrassP c] = threeTermDet L b c a := by
  rw [Matrix.det_fin_three]
  simp [threeTermDet]
  ring

lemma threeTermDet_cycle (a : ℂ) : threeTermDet L b c a = threeTermDet L c a b := by
  unfold threeTermDet
  ring

end ThreeTermRelation

open ThreeTermRelation in


open ThreeTermRelation in
theorem thetaLine_of (h1 : EllipticOnePole) (hq : SgStarQuasi) (hb : SgStarBasic) : ThetaLine := by
  intro L F hF hfe
  obtain ⟨hd, -, hzero, hder, -⟩ := hb L
  have hmer : ∀ z, MeromorphicAt (fun z => F z / sgStar L z) z := fun z =>
    (hF.analyticAt z).meromorphicAt.div (hd.analyticAt z).meromorphicAt
  have hper : IsPeriodic L fun z => F z / sgStar L z := by
    intro ω hω z
    have e1 := hfe ω hω z
    have hχ : (semiChar L ω)⁻¹ = semiChar L ω := inv_eq_of_mul_eq_one_left $ semiChar_mul_self L ω
    unfold opU at e1
    have hE : exp (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2)
        = (exp $ (Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)⁻¹ := by
      rw [← Complex.exp_neg]
      congr 1; ring
    rw [hE] at e1
    show F (z + ω) / sgStar L (z + ω) = F z / sgStar L z
    rw [hq L ω z hω, ← e1, div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, hχ]
    ring
  have han : ∀ z, z ∉ L.lattice → AnalyticAt ℂ (fun z => F z / sgStar L z) z := fun z hz =>
    (hF.analyticAt z).div (hd.analyticAt z) fun h => hz $ (hzero z).1 h
  have hord0 : meromorphicOrderAt (sgStar L) 0 = 1 := by
    rw [(hd.analyticAt 0).meromorphicOrderAt_eq,
      (hd.analyticAt 0).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ((hzero 0).2 $ zero_mem _)
        (by rw [hder]; exact one_ne_zero)]
    rfl
  obtain ⟨c, hc⟩ := h1 L (fun z => F z / sgStar L z) 0 hmer hper
    (fun z hz => (han z $ by simpa using hz).meromorphicOrderAt_nonneg) $ by
      rw [fun_meromorphicOrderAt_div (hF.analyticAt 0).meromorphicAt (hd.analyticAt 0).meromorphicAt,
        hord0]
      have := le_sub_of_add_le (o := meromorphicOrderAt F 0) (m := 1) (k := -1) $ by simpa using ((hF.analyticAt 0).meromorphicOrderAt_nonneg)
      simpa using this
  have hoff : ∀ z, z ∉ L.lattice → F z = c * sgStar L z := by
    intro z hz
    have := hc z (han z hz).continuousAt
    have hne : sgStar L z ≠ 0 := fun h => hz $ (hzero z).1 h
    field_simp at this
    rw [this, mul_comm]
  refine ⟨c, fun z => ?_⟩
  refine eq_of_eventuallyEq_punctured (f := F) (g := fun z => c * sgStar L z)
    hF.continuous.continuousAt (continuous_const.mul hd.continuous).continuousAt ?_
  filter_upwards [eventually_notMem L z] with x hx using hoff x hx

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate Topology
open Complex (exp)
open Filter

namespace Formalism.L2.Th1.F
namespace HalfPeriodDerivative

lemma hasDerivAt_P (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have h := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  rwa [L.deriv_weierstrassP] at h

lemma isOpen_compl (L : PeriodPair) : IsOpen $ (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl

lemma isPreconnected_compl (L : PeriodPair) : IsPreconnected $ (L.lattice : Set ℂ)ᶜ := by
  have hc : (L.lattice : Set ℂ).Countable := by
    have : Countable L.lattice := L.latticeEquivProd.toEquiv.injective.countable
    exact Set.to_countable _
  exact (hc.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected

lemma derivWeierstrassP_not_eventually_zero (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ¬ ∀ᶠ w in 𝓝 z, L.derivWeierstrassP w = 0 := by
  intro h
  have h0 : Set.EqOn L.derivWeierstrassP 0 (L.lattice : Set ℂ)ᶜ :=
    L.analyticOnNhd_derivWeierstrassP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_compl L) hz h
  obtain ⟨c, hc⟩ : ∃ c, ∀ w ∈ (L.lattice : Set ℂ)ᶜ, L.weierstrassP w = c :=
    (isOpen_compl L).exists_is_const_of_deriv_eq_zero (isPreconnected_compl L)
      L.differentiableOn_weierstrassP fun w hw => by rw [L.deriv_weierstrassP]
                                                     exact h0 hw
  have h1 : L.weierstrassP =ᶠ[𝓝[≠] 0] fun _ => c := by
    have h2 : ((L.lattice : Set ℂ) \ {0})ᶜ ∈ 𝓝[≠] (0 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds $ L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [h2, self_mem_nhdsWithin] with w hw hw0
    exact hc w fun hwL => hw ⟨hwL, hw0⟩
  have h3 := meromorphicOrderAt_congr h1
  rw [L.order_weierstrassP 0 $ zero_mem _] at h3
  classical
  rw [meromorphicOrderAt_const] at h3
  split_ifs at h3
  exact absurd h3 $ by simp
  exact absurd h3 $ by decide

lemma derivP_half (L : PeriodPair) {t : ℂ} (h2 : 2 * t ∈ L.lattice) : L.derivWeierstrassP t = 0 := by
  have h := L.derivWeierstrassP_sub_coe t ⟨2 * t, h2⟩
  have e : t - 2 * t = -t := by ring
  simp [e, L.derivWeierstrassP_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

lemma prod_const (ha : SigmaAdd) (hq : SigmaQuasi) (hz : SigmaZero) (L : PeriodPair) {t z : ℂ}
    (ht : t ∉ L.lattice) (h2 : 2 * t ∈ L.lattice) (hzL : z ∉ L.lattice) (hzt : z + t ∉ L.lattice) :
    (L.weierstrassP (z + t) - L.weierstrassP t) * (L.weierstrassP z - L.weierstrassP t)
      * wSigma L t ^ 4 = exp (wEta L (2 * t) * t) := by
  have a1 := ha L (z + t) t hzt ht
  have q1 := hq L (2 * t) z h2
  have q2 := hq L (2 * t) (z - t) h2
  have e1 : z + t + t = z + 2 * t := by ring
  have e2 : z + t - t = z := by ring
  have e3 : z - t + 2 * t = z + t := by ring
  have e4 : z + 2 * t / 2 = z + t := by ring
  have e5 : z - t + 2 * t / 2 = z := by ring
  rw [e1, e2] at a1
  rw [e4] at q1
  rw [e3, e5] at q2
  have hE : exp (wEta L (2 * t) * (z + t))
      = exp (wEta L (2 * t) * z) * exp (wEta L (2 * t) * t) := by
    rw [← Complex.exp_add, mul_add]
  have hK : wSigma L (z + t) ^ 2 * wSigma L z ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ $ mt (hz L $ z + t).1 hzt) $ pow_ne_zero _ $ mt (hz L z).1 hzL
  apply mul_right_cancel₀ hK
  linear_combination (wSigma L z ^ 2 * wSigma L t ^ 2 * (L.weierstrassP z - L.weierstrassP t)) * a1
    - (wSigma L (z + 2 * t) * wSigma L z) * ha L z t hzL ht
    + (wSigma L z * wSigma L (z + t)) * (wSigma L (z - t) * q1
      - exp (wEta L (2 * t) * t) * wSigma L z * q2
      + semiChar L (2 * t) * wSigma L z * wSigma L (z - t) * hE)

lemma notMem_of_comb (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) (h2 : 2 * t ∈ L.lattice) (x : ℂ)
    (n m : ℤ) (hx : (n : ℂ) * x + (m : ℂ) * (2 * t) = t) : x ∉ L.lattice := by
  intro h
  apply ht
  rw [← hx, ← zsmul_eq_mul, ← zsmul_eq_mul]
  exact add_mem (zsmul_mem h n) $ zsmul_mem h2 m

end HalfPeriodDerivative

open HalfPeriodDerivative

theorem weierstrass_p_second_derivative : PSecond := by
  intro L z hz
  have hA := L.analyticOnNhd_derivWeierstrassP z hz
  have hd := hA.differentiableAt.hasDerivAt
  set D : ℂ → ℂ := fun w => deriv L.derivWeierstrassP w - (6 * L.weierstrassP w ^ 2 - L.g₂ / 2) with hD
  have hDan : AnalyticAt ℂ D z := by
    have h1 := hA.deriv
    have h2 := L.analyticOnNhd_weierstrassP z hz
    exact h1.sub $ ((analyticAt_const).mul $ h2.pow 2).sub analyticAt_const
  have hmem : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := (isOpen_compl L).mem_nhds hz
  have hmul : ∀ᶠ w in 𝓝 z, L.derivWeierstrassP w * D w = 0 := by
    have hev : ∀ᶠ w in 𝓝 z, ∀ᶠ v in 𝓝 w, v ∉ L.lattice := hmem.eventually_nhds
    filter_upwards [hev] with w hw
    have hwL : w ∉ L.lattice := hw.self_of_nhds
    have e1 : HasDerivAt (L.derivWeierstrassP · ^ 2)
        (2 * L.derivWeierstrassP w * deriv L.derivWeierstrassP w) w := by
      simpa using ((L.analyticOnNhd_derivWeierstrassP w hwL).differentiableAt.hasDerivAt).fun_pow 2
    have e2 : HasDerivAt (fun v => 4 * L.weierstrassP v ^ 3 - L.g₂ * L.weierstrassP v - L.g₃)
        (4 * (3 * L.weierstrassP w ^ 2 * L.derivWeierstrassP w) - L.g₂ * L.derivWeierstrassP w) w := by
      simpa using ((((hasDerivAt_P L hwL).fun_pow 3).const_mul 4).sub
        $ (hasDerivAt_P L hwL).const_mul L.g₂).sub_const L.g₃
    have e3 : (L.derivWeierstrassP · ^ 2) =ᶠ[𝓝 w]
        fun v => 4 * L.weierstrassP v ^ 3 - L.g₂ * L.weierstrassP v - L.g₃ := by
      filter_upwards [hw] with v hv using L.derivWeierstrassP_sq v hv
    simp only [hD]
    linear_combination (-1 / 2 : ℂ) * (e2.congr_of_eventuallyEq e3).unique e1
  have hD0 : D z = 0 := by
    rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
    exact absurd h $ derivWeierstrassP_not_eventually_zero L hz
    have h5 : ∀ᶠ w in 𝓝[≠] z, D w = 0 := by
      filter_upwards [h, hmul.filter_mono nhdsWithin_le_nhds] with w h1 h2
      exact (mul_eq_zero.mp h2).resolve_left h1
    have h6 : Tendsto D (𝓝[≠] z) $ 𝓝 $ D z := hDan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h7 : Tendsto D (𝓝[≠] z) $ 𝓝 0 := tendsto_const_nhds.congr' $ h5.mono fun w hw => hw.symm
    exact tendsto_nhds_unique h6 h7
  have : deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
    simpa [hD, sub_eq_zero] using hD0
  rwa [this] at hd


theorem halfShift_of (ha : SigmaAdd) (hq : SigmaQuasi) (hz : SigmaZero) (hi : PInjective) :
    HalfShift := by
  intro L t z ht h2 hzL hzt
  have hσt : wSigma L t ≠ 0 := mt (hz L t).1 ht
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = exp (wEta L (2 * t) * t) / wSigma L t ^ 4 := ⟨_, rfl⟩
  have hκ0 : κ ≠ 0 := by
    rw [hκdef]
    exact div_ne_zero (Complex.exp_ne_zero _) $ pow_ne_zero _ hσt
  have hconst : ∀ w, w ∉ L.lattice → w + t ∉ L.lattice →
      (L.weierstrassP (w + t) - L.weierstrassP t) * (L.weierstrassP w - L.weierstrassP t) = κ := by
    intro w hw hwt
    rw [hκdef, eq_div_iff $ pow_ne_zero _ hσt]
    exact prod_const ha hq hz L ht h2 hw hwt
  suffices hκ : κ = 3 * L.weierstrassP t ^ 2 - L.g₂ / 4 by rw [hconst z hzL hzt, hκ]
  have n1 : t / 4 ∉ L.lattice := notMem_of_comb L ht h2 _ 4 0 (by push_cast; ring)
  have n2 : t / 4 + t ∉ L.lattice := notMem_of_comb L ht h2 _ 4 (-2) (by push_cast; ring)
  have n3 : t / 4 + t + t / 4 ∉ L.lattice := notMem_of_comb L ht h2 _ 2 (-1) (by push_cast; ring)
  have hne : L.weierstrassP (t / 4 + t) - L.weierstrassP (t / 4) ≠ 0 := by
    intro h
    rcases (hi L _ _ n2 n1).1 (sub_eq_zero.mp h) with h | h
    exact ht $ by simpa using h
    exact n3 h
  have hev : ∀ᶠ w in 𝓝 $ t / 4, (L.weierstrassP (w + t) - L.weierstrassP t)
      * (L.weierstrassP w - L.weierstrassP t) = κ := by
    filter_upwards [(isOpen_compl L).mem_nhds n1, ((continuous_id.add continuous_const).tendsto $ t / 4).eventually $ (isOpen_compl L).mem_nhds n2] with w h1 h2 using hconst w h1 h2
  have hder : HasDerivAt (fun w => (L.weierstrassP (w + t) - L.weierstrassP t)
      * (L.weierstrassP w - L.weierstrassP t))
      (L.derivWeierstrassP (t / 4 + t) * (L.weierstrassP (t / 4) - L.weierstrassP t)
        + (L.weierstrassP (t / 4 + t) - L.weierstrassP t) * L.derivWeierstrassP (t / 4)) $ t / 4 :=
    (((hasDerivAt_P L n2).comp_add_const (t / 4) t).sub_const _).mul
      $ (hasDerivAt_P L n1).sub_const _
  have s0 := L.derivWeierstrassP_sq _ ht
  rw [derivP_half L h2] at s0
  have key : κ * (L.weierstrassP (t / 4 + t) - L.weierstrassP (t / 4))
      * (4 * κ - (12 * L.weierstrassP t ^ 2 - L.g₂)) = 0 := by
    rw [← hconst _ n1 n2]
    linear_combination
      (L.derivWeierstrassP (t / 4 + t) * (L.weierstrassP (t / 4) - L.weierstrassP t)
        - (L.weierstrassP (t / 4 + t) - L.weierstrassP t) * L.derivWeierstrassP (t / 4)) * hder.unique ((hasDerivAt_const (t / 4) κ).congr_of_eventuallyEq hev)
      - (L.weierstrassP (t / 4) - L.weierstrassP t) ^ 2 * L.derivWeierstrassP_sq _ n2
      + (L.weierstrassP (t / 4 + t) - L.weierstrassP t) ^ 2 * L.derivWeierstrassP_sq _ n1
      + ((L.weierstrassP (t / 4) - L.weierstrassP t) ^ 2
        - (L.weierstrassP (t / 4 + t) - L.weierstrassP t) ^ 2) * s0
  have h4 := (mul_eq_zero.mp key).resolve_left $ mul_ne_zero hκ0 hne
  linear_combination (1 / 4 : ℂ) * h4

end Formalism.L2.Th1.F
end
section
namespace Formalism.L2.Th1.F

namespace WeierstrassZetaQuasiPeriod

lemma isOpen_compl (L : PeriodPair) : IsOpen $ (L.lattice : Set ℂ)ᶜ :=
  L.isClosed_lattice.isOpen_compl

lemma isPreconnected_compl (L : PeriodPair) : IsPreconnected $ (L.lattice : Set ℂ)ᶜ :=
  (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    $ countable_of_Lindelof_of_discrete (X := L.lattice)).2

lemma add_notMem {L : PeriodPair} {ω z : ℂ} (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    z + ω ∉ L.lattice := fun h => hz $ by simpa using sub_mem h hω

lemma diff_const (hd : ZetaHasDeriv) (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice) {x y : ℂ}
    (hx : x ∉ L.lattice) (hy : y ∉ L.lattice) :
    wZeta L (x + ω) - wZeta L x = wZeta L (y + ω) - wZeta L y := by
  have hD : ∀ z, z ∉ L.lattice → HasDerivAt (fun z => wZeta L (z + ω) - wZeta L z) 0 z := by
    intro z hz
    have h2 := ((hd L (z + ω) $ add_notMem hω hz).comp_add_const z ω).sub $ hd L z hz
    have e : -L.weierstrassP (z + ω) - -L.weierstrassP z = 0 := by rw [L.weierstrassP_add_coe z ⟨ω, hω⟩]
                                                                   ring
    rwa [e] at h2
  exact (isOpen_compl L).is_const_of_deriv_eq_zero (f := fun z => wZeta L (z + ω) - wZeta L z)
    (isPreconnected_compl L)
    (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hD z hz).deriv) hx hy

lemma diff_eq (hd : ZetaHasDeriv) (ho : ZetaOdd) (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice)
    (hω2 : ω / 2 ∉ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    wZeta L (z + ω) = wZeta L z + 2 * wZeta L (ω / 2) := by
  have hm : -(ω / 2) ∉ L.lattice := fun h => hω2 $ by simpa using neg_mem h
  have h := diff_const hd L hω hz hm
  have e : -(ω / 2) + ω = ω / 2 := by ring
  rw [e, ho L $ ω / 2] at h
  linear_combination h

lemma wEta_ω₁ (L : PeriodPair) : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by
  have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0
  simpa [wEta] using this

lemma wEta_ω₂ (L : PeriodPair) : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by
  have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
  simpa [wEta] using this

end WeierstrassZetaQuasiPeriod

open WeierstrassZetaQuasiPeriod in

theorem zetaQuasi_of (hd : ZetaHasDeriv) (ho : ZetaOdd) : ZetaQuasi := by
  intro L ω z hω hz
  let G : AddSubgroup ℂ :=
    { carrier := { w | w ∈ L.lattice ∧
        ∀ x, x ∉ L.lattice → wZeta L (x + w) = wZeta L x + wEta L w }
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun x hx => ?_⟩
        rw [← add_assoc, hb' _ $ add_notMem ha hx, ha' x hx, map_add, add_assoc]
      zero_mem' := ⟨zero_mem _, fun x _ => by simp⟩
      neg_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨neg_mem ha, fun x hx => ?_⟩
        have h := ha' (x + -a) $ add_notMem (neg_mem ha) hx
        rw [neg_add_cancel_right] at h
        rw [map_neg, h]
        ring }
  have hG : L.lattice ≤ G.toIntSubmodule := by
    rw [PeriodPair.lattice, Submodule.span_le]
    rintro _ (rfl | rfl)
    exact ⟨L.ω₁_mem_lattice, fun x hx => by
      rw [wEta_ω₁]
      exact diff_eq hd ho L L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice hx⟩
    exact ⟨L.ω₂_mem_lattice, fun x hx => by
      rw [wEta_ω₂]
      exact diff_eq hd ho L L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice hx⟩
  exact (hG hω).2 z hz

end Formalism.L2.Th1.F
end
section
namespace Formalism.L2.Th1.F

theorem zetaSummable : ZetaSummable := zeta_summable
theorem zetaHasDeriv : ZetaHasDeriv := zeta_has_deriv
theorem zetaOdd : ZetaOdd := zeta_odd
theorem zetaQuasi : ZetaQuasi := zetaQuasi_of zetaHasDeriv zetaOdd
theorem sigmaSummable : SigmaSummable := sigma_summable
theorem sigmaProdLU : SigmaProdLU := sigma_product_locally_uniform
theorem sigmaEntire : SigmaEntire := sigmaEntire_of sigmaProdLU
theorem sigmaOdd : SigmaOdd := sigma_odd
theorem sigmaZero : SigmaZero := sigmaZero_of sigmaSummable
theorem sigmaLogDeriv : SigmaLogDeriv := sigmaLogDeriv_of sigmaProdLU sigmaSummable zetaSummable
theorem sigmaQuasi : SigmaQuasi := sigmaQuasi_of zetaQuasi sigmaLogDeriv sigmaEntire sigmaOdd sigmaZero
theorem sigmaSimple : SigmaSimple := sigmaSimple_of sigmaQuasi sigmaEntire $ sigmaDerivZero_of sigmaProdLU
theorem etaEisenstein : EtaEisenstein := etaEisenstein_of zetaSummable zetaOdd
theorem legendre : Legendre := legendre_of etaEisenstein

end Formalism.L2.Th1.F
end
section
namespace Formalism.L2.Th1.F

theorem areaPos : AreaPos := areaPos_thm
theorem etaSplit : EtaSplit := etaSplit_of legendre
theorem sgStarQuasi : SgStarQuasi := sgStarQuasi_of sigmaQuasi etaSplit
theorem sigmaTaylorLow :
    ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0 :=
  sigmaTaylorLow_of sigmaEntire sigmaSummable
theorem sgStarBasic : SgStarBasic :=
  sgStarBasic_of sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaTaylorLow

end Formalism.L2.Th1.F
end
section
namespace Formalism.L2.Th1.F

theorem ellipticNoPole : EllipticNoPole := elliptic_no_pole_const
theorem sigmaOrder : SigmaOrder := sigmaOrder_of sigmaEntire sigmaZero sigmaSimple
theorem sigmaAdd : SigmaAdd :=
  sigmaAdd_of ellipticNoPole sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaQuasi sigmaOrder
theorem sgStarAdd : SgStarAdd := sgStarAdd_of sigmaAdd
theorem pInjective : PInjective := pInjective_of sigmaAdd sigmaZero
theorem sigmaDouble : SigmaDouble := sigmaDouble_of sigmaAdd sigmaEntire sigmaSimple
theorem pDerivZero : PDerivZero := pDerivZero_of sigmaDouble sigmaZero

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate
open Complex (I_sq conj_I mul_conj normSq_eq_norm_sq)
open LinearMap (comp_apply mulLeft mulLeft_apply)
open PeriodPair (basis g₂ g₃ mem_lattice weierstrassP)

namespace Formalism.L2.Th1.F

namespace LatOnly

lemma tsum_sub {Λ Λ' : Submodule ℤ ℂ} (h : Λ = Λ') (f : ℂ → ℂ) :
    ∑' l : Λ, f (l : ℂ) = ∑' l : Λ', f (l : ℂ) := by
  subst h
  rfl

lemma tprod_submodule_congr {Λ Λ' : Submodule ℤ ℂ} (h : Λ = Λ') (f : ℂ → ℂ) :
    ∏' l : Λ, f (l : ℂ) = ∏' l : Λ', f (l : ℂ) := by
  subst h
  rfl

variable {L L' : PeriodPair}

lemma wZeta_eq (h : L.lattice = L'.lattice) : wZeta L = wZeta L' := by
  funext z
  simp only [wZeta]
  exact tsum_sub h fun w => 1 / (z - w) + 1 / w + z / w ^ 2

lemma wSigma_eq (h : L.lattice = L'.lattice) : wSigma L = wSigma L' := by
  funext z
  simp only [wSigma]
  rw [tprod_submodule_congr h fun w => wFactor w z]

lemma wp_eq (h : L.lattice = L'.lattice) : L.weierstrassP = L'.weierstrassP := by
  funext z
  simp only [weierstrassP]
  exact tsum_sub h fun w => 1 / (z - w) ^ 2 - 1 / w ^ 2

lemma G_eq (h : L.lattice = L'.lattice) (n : ℕ) : L.G n = L'.G n := by
  simp [PeriodPair.G]
  exact tsum_sub h fun w => (w ^ n)⁻¹

lemma wEta_eq_on (h : L.lattice = L'.lattice) {ω : ℂ} (hω : ω ∈ L.lattice) :
    wEta L ω = wEta L' ω := by
  have hhalf : L.ω₁ / 2 ∉ L.lattice := by
    intro hx
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp hx
    have hli := L.indep
    rw [LinearIndependent.pair_iff] at hli
    obtain ⟨h1, h2⟩ := hli ((p : ℝ) - 1 / 2) (q : ℝ) $ by
      simp [Complex.real_smul]
      push_cast
      linear_combination hpq
    have h3 : (2 : ℝ) * p = 1 := by linarith
    have h2p : (2 * p : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hω' : ω ∈ L'.lattice := by rw [← h]
                                  exact hω
  have e1 := zetaQuasi L ω (L.ω₁ / 2) hω hhalf
  rw [wZeta_eq h] at e1
  linear_combination (zetaQuasi L' ω (L.ω₁ / 2) hω' (by rw [← h]; exact hhalf)) - e1

lemma wEta_eq (h : L.lattice = L'.lattice) : wEta L = wEta L' := by
  have hb0 : L.basis 0 = L.ω₁ := by
    first
      | exact L.basis_zero
      | simp [basis]
  have hb1 : L.basis 1 = L.ω₂ := by
    first
      | exact L.basis_one
      | simp [basis]
  have hω₁ : L.ω₁ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨1, 0, by simp⟩
  have hω₂ : L.ω₂ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨0, 1, by simp⟩
  apply L.basis.ext
  intro i
  fin_cases i
  show wEta L (L.basis 0) = wEta L' (L.basis 0)
  rw [hb0]
  exact wEta_eq_on h hω₁
  show wEta L (L.basis 1) = wEta L' (L.basis 1)
  rw [hb1]
  exact wEta_eq_on h hω₂

lemma quasiPeriodConst_formula (L : PeriodPair) : s2 L = (wEta L 1 - Complex.I * wEta L Complex.I) / 2 := by
  rw [etaSplit L 1, etaSplit L Complex.I]
  simp [map_one, conj_I]
  linear_combination ((s2 L - (Real.pi : ℂ) / (area L : ℂ)) / 2) * I_sq

lemma piA_formula (L : PeriodPair) :
    (Real.pi : ℂ) / (area L : ℂ) = (wEta L 1 + Complex.I * wEta L Complex.I) / 2 := by
  rw [etaSplit L 1, etaSplit L Complex.I]
  simp [map_one, conj_I]
  linear_combination (((Real.pi : ℂ) / (area L : ℂ) - s2 L) / 2) * I_sq

lemma quasiPeriodConst_eq (h : L.lattice = L'.lattice) : s2 L = s2 L' := by
  rw [quasiPeriodConst_formula L, quasiPeriodConst_formula L', wEta_eq h]

lemma area_eq (h : L.lattice = L'.lattice) : area L = area L' := by
  have h1 := piA_formula L
  rw [wEta_eq h, ← piA_formula L'] at h1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (area L : ℂ)⁻¹ = (area L' : ℂ)⁻¹ := by
    rw [div_eq_mul_inv, div_eq_mul_inv] at h1
    exact mul_left_cancel₀ hpi h1
  exact_mod_cast (inv_inj.mp h2)

lemma sgStar_eq (h : L.lattice = L'.lattice) : sgStar L = sgStar L' := by
  funext z
  simp [sgStar]
  rw [wSigma_eq h, quasiPeriodConst_eq h]

end LatOnly


namespace Homog

variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)

lemma mem_scale (z : ℂ) : z ∈ (scalePair L c hc).lattice ↔ c⁻¹ * z ∈ L.lattice := by
  rw [mem_lattice, mem_lattice]
  constructor
  rintro ⟨m, n, hmn⟩
  use m, n
  change (m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = z at hmn
  rw [← hmn, show c⁻¹ * ((m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂))
      = (c⁻¹ * c) * ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) by ring, inv_mul_cancel₀ hc, one_mul]
  rintro ⟨m, n, hmn⟩
  use m, n
  change (m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = z
  rw [show (m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = c * ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) by ring,
    hmn, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

def scaleEquiv : L.lattice ≃ (scalePair L c hc).lattice where
  toFun l := ⟨c * (l : ℂ), (mem_scale L c hc _).2 (by rw [inv_mul_cancel_left₀ hc]; exact l.2)⟩
  invFun l := ⟨c⁻¹ * (l : ℂ), (mem_scale L c hc _).1 l.2⟩
  left_inv l := by ext; simp [hc]
  right_inv l := by ext; simp [hc]

lemma tsum_scale (f : ℂ → ℂ) :
    ∑' l : (scalePair L c hc).lattice, f (l : ℂ) = ∑' l : L.lattice, f (c * (l : ℂ)) := (Equiv.tsum_eq (scaleEquiv L c hc) fun l => f (l : ℂ)).symm

lemma tprod_scale (f : ℂ → ℂ) :
    ∏' l : (scalePair L c hc).lattice, f (l : ℂ) = ∏' l : L.lattice, f (c * (l : ℂ)) := (Equiv.tprod_eq (scaleEquiv L c hc) fun l => f (l : ℂ)).symm

lemma wZeta_scale (z : ℂ) : wZeta (scalePair L c hc) (c * z) = c⁻¹ * wZeta L z := by
  simp only [wZeta]
  rw [tsum_scale L c hc fun w => 1 / (c * z - w) + 1 / w + c * z / w ^ 2, ← tsum_mul_left]
  congr 1
  funext l
  try dsimp only
  have e : c * z - c * (l : ℂ) = c * (z - l) := by ring
  have hc2 : c * (c ^ 2)⁻¹ = c⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [e]
  simp only [mul_inv, div_eq_mul_inv, mul_pow]
  linear_combination (z * ((l : ℂ) ^ 2)⁻¹) * hc2

omit L in
include hc in
lemma wFactor_scale (l z : ℂ) : wFactor (c * l) (c * z) = wFactor l z := by
  unfold wFactor
  have h2 : (c * z) ^ 2 / (2 * (c * l) ^ 2) = z ^ 2 / (2 * l ^ 2) := by
    rw [show (c * z) ^ 2 = c ^ 2 * z ^ 2 by ring, show 2 * (c * l) ^ 2 = c ^ 2 * (2 * l ^ 2) by ring]
    exact mul_div_mul_left _ _ $ pow_ne_zero 2 hc
  rw [mul_div_mul_left z l hc, h2]

lemma wSigma_scale (z : ℂ) : wSigma (scalePair L c hc) (c * z) = c * wSigma L z := by
  simp [wSigma]
  rw [tprod_scale L c hc fun w => wFactor w $ c * z]
  try dsimp only
  simp [wFactor_scale c hc]
  ring

lemma wp_scale (z : ℂ) :
    (scalePair L c hc).weierstrassP (c * z) = (c ^ 2)⁻¹ * L.weierstrassP z := by
  simp only [weierstrassP]
  rw [tsum_scale L c hc fun w => 1 / (c * z - w) ^ 2 - 1 / w ^ 2, ← tsum_mul_left]
  congr 1
  funext l
  try dsimp only
  rw [show c * z - c * (l : ℂ) = c * (z - l) by ring]
  simp only [one_div, mul_inv, mul_pow]
  ring

lemma G_scale (n : ℕ) : (scalePair L c hc).G n = (c ^ n)⁻¹ * L.G n := by
  simp [PeriodPair.G]
  rw [tsum_scale L c hc fun w => (w ^ n)⁻¹, ← tsum_mul_left]
  congr 1
  funext l
  try dsimp only
  rw [mul_pow, mul_inv]

lemma wEta_basis₁ (L : PeriodPair) : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by
  have hb : L.basis 0 = L.ω₁ := by
    first
      | exact L.basis_zero
      | simp [basis]
  have h1 := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0
  rw [hb] at h1
  simpa [wEta] using h1

lemma wEta_basis₂ (L : PeriodPair) : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by
  have hb : L.basis 1 = L.ω₂ := by
    first
      | exact L.basis_one
      | simp [basis]
  have h1 := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
  rw [hb] at h1
  simpa [wEta] using h1

lemma wEta_scale (z : ℂ) : wEta (scalePair L c hc) (c * z) = c⁻¹ * wEta L z := by
  have hb0 : L.basis 0 = L.ω₁ := by
    first
      | exact L.basis_zero
      | simp [basis]
  have hb1 : L.basis 1 = L.ω₂ := by
    first
      | exact L.basis_one
      | simp [basis]
  have k1 : wEta (scalePair L c hc) (c * L.ω₁) = c⁻¹ * wEta L L.ω₁ := by
    have h := wEta_basis₁ $ scalePair L c hc
    change wEta (scalePair L c hc) (c * L.ω₁) = 2 * wZeta (scalePair L c hc) (c * L.ω₁ / 2) at h
    rw [h, show c * L.ω₁ / 2 = c * (L.ω₁ / 2) by ring, wZeta_scale L c hc, wEta_basis₁ L]
    ring
  have k2 : wEta (scalePair L c hc) (c * L.ω₂) = c⁻¹ * wEta L L.ω₂ := by
    have h := wEta_basis₂ $ scalePair L c hc
    change wEta (scalePair L c hc) (c * L.ω₂) = 2 * wZeta (scalePair L c hc) (c * L.ω₂ / 2) at h
    rw [h, show c * L.ω₂ / 2 = c * (L.ω₂ / 2) by ring, wZeta_scale L c hc, wEta_basis₂ L]
    ring
  have key : (wEta $ scalePair L c hc).comp (mulLeft ℝ c)
      = (mulLeft ℝ c⁻¹).comp (wEta L) := by
    apply L.basis.ext
    intro i
    fin_cases i
    first
      | (show wEta (scalePair L c hc) (c * L.basis 0) = c⁻¹ * wEta L (L.basis 0)
         rw [hb0]
         exact k1)
      | (simp [comp_apply, mulLeft_apply, Fin.zero_eta, hb0]
         exact k1)
    first
      | (show wEta (scalePair L c hc) (c * L.basis 1) = c⁻¹ * wEta L (L.basis 1)
         rw [hb1]
         exact k2)
      | (simp [comp_apply, mulLeft_apply, Fin.mk_one, hb1]
         exact k2)
  exact LinearMap.congr_fun key z

lemma area_scale : area (scalePair L c hc) = ‖c‖ ^ 2 * area L := by
  simp only [area]
  change |(conj (c * L.ω₁) * (c * L.ω₂)).im| = ‖c‖ ^ 2 * |(conj L.ω₁ * L.ω₂).im|
  have hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
    rw [mul_conj, normSq_eq_norm_sq]
  have e : conj (c * L.ω₁) * (c * L.ω₂) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (conj L.ω₁ * L.ω₂) := by
    rw [map_mul, hn]
    ring
  rw [e]
  first
    | rw [Complex.im_ofReal_mul]
    | simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [abs_mul, abs_of_nonneg $ by positivity]

lemma quasiPeriodConst_scale : s2 (scalePair L c hc) = (c ^ 2)⁻¹ * s2 L := by
  have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
  simp [s2]
  change (wEta (scalePair L c hc) (c * L.ω₁) * conj (c * L.ω₂)
      - wEta (scalePair L c hc) (c * L.ω₂) * conj (c * L.ω₁))
      / (c * L.ω₁ * conj (c * L.ω₂) - c * L.ω₂ * conj (c * L.ω₁)) = _
  rw [wEta_scale L c hc, wEta_scale L c hc, map_mul, map_mul]
  rw [show c⁻¹ * wEta L L.ω₁ * (conj c * conj L.ω₂) - c⁻¹ * wEta L L.ω₂ * (conj c * conj L.ω₁)
      = (c⁻¹ * conj c) * (wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁) by ring,
    show c * L.ω₁ * (conj c * conj L.ω₂) - c * L.ω₂ * (conj c * conj L.ω₁)
      = (c * conj c) * (L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁) by ring,
    mul_div_mul_comm]
  congr 1
  first
    | (field_simp
       done)
    | (field_simp
       ring)
    | (rw [div_eq_iff $ mul_ne_zero hc hcc]
       field_simp
       ring)

lemma sgStar_scale (z : ℂ) : sgStar (scalePair L c hc) (c * z) = c * sgStar L z := by
  simp only [sgStar]
  rw [wSigma_scale L c hc, quasiPeriodConst_scale L c hc]
  have he : -((c ^ 2)⁻¹ * s2 L) * (c * z) ^ 2 / 2 = -(s2 L) * z ^ 2 / 2 := by
    linear_combination (-(s2 L) * z ^ 2 / 2) * inv_mul_cancel₀ (pow_ne_zero 2 hc)
  rw [he]
  ring

lemma herm_scale (z w : ℂ) : herm (scalePair L c hc) (c * z) (c * w) = herm L z w := by
  simp only [herm, area_scale L c hc]
  have hA : (area L : ℂ) ≠ 0 := by exact_mod_cast (areaPos L).ne'
  have hn : ((‖c‖ ^ 2 * area L : ℝ) : ℂ) = c * conj c * (area L : ℂ) := by
    rw [Complex.ofReal_mul, mul_conj, normSq_eq_norm_sq]
  rw [hn, map_mul, div_eq_div_iff (mul_ne_zero (mul_ne_zero hc $ (map_ne_zero _).mpr hc) hA) hA]
  ring

lemma opU_scale (t z : ℂ) :
    opU (scalePair L c hc) (c * t) (sgStar $ scalePair L c hc) (c * z)
      = c * opU L t (sgStar L) z := by
  simp [opU]
  rw [show c * z + c * t = c * (z + t) by ring, sgStar_scale L c hc, herm_scale L c hc,
    herm_scale L c hc]
  ring

lemma normalizedTheta_scale (t z : ℂ) : th0 (scalePair L c hc) (c * t) (c * z) = th0 L t z := by
  simp [th0]
  have h0 := opU_scale L c hc t 0
  rw [mul_zero] at h0
  rw [opU_scale L c hc t z, h0]
  exact mul_div_mul_left _ _ hc

end Homog

theorem homogeneity_thm : Homogeneity := by
  intro L c hc
  refine ⟨Homog.mem_scale L c hc, Homog.wZeta_scale L c hc, Homog.wSigma_scale L c hc,
    Homog.wp_scale L c hc, Homog.wEta_scale L c hc, Homog.area_scale L c hc, Homog.quasiPeriodConst_scale L c hc,
    Homog.sgStar_scale L c hc, Homog.normalizedTheta_scale L c hc, ?_, ?_⟩
  first
    | (simp [g₂, Homog.G_scale L c hc]
       ring)
    | (unfold g₂
       done)
  first
    | (simp [g₃, Homog.G_scale L c hc]
       ring)
    | (unfold g₃
       done)

end Formalism.L2.Th1.F
end
section
namespace Formalism.L2.Th1.F

theorem homogeneity : Homogeneity := homogeneity_thm
theorem kerRepsExist : KerRepsExist := kernel_reps_exist
theorem kerRepsCard : KerRepsCard := kernel_reps_card
theorem isogenyP : IsogenyP := isogenyWeierstrassP_of_ellipticNoPole ellipticNoPole
theorem pSecond : PSecond := weierstrass_p_second_derivative
theorem isogenySigma : IsogenySigma :=
  isogenySigma_of ellipticNoPole sigmaOrder sgStarAdd sgStarQuasi sgStarBasic kerRepsCard sigmaEntire
theorem halfShift : HalfShift := halfShift_of sigmaAdd sigmaQuasi sigmaZero pInjective

end Formalism.L2.Th1.F
end
end
