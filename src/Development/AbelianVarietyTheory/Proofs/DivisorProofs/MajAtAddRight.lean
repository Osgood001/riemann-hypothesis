module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements

@[expose] public section

open NumberField GlobalTheory.AllWt

namespace GlobalTheory.CutNum

open Module Formalism.HermitianLatticesTheory

section Maj

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)

theorem fcoord_add' (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
    funext i
    simp [vecAt]
  simp only [fcoord, hv, Matrix.mulVec_add]

theorem fcoord_smul' (a : K) (x : V) : fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i
    simp [vecAt]
  simp only [fcoord, hv, Matrix.mulVec_smul]

theorem normAt_add_sq (x y : V) :
    normAt b X v (x + y) ^ 2 = normAt b X v x ^ 2 + normAt b X v y ^ 2 + 2 * (majAt b X v x y).re := by
  simp only [normAt, cnorm, majAt, fcoord_add']
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_smul_left' (a : K) (x y : V) :
    majAt b X v (a • x) y = star (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem majAt_add_right' (x y z : V) : majAt b X v x (y + z) = majAt b X v x y + majAt b X v x z := by
  simp only [majAt, fcoord_add', Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem star_majAt' (x y : V) : star (majAt b X v x y) = majAt b X v y x := by
  simp only [majAt, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem selfAdj_of_pyth (hv : v.IsComplex) (e : V →ₗ[K] V)
    (h : ∀ x y, normAt b X v (e x + (y - e y)) ^ 2 = normAt b X v (e x) ^ 2 + normAt b X v (y - e y) ^ 2) (x y : V) :
    majAt b X v (e x) y = majAt b X v x (e y) := by
  have hre : ∀ x y, (majAt b X v (e x) (y - e y)).re = 0 := by
    intro x y
    have h1 := normAt_add_sq b X v (e x) (y - e y)
    have h2 := h x y
    linarith
  obtain ⟨a, ha⟩ : ∃ a : K, (v.embedding a).im ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply InfinitePlace.isComplex_iff.mp hv
    rw [ComplexEmbedding.isReal_iff]
    ext t
    exact Complex.conj_eq_iff_im.mpr (hcon t)
  have hzero : ∀ x y, majAt b X v (e x) (y - e y) = 0 := by
    intro x y
    have h0 := hre x y
    have h1 := hre (a • x) y
    rw [map_smul, majAt_smul_left'] at h1
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, h0] at h1
    have hm : (v.embedding a).im * (majAt b X v (e x) (y - e y)).im = 0 := by linarith
    refine Complex.ext (by simpa using h0) ?_
    rcases mul_eq_zero.mp hm with hm | hm
    · exact absurd hm ha
    · simpa using hm
  have hL : majAt b X v (e x) y = majAt b X v (e x) (e y) := by
    have := majAt_add_right' b X v (e x) (e y) (y - e y)
    rw [hzero, add_zero, show e y + (y - e y) = y by abel] at this
    exact this
  have hR : majAt b X v x (e y) = majAt b X v (e x) (e y) := by
    have := majAt_add_right' b X v (e y) (e x) (x - e x)
    rw [hzero, add_zero, show e x + (x - e x) = x by abel] at this
    rw [← star_majAt' b X v (e y) x, this, star_majAt']
  rw [hL, hR]

end Maj

/-- The bad-rank fraction costs at most its odds times the slope gap. -/
theorem numeric_sharp {dg db μ μg m lg δ Q : ℝ} (hd : 0 < dg + db) (hdg : 0 ≤ dg) (hdb : 0 ≤ db)
    (hcut : (dg + db) * μ ≤ dg * μg + db * (m + lg)) (hδ' : δ < 1 / 3)
    (hb : db ≤ 3 * δ * (dg + db)) (hm : m ≤ Q) (hμ : -Q ≤ μ) (hlg : lg ≤ Q) (hlg0 : 0 ≤ lg) :
    μ - 9 * δ * Q / (1 - 3 * δ) ≤ μg := by
  have hden : 0 < 1 - 3 * δ := by linarith
  have hg : 0 < dg := lt_of_le_of_ne hdg fun he => by nlinarith [mul_pos hden hd]
  have hbad : (1 - 3 * δ) * db ≤ 3 * δ * dg := by linarith
  have hgap : dg * (μ - μg) ≤ db * (3 * Q) := by
    nlinarith [mul_nonneg hdb (show 0 ≤ 3 * Q - (m + lg - μ) by linarith)]
  have h := (mul_le_mul_of_nonneg_left hgap hden.le).trans
    (show (1 - 3 * δ) * (db * (3 * Q)) ≤ dg * (9 * δ * Q) by
      nlinarith [mul_le_mul_of_nonneg_right hbad (show 0 ≤ 3 * Q by linarith)])
  have h' : (μ - μg) * (1 - 3 * δ) ≤ 9 * δ * Q := by
    apply le_of_mul_le_mul_left (a := dg)
    · linarith
    · exact hg
  linarith [(le_div_iff₀ hden).2 h']

theorem numeric {dg db μ μg m lg δ Q : ℝ} (hd : 0 < dg + db) (hdg : 0 ≤ dg) (hdb : 0 ≤ db)
    (hcut : (dg + db) * μ ≤ dg * μg + db * (m + lg)) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 12)
    (hb : db ≤ 3 * δ * (dg + db)) (hm : m ≤ Q) (hμ : -Q ≤ μ) (hlg : lg ≤ Q) (hlg0 : 0 ≤ lg) :
    μ - 12 * δ * Q ≤ μg := by
  have h := numeric_sharp hd hdg hdb hcut (by linarith) hb hm hμ hlg hlg0
  have hle : 9 * δ * Q / (1 - 3 * δ) ≤ 12 * δ * Q := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - 3 * δ)).2
    nlinarith [mul_nonneg (mul_nonneg hδ (hlg0.trans hlg)) (show 0 ≤ 1 - 12 * δ by linarith)]
  linarith

section

variable (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (N : (K →+* ℂ) → V → ℝ) (L M : Submodule (𝓞 K) V) (e : V →ₗ[K] V) (g : ℕ)

local notation "G₀" => L ⊓ Submodule.restrictScalars (𝓞 K) (LinearMap.range e)
local notation "B₀" => L ⊓ Submodule.restrictScalars (𝓞 K) (LinearMap.ker e)

open Formalism.HN (rkK)

private theorem weighted_slope_cut (hGram : HasGram N) (hM : M.FG) (hLM : L ≤ M) (hL0 : L ≠ ⊥)
    (hee : e ∘ₗ e = e) (hpyth : ∀ σ x y, N σ (e x + (y - e y)) ^ 2 = N σ (e x) ^ 2 + N σ (y - e y) ^ 2)
    (hg : 1 ≤ g) (hint : ∀ x ∈ L, (g : K) • e x ∈ L) :
    rkK G₀ + rkK B₀ = rkK L ∧ 0 < rkK L ∧ (G₀ ≠ ⊥ → 0 < rkK G₀) ∧
    (rkK L : ℝ) * slope_sq N L ≤ rkK G₀ * slope_sq N G₀ + rkK B₀ * (slopeMax_sq N M + 2 * Real.log g) := by
  let : StarRing K := starRingOfComm
  obtain ⟨F⟩ := hGram
  obtain ⟨n, ⟨⟨b, X⟩, hG⟩⟩ := F
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  have hLfg : L.FG := Submodule.FG.of_le hM hLM
  have hRfg : (G₀).FG := Submodule.FG.of_le hM (inf_le_left.trans hLM)
  have hsa : ∀ v x y, majAt b X v (e x) y = majAt b X v x (e y) := by
    intro v
    apply selfAdj_of_pyth b X v (IsTotallyComplex.isComplex v) e
    intro x y
    simp only [(hG v).2]
    exact hpyth v.embedding x y
  obtain ⟨hrk, hcut, hmaj⟩ := Formalism.ExtensionFiltration.goodBadCut K V (Fin n) b X hX e g L hLfg hg hee hsa hint
  have hM0 : M ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hLM))
  have hpos (S : Submodule (𝓞 K) V) (hne : S ≠ ⊥) : 0 < rkK S :=
    Nat.pos_of_ne_zero (Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b S hne)
  refine ⟨hrk, hpos L hL0, hpos _, ?_⟩
  rw [slope_sq_eq hG hLfg, slope_sq_eq hG hRfg, (slopeMax_slopeMin_eq hG hM hM0).1]
  linarith [hmaj M hM hLM]

/-- A finite-rank cut: only the actual bad-to-good rank ratio and slope gap cost anything. -/
theorem slope_good_ge_of_rank (hGram : HasGram N) (hM : M.FG) (hLM : L ≤ M) (hR0 : G₀ ≠ ⊥)
    (hee : e ∘ₗ e = e) (hpyth : ∀ σ x y, N σ (e x + (y - e y)) ^ 2 = N σ (e x) ^ 2 + N σ (y - e y) ^ 2)
    (hg : 1 ≤ g) (hint : ∀ x ∈ L, (g : K) • e x ∈ L) :
    rkK G₀ + rkK B₀ = rkK L ∧ slope_sq N L - (rkK B₀ / (rkK G₀ : ℝ)) *
      (slopeMax_sq N M + 2 * Real.log g - slope_sq N L) ≤ slope_sq N G₀ := by
  have hL0 : L ≠ ⊥ := fun h => hR0 (le_bot_iff.mp (show G₀ ≤ ⊥ from h ▸ inf_le_left))
  obtain ⟨hrk, -, hpos, hcut⟩ := weighted_slope_cut K V N L M e g hGram hM hLM hL0 hee hpyth hg hint
  have hg' : 0 < (rkK G₀ : ℝ) := by exact_mod_cast hpos hR0
  rw [← hrk, Nat.cast_add] at hcut
  refine ⟨hrk, ?_⟩
  field_simp [hg'.ne']
  linarith

theorem slope_good_ge_sharp (δ Q : ℝ) (hGram : HasGram N) (hM : M.FG) (hLM : L ≤ M) (hL0 : L ≠ ⊥)
    (hee : e ∘ₗ e = e) (hpyth : ∀ σ x y, N σ (e x + (y - e y)) ^ 2 = N σ (e x) ^ 2 + N σ (y - e y) ^ 2)
    (hg : 1 ≤ g) (hint : ∀ x ∈ L, (g : K) • e x ∈ L) (hδ' : δ < 1 / 3)
    (hrk : (rkK B₀ : ℝ) ≤ 3 * δ * rkK L) (hmax : slopeMax_sq N M ≤ Q)
    (hmin : -Q ≤ slope_sq N L) (hlog : 2 * Real.log g ≤ Q) :
    slope_sq N L - 9 * δ * Q / (1 - 3 * δ) ≤ slope_sq N G₀ := by
  obtain ⟨hsum, hpos, -, hcut⟩ := weighted_slope_cut K V N L M e g hGram hM hLM hL0 hee hpyth hg hint
  have htotal : (0 : ℝ) < rkK L := by exact_mod_cast hpos
  rw [← hsum, Nat.cast_add] at htotal hcut hrk
  exact numeric_sharp htotal (Nat.cast_nonneg _) (Nat.cast_nonneg _) hcut hδ' hrk hmax hmin hlog
    (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hg)))

end

theorem slope_good_ge : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L M : Submodule (𝓞 K) V) (e : V →ₗ[K] V) (g : ℕ) (δ Q : ℝ), HasGram N → M.FG → L ≤ M → L ≠ ⊥ → e ∘ₗ e = e → (∀ σ x y, N σ (e x + (y - e y)) ^ 2 = N σ (e x) ^ 2 + N σ (y - e y) ^ 2) → 1 ≤ g → (∀ x ∈ L, (g : K) • e x ∈ L) → 0 ≤ δ → δ ≤ 1 / 12 → (Formalism.HN.rkK (L ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ≤ 3 * δ * Formalism.HN.rkK L → slopeMax_sq N M ≤ Q → -Q ≤ slope_sq N L → 2 * Real.log g ≤ Q → slope_sq N L - 12 * δ * Q ≤ slope_sq N (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) := by
  intro K V _ _ _ _ _ _ _ N L M e g δ Q hGram hM hLM hL0 hee hpyth hg hint hδ hδ' hrk hmax hmin hlog
  have h := slope_good_ge_sharp K V N L M e g δ Q hGram hM hLM hL0 hee hpyth hg hint (by linarith) hrk hmax hmin hlog
  have hQ : 0 ≤ Q := le_trans (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hg))) hlog
  have hle : 9 * δ * Q / (1 - 3 * δ) ≤ 12 * δ * Q := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - 3 * δ)).2
    nlinarith [mul_nonneg (mul_nonneg hδ hQ) (show 0 ≤ 1 - 12 * δ by linarith)]
  linarith

end GlobalTheory.CutNum
