import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem aeval_const_mul {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℤ R] {G : MvPolynomial σ ℤ} {n : ℕ}
    (hG : G.IsHomogeneous n) (κ : R) (a : σ → R) :
    aeval (fun j => κ * a j) G = κ ^ n * aeval a G := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = n := by
    have h := hG (mem_support_iff.1 hm)
    have e : Finsupp.weight (1 : σ → ℕ) m = ∑ i, m i := by
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
    rw [← e]
    exact h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_homog {σ Ω : Type} [Field Ω] [CharZero Ω] (r : σ → Ω) (c₀ : σ) (h1 : r c₀ = 1)
    (t : Algebra.adjoin ℚ (Set.range r)) :
    ∃ (m : ℤ) (n : ℕ) (G : MvPolynomial σ ℤ), m ≠ 0 ∧ G.IsHomogeneous n ∧
      aeval r G = (m : Ω) * (t : Ω) := by
  obtain ⟨t, ht⟩ := t
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, 1, X j, one_ne_zero, isHomogeneous_X _ _, by simp⟩
  | algebraMap q =>
    refine ⟨q.den, 0, C q.num, by exact_mod_cast q.den_nz, isHomogeneous_C _ _, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := by exact_mod_cast q.den_nz
    simp only [map_intCast, eq_intCast, eq_ratCast, Int.cast_natCast]
    rw [Rat.cast_def]
    field_simp
  | add x y hx hy ihx ihy =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihx
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihy
    refine ⟨m₁ * m₂, n₁ + n₂, C m₂ * X c₀ ^ n₂ * G₁ + C m₁ * X c₀ ^ n₁ * G₂, mul_ne_zero hm₁ hm₂, ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · have := ((isHomogeneous_C σ m₂).mul ((isHomogeneous_X ℤ c₀).pow n₂)).mul hG₁
        convert this using 1
        ring
      · have := ((isHomogeneous_C σ m₁).mul ((isHomogeneous_X ℤ c₀).pow n₁)).mul hG₂
        convert this using 1
        ring
    · simp only [map_add, map_mul, map_pow, aeval_X, h1, one_pow, mul_one, eq_intCast, map_intCast, e₁, e₂]
      push_cast
      ring
  | mul x y hx hy ihx ihy =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihx
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihy
    refine ⟨m₁ * m₂, n₁ + n₂, G₁ * G₂, mul_ne_zero hm₁ hm₂, hG₁.mul hG₂, ?_⟩
    simp only [map_mul, e₁, e₂]
    push_cast
    ring

theorem smooth_away_mul {B : Type} [CommRing B] [Algebra ℚ B] (s u : B) (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)] :
    Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away (s * u)) := by
  let S := Localization.Away s
  let T := Localization.Away (algebraMap B S u)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 S T :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (algebraMap B S u)
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans e 0 ℚ S T
  rw [zero_add] at h
  haveI : IsLocalization.Away (s * u) T := IsLocalization.Away.mul' S T s u
  let f : T ≃ₐ[B] Localization.Away (s * u) :=
    IsLocalization.algEquiv (Submonoid.powers (s * u)) T (Localization.Away (s * u))
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv e (f.restrictScalars ℚ)


end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
