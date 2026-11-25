module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Mathlib
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf

@[expose] public section

section
noncomputable section
namespace GlobalTheory.CovTop.LevelIndex
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV
open scoped nonZeroDivisors

open UniqueFactorizationMonoid

private theorem prod_places_of_squarefree {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E))
    (hsq : Squarefree I) (P : Finset (HeightOneSpectrum (𝓞 E)))
    (hP : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ P ↔ I ≤ w.asIdeal) :
    ∏ w ∈ P, Ideal.absNorm w.asIdeal = Ideal.absNorm I := by
  classical
  have hf : P.image HeightOneSpectrum.asIdeal = (normalizedFactors I).toFinset := by
    ext J
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hsq.ne_zero]
    constructor
    · intro hj
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨w.isPrime, (hP w).mp hw⟩
    · rintro ⟨hJ, hle⟩
      have hn : J ≠ ⊥ := fun he => hsq.ne_zero (bot_unique (he ▸ hle))
      let w : HeightOneSpectrum (𝓞 E) := ⟨J, hJ, hn⟩
      exact Finset.mem_image.mpr ⟨w, (hP w).mpr hle, rfl⟩
  have hn := (squarefree_iff_nodup_normalizedFactors hsq.ne_zero).mp hsq
  have hprod : ∏ w ∈ P, w.asIdeal = I := by
    calc
      _ = ∏ J ∈ P.image HeightOneSpectrum.asIdeal, J := (Finset.prod_image (fun w _ v _ h => HeightOneSpectrum.ext h)).symm
      _ = I := by
        rw [hf, Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hn.dedup]
        simpa using Ideal.prod_normalizedFactors_eq_self hsq.ne_zero
  rw [← hprod, map_prod]

/-- Exact norm product when both base primes are unramified in the extension. -/
theorem prod_eq_relative {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] (v : Fin 2 → HeightOneSpectrum (𝓞 K))
    (P : Finset (HeightOneSpectrum (𝓞 E))) (hP : ∀ w, w ∈ P ↔ ∃ k, w.under (𝓞 K) = v k)
    (hsq : Squarefree (((v 0).asIdeal * (v 1).asIdeal).map (algebraMap (𝓞 K) (𝓞 E)))) :
    ∏ w ∈ P, Ideal.absNorm w.asIdeal =
      (Ideal.absNorm (v 0).asIdeal * Ideal.absNorm (v 1).asIdeal) ^ Module.finrank K E := by
  rw [prod_places_of_squarefree _ hsq P, Ideal.absNorm_algebraMap, map_mul, ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E]
  intro w
  rw [hP, Ideal.map_le_iff_le_comap]
  change (∃ k, w.under (𝓞 K) = v k) ↔ (v 0).asIdeal * (v 1).asIdeal ≤ (w.under (𝓞 K)).asIdeal
  rw [(w.under (𝓞 K)).isPrime.mul_le]
  have he (k : Fin 2) : (v k).asIdeal ≤ (w.under (𝓞 K)).asIdeal ↔ w.under (𝓞 K) = v k :=
    ⟨fun h => HeightOneSpectrum.ext ((v k).isMaximal.eq_of_le (w.under (𝓞 K)).isPrime.ne_top h).symm,
      fun h => h.symm ▸ le_rfl⟩
  rw [he, he, Fin.exists_fin_two]

open Formalism.BasicNotions Formalism.IndefR.Links
open Formalism.MainNotions Formalism.L2 Formalism.L2.DIV

theorem prod_absNorm_aux_eq (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) :
    ∏ w ∈ C.Pg, Ideal.absNorm w.asIdeal = (D.host.g 0 * D.host.g 1) ^ D.R.f := by
  classical
  let M (k : Fin 2) := Ideal.span {(D.host.g k : 𝓞 D.host.E)}
  have hM (k : Fin 2) : Squarefree (M k) := by
    have hn : M k ≠ ⊥ := by simpa [M] using (D.host.g_prime k).ne_zero
    exact (squarefree_iff_nodup_normalizedFactors hn).mpr
      (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D k).2
  have hcop : IsCoprime (D.host.g 0 : 𝓞 D.host.E) (D.host.g 1 : 𝓞 D.host.E) := by
    have hg := Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1) |>.mpr D.host.g_ne
    simpa only [map_natCast] using hg.isCoprime.map (Int.castRingHom (𝓞 D.host.E))
  have hsq := squarefree_mul_iff.mpr
    ⟨((Ideal.isCoprime_span_singleton_iff _ _).mpr hcop).isRelPrime, hM 0, hM 1⟩
  have hd (k : Fin 2) : (C.C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ∣ M k := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (C.C.P.pb_over k)
  have hprod := prod_eq_relative C.C.P.pb C.Pg hC.Pg
    (by rw [Ideal.map_mul]; exact hsq.squarefree_of_dvd (mul_dvd_mul (hd 0) (hd 1)))
  have hp (k : Fin 2) : Ideal.absNorm (C.C.P.pb k).asIdeal = D.host.g k := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Formalism.MainNotions.J.splits_sub D.host.K (D.host.g k) D.host.E (D.host.g_prime k)
      (D.nd.g_split k)).2 _ (C.C.P.pb_over k)
  have hrel : Module.finrank D.host.K D.host.E = D.R.f := D.host.toHostAx.finrank_EK
  simpa only [hp, hrel] using hprod

end GlobalTheory.CovTop.LevelIndex
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.CovTop.LevelIndex.level_index_le_half (D : D7) (Tu : Type) (C : LevCh D Tu)
    (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P).relIndex
      (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (LevelP.full _ _ _)) ≠ 0 ∧
    Real.log ((GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P).relIndex
      (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (LevelP.full _ _ _))) ≤
      D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (LevelP.full _ _ _) = parLev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P) := by
    have e : C.datWp i (LevelP.full _ _ _) = { C.datWp i P with P := LevelP.full (C.datWp i P).Pg (C.datWp i P).r ℂ } := by
      simp only [LevCh.datWp, datY, ite_true]
    rw [← GlobalTheory.CovTop.LevelIndex.lev_full, ← e]
  obtain ⟨h0, h1⟩ := GlobalTheory.CovTop.LevelIndex.relIndex_lev_le D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P) _ hB
  refine ⟨h0, ?_⟩
  have h2 := GlobalTheory.CovTop.LevelIndex.prod_absNorm_aux_eq D Tu C t0 hC
  have h3 := GlobalTheory.CovTop.LevelIndex.card_levelQuotientGroup_le_prod_absNorm_pow_sq C.Pg D.R.r
  have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (LevelP.full _ _ _)) ≤
      (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r ^ 2) := by
    rw [pow_mul]
    exact h1.trans (h2 ▸ h3)
  have h5 := Real.log_le_log (Nat.cast_pos.2 (Nat.pos_of_ne_zero h0)) (Nat.cast_le (α := ℝ).2 h4)
  refine h5.trans (le_of_eq ?_)
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

theorem GlobalTheory.CovTop.LevelIndex.level_index_le_bound (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems)
    (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m)
    (P : LevelP C.Pg D.R.r ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.IndexBound C i P := by
  obtain ⟨hn, h⟩ := GlobalTheory.CovTop.LevelIndex.level_index_le_half D Tu C t0 hC i P
  refine Function.const _ ⟨hn, h.trans ?_⟩ hP
  have hp : 1 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hg : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := Real.log_nonneg (by exact_mod_cast hp)
  have hpos : 0 ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by positivity
  linarith
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
theorem _root_.GlobalTheory.T.level_subgroup_index_bounded (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems)
    (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m)
    (P : LevelP C.Pg D.R.r ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.IndexBound C i P :=
  _root_.GlobalTheory.CovTop.LevelIndex.level_index_le_bound hP D Tu C t0 hC i P
end
