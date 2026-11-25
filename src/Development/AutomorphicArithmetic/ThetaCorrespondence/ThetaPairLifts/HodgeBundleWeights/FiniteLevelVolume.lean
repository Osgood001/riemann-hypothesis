module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogMeasureRatioBounded

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR.Links
open NumberField IsDedekindDomain

namespace GlobalTheory.CovTop.LevelIndex

open UniqueFactorizationMonoid

/-- Unique factorization recovers the two-prime multiset from its product. -/
private theorem prime_profile {ι : Type*} (S : Finset ι) (u : ι → ℕ) (p q f : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hu : ∀ w ∈ S, (u w).Prime)
    (h : ∏ w ∈ S, u w = (p * q) ^ f) :
    S.val.map u = Multiset.replicate f p + Multiset.replicate f q := by
  have fac (T : Multiset ℕ) (hT : ∀ z ∈ T, z.Prime) : normalizedFactors T.prod = T := by
    simpa using normalizedFactors_prod_eq T (fun z hz => (Nat.prime_iff.mp (hT z hz)).irreducible)
  have hprod : (S.val.map u).prod = (Multiset.replicate f p + Multiset.replicate f q).prod := by
    rw [Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_replicate, ← mul_pow]
    exact h
  apply ((fac _ (by simpa using hu)).symm.trans ((congrArg normalizedFactors hprod).trans ?_))
  exact fac _ (fun z hz => by
    rcases Multiset.mem_add.mp hz with hz | hz
    · exact (Multiset.eq_of_mem_replicate hz) ▸ hp
    · exact (Multiset.eq_of_mem_replicate hz) ▸ hq)

/-- The level chooses exactly f places of each residual order, counting multiplicity. -/
theorem aux_residue_norms (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) :
    C.Pg.val.map (fun w => Ideal.absNorm w.asIdeal) =
      Multiset.replicate D.R.f (D.host.g 0) + Multiset.replicate D.R.f (D.host.g 1) := by
  refine prime_profile _ _ _ _ _ (D.host.g_prime 0) (D.host.g_prime 1) ?_
    (prod_absNorm_aux_eq D Tu C t0 hC)
  intro w hw
  obtain ⟨k, hk⟩ := (hC.Pg w).mp hw
  have e := (Formalism.MainNotions.J.splits_sub D.host.E (D.host.g k) D.host.E (D.host.g_prime k)
    (D.nd.g_split k)).2 w (C.C.P.overP hk)
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, e] using D.host.g_prime k

/-- Evaluate a placewise product directly at the two rational primes. -/
theorem eval_aux_residue_norms {M : Type*} [CommMonoid M] (B : ℕ → M)
    (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) :
    ∏ w ∈ C.Pg, B (Ideal.absNorm w.asIdeal) = (B (D.host.g 0) * B (D.host.g 1)) ^ D.R.f := by
  change (C.Pg.val.map (B ∘ fun w => Ideal.absNorm w.asIdeal)).prod = _
  have h := congrArg (fun t : Multiset ℕ => (t.map B).prod) (aux_residue_norms D Tu C t0 hC)
  simpa only [Multiset.map_map, Multiset.map_add, Multiset.map_replicate,
    Multiset.prod_add, Multiset.prod_replicate, mul_pow] using h

/-- Exact ambient residue order in terms of the rational auxiliary primes. -/
theorem card_GL_aux (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (r : ℕ) :
    Nat.card (G0 C.Pg r) =
      ((∏ i : Fin r, ((D.host.g 0) ^ r - (D.host.g 0) ^ (i : ℕ))) *
       (∏ i : Fin r, ((D.host.g 1) ^ r - (D.host.g 1) ^ (i : ℕ)))) ^ D.R.f := by
  calc
    _ = ∏ w ∈ C.Pg, ∏ i : Fin r, (Ideal.absNorm w.asIdeal ^ r - Ideal.absNorm w.asIdeal ^ (i : ℕ)) := by
      rw [Nat.card_pi, ← Finset.prod_coe_sort C.Pg]
      refine Finset.prod_congr rfl fun w _ => ?_
      let : Field (kP w.1) := Ideal.Quotient.field _
      let : Fintype (kP w.1) := Fintype.ofFinite _
      simpa [Ideal.absNorm_eq_natCard, Nat.card_eq_fintype_card] using Matrix.card_GL_field (𝔽 := kP w.1) r
    _ = _ := eval_aux_residue_norms (fun n => ∏ i : Fin r, (n ^ r - n ^ (i : ℕ))) D Tu C t0 hC


open Formalism.IndefR.Lev Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {Tu : Type} {C : LevCh D Tu} {t0 : Tu}

/-- Every residue matrix tuple lifts at each grid vertex. -/
theorem grid_reduction_surjective (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) :
    Function.Surjective (rHom D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P)) := by
  intro g
  obtain ⟨κ, -, hκ, hg⟩ := GlobalTheory.GeoActRoad.levelLiftsExist_gridVertexSpaces hC i g
  exact ⟨⟨finE (Wc D i) κ, hκ⟩, hg⟩

/-- The geometric index is the index of the original finite subgroup, without an image hypothesis. -/
theorem grid_level_index (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) :
    (levW C i P).relIndex (levW C i (LevelP.full _ _ _)) = P.H.index := by
  let B := parLev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P)
  have hfull : levW C i (LevelP.full _ _ _) = B := by
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h, Subgroup.mem_top _⟩⟩
  have e : (levW C i P).subgroupOf B =
      P.H.comap (rHom D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P)) := by
    ext x
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  rw [hfull, Subgroup.relIndex, e]
  exact P.H.index_comap_of_surjective (grid_reduction_surjective hC i P)

open Matrix

/-- The determinant-one residue condition ignores the rank, once the rank is positive. -/
private theorem residue_det_index {ι : Type*} [Fintype ι] (K : ι → Type*) [∀ i, Field (K i)]
    (r : ℕ) [Nonempty (Fin r)] :
    (MonoidHom.piMap (fun i => (GeneralLinearGroup.det : GL (Fin r) (K i) →* (K i)ˣ))).ker.index =
      ∏ i, (Nat.card (K i) - 1) := by
  classical
  let d := MonoidHom.piMap (fun i => (GeneralLinearGroup.det : GL (Fin r) (K i) →* (K i)ˣ))
  have hs : Function.Surjective d := by
    intro u
    choose A hA using fun i => GeneralLinearGroup.det_surjective (n := Fin r) (u i)
    exact ⟨A, funext hA⟩
  change d.ker.index = _
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs, Subgroup.card_top, Nat.card_pi]
  simp only [Nat.card_units]

/-- Applying the determinant at every auxiliary place. -/
def determinantOneLevel (D : D7) {Tu : Type} (C : LevCh D Tu) : LevelP C.Pg D.R.r ℂ :=
  ⟨(MonoidHom.piMap fun w : C.Pg => (Matrix.GeneralLinearGroup.det : GL (Fin D.R.r) (kP w.1) →* (kP w.1)ˣ)).ker, 1⟩

theorem determinant_level_index (hC : C.Is t0) (i : Fin D.R.m) :
    (levW C i (determinantOneLevel D C)).relIndex (levW C i (LevelP.full _ _ _)) =
      ((D.host.g 0 - 1) * (D.host.g 1 - 1)) ^ D.R.f := by
  classical
  have hpos : 0 < D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  let : Nonempty (Fin D.R.r) := ⟨⟨0, hpos⟩⟩
  let : ∀ w : C.Pg, Field (kP w.1) := fun w => Ideal.Quotient.field _
  rw [grid_level_index hC i, determinantOneLevel,
    residue_det_index (K := fun w : C.Pg => kP w.1) D.R.r]
  refine (Finset.prod_coe_sort C.Pg (fun w => Nat.card (kP w) - 1)).trans ?_
  simpa only [Ideal.absNorm_eq_natCard] using
    eval_aux_residue_norms (fun n => n - 1) D Tu C t0 hC

end GlobalTheory.CovTop.LevelIndex

namespace GlobalTheory.OneMeasureRatio

open Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.BasicNotions.TH
open GlobalTheory.CovTop.LevelIndex MainStatements.Tam GlobalTheory.CovTop.MeasRd
open MeasureTheory Formalism.L2.Theta
open scoped ENNReal

variable {D : D7} {Tu : Type} {C : LevCh D Tu} {t0 : Tu}

/-- Actual normalized fundamental-domain measure in terms of the finite residue subgroup alone. -/
theorem measure_eq_residue_index (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ)
    (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕) :
    μ 𝓕 = (P.H.index : ℝ≥0∞) * ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f *
        Formalism.MainNotions.StandardLattice.massI D D.R.r) := by
  rw [A.measure_eq_index_mul_mass vol stab D Tu C t0 hC i P μ 𝓕 hF, grid_level_index hC]

/-- Character and subgroup placement do not matter: the weighted ratio times subgroup order is constant. -/
theorem ratio_mul_residue_card (hC : C.Is t0) (i : Fin D.R.m) (P Q : LevelP C.Pg D.R.r ℂ)
    (μ ν : Measure (GA D (Wc D i))) (𝓕 𝓖 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕)
    (hG : IsMeasFD (Wc D i) (levW C i Q) ν 𝓖) :
    ratio D i μ 𝓕 * Nat.card P.H = ratio D i ν 𝓖 * Nat.card Q.H := by
  have h : (P.H.index : ℝ) * Nat.card P.H = (Q.H.index : ℝ) * Nat.card Q.H := by
    exact_mod_cast P.H.index_mul_card.trans Q.H.index_mul_card.symm
  simp only [ratio, measure_eq_residue_index hC i P μ 𝓕 hF, measure_eq_residue_index hC i Q ν 𝓖 hG,
    ENNReal.toReal_mul, ENNReal.toReal_natCast]
  linear_combination (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f *
    Formalism.MainNotions.StandardLattice.massI D D.R.r)).toReal * (∏ τ, dimAt D i τ) * h


/-- Cross-multiplication gives a closed formula at every level without a division hypothesis. -/
theorem measure_mul_residue_card (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ)
    (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕) :
    μ 𝓕 * (Nat.card P.H : ℝ≥0∞) =
      ((((∏ j : Fin D.R.r, (D.host.g 0 ^ D.R.r - D.host.g 0 ^ (j : ℕ))) *
         (∏ j : Fin D.R.r, (D.host.g 1 ^ D.R.r - D.host.g 1 ^ (j : ℕ)))) ^ D.R.f : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f *
        Formalism.MainNotions.StandardLattice.massI D D.R.r) := by
  rw [measure_eq_residue_index hC i P μ 𝓕 hF, ← card_GL_aux D Tu C t0 hC, ← P.H.index_mul_card, Nat.cast_mul]
  ring

/-- The selected subgroup's full logarithmic size is subtracted from the uniform weighted bound. -/
theorem log_covolume_ratio_add_log_card_le (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ)
    (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕)
    (L : ℝ) (hL : Sizes D L) :
    Real.log (ratio D i μ 𝓕) + Real.log (Nat.card P.H : ℝ) ≤
      (139 / 2) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  have hv := log_covolume_ratio_le_index D Tu C t0 hC i P μ 𝓕 hF L hL
  rw [grid_level_index hC] at hv
  have hi := (level_index_le_half D Tu C t0 hC i (LevelP.triv _ _ _)).2
  rw [grid_level_index hC] at hi
  change Real.log ((⊥ : Subgroup (G0 C.Pg D.R.r)).index : ℝ) ≤ _ at hi
  rw [Subgroup.index_bot] at hi
  have hi0 : (0 : ℝ) < P.H.index := by exact_mod_cast P.H.index_pos
  have hc0 : (0 : ℝ) < Nat.card P.H := by exact_mod_cast (Nat.card_pos : 0 < Nat.card P.H)
  have hlog : Real.log (P.H.index : ℝ) + Real.log (Nat.card P.H : ℝ) =
      Real.log (Nat.card (G0 C.Pg D.R.r) : ℝ) := by
    rw [← Real.log_mul hi0.ne' hc0.ne', ← Nat.cast_mul, P.H.index_mul_card]
  have haux := mul_le_mul_of_nonneg_left hL.2.2.1
    (show 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 by positivity)
  linarith only [hv, hi, hlog, haux]

end GlobalTheory.OneMeasureRatio
