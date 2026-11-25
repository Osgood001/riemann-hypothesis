module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureLevelRealBoxEqIndexMul
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.LowSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMassUpperBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.A

theorem exists_box {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, BorelSpace (X i)] [∀ i, Group (X i)] [∀ i, IsTopologicalGroup (X i)] [∀ i, LocallyCompactSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, SecondCountableTopology (X i)] (m : ∀ i, Measure (X i)) [∀ i, (m i).IsHaarMeasure] :
    ∃ B : Set (∀ i, X i), MeasurableSet B ∧ Measure.pi m B ≠ 0 ∧ Measure.pi m B ≠ ⊤ := by
  choose K hK hKn using fun i => exists_compact_mem_nhds (1 : X i)
  refine ⟨Set.univ.pi K, MeasurableSet.univ_pi fun i => (hK i).measurableSet, ?_, ?_⟩
  · rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (Measure.measure_pos_of_mem_nhds (μ := m i) (hKn i)).ne'
  · rw [Measure.pi_pi]
    exact ENNReal.prod_ne_top fun i _ => (hK i).measure_lt_top.ne

theorem le_exp_three : (13 : ℝ) ≤ Real.exp 3 := by
  have e1 := Real.exp_one_gt_d9
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (13 : ℝ) ≤ 2.7 ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3

theorem bound (f r d : ℕ) (L n v M rd : ℝ) (hd : (d : ℝ) = 2 * f) (hL : 1 ≤ L)
    (hfr : (f : ℝ) * (r : ℝ) ^ 2 ≤ Real.exp L) (hrd1 : 1 ≤ rd) (hrdL : Real.log rd ≤ 2 * L) (hn1 : 1 ≤ n)
    (hn : Real.log n ≤ 60 * (f * (r : ℝ) ^ 2 * L)) (hv0 : 0 ≤ v) (hv : v ≤ 13 ^ (r ^ 2))
    (hM : M ≤ (3 * ((d : ℝ) ^ 2 * (r : ℝ) ^ 4 * rd ^ 2)) ^ (3 * d * r ^ 2)) :
    n * (v ^ f * M) ≤ Real.exp (117 * (f * (r : ℝ) ^ 2 * L)) := by
  have ha : 0 ≤ (f : ℝ) * (r : ℝ) ^ 2 := by positivity
  have hn' : n ≤ Real.exp (60 * (f * (r : ℝ) ^ 2 * L)) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < n)]; exact Real.exp_le_exp.2 hn
  have h13 := le_exp_three
  have hv' : v ^ f ≤ Real.exp (3 * (f * (r : ℝ) ^ 2 * L)) := by
    calc v ^ f ≤ ((13 : ℝ) ^ (r ^ 2)) ^ f := pow_le_pow_left₀ hv0 hv f
      _ = (13 : ℝ) ^ (r ^ 2 * f) := by rw [pow_mul]
      _ ≤ Real.exp 3 ^ (r ^ 2 * f) := pow_le_pow_left₀ (by norm_num) h13 _
      _ = Real.exp (((r ^ 2 * f : ℕ) : ℝ) * 3) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp (3 * (f * (r : ℝ) ^ 2 * L)) := by
        refine Real.exp_le_exp.2 ?_
        push_cast
        nlinarith
  have hrd : rd ≤ Real.exp (2 * L) := (Real.log_le_iff_le_exp (by linarith)).1 hrdL
  have hX : 3 * ((d : ℝ) ^ 2 * (r : ℝ) ^ 4 * rd ^ 2) ≤ Real.exp (9 * L) := by
    have e1 : ((f : ℝ) * (r : ℝ) ^ 2) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ ha hfr 2
    have e2 : rd ^ 2 ≤ Real.exp (2 * L) ^ 2 := pow_le_pow_left₀ (by linarith) hrd 2
    have e3 : Real.exp (9 * L) = Real.exp 3 * Real.exp L ^ 2 * Real.exp (2 * L) ^ 2 * Real.exp (3 * L - 3) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
    have e4 : 1 ≤ Real.exp (3 * L - 3) := Real.one_le_exp (by linarith)
    have e5 : 3 * ((d : ℝ) ^ 2 * (r : ℝ) ^ 4 * rd ^ 2) = 12 * (((f : ℝ) * (r : ℝ) ^ 2) ^ 2 * rd ^ 2) := by rw [hd]; ring
    rw [e3, e5]
    have p1 : 0 ≤ ((f : ℝ) * (r : ℝ) ^ 2) ^ 2 * rd ^ 2 := by positivity
    have p2 : ((f : ℝ) * (r : ℝ) ^ 2) ^ 2 * rd ^ 2 ≤ Real.exp L ^ 2 * Real.exp (2 * L) ^ 2 :=
      mul_le_mul e1 e2 (by positivity) (by positivity)
    have p3 : 0 ≤ Real.exp L ^ 2 * Real.exp (2 * L) ^ 2 := by positivity
    calc 12 * (((f : ℝ) * (r : ℝ) ^ 2) ^ 2 * rd ^ 2) ≤ Real.exp 3 * (Real.exp L ^ 2 * Real.exp (2 * L) ^ 2) :=
          mul_le_mul (by linarith) p2 p1 (Real.exp_pos _).le
      _ = Real.exp 3 * Real.exp L ^ 2 * Real.exp (2 * L) ^ 2 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)
  have hM' : M ≤ Real.exp (54 * (f * (r : ℝ) ^ 2 * L)) := by
    refine hM.trans ?_
    calc (3 * ((d : ℝ) ^ 2 * (r : ℝ) ^ 4 * rd ^ 2)) ^ (3 * d * r ^ 2) ≤ Real.exp (9 * L) ^ (3 * d * r ^ 2) :=
          pow_le_pow_left₀ (by positivity) hX _
      _ = Real.exp (((3 * d * r ^ 2 : ℕ) : ℝ) * (9 * L)) := by rw [Real.exp_nat_mul]
      _ = _ := by congr 1; push_cast; rw [hd]; ring
  rcases le_or_gt M 0 with hM0 | hM0
  · have : n * (v ^ f * M) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hv0 _) hM0)
    exact this.trans (Real.exp_pos _).le
  · calc n * (v ^ f * M) ≤ Real.exp (60 * (f * (r : ℝ) ^ 2 * L)) *
          (Real.exp (3 * (f * (r : ℝ) ^ 2 * L)) * Real.exp (54 * (f * (r : ℝ) ^ 2 * L))) :=
          mul_le_mul hn' (mul_le_mul hv' hM' hM0.le (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring


/-- Retain the actual level index instead of charging every level the worst allowed index. -/
theorem level_mass_bound (f r d : ℕ) (L n v M rd : ℝ) (hd : (d : ℝ) = 2 * f)
    (hfr : 2 * ((f : ℝ) * (r : ℝ) ^ 2) ≤ Real.exp L) (hrd : 0 < rd)
    (hrdL : Real.log rd ≤ 2 * L) (hn : 0 ≤ n) (hv : 0 ≤ v) (hv' : v ≤ 13 ^ (r ^ 2))
    (hM : M ≤ (3 * ((d : ℝ) ^ 2 * (r : ℝ) ^ 4 * rd ^ 2)) ^ (3 * d * r ^ 2)) :
    n * (v ^ f * M) ≤ n * Real.exp ((f * (r : ℝ) ^ 2) *
      (36 * L + 6 * Real.log 3 + Real.log 13)) := by
  have hrd' := (Real.log_le_iff_le_exp hrd).mp hrdL
  have hX : 3 * ((d : ℝ) ^ 2 * (r : ℝ) ^ 4 * rd ^ 2) ≤ Real.exp (6 * L + Real.log 3) := by
    have he : Real.exp (6 * L + Real.log 3) = 3 * (Real.exp L ^ 2 * Real.exp (2 * L) ^ 2) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3),
        ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      ring_nf
    rw [he, hd]
    calc _ = 3 * ((2 * ((f : ℝ) * r ^ 2)) ^ 2 * rd ^ 2) := by ring
         _ ≤ _ := by gcongr
  have hmass : M ≤ (Real.exp (6 * L + Real.log 3)) ^ (3 * d * r ^ 2) :=
    hM.trans (pow_le_pow_left₀ (by positivity) hX _)
  have hvf : v ^ f ≤ ((13 : ℝ) ^ (r ^ 2)) ^ f := pow_le_pow_left₀ hv hv' _
  apply mul_le_mul_of_nonneg_left _ hn
  calc v ^ f * M ≤ v ^ f * (Real.exp (6 * L + Real.log 3)) ^ (3 * d * r ^ 2) :=
         mul_le_mul_of_nonneg_left hmass (pow_nonneg hv _)
       _ ≤ ((13 : ℝ) ^ (r ^ 2)) ^ f * (Real.exp (6 * L + Real.log 3)) ^ (3 * d * r ^ 2) :=
         mul_le_mul_of_nonneg_right hvf (by positivity)
       _ = _ := by
         rw [← Real.exp_log (by norm_num : (0 : ℝ) < 13), ← pow_mul, ← Real.exp_nat_mul,
           ← Real.exp_nat_mul, ← Real.exp_add, Real.log_exp]
         congr 1
         push_cast
         rw [hd]
         ring

private theorem fixed_loss_le (L : ℝ) (hL : (120 : ℝ) ≤ Real.exp L) :
    6 * Real.log 3 + Real.log 13 ≤ 2 * L := by
  have h : Real.exp (6 * Real.log 3 + Real.log 13) ≤ Real.exp (2 * L) := by
    rw [Real.exp_add, show (6 : ℝ) = ((6 : ℕ) : ℝ) from rfl, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 3), Real.exp_log (by norm_num : (0 : ℝ) < 13),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Real.exp_nat_mul]
    calc (3 : ℝ) ^ 6 * 13 ≤ 120 ^ 2 := by norm_num
         _ ≤ _ := pow_le_pow_left₀ (by norm_num) hL _
  exact Real.exp_le_exp.mp h

open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in
theorem measure_eq_index_mul_mass (hV : VolSt) (hS : StabSt) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0)
    (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕)
    :
    μ 𝓕 = ((levW C i P).relIndex (levW C i (LevelP.full _ _ _)) : ℝ≥0∞) *
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f *
        Formalism.MainNotions.StandardLattice.massI D D.R.r) := by
  have hfull : levW C i (LevelP.full _ _ _) = parLev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P) := by
    have e : C.datWp i (LevelP.full _ _ _) = { C.datWp i P with P := LevelP.full (C.datWp i P).Pg (C.datWp i P).r ℂ } := by
      simp only [LevCh.datWp, datY, ite_true]
    rw [← GlobalTheory.CovTop.LevelIndex.lev_full, ← e]
  have hn := (GlobalTheory.CovTop.LevelIndex.relIndex_lev_le D.sp.cm (Wc D i).gram (C.βW i)
    (C.datWp i P) _ hfull).1
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have := hF.1.1
  obtain ⟨⟨θ, hθ⟩, H1⟩ := hF.1.2
  obtain ⟨⟨A, hA⟩, H2⟩ := H1 θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := H2 A hA
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic D (Wc D i) θ A (D.sp.W_sig _) hθ hA
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1
  obtain ⟨B, hBm, hB0, hBt⟩ := MainStatements.Tam.A.exists_box m
  have hvol := hV D (Wc D i) _ _ (D.sp.W_sig _) (D.sp.W_sigval _ (Nat.le_add_left _ _) i.2) μ 𝓕 hF.2 θ A m rp hθ hA hm
    hrpc hrp B hBm
  set K₀ := levW C i (Formalism.L2.DIV.LevelP.full _ _ _) with hK₀
  set n := (levW C i P).relIndex K₀ with hndef
  have hsub : {h | h ∈ Stab (Wc D i) ∧ rp h ∈ B} ⊆ {h | finE (Wc D i) (1⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} := by
    rintro h ⟨hh, hb⟩
    refine ⟨?_, hb⟩
    rw [inv_one, one_mul]
    have hk : h ∈ KM (Wc D i) 1 := (hS.1 D (Wc D i)).1 ▸ hh
    exact GlobalTheory.T.finitePart_mem_fullLevel_of_keeps_selfDualLattice D (Wc D i) (C.βW i) (C.ΛW i) _ (hC.βW i) hrk.le rfl h hk
  have rev : {h | finE (Wc D i) (1⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ⊆
      {h | h ∈ Stab (Wc D i) ∧ rp h ∈ B} := by
    intro h hh
    refine ⟨hS.2 D Tu C t0 hC i (LevelP.full _ _ _) h ?_, hh.2⟩
    simpa [K₀] using hh.1
  have heq := GlobalTheory.CovTop.VolBox.meas_level_eq_index_mul (Wc D i) θ A m rp (levW C i P) K₀ μ
    (D.sp.W_sig _) hθ hA hm hrpc hrp (fun k hk => ⟨hk.1, Subgroup.mem_top _⟩) hn
    (fun _ hk => lev_le_UA hk) (GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _) hF.1 B hBm
  have hstab : μ {h | h ∈ Stab (Wc D i) ∧ rp h ∈ B} = (n : ℝ≥0∞) * Measure.pi m B := by
    rw [Set.Subset.antisymm hsub rev]
    simpa [n] using heq
  have hc := congrArg (fun r : ℕ => ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU r ^ D.R.f *
    Formalism.MainNotions.StandardLattice.massI D r)) hrk
  apply (ENNReal.mul_left_inj hB0 hBt).mp
  rw [hvol, hstab, hc]
  ring

open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in
theorem log_measure_le_log_index_add (hV : VolSt) (hS : StabSt) (hN : NumSt) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0)
    (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕) (L : ℝ) (hL : Sizes D L)
    (hn : (levW C i P).relIndex (levW C i (LevelP.full _ _ _)) ≠ 0) :
    Real.log (μ 𝓕).toReal ≤ Real.log ((levW C i P).relIndex (levW C i (LevelP.full _ _ _))) +
      38 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  let n := (levW C i P).relIndex (levW C i (LevelP.full _ _ _))
  have hμ := (measure_eq_index_mul_mass hV hS D Tu C t0 hC i P μ 𝓕 hF).le
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [show Module.finrank ℚ D.host.E = 4 * D.R.ord from D.host.finrank_cmField]
    unfold Ranks.f Ranks.n; ring
  have hu : Formalism.MainNotions.StandardLattice.massI D D.R.r ≤ (3 * ((Module.finrank ℚ D.host.E : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 * D.host.rdE ^ 2)) ^
      (3 * Module.finrank ℚ D.host.E * D.R.r ^ 2) := GlobalTheory.mass_stdLat_le D.host.E (fun _ => rfl) D.R.r
  obtain ⟨hN1, hN2⟩ := hN D.R.r hr
  have hfv : (2 : ℝ) ≤ D.R.f := by
    exact_mod_cast (show 2 ≤ D.R.f by
      unfold Ranks.f Ranks.n
      have := D.R.ord_pos
      omega)
  have hrv : (6 : ℝ) ≤ D.R.r := by
    exact_mod_cast (show 6 ≤ D.R.r by
      unfold Ranks.r
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      omega)
  have hnv : 2 * (D.R.r : ℝ) ≤ D.R.nV := by
    exact_mod_cast (show 2 * D.R.r ≤ D.R.nV by
      have h := D.R.rank_add_five_le
      unfold Ranks.nV Ranks.r
      omega)
  have hfr : 2 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ≤ Real.exp L := by
    apply le_trans _ hL.1
    calc _ = ((D.R.f : ℝ) * D.R.r) * (2 * D.R.r) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hnv (by positivity)
  have h120 : (120 : ℝ) ≤ Real.exp L := by
    apply le_trans _ hfr
    calc (120 : ℝ) ≤ 2 * (2 * 6 ^ 2) := by norm_num
         _ ≤ _ := by gcongr
  have hd1 : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero D.host.E)
  have hrd : 0 < D.host.rdE := Real.rpow_pos_of_pos (zero_lt_one.trans_le hd1) _
  have hrdL : Real.log D.host.rdE ≤ 2 * L := by linarith [hL.2.2.2, abs_nonneg (dlogL D 1)]
  have hvol := level_mass_bound D.R.f D.R.r (Module.finrank ℚ D.host.E) L n _ _ D.host.rdE
    (by rw [hfin]; push_cast; ring) hfr hrd hrdL (Nat.cast_nonneg _) (le_trans (by positivity) hN1) hN2 hu
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hlt : (μ 𝓕).toReal ≤ (n : ℝ) * Real.exp ((D.R.f * (D.R.r : ℝ) ^ 2) *
      (36 * L + 6 * Real.log 3 + Real.log 13)) := by
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    apply hμ.trans
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hvol
  have hL0 : 0 ≤ L := Real.one_le_exp_iff.mp (by linarith : 1 ≤ Real.exp L)
  have hb := mul_le_mul_of_nonneg_left (fixed_loss_le L h120)
    (show 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 by positivity)
  rcases ENNReal.toReal_nonneg (a := μ 𝓕) |>.eq_or_lt with hz | hz
  · rw [← hz, Real.log_zero]
    have hln := Real.log_nonneg ((Nat.one_le_cast).mpr (Nat.one_le_iff_ne_zero.mpr hn) : (1 : ℝ) ≤ n)
    positivity
  · have hh := Real.log_le_log hz hlt
    rw [Real.log_mul hnpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hh
    dsimp [n] at *
    linarith only [hh, hb]

open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in
theorem up_core (hV : VolSt) (hS : StabSt) (hN : NumSt) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0)
    (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (levW C i P) μ 𝓕) (L : ℝ) (hL : Sizes D L) (hIB : IndexBound C i P) :
    Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  have hh := log_measure_le_log_index_add hV hS hN D Tu C t0 hC i P μ 𝓕 hF L hL hIB.1
  have h₁ := mul_le_mul_of_nonneg_left hL.2.2.1 (show 0 ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 by positivity)
  have h₂ := hIB.2
  have hlogg : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le ((Nat.one_le_cast).mpr (D.host.g_prime 0).one_le)
      ((Nat.one_le_cast).mpr (D.host.g_prime 1).one_le)
  have hL0 : 0 ≤ L := by linarith [hL.2.2.1]
  have hA : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L := by positivity
  have hB : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D.R.r; linarith))
  linarith only [hh, h₁, h₂, hA, hB]

end MainStatements.Tam.A

namespace MainStatements.Tam

end MainStatements.Tam

end
