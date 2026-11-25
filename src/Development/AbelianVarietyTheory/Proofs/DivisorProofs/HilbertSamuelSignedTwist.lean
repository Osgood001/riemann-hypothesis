module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMovingTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLogTwistContinuityAboveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsLeOfHermLBLeBySmallSection

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Asymptotics
open GlobalTheory GlobalTheory.ArInt GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.HermLB

namespace GlobalTheory.HSNef
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
variable {A B : HermLB p}

private theorem Le.congr_classes {C E : HermLB p} (h : Le A B)
    (hAC : A.icls = C.icls) (hBE : B.icls = E.icls) : Le C E :=
  (le_of_isometric (icls_eq_iff.mp hAC.symm)).trans (h.trans (le_of_isometric (icls_eq_iff.mp hBE)))

private theorem Le.tens_pair {C E : HermLB p} (h : Le A B) (g : Le C E) :
    Le (A.tens C) (B.tens E) := by
  apply (g.tens A).trans
  exact (h.tens E).congr_classes (by simp only [icls_tens, add_comm]) (by simp only [icls_tens, add_comm])

theorem Le.pow_nat (h : Le A B) (n : ℕ) : Le (A.pow n) (B.pow n) := by
  induction n with
  | zero => exact le_of_isometric (icls_eq_iff.mp (by simp only [icls_pow, zero_nsmul]))
  | succ n ih =>
      exact (ih.tens_pair h).congr_classes (by simp only [icls_tens, icls_pow, succ_nsmul])
        (by simp only [icls_tens, icls_pow, succ_nsmul])

theorem Le.dual_swap (h : Le A B) : Le B.dual A.dual := by
  apply (h.tens (B.dual.tens A.dual)).congr_classes <;> simp only [icls_tens, icls_dual] <;> abel

private theorem normalized_tendsto_zero_of_floor_bound
    (F : ℕ → ℕ → ℝ) (G : ℕ → ℝ) (j : ℕ → ℕ) (c d : ℕ)
    (hG : ∀ n, 0 ≤ G n) (hcmp : ∀ n i, c * j n ≤ i → G n ≤ F n i)
    (hfloor : ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      F n (n / q) ≤ F n 0 + ε * (n : ℝ) ^ d)
    (hbase : Tendsto (fun n : ℕ => F n 0 / (n : ℝ) ^ d) atTop (𝓝 0))
    (hj : Tendsto (fun n : ℕ => (j n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => G n / (n : ℝ) ^ d) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (div_nonneg (hG n) (by positivity))
  · intro ε hε
    obtain ⟨q, hq, hq0⟩ := ((hfloor (ε / 2) (half_pos hε)).and (eventually_gt_atTop 0)).exists
    have hsmall : Tendsto (fun n : ℕ => ((c * q : ℕ) : ℝ) * ((j n : ℝ) / n)) atTop (𝓝 0) := by
      simpa using hj.const_mul ((c * q : ℕ) : ℝ)
    filter_upwards [hq, hbase.eventually (gt_mem_nhds (half_pos hε)),
      hsmall.eventually (gt_mem_nhds zero_lt_one), eventually_gt_atTop 0] with n hfn hbn hsn hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hcj : c * j n ≤ n / q := by
      apply (Nat.le_div_iff_mul_le hq0).2
      have hr := (div_lt_iff₀ hn').mp (by simpa only [← mul_div_assoc] using hsn)
      exact_mod_cast (show ((c : ℝ) * j n) * q ≤ n by
        simpa only [Nat.cast_mul, one_mul, mul_right_comm] using hr.le)
    have hpow := pow_pos hn' d
    calc G n / (n : ℝ) ^ d ≤ (F n 0 + ε / 2 * (n : ℝ) ^ d) / (n : ℝ) ^ d :=
          div_le_div_of_nonneg_right ((hcmp n _ hcj).trans hfn) hpow.le
      _ = F n 0 / (n : ℝ) ^ d + ε / 2 := by rw [add_div, mul_div_cancel_right₀ _ hpow.ne']
      _ < ε := by linarith

private theorem encard_block (P : Pair p) {M : HermLB p} {a b : ℤ} (h : P.Rep a b M) :
    M.smallSec.encard = (P.Bl a b 1).encard :=
  SmallBall.encard_eq_Bl P h _ 1 zero_le_one (fun _ => by simp only [HermLB.smallSec, Set.mem_ofPred_eq, one_pow])

private theorem rep_twist (P : Pair p) {W : HermLB p} {e : ℤ} (hW : P.Rep 0 e W) (n j : ℕ) :
    P.Rep n (j * e) ((P.L.pow n).tens (W.pow j)) := by
  have hL := (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).1
  have h := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ _ _ _ _
    (GlobalTheory.T.represents_hermitianLineBundle_pow k X p P _ _ _ n hL)
    (GlobalTheory.T.represents_hermitianLineBundle_pow k X p P _ _ _ j hW)
  simpa only [mul_zero, mul_one, zero_add, add_zero] using h

private theorem lc_compare_zero_direction (P Q : Pair p) (W T : HermLB p) (c : ℕ) (e : ℤ)
    (hW : P.Rep 0 e W) (hWT : W.icls = -T.icls) (hQ : Q.L = P.L)
    (h : Le (Q.A.pow c).dual T) (D : ℕ) (hX : IsArithVar p D) (n j : ℕ) :
    P.lc n (j * e) 1 ≤ Q.lc n (c * j : ℕ) 1 := by
  have hcmp : Le (W.pow j) (Q.A.pow (c * j)) := by
    apply (h.dual_swap.pow_nat j).congr_classes
    · simp only [icls_pow, icls_dual, hWT]
    · simp only [icls_pow, icls_dual, neg_neg, ← mul_nsmul, mul_comm c j]
  have hle := LeCard.encard_smallSec_le k X p _ _ (hcmp.tens (P.L.pow n))
  have rhs := rep_twist Q (GlobalTheory.T.represents_base_bundles_and_trivial k X p Q).2.1 n (c * j)
  simp only [mul_one] at rhs
  rw [encard_block P (rep_twist P hW n j), ← hQ, encard_block Q rhs] at hle
  have hf := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX
  rw [← (hf P _ _ _).cast_ncard_eq, ← (hf Q _ _ _).cast_ncard_eq] at hle
  have hcard : (P.Bl n (j * e) 1).ncard ≤ (Q.Bl n (c * j : ℕ) 1).ncard := by exact_mod_cast hle
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl n (j * e) 1).ncard with h0 | hp
  · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hcard)

private theorem lc_dir_zero (hHS : GlobalTheory.Published.ArithHilbertSamuel)
    (hAC : GlobalTheory.Published.ArCalc) (hAm : AmpleHS)
    (D : ℕ) (hX : IsArithVar p D) (P : Pair p) (hL : P.L.IsNef D) (ha : P.L.IsSelfInter 0)
    (W T : HermLB p) (e : ℤ) (hW : P.Rep 0 e W) (hWT : W.icls = -T.icls)
    (j : ℕ → ℕ) (hj : Tendsto (fun n : ℕ => (j n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => P.lc n (j n * e) 1 / (n : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
  obtain ⟨Q, b, s, t, c, hQ, hG, -, hreg, hle⟩ :=
    GlobalTheory.T.exists_goodHermPair_adapted_twist hAC hAm k X p D hX P.L T
  obtain ⟨c₀, -, hc₀⟩ := GlobalTheory.T.exists_globalGeneration_ample_pair_multiples k X p D hX Q hG.ample
  have hg0 : GenAt Q 0 := by simpa using hc₀ 0
  have hfloor := GlobalTheory.T.smallSectionCount_log_twist_continuity_above k X p D hX Q b s t hG 0 hg0 hreg
  have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX
  apply normalized_tendsto_zero_of_floor_bound (fun n m : ℕ => Q.lc n m 1)
    (fun n : ℕ => P.lc n (j n * e) 1) j c (D + 1) (fun _ => Real.log_natCast_nonneg _)
  · intro n i hi
    exact (lc_compare_zero_direction P Q W T c e hW hWT hQ hle D hX n (j n)).trans
      (GlobalTheory.VolBr.lc_mono_twist_of_small Q hG.s_mem hG.s_ne n (by exact_mod_cast hi) (hfin Q _ _ _))
  · simpa only [Nat.cast_zero, sub_zero, neg_zero] using hfloor
  · have hnef : Q.L.IsNef D := by simpa only [hQ] using hL
    have hzero : Q.L.IsSelfInter 0 := by simpa only [hQ] using ha
    simpa only [zero_div, Nat.cast_zero] using (lc_fixed_twist_tendsto hHS hX Q hnef hzero 0).2
  · exact hj

/-- Zero leading intersection does not require nonzero sections for opposite twists. -/
private theorem tendsto_lc_signed_twist_of_zero (hHS : GlobalTheory.Published.ArithHilbertSamuel)
    (hAC : GlobalTheory.Published.ArCalc) (hAm : AmpleHS)
    (D : ℕ) (hX : IsArithVar p D) (P : Pair p) (hL : P.L.IsNef D) (ha : P.L.IsSelfInter 0)
    (z : ℕ → ℤ) (hz : Tendsto (fun n : ℕ => ((z n).natAbs : ℝ) / n) atTop (𝓝 0)) :
    (∀ n : ℕ, (P.Bl n (z n) 1).Finite) ∧
      Tendsto (fun n : ℕ => P.lc n (z n) 1 / (n : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
  refine ⟨fun n => GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P n (z n) 1, ?_⟩
  have hA := (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
  have hp := lc_dir_zero hHS hAC hAm D hX P hL ha P.A P.A.dual 1 hA
    (by simp only [icls_dual, neg_neg]) (fun n => (z n).natAbs) hz
  have hm := lc_dir_zero hHS hAC hAm D hX P hL ha P.A.dual P.A (-1)
    (by simpa only [neg_zero] using GlobalTheory.T.represents_hermitianLineBundle_dual k X p P _ _ _ hA)
    (by rfl) (fun n => (z n).natAbs) hz
  simp only [mul_one, mul_neg_one, Int.natCast_natAbs] at hp hm
  apply (hp.if' (p := fun n => 0 ≤ z n) hm).congr
  intro n
  split_ifs with h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h), neg_neg]

end GlobalTheory.HSNef

namespace GlobalTheory.VolBr
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/-- The ball form of Hilbert–Samuel along an arbitrary signed sublinear twist, including zero volume. -/
theorem lc_signed_twist (hHS : Published.ArithHilbertSamuel) (hAC : Published.ArCalc)
    (hAm : AmpleHS) {D : ℕ} (hX : IsArithVar p D) (P : Pair p)
    {a : ℝ} (hnef : P.L.IsNef D) (ha : P.L.IsSelfInter a)
    (z : ℕ → ℤ) (hz : Tendsto (fun n : ℕ => ((z n).natAbs : ℝ) / n) atTop (𝓝 0)) :
    (∀ᶠ n : ℕ in atTop, (P.Bl n (z n) 1).Finite) ∧
      (fun n : ℕ => P.lc n (z n) 1 - a / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have hnonneg : 0 ≤ a := ge_of_tendsto' (hHS.tendsto_of_triv hX hnef ha) (fun n =>
    mul_nonneg (Real.log_natCast_nonneg _) (by positivity))
  rcases hnonneg.eq_or_lt with rfl | hpos
  · obtain ⟨hfin, hlim⟩ := HSNef.tendsto_lc_signed_twist_of_zero hHS hAC hAm D hX P hnef ha z hz
    refine ⟨Eventually.of_forall hfin, ?_⟩
    simp only [zero_div, zero_mul, sub_zero]
    refine (isLittleO_iff_tendsto' ?_).mpr hlim
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact fun h => ((pow_pos hn' (D + 1)).ne' h).elim
  · exact lc_signed_twist_of_pos hHS hX P hnef ha hpos z hz

/-- Arithmetic Hilbert–Samuel with any signed sublinear power of any auxiliary Hermitian line bundle. -/
theorem _root_.GlobalTheory.Published.ArithHilbertSamuel.signed_twist
    (hHS : Published.ArithHilbertSamuel) (hAC : Published.ArCalc) (hAm : AmpleHS)
    {D : ℕ} (hX : IsArithVar p D) (L A : HermLB p) {a : ℝ}
    (hnef : L.IsNef D) (ha : L.IsSelfInter a)
    (z : ℕ → ℤ) (hz : Tendsto (fun n : ℕ => ((z n).natAbs : ℝ) / n) atTop (𝓝 0)) :
    let S := fun n : ℕ => ((L.pow n).tens (zp A (z n))).smallSec
    (∀ᶠ n : ℕ in atTop, (S n).Finite) ∧
      (fun n : ℕ => Real.log ((S n).ncard : ℝ) - a / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  obtain ⟨P, rfl, rfl⟩ := exists_pair L A
  exact signed_twist_of_ball_asymptotic P _ _ z (lc_signed_twist hHS hAC hAm hX P hnef ha z hz)

end GlobalTheory.VolBr

namespace GlobalTheory.VolBr

open GlobalTheory.Cartier GlobalTheory.CxPts

/-- On any integral projective scheme, choose a projective coordinate as rational
frame so that the constant function one is a regular section of the ample bundle. -/
private theorem exists_ample_pair_one {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (hp : IsProjOver p) :
    ∃ P : Pair p, IsAmpleLB P.A.B ∧ (1 : X.functionField) ∈ P.H 0 1 := by
  obtain ⟨n, j, hj, hjp⟩ := hp
  let A := (ProjSpace.hermitianTwistingSheaf k n).pull j hjp
  have ha : IsAmpleLB A.B := (isAmple_projective_O_one k n).pull_of_isClosedImmersion j
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    ((ProjSpace.iSup_nonzeroLocus_coord k n).ge (Opens.mem_top (j (genericPoint X))))
  let c : A.B.Sec := Cartier.secPull (ProjSpace.coord k n i) j
  have hc : genericPoint X ∈ Out.nonzeroLocus c := by
    show genericPoint X ∈ Out.nonzeroLocus (Cartier.secPull (ProjSpace.coord k n i) j)
    rw [Cartier.nonzeroLocus_secPull]
    exact hi
  let r := ratOfSec c hc
  refine ⟨⟨A, A, r, r, isRatSec_ratOfSec c hc, isRatSec_ratOfSec c hc⟩, ha, ?_⟩
  intro x _ l _ hl
  simpa only [Pair.loc, zpow_zero, one_mul, zpow_one, r, val_ratOfSec (gen_mem hl)] using
    regAt_fnOf hl (gen_mem hl) (c.f l)

end GlobalTheory.VolBr

namespace GlobalTheory.HSNef

/-- All members of a finite family and their duals are bounded by a single Hermitian line bundle. -/
theorem exists_common_dominator_of_finite
    (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) {ι : Type*} [Finite ι] (A : ι → HermLB p) :
    ∃ B : HermLB p, ∀ i, Le (A i) B ∧ Le (A i).dual B := by
  obtain ⟨P, hP, hs⟩ := VolBr.exists_ample_pair_one hX.isProjOver
  let N (j : ι × Bool) := if j.2 then (A j.1).dual else A j.1
  have hb (j : ι × Bool) :
      ∀ᶠ c : ℕ in atTop, ∀ᶠ u : ℝ in atTop, Le ((shiftA P u).A.pow c).dual (N j) := by
    obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.exists_small_section_add_multiple_ample_after_shift
      k X p D hX P (N j) 1 hP hs one_ne_zero
    filter_upwards [eventually_ge_atTop c₀, eventually_gt_atTop 0] with c hc hpos
    exact eventually_atTop.mpr (hc₀ c hc hpos)
  obtain ⟨c, hc⟩ := (eventually_all.mpr hb).exists
  obtain ⟨u, hu⟩ := (eventually_all.mpr hc).exists
  refine ⟨((shiftA P u).A.pow c).dual.dual, fun i => ⟨?_, (hu (i, false)).dual_swap⟩⟩
  have hd : Le (A i) (A i).dual.dual :=
    le_of_isometric (icls_eq_iff.mp (by simp only [icls_dual, neg_neg]))
  exact hd.trans (hu (i, true)).dual_swap


variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
variable {A B : HermLB p}

private theorem zp_le_pow (h : Le A B) (g : Le A.dual B) (z : ℤ) :
    Le (zp A z) (B.pow z.natAbs) := by
  cases z with
  | ofNat n =>
    exact (h.pow_nat n).congr_classes (by simp [icls_zp, icls_pow]) rfl
  | negSucc n =>
    apply (g.pow_nat (n+1)).congr_classes _ rfl
    simp only [icls_pow, icls_dual, icls_zp]
    rw [show Int.negSucc n = -((n+1 : ℕ) : ℤ) by omega, neg_smul, natCast_zsmul, smul_neg]

private theorem comb_le_symmetric_bound {ι : Type} [Fintype ι] (A : ι → HermLB p)
    (B : HermLB p) (dom : ∀ i, Le (A i) B ∧ Le (A i).dual B) (z : ι → ℤ) :
    Le (comb A z) (B.pow (∑ i, (z i).natAbs)) := by
  classical
  have aux (l : List ι) :
      Le (l.foldr (fun i M => (zp (A i) (z i)).tens M) (HermLB.triv p))
        (B.pow ((l.map fun i => (z i).natAbs).sum)) := by
    induction l with
    | nil => exact le_of_isometric (icls_eq_iff.mp (by simp only [List.foldr_nil,
          List.map_nil, List.sum_nil, icls_pow, zero_nsmul]; rfl))
    | cons i l ih =>
      apply ((zp_le_pow (dom i).1 (dom i).2 (z i)).tens_pair ih).congr_classes rfl
      simp only [List.map_cons, List.sum_cons, icls_tens, icls_pow, add_nsmul]
  rw [← Finset.sum_map_toList]
  exact aux Finset.univ.toList

private theorem symmetric_bound_le_comb {ι : Type} [Fintype ι] (A : ι → HermLB p)
    (B : HermLB p) (dom : ∀ i, Le (A i) B ∧ Le (A i).dual B) (z : ι → ℤ) :
    Le (B.pow (∑ i, (z i).natAbs)).dual (comb A z) := by
  have h := (comb_le_symmetric_bound A B dom fun i => -(z i)).dual_swap
  apply h.congr_classes (by simp only [Int.natAbs_neg]) ?_
  simp only [icls_dual, icls_comb, neg_smul, Finset.sum_neg_distrib, neg_neg]

private theorem card_log_le {M N : HermLB p} (h : Le M N) (hN : N.smallSec.Finite) :
    M.smallSec.Finite ∧ Real.log (M.smallSec.ncard : ℝ) ≤ Real.log (N.smallSec.ncard : ℝ) := by
  have hc := LeCard.encard_smallSec_le k X p N M h
  have hf := Set.encard_lt_top_iff.mp (hc.trans_lt hN.encard_lt_top)
  rw [← hf.cast_ncard_eq, ← hN.cast_ncard_eq] at hc
  have hcard : M.smallSec.ncard ≤ N.smallSec.ncard := by exact_mod_cast hc
  refine ⟨hf, ?_⟩
  rcases Nat.eq_zero_or_pos M.smallSec.ncard with h0 | hp
  · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hcard)

private theorem finite_twists_of_squeeze {ι : Type} [Fintype ι]
    {D : ℕ} (hX : IsArithVar p D) (L : HermLB p) (A : ι → HermLB p) {a : ℝ}
    (signed : ∀ (B : HermLB p) (b : ℕ → ℤ),
      Tendsto (fun n : ℕ => ((b n).natAbs : ℝ) / n) atTop (𝓝 0) →
      let S := fun n : ℕ => ((L.pow n).tens (zp B (b n))).smallSec
      (∀ᶠ n : ℕ in atTop, (S n).Finite) ∧
        (fun n : ℕ => Real.log ((S n).ncard : ℝ) - a / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1))
          =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (z : ℕ → ι → ℤ)
    (hz : ∀ i, Tendsto (fun n : ℕ => ((z n i).natAbs : ℝ) / n) atTop (𝓝 0)) :
    let S := fun n : ℕ => ((L.pow n).tens (comb A (z n))).smallSec
    (∀ᶠ n : ℕ in atTop, (S n).Finite) ∧
      (fun n : ℕ => Real.log ((S n).ncard : ℝ) - a / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  classical
  obtain ⟨B, dom⟩ := exists_common_dominator_of_finite k X p D hX A
  let m (n : ℕ) := ∑ i, (z n i).natAbs
  have h0 : Tendsto (fun n : ℕ => (m n : ℝ) / n) atTop (𝓝 0) := by
    simpa [m, Nat.cast_sum, Finset.sum_div] using (tendsto_finsetSum Finset.univ fun i _ => hz i)
  have up := signed B (fun n => (m n : ℤ)) (by simpa using h0)
  have lo := signed B (fun n => -(m n : ℤ)) (by simpa using h0)
  have hup (n : ℕ) : Le ((L.pow n).tens (comb A (z n))) ((L.pow n).tens (zp B (m n))) :=
    ((comb_le_symmetric_bound A B dom (z n)).tens (L.pow n)).congr_classes rfl
      (by simp only [icls_tens, icls_pow, icls_zp, natCast_zsmul]; rfl)
  have hlo (n : ℕ) : Le ((L.pow n).tens (zp B (-(m n : ℤ)))) ((L.pow n).tens (comb A (z n))) :=
    ((symmetric_bound_le_comb A B dom (z n)).tens (L.pow n)).congr_classes
      (by simp only [icls_tens, icls_pow, icls_dual, icls_zp, neg_smul, natCast_zsmul]; rfl) rfl
  have e := up.1.mono fun n hn => card_log_le (hup n) hn
  refine ⟨e.mono fun _ h => h.1, (isLittleO_iff_tendsto' ?_).mpr ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have h : (0 : ℝ) < n := by exact_mod_cast hn
    exact fun h0 => ((pow_pos h (D+1)).ne' h0).elim
  apply (lo.2.tendsto_div_nhds_zero).squeeze' (up.2.tendsto_div_nhds_zero)
  · filter_upwards [e] with n hn
    exact div_le_div_of_nonneg_right (sub_le_sub_right (card_log_le (hlo n) hn.1).2 _) (by positivity)
  · filter_upwards [e] with n hn
    exact div_le_div_of_nonneg_right (sub_le_sub_right hn.2 _) (by positivity)

/-- Positive self-intersection only needs the fixed-twist Hilbert–Samuel theorem. -/
theorem _root_.GlobalTheory.Published.ArithHilbertSamuel.finite_twists_of_pos {ι : Type} [Fintype ι]
    (hHS : Published.ArithHilbertSamuel)
    {D : ℕ} (hX : IsArithVar p D) (L : HermLB p) (A : ι → HermLB p) {a : ℝ}
    (hnef : L.IsNef D) (ha : L.IsSelfInter a) (hpos : 0 < a) (z : ℕ → ι → ℤ)
    (hz : ∀ i, Tendsto (fun n : ℕ => ((z n i).natAbs : ℝ) / n) atTop (𝓝 0)) :
    let S := fun n : ℕ => ((L.pow n).tens (comb A (z n))).smallSec
    (∀ᶠ n : ℕ in atTop, (S n).Finite) ∧
      (fun n : ℕ => Real.log ((S n).ncard : ℝ) - a / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
  finite_twists_of_squeeze hX L A (fun B => hHS.signed_twist_of_pos hX L B hnef ha hpos) z hz

/-- Simultaneous sublinear powers in any fixed finite family preserve the Hilbert–Samuel term. -/
theorem _root_.GlobalTheory.Published.ArithHilbertSamuel.finite_twists {ι : Type} [Fintype ι]
    (hHS : Published.ArithHilbertSamuel) (hAC : Published.ArCalc) (hAm : AmpleHS)
    {D : ℕ} (hX : IsArithVar p D) (L : HermLB p) (A : ι → HermLB p) {a : ℝ}
    (hnef : L.IsNef D) (ha : L.IsSelfInter a) (z : ℕ → ι → ℤ)
    (hz : ∀ i, Tendsto (fun n : ℕ => ((z n i).natAbs : ℝ) / n) atTop (𝓝 0)) :
    let S := fun n : ℕ => ((L.pow n).tens (comb A (z n))).smallSec
    (∀ᶠ n : ℕ in atTop, (S n).Finite) ∧
      (fun n : ℕ => Real.log ((S n).ncard : ℝ) - a / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
  finite_twists_of_squeeze hX L A (fun B => hHS.signed_twist hAC hAm hX L B hnef ha) z hz

end GlobalTheory.HSNef
