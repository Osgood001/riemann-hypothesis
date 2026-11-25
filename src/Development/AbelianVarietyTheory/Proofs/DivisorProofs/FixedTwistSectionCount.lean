module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

/-- A fixed integral twist does not change the leading asymptotic of log section counts. -/
theorem lc_fixed_twist_tendsto (hHS : Published.ArithHilbertSamuel)
    {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) (P : Pair p) {a : ℝ} (hnef : P.L.IsNef D) (ha : P.L.IsSelfInter a)
    (b : ℤ) :
    (∀ᶠ n : ℕ in atTop, (P.Bl n b 1).Finite) ∧
    Tendsto (fun n : ℕ => P.lc n b 1 / (n : ℝ) ^ (D + 1)) atTop (𝓝 (a / (D + 1).factorial)) := by
  obtain ⟨N, hN⟩ := Pair.exists_rep k X p P 0 b
  have hL := (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  have hencard (n : ℕ) : ((P.L.pow n).tens N).smallSec.encard = (P.Bl n b 1).encard := by
    have hpow := GlobalTheory.VolBr.Pair.rep_pow k X p P 1 0 P.L n hL
    have ht := GlobalTheory.VolBr.Pair.rep_tens k X p P _ _ _ _ _ _ hpow hN
    have hrep : P.Rep n b ((P.L.pow n).tens N) := by simpa using ht
    exact SmallBall.encard_eq_Bl P hrep _ 1 zero_le_one (fun _ => by simp only [HermLB.smallSec, Set.mem_ofPred_eq, one_pow])
  have hcard (n : ℕ) : ((P.L.pow n).tens N).smallSec.ncard = (P.Bl n b 1).ncard := congrArg ENat.toNat (hencard n)
  constructor
  · filter_upwards [(hHS k X p D hX P.L N a hnef ha).1] with n hn
    exact Set.encard_lt_top_iff.mp (by rw [← hencard]; exact hn.encard_lt_top)
  have hlim := (hHS k X p D hX P.L N a hnef ha).2.tendsto_div_nhds_zero
  have hc : Tendsto (fun _ : ℕ => a / (D + 1).factorial) atTop (𝓝 (a / (D + 1).factorial)) := tendsto_const_nhds
  have h := hlim.add hc
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change (Real.log (((P.L.pow n).tens N).smallSec.ncard : ℝ) - _ * _) / _ + _ = _
  rw [hcard, Pair.lc]
  have hpow : (n : ℝ) ^ (D + 1) ≠ 0 := by positivity
  field_simp; ring

end GlobalTheory.VolBr
