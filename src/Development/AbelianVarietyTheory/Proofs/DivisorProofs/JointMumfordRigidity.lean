module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordChartRigidityCriteria

@[expose] public section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.ToricData
open MvPowerSeries TrivSqZeroExt
open scoped Matrix

namespace GlobalTheory.RigChart

/-- A calibrated period reads the relation between transverse and boundary directions
whenever the jet is already constant on its ring of definition. -/
theorem transverseJet_period_dlog_of_base_const {W K k : Type} [CommRing W] [Field K] [Field k]
    {m d : ℕ}
    {Q : DegPre (ChartRing K m d)} {gam : Fin m → LinearMap.BilinForm ℤ Q.X}
    {τ : Gens Q} {iBase : W →+* ChartRing K m d} (hbase : FromBase Q τ iBase)
    (e : K →+* k) (b : Fin d → k) (a : Fin m → k)
    (hρ : (transverseJet e b).comp iBase = constHom ((transverseJet e b).comp iBase))
    (hc : IsConstAlong Q (bdParam K m d) gam (transverseJet e b) a)
    (y z : Q.X) (v : (ChartRing K m d)ˣ)
    (hv : IsUnitTau Q (bdParam K m d) gam y z (UU.scaleGen (unitOn v) (τ y z))) :
    ∑ j, b j * e (constantCoeff (pderiv (Sum.inr j) (v : ChartRing K m d)) /
      constantCoeff (v : ChartRing K m d)) = ∑ i, a i * (gam i y z : k) := by
  have hu := map_period_unit_of_constAlong hbase hρ hc y z v hv
  have h := congrArg (fun x => Multiplicative.toAdd (TautRigid.dlog k x)) hu
  rw [map_mul, toAdd_mul, TautRigid.dlog_onePlus] at h
  have h₀ : Multiplicative.toAdd (TautRigid.dlog k
      (Units.map (constHom (transverseJet (m := m) e b)).toMonoidHom v)) = 0 := by
    rw [TautRigid.dlog_apply]
    change 0 / _ = 0
    exact zero_div _
  rw [h₀, add_zero, TautRigid.dlog_apply] at h
  change (∑ i : Fin m ⊕ Fin d, Sum.elim (fun _ => 0) b i * e (constantCoeff (pderiv i (v : ChartRing K m d)))) /
    e (constantCoeff (v : ChartRing K m d)) = _ at h
  rw [Fintype.sum_sum_type] at h
  simpa [map_div, ← mul_div_assoc, Finset.sum_div] using h

/-- The derivative of a coordinate difference between marked sections that meet
on the closed fibre vanishes along a constant deformation. -/
theorem IsConstAlong.section_difference_derivative_eq_zero {K k S : Type}
    [Field K] [Field k] [CommRing S] {m d : ℕ}
    {Q : DegPre (ChartRing K m d)} {gam : Fin m → LinearMap.BilinForm ℤ Q.X}
    {e : K →+* k} {b : Fin d → k} {a : Fin m → k}
    (h : IsConstAlong Q (bdParam K m d) gam (transverseJet e b) a)
    {u : Sp S ⟶ Q.P.A.left} [Mono u] {y z : Q.X} {f g : S →+* ChartRing K m d}
    (hf : spMap f ≫ u = (Q.c y).left) (hg : spMap g ≫ u = (Q.c z).left)
    (h₀ : spMap (constantCoeff (R := K) (σ := Fin m ⊕ Fin d)) ≫ (Q.c y).left =
      spMap constantCoeff ≫ (Q.c z).left) (v : S) :
    ∑ j, e (constantCoeff (pderiv (Sum.inr j) (f v - g v))) * b j = 0 := by
  have he := DFunLike.congr_fun (h.transverse_coordinate_eq Q hf hg h₀) v
  have hz : transverseJet (m := m) e b (f v - g v) = 0 :=
    (map_sub _ _ _).trans (sub_eq_zero.mpr he)
  have hd := congrArg TrivSqZeroExt.snd hz
  change (∑ j, Sum.elim (fun _ : Fin m => (0 : k)) b j *
    e (constantCoeff (pderiv j (f v - g v)))) = 0 at hd
  simpa [Fintype.sum_sum_type, mul_comm] using hd

/-- The joint matrix has one row per colliding pair and one per calibrated period.
Only the transverse coordinates need to be recovered; the boundary coordinates
are nuisance variables and may have undetected directions. -/
noncomputable def jointMumfordMatrix {K : Type} [Field K] {s p : Type}
    {m d : ℕ} (J : Matrix s (Fin d) K) (u : p → (ChartRing K m d)ˣ)
    (g : p → Fin m → ℤ) : Matrix (s ⊕ p) (Fin d ⊕ Fin m) K :=
  fun r j => r.elim (fun i => j.elim (J i) (fun _ => 0))
    (fun i => augmentedPeriodRow (u i) (g i) j)

/-- The marked sections first freeze the period's ring of definition. If the
combined observations then recover the transverse coordinates, the pre-datum
is rigid. This permits different probes to detect different transverse directions. -/
theorem isRigid_of_joint_mumford_recovery {W K s p : Type} [CommRing W] [Field K]
    [CharZero K] [Algebra.IsAlgebraic ℚ K] [Fintype s] [Fintype p] {m d : ℕ}
    {Q : DegPre (ChartRing K m d)} {gam : Fin m → LinearMap.BilinForm ℤ Q.X}
    {τ : Gens Q} {iBase : W →+* ChartRing K m d} (hbase : FromBase Q τ iBase)
    {S : s → Type} [∀ i, CommRing (S i)] (patch : ∀ i, Sp (S i) ⟶ Q.P.A.left)
    [∀ i, Mono (patch i)] (y z : s → Q.X) (f g : ∀ i, S i →+* ChartRing K m d) (v : ∀ i, S i)
    (hf : ∀ i, spMap (f i) ≫ patch i = (Q.c (y i)).left)
    (hg : ∀ i, spMap (g i) ≫ patch i = (Q.c (z i)).left)
    (h₀ : ∀ i, spMap (constantCoeff (R := K) (σ := Fin m ⊕ Fin d)) ≫ (Q.c (y i)).left =
      spMap constantCoeff ≫ (Q.c (z i)).left)
    (hfreeze : ∀ (k : Type) [Field k] (e : K →+* k) (b : Fin d → k),
      (∀ i, ∑ j, e (constantCoeff (pderiv (Sum.inr j) (f i (v i) - g i (v i)))) * b j = 0) →
      (transverseJet e b).comp iBase = constHom ((transverseJet e b).comp iBase))
    (y' z' : p → Q.X) (u : p → (ChartRing K m d)ˣ)
    (hu : ∀ r, IsUnitTau Q (bdParam K m d) gam (y' r) (z' r)
      (UU.scaleGen (unitOn (u r)) (τ (y' r) (z' r))))
    (B : Matrix (Fin d) (s ⊕ p) K)
    (hB : B * jointMumfordMatrix
      (fun i j => constantCoeff (pderiv (Sum.inr j) (f i (v i) - g i (v i))))
      u (fun r i => gam i (y' r) (z' r)) = fun i j => j.elim (fun j => if i = j then 1 else 0) (fun _ => 0)) :
    IsRigid Q (bdParam K m d) gam := by
  classical
  apply (isRigid_iff_transverse_jets Q gam).mpr
  intro k _ e b a hc
  let M := jointMumfordMatrix
      (fun i j => constantCoeff (pderiv (Sum.inr j) (f i (v i) - g i (v i))))
      u (fun r i => gam i (y' r) (z' r))
  have hmark i := hc.section_difference_derivative_eq_zero (hf i) (hg i) (h₀ i) (v i)
  have hfixed := hfreeze k e b hmark
  have hz : (M.map e) *ᵥ Sum.elim b a = 0 := by
    funext r
    cases r with
    | inl i =>
      simpa [Matrix.mulVec, dotProduct, M, jointMumfordMatrix, Fintype.sum_sum_type] using hmark i
    | inr i =>
      have h := transverseJet_period_dlog_of_base_const hbase e b a hfixed hc
        (y' i) (z' i) (u i) (hu i)
      simp [Matrix.mulVec, dotProduct, M, jointMumfordMatrix, augmentedPeriodRow,
        Fintype.sum_sum_type, Finset.sum_neg_distrib, mul_comm, ← h]
  have hh := Matrix.mulVec_mulVec (Sum.elim b a) (B.map e) (M.map e)
  rw [hz, Matrix.mulVec_zero, ← Matrix.map_mul, hB] at hh
  funext i
  have hi := congrFun hh.symm i
  change (∑ j : Fin d ⊕ Fin m, e (j.elim (fun t => if i = t then 1 else 0) (fun _ => 0)) *
    Sum.elim b a j) = 0 at hi
  simpa [Fintype.sum_sum_type, apply_ite e, ite_mul, eq_comm] using hi

end GlobalTheory.RigChart

