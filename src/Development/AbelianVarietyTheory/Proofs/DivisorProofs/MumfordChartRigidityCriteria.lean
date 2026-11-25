module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartTransverseJets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRigiditySndEqZeroCanonicalChart

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.Toroidal MvPowerSeries TrivSqZeroExt

namespace GlobalTheory.RigChart

/-- A collision of two marked Mumford sections persists in every constant deformation. -/
theorem IsConstAlong.sections_eq_iff {R k : Type} [CommRing R] [IsDomain R] [Field k]
    {Q : DegPre R} {m : ℕ} {t : Fin m → R} {gam : Fin m → LinearMap.BilinForm ℤ Q.X}
    {ρ : R →+* DualNumber k} {a : Fin m → k} (h : IsConstAlong Q t gam ρ a)
    (y z : Q.X) :
    spMap ρ ≫ (Q.c y).left = spMap ρ ≫ (Q.c z).left ↔
      spMap (constHom ρ) ≫ (Q.c y).left = spMap (constHom ρ) ≫ (Q.c z).left := by
  obtain ⟨B, _, π₁, π₂, _, c, hp₁, hp₂, _, _, hc, _⟩ := h
  constructor
  · intro he
    have hcz : c y = c z := hp₁.1.hom_ext ((hc y).2.1.trans (he.trans (hc z).2.1.symm))
      ((hc y).1.trans (hc z).1.symm)
    rw [← (hc y).2.2, ← (hc z).2.2, hcz]
  · intro he
    have hcz : c y = c z := hp₂.1.hom_ext ((hc y).2.2.trans (he.trans (hc z).2.2.symm))
      ((hc y).1.trans (hc z).1.symm)
    rw [← (hc y).2.1, ← (hc z).2.1, hcz]

private theorem affineSections_eq_iff {S R T : Type} [CommRing S] [CommRing R] [CommRing T]
    {X : Scheme.{0}} (u : Sp S ⟶ X) [Mono u] (f g : S →+* R) (ρ : R →+* T) :
    spMap ρ ≫ spMap f ≫ u = spMap ρ ≫ spMap g ≫ u ↔ ρ.comp f = ρ.comp g := by
  simp only [← Category.assoc, cancel_mono, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact ⟨fun h => congrArg (fun q => q.hom) (Spec.map_injective h), fun h => by rw [h]⟩

/-- Closed-point agreement of the two marked sections in a common affine patch
forces agreement of their infinitesimal affine readings for every constant jet. -/
theorem IsConstAlong.transverse_coordinate_eq {K k S : Type} [Field K] [Field k] [CommRing S]
    {m d : ℕ} (Q : DegPre (ChartRing K m d)) {gam : Fin m → LinearMap.BilinForm ℤ Q.X}
    {e : K →+* k} {b : Fin d → k} {a : Fin m → k}
    (h : IsConstAlong Q (bdParam K m d) gam (transverseJet e b) a)
    {u : Sp S ⟶ Q.P.A.left} [Mono u] {y z : Q.X} {f g : S →+* ChartRing K m d}
    (hf : spMap f ≫ u = (Q.c y).left) (hg : spMap g ≫ u = (Q.c z).left)
    (h₀ : spMap (constantCoeff (R := K) (σ := Fin m ⊕ Fin d)) ≫ (Q.c y).left =
      spMap constantCoeff ≫ (Q.c z).left) :
    (transverseJet e b).comp f = (transverseJet e b).comp g := by
  apply (affineSections_eq_iff u f g _).mp
  rw [hf, hg, h.sections_eq_iff, ← hf, ← hg, affineSections_eq_iff]
  apply RingHom.ext
  intro s
  rw [← hf, ← hg, affineSections_eq_iff] at h₀
  have hbase : constantCoeff (f s) = constantCoeff (g s) := DFunLike.congr_fun h₀ s
  change (TrivSqZeroExt.inl (e (constantCoeff (f s))) : DualNumber k) =
    TrivSqZeroExt.inl (e (constantCoeff (g s)))
  rw [hbase]

/-- A finite transverse Jacobian test using the marked sections of the Mumford data.
Each pair specializes to the same point in its own affine patch. If the
differences of their coordinate readings give an invertible transverse Jacobian
at the closed point, then the full chart is rigid, independently of its periods. -/
theorem isRigid_of_section_jacobian {K : Type} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    {m d : ℕ} (Q : DegPre (ChartRing K m d))
    (gam : Fin m → LinearMap.BilinForm ℤ Q.X)
    {S : Fin d → Type} [∀ i, CommRing (S i)] (u : ∀ i, Sp (S i) ⟶ Q.P.A.left) [∀ i, Mono (u i)]
    (y z : Fin d → Q.X) (f g : ∀ i, S i →+* ChartRing K m d) (v : ∀ i, S i)
    (hf : ∀ i, spMap (f i) ≫ u i = (Q.c (y i)).left)
    (hg : ∀ i, spMap (g i) ≫ u i = (Q.c (z i)).left)
    (h₀ : ∀ i, spMap (constantCoeff (R := K) (σ := Fin m ⊕ Fin d)) ≫ (Q.c (y i)).left =
      spMap constantCoeff ≫ (Q.c (z i)).left)
    (hJ : IsUnit (Matrix.of (fun i j : Fin d =>
      constantCoeff (pderiv (Sum.inr j) (f i (v i) - g i (v i)))))) :
    IsRigid Q (bdParam K m d) gam := by
  rw [isRigid_iff_transverse_jets]
  intro k _ e b a hc
  let J : Matrix (Fin d) (Fin d) K := fun i j =>
    constantCoeff (pderiv (Sum.inr j) (f i (v i) - g i (v i)))
  have hu : IsUnit (J.map e) := hJ.map (e.mapMatrix : _ →+* Matrix (Fin d) (Fin d) k)
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  rw [Matrix.mulVec_zero]
  funext i
  have eqv := DFunLike.congr_fun (hc.transverse_coordinate_eq Q (hf i) (hg i) (h₀ i)) (v i)
  have hz : transverseJet (m := m) e b (f i (v i) - g i (v i)) = 0 :=
    (map_sub _ _ _).trans (sub_eq_zero.mpr eqv)
  have hz' := congrArg TrivSqZeroExt.snd hz
  change (∑ j, Sum.elim (fun _ : Fin m => (0 : k)) b j *
    e (constantCoeff (pderiv j (f i (v i) - g i (v i))))) = 0 at hz'
  change (∑ j, e (J i j) * b j) = 0
  simpa [Fintype.sum_sum_type, J, mul_comm] using hz'

/-- With one transverse parameter, one genuine splitting section through another
to first order suffices. A unit multiple of the parameter is enough. -/
theorem isRigid_of_simple_section_collision {K S : Type} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] [CommRing S] {m : ℕ} (Q : DegPre (ChartRing K m 1))
    (gam : Fin m → LinearMap.BilinForm ℤ Q.X) (u : Sp S ⟶ Q.P.A.left) [Mono u]
    (y z : Q.X) (f g : S →+* ChartRing K m 1)
    (hf : spMap f ≫ u = (Q.c y).left) (hg : spMap g ≫ u = (Q.c z).left)
    (h₀ : spMap (constantCoeff (R := K) (σ := Fin m ⊕ Fin 1)) ≫ (Q.c y).left =
      spMap constantCoeff ≫ (Q.c z).left)
    (v : S) (w : (ChartRing K m 1)ˣ)
    (hw : f v - g v = (w : ChartRing K m 1) * X (.inr 0)) :
    IsRigid Q (bdParam K m 1) gam := by
  apply isRigid_of_section_jacobian Q gam (S := fun _ => S) (fun _ => u) (fun _ => y) (fun _ => z)
    (fun _ => f) (fun _ => g) (fun _ => v) (fun _ => hf) (fun _ => hg) (fun _ => h₀)
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one]
  simpa [hw] using (w.isUnit.map (constantCoeff (R := K) (σ := Fin m ⊕ Fin 1)))

open GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.ToricData
open scoped Matrix

/-- A single calibrated period measures the transverse logarithmic derivative
against its boundary exponents, for an arbitrary extension of coefficient fields. -/
theorem transverseJet_period_dlog {K k : Type} [Field K] [Field k] {m d : ℕ}
    {Q : DegPre (ChartRing K m d)} {gam : Fin m → LinearMap.BilinForm ℤ Q.X}
    {τ : Gens Q} (hbase : FromBase Q τ (C : K →+* ChartRing K m d))
    (e : K →+* k) (b : Fin d → k) (a : Fin m → k)
    (hc : IsConstAlong Q (bdParam K m d) gam (transverseJet e b) a)
    (y z : Q.X) (v : (ChartRing K m d)ˣ)
    (hv : IsUnitTau Q (bdParam K m d) gam y z (UU.scaleGen (unitOn v) (τ y z))) :
    ∑ j, b j * e (constantCoeff (pderiv (Sum.inr j) (v : ChartRing K m d)) /
      constantCoeff (v : ChartRing K m d)) = ∑ i, a i * (gam i y z : k) := by
  have hh : (transverseJet (m := m) e b).comp C = constHom ((transverseJet (m := m) e b).comp C) := by
    ext x <;> simp [transverseJet, constHom, TrivSqZeroExt.algebraMap_eq_inl]
  have hu := map_period_unit_of_constAlong hbase hh hc y z v hv
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

/-- The smooth logarithmic derivatives and the negated boundary exponents of a calibrated period. -/
noncomputable def augmentedPeriodRow {K : Type} [Field K] {m d : ℕ}
    (v : (ChartRing K m d)ˣ) (exponents : Fin m → ℤ) : Fin d ⊕ Fin m → K :=
  Sum.elim (fun j => constantCoeff (pderiv (.inr j) (v : ChartRing K m d)) /
    constantCoeff (v : ChartRing K m d)) (fun i => -(exponents i : K))

/-- A nonsingular finite matrix of genuine calibrated periods detects every transverse tangent,
even when none of the periods is individually constant along the boundary directions. -/
theorem isRigid_of_augmented_period_det {K : Type} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    {m d : ℕ} {Q : DegPre (ChartRing K m d)} {gam : Fin m → LinearMap.BilinForm ℤ Q.X}
    {τ : Gens Q} (hbase : FromBase Q τ (C : K →+* ChartRing K m d))
    (y z : Fin d ⊕ Fin m → Q.X) (u : Fin d ⊕ Fin m → (ChartRing K m d)ˣ)
    (hu : ∀ r, IsUnitTau Q (bdParam K m d) gam (y r) (z r)
      (UU.scaleGen (unitOn (u r)) (τ (y r) (z r))))
    (hdet : (Matrix.of fun r => augmentedPeriodRow (u r) (fun i => gam i (y r) (z r))).det ≠ 0) :
    IsRigid Q (bdParam K m d) gam := by
  apply (isRigid_iff_transverse_jets Q gam).mpr
  intro k _ e b a hc
  let M := Matrix.of fun r => augmentedPeriodRow (u r) (fun i => gam i (y r) (z r))
  have hM : (M.map e).det ≠ 0 := by
    change (e.mapMatrix M).det ≠ 0
    rw [← e.map_det]
    exact (map_ne_zero_iff e e.injective).mpr hdet
  have hz : (M.map e) *ᵥ Sum.elim b a = 0 := by
    funext r
    have h := transverseJet_period_dlog hbase e b a hc (y r) (z r) (u r) (hu r)
    simp [Matrix.mulVec, dotProduct, M, augmentedPeriodRow, Fintype.sum_sum_type,
      Finset.sum_neg_distrib, mul_comm, ← h]
  by_contra hb
  apply hM (Matrix.exists_mulVec_eq_zero_iff.mp ⟨Sum.elim b a, ?_, hz⟩)
  exact fun he => hb (funext fun j => congrFun he (.inl j))

end GlobalTheory.RigChart
