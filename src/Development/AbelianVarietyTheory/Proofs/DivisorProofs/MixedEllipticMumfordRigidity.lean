module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordChartRigidityCriteria
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasTrivialKernelIff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsUnimodularSolZeroNeg

@[expose] public section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.Toroidal GlobalTheory.WeierstrassCurve MvPowerSeries

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigChart.MixedElliptic

noncomputable section

private abbrev R := ChartRing ℚ 1 1
private abbrev Y : R := X (Sum.inr 0)
private def W : WeierstrassCurve R := ⟨Y^3, 0, 0, -1, 0⟩

private theorem disc : IsUnit W.Δ := by
  rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  norm_num [W, WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈,Y]
  change (constantCoeff : R →+* ℚ) ((64 : ℕ) : R) ≠ 0
  rw [map_natCast]
  norm_num

private theorem point_eqn : (W.map (RingHom.id R)).toProjective.Equation ![Y,-1,Y^3] := by
  rw [equation_origin_iff]
  change Y^3 = Y^3 + (Y^3) * Y * Y^3 + 0 * Y^2 * Y^3 + 0 * (Y^3)^2 +
    (-1) * Y * (Y^3)^2 + 0 * (Y^3)^3
  ring

private def moving : OriginRing W →+* R := originEval W (RingHom.id R) Y (Y^3) point_eqn
private abbrev fixed : OriginRing W →+* R := (originAug W).toRingHom

/-- An actual polarized elliptic scheme on the mixed chart, with a section through
the identity whose first coordinate is precisely the transverse parameter. -/
private theorem actual_marks :
    ∃ (P : PolAV (Sp R)) (s : 𝟙_ (Over (Sp R)) ⟶ P.A) (u : Sp (OriginRing W) ⟶ P.A.left),
      P.g = 1 ∧ Mono u ∧ spMap moving ≫ u = s.left ∧ spMap fixed ≫ u = eSec P.A ∧
      spMap (constantCoeff (R := ℚ) (σ := Fin 1 ⊕ Fin 1)) ≫ s.left =
        spMap constantCoeff ≫ eSec P.A ∧
      moving (originZ W) - fixed (originZ W) = Y := by
  obtain ⟨P, ψ, _, hg, hψ, hstr, he, _⟩ := exists_polAV R W disc
  let u := chartY W ≫ inv ψ
  have hu : u ≫ P.A.hom = spMap (algebraMap R (OriginRing W)) := by
    dsimp only [u]
    rw [← hstr, Category.assoc, IsIso.inv_hom_id_assoc, chartY_toSpec]
  have hs : (spMap moving ≫ u) ≫ P.A.hom = 𝟙 (Sp R) := by
    rw [Category.assoc, hu]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact originEval_algebraMap W (RingHom.id R) Y (Y^3) point_eqn
  let s : 𝟙_ (Over (Sp R)) ⟶ P.A := Over.homMk (spMap moving ≫ u) hs
  have hfixed : spMap fixed ≫ u = eSec P.A := by
    apply (cancel_mono ψ).mp
    dsimp only [u]
    rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id, he]
    exact SpecMap_originAug_chartY W
  have hc : constantCoeff.comp moving = constantCoeff.comp fixed := by
    apply origin_hom_ext W
    · intro r
      simp [moving, fixed]
    · simp [moving, fixed, Y]
    · simp [moving, fixed, Y]
  refine ⟨P, s, u, hg, inferInstanceAs (Mono (chartY W ≫ inv ψ)), rfl, hfixed, ?_, ?_⟩
  · rw [← hfixed]
    change spMap constantCoeff ≫ spMap moving ≫ u = spMap constantCoeff ≫ spMap fixed ≫ u
    simp only [← Category.assoc, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  · simp [moving, fixed]

/-- On the mixed chart over ℚ the elliptic family
  y² + Y³xy = x³ − x
has a marked section [Y : −1 : Y³]. It collides with the identity on the closed
fibre but separates from it at Y = ε. Thus its actual Mumford pre-datum is rigid
for every boundary form, without any period calibrations. -/
theorem exists_rigid_mixed_elliptic :
    ∃ (Q : DegPre (ChartRing ℚ 1 1)) (y : Q.X), Q.P.g = 1 ∧
      spMap (constantCoeff (R := ℚ) (σ := Fin 1 ⊕ Fin 1)) ≫ (Q.c y).left =
        spMap constantCoeff ≫ (Q.c 0).left ∧
      spMap (transverseJet (m := 1) (RingHom.id ℚ) (fun _ : Fin 1 => 1)) ≫ (Q.c y).left ≠
        spMap (transverseJet (m := 1) (RingHom.id ℚ) (fun _ : Fin 1 => 1)) ≫ (Q.c 0).left ∧
      ∀ gam : Fin 1 → LinearMap.BilinForm ℤ Q.X, IsRigid Q (bdParam ℚ 1 1) gam := by
  obtain ⟨P, s, u, hg, hu, hs, he, hc, hz⟩ := actual_marks
  obtain ⟨Q, y, rfl, hy⟩ := GlobalTheory.TwistCompare.exists_degPre P s
  change Q.c y = s at hy
  have hc0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have h0 : Q.c 0 = MonObj.one := hc0.trans (Category.id_comp _)
  have : Mono u := hu
  refine ⟨Q, y, hg, ?_, ?_, fun gam => isRigid_of_simple_section_collision Q gam u y 0 moving fixed
    (by rwa [hy]) (by rwa [h0]) (by rwa [hy, h0]) (originZ W) 1 (by simpa using hz)⟩
  · rwa [hy, h0]
  · let ρ := transverseJet (m := 1) (RingHom.id ℚ) (fun _ : Fin 1 => 1)
    intro eqv
    rw [hy, h0] at eqv
    change spMap ρ ≫ s.left = spMap ρ ≫ eSec Q.P.A at eqv
    rw [← hs, ← he] at eqv
    simp only [← Category.assoc, cancel_mono, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at eqv
    have hr := congrArg (fun q => q.hom) (Spec.map_injective eqv)
    have hy' : ρ Y = 0 := by
      rw [← hz, map_sub, sub_eq_zero]
      exact RingHom.congr_fun hr (originZ W)
    have := congrArg TrivSqZeroExt.snd hy'
    simp [ρ, Y] at this

end

end GlobalTheory.RigChart.MixedElliptic
