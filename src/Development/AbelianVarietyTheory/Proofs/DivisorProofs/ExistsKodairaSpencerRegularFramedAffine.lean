module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerInteriorAffineOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRegularNearRigidBoundaryPointStatement

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KReg

section Cartier

open GlobalTheory.LocM GlobalTheory.MumfordChart GlobalTheory.PolFan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F))

/-- An effective Cartier boundary already makes the interior affine over its model,
without a smoothness or normal-crossings condition. -/
theorem isAffineOpen_inf_interior_of_cartier (B : EffCartierData Y.X)
    (hB : ∀ x ∈ B.idealSheaf.support, x ∉ abLocus Y.t.G)
    (hcover : ∀ x ∈ genBd Y, genι Y x ∈ B.idealSheaf.support) (U : Y.X.affineOpens) :
    IsAffineOpen (U.1 ⊓ interior Y) := by
  have := isIso_fst Y
  have he : interior Y = nonzeroLocus B.canonical := by
    ext x
    change x ∈ (interior Y : Set Y.X) ↔ x ∈ (nonzeroLocus B.canonical : Set Y.X)
    rw [coe_interior, B.coe_nonzeroLocus_canonical]
    refine ⟨fun hx h => hB x h hx, fun hx => ?_⟩
    by_contra h
    obtain ⟨z, rfl⟩ := (genι Y).surjective x
    exact hx (hcover z (mem_genBd_iff.mpr h))
  rw [he, inf_comm]
  exact GlobalTheory.isAffineOpen_nonzeroLocus_inf B.isLB_lb B.canonical U.2

theorem isAffineOpen_inf_interior_of_fan {φ : InvFun (𝓞 E)}
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (BD : EffCartierData Y.X) {d : ℕ} (hd : 1 ≤ d)
    (hB : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G)
    (hc : ∀ x ∈ genBd Y, HasChartOf φ Y BD d x) (U : Y.X.affineOpens) :
    IsAffineOpen (U.1 ⊓ interior Y) :=
  isAffineOpen_inf_interior_of_cartier Y BD hB (fun x hx =>
    (ReciprocityTheory.AnForm.R.mem_support_iff_stalkId _ _).mpr
      (GlobalTheory.FanChartTest.idlAlong_ne_top hφ hd hx (hc x hx))) U

end Cartier

theorem exists_res_eq {X : Scheme.{0}} (U W : X.affineOpens) (V : X.Opens) (hW : W.1 = U.1 ⊓ V) (θ : Γ(X, W.1))
    (h : ∀ m : Ideal Γ(X, U.1), m.IsMaximal → (∃ x ∈ U.1, (∀ f ∈ m, x ∉ X.basicOpen f) ∧ x ∉ V) →
      ∃ g ∉ m, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s =
        (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom g * θ) :
    ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s = θ := by
  have hWU : W.1 ≤ U.1 := hW.le.trans inf_le_left
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (X.presheaf.map (homOfLE hWU).op).hom := ⟨_, rfl⟩
  have hres : ∀ {A B C : X.Opens} (h1 : B ≤ A) (h2 : C ≤ B) (h3 : C ≤ A) (z : Γ(X, A)),
      (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom z) =
        (X.presheaf.map (homOfLE h3).op).hom z := fun h1 h2 h3 z => by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  let J : Ideal Γ(X, U.1) :=
    { carrier := {g | ∃ s : Γ(X, U.1), ρ s = ρ g * θ}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := fun {g g'} ⟨s, hs⟩ ⟨s', hs'⟩ => ⟨s + s', by rw [map_add (f := _), map_add (f := _), hs, hs', add_mul]⟩
      smul_mem' := fun r g ⟨s, hs⟩ => ⟨r * s, by rw [smul_eq_mul, map_mul, map_mul, hs, _root_.mul_assoc]⟩ }
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hne
    let p : PrimeSpectrum Γ(X, U.1) := ⟨m, hm.isPrime⟩
    have hxU : U.2.fromSpec p ∈ U.1 := by
      have : U.2.fromSpec p ∈ Set.range U.2.fromSpec := ⟨p, rfl⟩
      rwa [U.2.range_fromSpec] at this
    have hxf : ∀ f, U.2.fromSpec p ∈ X.basicOpen f ↔ f ∉ m := fun f => by
      change p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f ↔ _
      rw [U.2.fromSpec_preimage_basicOpen]; rfl
    by_cases hxV : U.2.fromSpec p ∈ V
    · obtain ⟨g, hgW, hxg⟩ := U.2.exists_basicOpen_le (V := W.1) ⟨U.2.fromSpec p, hW ▸ ⟨hxU, hxV⟩⟩ hxU
      have hgm : g ∉ m := (hxf g).1 hxg
      apply hgm
      have := U.2.isLocalization_basicOpen g
      obtain ⟨⟨s, ⟨_, N, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers g)
        ((X.presheaf.map (homOfLE hgW).op).hom θ)
      have hbo : X.basicOpen (ρ g) ≤ X.basicOpen g := by
        rw [hρ, Scheme.basicOpen_res]; exact inf_le_right
      have e3 : ∀ z, (X.presheaf.map (homOfLE hgW).op).hom (ρ z) =
          algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) z := fun z => by
        rw [hρ]; exact hres hWU hgW (hgW.trans hWU) z
      have hz : (X.presheaf.map (homOfLE hgW).op).hom (ρ g ^ N * θ - ρ s) = 0 := by
        rw [map_sub, map_mul, map_pow, e3, e3, ← map_pow, mul_comm, hs, sub_self]
      have hz' : (X.presheaf.map (homOfLE (X.basicOpen_le (ρ g))).op).hom (ρ g ^ N * θ - ρ s) = 0 := by
        have := congrArg (X.presheaf.map (homOfLE hbo).op).hom hz
        rwa [map_zero, hres hgW hbo (X.basicOpen_le (ρ g))] at this
      obtain ⟨M, hM⟩ := AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X
        W.2.isCompact (ρ g ^ N * θ - ρ s) (ρ g) hz'
      refine hm.isPrime.mem_of_pow_mem (M + N) (hJm ⟨g ^ M * s, ?_⟩)
      rw [map_mul, map_pow, map_pow, pow_add]
      linear_combination (-1 : Γ(X, W.1)) * hM
    · obtain ⟨g, hgm, s, hs⟩ := h m hm ⟨_, hxU, fun f hf hx => (hxf f).1 hx hf, hxV⟩
      exact hgm (hJm ⟨s, hρ ▸ hs⟩)
  obtain ⟨s, hs⟩ : (1 : Γ(X, U.1)) ∈ J := hJ ▸ Submodule.mem_top
  exact ⟨s, by rw [← hρ, hs, map_one, _root_.one_mul]⟩

theorem exists_der_res {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) :
    ∃ DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1), ∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) =
      (X.presheaf.map (homOfLE hW).op).hom (D r) := by
  set ρ := (X.presheaf.map (homOfLE hW).op).hom with hρ
  let : Algebra Γ(X, U.1) Γ(X, W.1) := ρ.toAlgebra
  have h1 : IsOpenImmersion (chart W) := W.2.isOpenImmersion_fromSpec
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1))) ≫ chart U = chart W :=
    GlobalTheory.LogKSDiv.GenChange.chart_res U W hW
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1))) ≫ chart U) := e ▸ h1
  have : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1)))) :=
    IsOpenImmersion.of_comp _ (chart U)
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1)))) := inferInstance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at hs
  have : Algebra.Smooth Γ(X, U.1) Γ(X, W.1) := RingHom.smooth_algebraMap.1 hs
  let g : Γ(X, U.1) →+* DualNumber Γ(X, W.1) :=
    { toFun := fun r => TrivSqZeroExt.inl (ρ r) + TrivSqZeroExt.inr (ρ (D r))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz]; ring }
  let : Algebra Γ(X, U.1) (DualNumber Γ(X, W.1)) := g.toAlgebra
  let π : DualNumber Γ(X, W.1) →ₐ[Γ(X, U.1)] Γ(X, W.1) :=
    { (TrivSqZeroExt.fstHom Γ(X, W.1) Γ(X, W.1) Γ(X, W.1)).toRingHom with
      commutes' := fun r => by simp [g, RingHom.algebraMap_toAlgebra] }
  have hsur : Function.Surjective π := fun s => ⟨TrivSqZeroExt.inl s, rfl⟩
  have hk : IsNilpotent (RingHom.ker (π : DualNumber Γ(X, W.1) →+* Γ(X, W.1))) := by
    refine ⟨2, ?_⟩
    rw [Submodule.zero_eq_bot, eq_bot_iff, pow_two]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Submodule.mem_bot]
    ext <;> simp [ha', hb']
  let l := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id Γ(X, U.1) Γ(X, W.1)) π hsur hk
  have hl1 : ∀ s, (l s).fst = s := fun s =>
    AlgHom.congr_fun (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id Γ(X, U.1) Γ(X, W.1)) π hsur hk) s
  have hl2 : ∀ r, l (ρ r) = g r := fun r => l.commutes r
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun s => (l s).snd, map_zero' := by simp, map_add' := fun x y => by rw [map_add (f := _)]; rfl }) fun a b => ?_,
    fun r => ?_⟩
  · change (l (a * b)).snd = a • (l b).snd + b • (l a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hl1, hl1]
    simp [smul_eq_mul, mul_comm]
  · change (l (ρ r)).snd = _
    rw [hl2]
    simp [g]

/-- Every tangent frame has a regular log KS matrix when its affine chart meets the interior affinely. -/
theorem exists_isKS_regular_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → GlobalTheory.MumfordChart.HasChart Y x) → ∀ (U : Y.X.affineOpens), IsAffineOpen (U.1 ⊓ interior Y) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U, ∃ Θ, IsKS Y.t (interior Y) U v D.1 Θ := by
  intro E _ _ _ H Dw l Xo c Y hchart U hU n v hv hb D
  obtain ⟨W, hW⟩ : ∃ W : Y.X.affineOpens, W.1 = U.1 ⊓ interior Y := ⟨⟨_, hU⟩, rfl⟩
  have hWU : W.1 ≤ U.1 := hW.le.trans inf_le_left
  obtain ⟨DW, hDW⟩ := exists_der_res U W hWU D.1
  obtain ⟨hv', hb'⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange Y.t (Y.X.presheaf.map (homOfLE hWU).op).hom
    (chart U) n v hv hb
  rw [GlobalTheory.LogKSDiv.GenChange.chart_res U W hWU] at hv' hb'
  obtain ⟨ΘW, hΘW⟩ := GlobalTheory.T.exists_kodairaSpencer_interior_affine_open E H Dw l Xo c Y W (hW.le.trans inf_le_right) n _ hv' hb' DW
  have key := fun (m : Ideal Γ(Y.X, U.1)) (hm : m.IsMaximal) hx =>
    GlobalTheory.LocRegRig.isKS_regular_at_chart E H Dw l Xo c Y hchart U W hW n v hv hb D DW ΘW hDW hΘW m hm hx
  choose Θ hΘ using fun a b => exists_res_eq U W (interior Y) hW (ΘW a b) fun m hm hx =>
    (key m hm hx).imp fun g hg => ⟨hg.1, hg.2 a b⟩
  refine ⟨Θ, GlobalTheory.LogKSUp.isKS_of_inf E H Y.X Y.t (interior Y) U W hW n v D.1 DW Θ hDW ?_⟩
  convert hΘW using 1
  ext a b
  exact hΘ a b

theorem exists_isKS_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U, ∃ Θ, IsKS Y.t (interior Y) U v D.1 Θ := by
  intro E _ _ _ H Dw l Xo c Y _ _ hsnc hrig U n v _ hv hb _
  exact exists_isKS_regular_of_chart E H Dw l Xo c Y (fun x hx hc => (hrig x hx hc).hasChart)
    U (GlobalTheory.AffOff.isAffineOpen_inf_interior E H Dw l Xo c Y hsnc U) n v hv hb

end GlobalTheory.KReg
