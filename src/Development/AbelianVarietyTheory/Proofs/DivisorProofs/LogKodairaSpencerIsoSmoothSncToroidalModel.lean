module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfInjectiveModMaximal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerRegularFramedAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerInjectiveClosedInteriorPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizedModuleRes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBalancedTensorsFiniteProjectiveRankDim

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

namespace GlobalTheory.LogKSAssembly

theorem entry_mem_of_mem_smul_top {R : Type} [CommRing R] {n : ℕ} (N : Submodule R (Matrix (Fin n) (Fin n) R))
    (m : Ideal R) (y : N) (hy : y ∈ m • (⊤ : Submodule R N)) (a b : Fin n) : (y : Matrix (Fin n) (Fin n) R) a b ∈ m := by
  refine Submodule.smul_induction_on (p := fun y : N => (y : Matrix (Fin n) (Fin n) R) a b ∈ m) hy ?_ ?_
  · intro r hr x _
    simpa using m.mul_mem_right _ hr
  · intro x y hx hy
    simpa using m.add_mem hx hy

private theorem exists_unique_matrix_map {R L : Type} [CommRing R] [AddCommGroup L] [Module R L]
    {n : ℕ} (N : Submodule R (Matrix (Fin n) (Fin n) R))
    (K : L → Matrix (Fin n) (Fin n) R → Prop) (hex : ∀ D, ∃ Θ, K D Θ) (huniq : ∀ D Θ Θ', K D Θ → K D Θ' → Θ = Θ')
    (hlin : ∀ D D' (r : R) Θ Θ', K D Θ → K D' Θ' → K (D + D') (Θ + Θ') ∧ K (r • D) (r • Θ))
    (hN : ∀ D Θ, K D Θ → Θ ∈ N) :
    ∃! f : L →ₗ[R] N, ∀ D Θ, K D Θ ↔ Θ = (f D).1 := by
  classical
  choose Θ hΘ using hex
  let f : L →ₗ[R] N :=
    { toFun := fun D => ⟨Θ D, hN D _ (hΘ D)⟩
      map_add' := fun D D' => Subtype.ext (huniq _ _ _ (hΘ (D + D')) (hlin D D' 1 _ _ (hΘ D) (hΘ D')).1)
      map_smul' := fun r D => Subtype.ext (huniq _ _ _ (hΘ (r • D)) (hlin D D r _ _ (hΘ D) (hΘ D)).2) }
  have hf : ∀ D Θ', K D Θ' ↔ Θ' = (f D).1 :=
    fun D Θ' => ⟨fun h => huniq _ _ _ h (hΘ D), fun h => h ▸ hΘ D⟩
  refine ⟨f, hf, fun g hg => ?_⟩
  ext D : 1
  exact Subtype.ext ((hf D _).mp ((hg D _).mpr rfl))

private theorem exists_equiv_of_graph {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L]
    {n : ℕ} (N : Submodule R (Matrix (Fin n) (Fin n) R)) [Module.Finite R N] [Module.Projective R N]
    (K : L → Matrix (Fin n) (Fin n) R → Prop)
    (f : L →ₗ[R] N) (hg : ∀ D Θ, K D Θ ↔ Θ = (f D).1)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] L) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hfib : ∀ D Θ (m : Ideal R), m.IsMaximal → K D Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule R L)) :
    ∃ e : L ≃ₗ[R] N, ∀ D Θ, K D Θ ↔ Θ = (e D).1 := by
  have hf := GlobalTheory.ProjBij.bijective_of_injective_mod_maximal R L N f hrk
    (fun m hm x hx => hfib x _ m hm ((hg x _).mpr rfl) (entry_mem_of_mem_smul_top N m (f x) hx))
  exact ⟨LinearEquiv.ofBijective f hf, hg⟩

theorem exists_equiv {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L]
    {n : ℕ} (N : Submodule R (Matrix (Fin n) (Fin n) R)) [Module.Finite R N] [Module.Projective R N]
    (K : L → Matrix (Fin n) (Fin n) R → Prop) (hex : ∀ D, ∃ Θ, K D Θ) (huniq : ∀ D Θ Θ', K D Θ → K D Θ' → Θ = Θ')
    (hlin : ∀ D D' (r : R) Θ Θ', K D Θ → K D' Θ' → K (D + D') (Θ + Θ') ∧ K (r • D) (r • Θ))
    (hN : ∀ D Θ, K D Θ → Θ ∈ N)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] L) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hfib : ∀ D Θ (m : Ideal R), m.IsMaximal → K D Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule R L)) :
    ∃ e : L ≃ₗ[R] N, ∀ D Θ, K D Θ ↔ Θ = (e D).1 := by
  obtain ⟨f, hg, _⟩ := exists_unique_matrix_map N K hex huniq hlin hN
  exact exists_equiv_of_graph N K f hg hrk hfib

/-- A relative Kodaira–Spencer matrix cannot vanish unless its derivation does.
It is enough to test on the dense abelian interior; no boundary charts are required. -/
theorem derivation_eq_zero_of_isKS_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F)) {U : Y.X.affineOpens} {n : ℕ}
    {v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)}
    (hv : ∀ i, IsTanAtG Y.t (chart U) (v i))
    {D : Derivation ℤ Γ(Y.X, U.1) Γ(Y.X, U.1)}
    (hc : ∀ a, D (constFn Y.s U.1 a) = 0)
    (hKS : IsKS Y.t (interior Y) U v D 0) : D = 0 := by
  let _ : IsReduced Y.X := GlobalTheory.Coisotropic.isReduced_of_isNormalScheme Y.normal
  apply Derivation.ext
  intro r
  apply GlobalTheory.LogKSBal.eq_zero_of_dense (dense_interior Y) U (D r)
  intro g hg K _ x
  let ψ := x.comp (resG Y.X (Y.X.basicOpen_le g))
  let φ := (dualMap ψ).comp (epsHom D)
  have hf (s) : (φ s).fst = ψ s := by simp [φ, epsHom, dualMap]
  have hs (s) : (φ s).snd = ψ (D s) := by simp [φ, epsHom, dualMap]
  have hV : ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ interior Y := by
    intro p _
    apply hg
    change spMap φ p ∈ U.2.fromSpec ⁻¹ᵁ Y.X.basicOpen g
    rw [U.2.fromSpec_preimage_basicOpen]
    intro hp
    have hu : IsUnit (φ g) := by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hf]
      exact (Y.X.toRingedSpace.isUnit_res_basicOpen g).map x
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  exact (hs r).symm.trans (GlobalTheory.InteriorKS.snd_eq_zero Y U v D 0 hv hKS φ
    (fun s => (hs s).trans (hf _).symm) (by simp) hV
    (fun a => by rw [hs, hc a, map_zero]) r)

/-- On ordinary toroidal charts the regular balanced log Kodaira–Spencer map already
exists, is unique, and is injective on affine sections. No rigidity is needed here. -/
theorem exists_logKSMap_of_chart {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F))
    (hchart : ∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → GlobalTheory.MumfordChart.HasChart Y x)
    {U : Y.X.affineOpens} (hU : IsAffineOpen (U.1 ⊓ interior Y)) {n : ℕ} {v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)}
    {A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)}
    (hv : ∀ i, IsTanAtG Y.t (chart U) (v i))
    (hb : ∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w)
    (hA : ∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) :
    ∃! f : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U →ₗ[Γ(Y.X, U.1)] balanced H.bar A,
      Function.Injective f ∧ ∀ D Θ, IsKS Y.t (interior Y) U v D.1 Θ ↔ Θ = (f D).1 := by
  obtain ⟨f, hf, hu⟩ := exists_unique_matrix_map (L := logDer Y.s _ U) (balanced H.bar A) (fun D Θ => IsKS Y.t (interior Y) U v D.1 Θ)
    (GlobalTheory.KReg.exists_isKS_regular_of_chart E H Dw l Xo c Y hchart U hU n v hv hb)
    (fun _ _ _ h h' => GlobalTheory.KSUniq.isKS_unique_of_frame Y hv hb h h')
    (GlobalTheory.LogKSLin.isKS_linear E H Dw l Xo c Y U n v A hv hb hA)
    (fun D _ h => GlobalTheory.LogKSBal.isKS_mem_balanced_of_frame Y hv hb hA (D := D.1) h)
  refine ⟨f, ⟨LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_), hf⟩, fun g hg => hu g hg.2⟩
  intro D hD
  exact Subtype.ext (derivation_eq_zero_of_isKS_zero Y hv D.2.1 ((hf D 0).mpr (by rw [hD]; rfl)))


private theorem subsingleton_of_finrank_zero_mod_maximal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ m : Ideal R, m.IsMaximal → Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = 0) :
    Subsingleton M := by
  rw [← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top, eq_comm]
  apply GlobalTheory.ProjBij.eq_bot_of_forall_le_smul _ Module.Finite.fg_top
  intro m hm x _
  let _ := Ideal.Quotient.field m
  have := Module.finrank_zero_iff.mp (h m hm)
  exact (GlobalTheory.ProjBij.one_tmul_eq_zero_iff m x).mp (Subsingleton.elim _ _)

/-- In dimension zero the balanced target vanishes, so the ordinary-chart map is an
isomorphism without a smoothness, normal-crossings, or rigidification hypothesis. -/
theorem hasLogKS_of_dim_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F)) (hzero : Dw.dim = 0)
    (hchart : ∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → GlobalTheory.MumfordChart.HasChart Y x)
    (haff : ∀ U : Y.X.affineOpens, IsAffineOpen (U.1 ⊓ interior Y)) : HasLogKS Y.t Y.s (interior Y) := by
  intro U n v A hv hb hA
  obtain ⟨hfin, _, hrank⟩ := GlobalTheory.BalProj.balanced_rank_of_frame E H Dw l Xo c Y U n v A hv hb hA
  have := subsingleton_of_finrank_zero_mod_maximal (fun m hm => (hrank m hm).trans hzero)
  obtain ⟨f, ⟨hinj, hf⟩, _⟩ := exists_logKSMap_of_chart Y hchart (haff U) hv hb hA
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, fun y => ⟨0, Subsingleton.elim _ y⟩⟩, hf⟩

set_option maxHeartbeats 2000000 in
theorem hasLogKS_of_rigid : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → HasLogKS Y.t Y.s (interior Y) := by
  intro E _ _ _ H Dw l Xo c Y hsm hsnc hrig
  by_cases hr : 1 ≤ Dw.p + Dw.q
  case neg =>
    have hp : Dw.p = 0 := by omega
    exact hasLogKS_of_dim_zero Y (by simp [Datum.dim, hp]) (fun x hx hc => (hrig x hx hc).hasChart)
      (GlobalTheory.AffOff.isAffineOpen_inf_interior E H Dw l Xo c Y hsnc)
  unfold HasLogKS
  intro U n v A hv hb hA
  obtain ⟨hLf, hLp, hLr⟩ := GlobalTheory.LogDerProj.main E H Dw l Xo c Y hr hsm hsnc U
  obtain ⟨hBf, hBp, hBr⟩ := GlobalTheory.BalProj.balanced_rank_of_frame E H Dw l Xo c Y U n v A hv hb hA
  obtain ⟨f, ⟨_, hf⟩, _⟩ := exists_logKSMap_of_chart Y (fun x hx hc => (hrig x hx hc).hasChart)
    (GlobalTheory.AffOff.isAffineOpen_inf_interior E H Dw l Xo c Y hsnc U) hv hb hA
  exact exists_equiv_of_graph (balanced H.bar A) (fun D Θ => IsKS Y.t (interior Y) U v D.1 Θ) f hf
    (fun m hm => (hLr m hm).trans (hBr m hm).symm)
    (GlobalTheory.T.logKodairaSpencer_injective_mod_maximalIdeal E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)

theorem hasLogKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → HasLogKS Y.t Y.s (interior Y) := by
  intro E _ _ _ H Dw l Xo c Y _
  exact hasLogKS_of_rigid E H Dw l Xo c Y

end GlobalTheory.LogKSAssembly
