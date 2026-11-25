module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.CharGal
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyGridDataIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalToGlobal.HermitianColumns.SymAll
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatLatSmulLeOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

abbrev Df (p : PtAt ex Csz) : DefSide p.P.A3.fam3.base3 := lv (p.F.fc (p.R.toCx3 p.F).zs) false

abbrev Tup (p : PtAt ex Csz) : Type := p.P.A3.fam3.base3.Tup

abbrev PlL (D : D7) : Type := HeightOneSpectrum (𝓞 D.what₂.LL)

abbrev Sq (D : D7) : Type := Fin D.R.m × Fin D.R.m

abbrev Grid (p : PtAt ex Csz) (CF : ℝ) : Type 1 := GlobalTheory.ChiGrid.GridData p.R.toRealDat.toLevCh ⟨1, CF, p.Z.b⟩


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure FunIn (p : PtAt ex Csz) (CF : ℝ) where

  G : GlobalTheory.ChiGrid.GridData p.R.toRealDat.toLevCh ⟨1, CF, p.Z.b⟩

  W : G.Weil

  ext : W.Over p.R.toRealDat

  n : ℕ

  X' : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ

  M : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL)

  V : ∀ t : Tup p, Matrix (Fin n) (Fin ((Df p).nV t)) D.what₂.LL

  rq : Tup p → Sq D → D.what₂.LL

  dl : PlL D → ℝ

  Sd : Finset ℕ

  Se : Finset ℕ

  N0 : Sq D → ℤ → ℕ → ℝ

  zA : Sq D → D.what₂.LL

  zA' : Sq D → D.what₂.LL

  zT : Sq D → ℤ → D.what₂.LL

  zTd : Sq D → Bool → ℤ → D.what₂.LL

  gT : Sq D → ℤ → PlL D → ℤ

  ch : PlL D → Bool

  Bw : ℝ


open Classical in
def cloud (D : D7) (τ i : ℕ) : ℤ :=
  if h : τ < Fintype.card D.what₂.Tau then
    (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)) 0 0 0).v i else 0

def sqRank (D : D7) (ij : Sq D) : ℕ :=
  GlobalTheory.ChiGrid.rankV D ij.1 ((ij.2 : ℕ) + 1) + GlobalTheory.ChiGrid.rankV D ((ij.1 : ℕ) + 1) ij.2


open Classical in
def FunIn.data {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) (ze : Tup p → D.what₂.LL) (Tf : Finset (PlL D)) (dF : PlL D → ℤ) :
    FunData D.what₂.LL (Df p) where
  n := d.n
  X' := d.X'
  M := d.M
  vmu t := (ze t)⁻¹ • d.V t
  Tf := Tf
  dF := dF
  m := D.R.m
  rq := d.rq
  dl := d.dl
  Sd := d.Sd
  Se := d.Se
  N0 := d.N0
  zA := d.zA
  zA' := d.zA'
  zT := d.zT
  zTd := d.zTd
  gT := d.gT
  ch := d.ch
  dd := sqRank D
  hd ij := sqRank D ij / 2
  yy ij := D.R.m - 1 - ij.2
  Sq := HeightOneSpectrum (𝓞 D.host.F)
  S0 := d.G.pl.S0
  sv0 := d.G.pl.v0
  cc v := if v = d.G.pl.v0 then 1 else 2
  qq v := Ideal.absNorm v.asIdeal
  f := D.R.f
  k := D.R.k
  tt := D.R.t
  cl := cloud D
  g1 := D.host.g 0
  g2 := D.host.g 1
  pd := D.host.pde
  pd' := D.host.pde'
  dE := discr D.host.E
  Bw := d.Bw

abbrev FunIn.O {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) : FunData D.what₂.LL (Df p) := d.data (fun _ => 1) ∅ fun _ => 0

abbrev TieT := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ), FunIn p CF → Prop

abbrev PropT := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ), FunIn p CF → ℝ → ℝ → Prop

def trivialTieCondition : TieT := fun _ _ _ => True

section Fit

open GlobalTheory.ChiGrid Formalism.L2.Host

variable {T : Type} {Lc : LevCh D T} {sc : Consts}

def lamOf (G : GridData Lc sc) : GlobalTheory.LamTie.LamDat D where
  C := Lc.C
  q0 := q0 D
  w0 := G.pl.w G.pl.v0
  c a g := cen D sc.cGap (D.eTau.symm g) (a.1 + 1)
  chi a := G.ch.chiH (a.1 + 1)

structure FieldHas (G : GridData Lc sc) {K : Type} [Field K] (e : K →+* ℂ) : Prop where

  values : ∀ i, 1 ≤ i → i ≤ D.R.m → (G.ch.chiH i).ValuesIn 0 e

  roots : ∀ v ∈ G.pl.S0, ∃ z : K, IsPrimitiveRoot z (Ideal.absNorm v.asIdeal ^ G.pl.depth sc v)

private theorem exists_primitiveRoot_lcm_iff {ι M : Type*} [CommMonoid M]
    (places : Finset ι) (degree : ι → ℕ) (hdegree : ∀ i ∈ places, degree i ≠ 0) :
    (∃ z : M, IsPrimitiveRoot z (places.lcm degree)) ↔
      ∀ i ∈ places, ∃ z : M, IsPrimitiveRoot z (degree i) := by
  classical
  constructor
  · rintro ⟨z, hz⟩ i hi
    obtain ⟨d, hd⟩ := Finset.dvd_lcm (f := degree) hi
    have hn := Finset.lcm_ne_zero_iff.mpr hdegree
    have hd0 : d ≠ 0 := by
      intro h
      exact hn (by simp [hd, h])
    refine ⟨z ^ d, ?_⟩
    simpa [hd, hd0] using hz.pow_of_dvd hd0 (Dvd.intro (degree i) (by rw [hd, mul_comm]))
  · revert hdegree
    induction places using Finset.induction_on with
    | empty =>
        intro _ _
        exact ⟨1, by simp⟩
    | @insert i places hi ih =>
        intro hdegree h
        obtain ⟨z, hz⟩ := h i (Finset.mem_insert_self _ _)
        have hprev : ∀ j ∈ places, degree j ≠ 0 :=
          fun j hj => hdegree j (Finset.mem_insert_of_mem hj)
        obtain ⟨y, hy⟩ := ih hprev (fun j hj => h j (Finset.mem_insert_of_mem hj))
        rw [Finset.lcm_insert]
        exact ⟨_, hz.pow_mul_pow_lcm hy (hdegree i (Finset.mem_insert_self _ _))
          (Finset.lcm_ne_zero_iff.mpr hprev)⟩

private theorem exists_primitiveRoot_iff_dvd_torsionOrder
    (K : Type*) [Field K] [NumberField K] (n : ℕ) [NeZero n] :
    (∃ z : K, IsPrimitiveRoot z n) ↔ n ∣ NumberField.Units.torsionOrder K := by
  constructor
  · rintro ⟨ζ, hζ⟩
    exact NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot hζ
  · intro h
    obtain ⟨μ, hμ⟩ : ∃ μ : NumberField.Units.torsion K,
        orderOf μ = NumberField.Units.torsionOrder K := IsCyclic.exists_ofOrder_eq_natCard
    rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
      ← IsPrimitiveRoot.coe_units_iff] at hμ
    have hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
    obtain ⟨d, hd⟩ := h
    have hd0 : d ≠ 0 := by
      intro hd0
      exact NumberField.Units.torsionOrder_ne_zero K (by simp [hd, hd0])
    refine ⟨((algebraMap (𝓞 K) K) (μ : (𝓞 K)ˣ)) ^ d, ?_⟩
    simpa [hd, hd0] using hμ.pow_of_dvd hd0 (Dvd.intro n (by rw [hd, mul_comm]))


/-- The least positive order supporting all of the grid's local root requirements. -/
def rootOrder (G : GridData Lc sc) : ℕ :=
  G.pl.S0.lcm fun v => Ideal.absNorm v.asIdeal ^ G.pl.depth sc v

theorem rootOrder_ne_zero (G : GridData Lc sc) : rootOrder G ≠ 0 :=
  Finset.lcm_ne_zero_iff.mpr fun v _ =>
    pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)

theorem FieldHas.iff_values_and_primitiveRoot {G : GridData Lc sc}
    {K : Type} [Field K] (e : K →+* ℂ) :
    FieldHas G e ↔
      (∀ i, 1 ≤ i → i ≤ D.R.m → (G.ch.chiH i).ValuesIn 0 e) ∧
        ∃ z : K, IsPrimitiveRoot z (rootOrder G) := by
  have h := exists_primitiveRoot_lcm_iff (M := K) G.pl.S0
    (fun v => Ideal.absNorm v.asIdeal ^ G.pl.depth sc v)
    (fun v _ => pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot))
  exact ⟨fun hG => ⟨hG.values, h.mpr hG.roots⟩, fun ⟨hv, hr⟩ => ⟨hv, h.mp hr⟩⟩

/-- The roots clause is one divisibility test against the field's torsion order. -/
theorem FieldHas.iff_values_and_dvd_torsionOrder {G : GridData Lc sc}
    {K : Type} [Field K] [NumberField K] (e : K →+* ℂ) :
    FieldHas G e ↔
      (∀ i, 1 ≤ i → i ≤ D.R.m → (G.ch.chiH i).ValuesIn 0 e) ∧
        rootOrder G ∣ NumberField.Units.torsionOrder K := by
  let : NeZero (rootOrder G) := ⟨rootOrder_ne_zero G⟩
  rw [FieldHas.iff_values_and_primitiveRoot, exists_primitiveRoot_iff_dvd_torsionOrder]

/-- The cyclotomic part of the coefficient field, without the character values. -/
def rootField (G : GridData Lc sc) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / rootOrder G)}

theorem rootField_finrank (G : GridData Lc sc) :
    Module.finrank ℚ (rootField G) = (rootOrder G).totient := by
  let : NeZero (rootOrder G) := ⟨rootOrder_ne_zero G⟩
  let : IsCyclotomicExtension {rootOrder G} ℚ (rootField G) :=
    (Complex.isPrimitiveRoot_exp _ (rootOrder_ne_zero G)).intermediateField_adjoin_isCyclotomicExtension ℚ
  exact IsCyclotomicExtension.Rat.finrank _ _

private theorem primitiveRoot_iff_rootField_le (G : GridData Lc sc) (M : IntermediateField ℚ ℂ) :
    (∃ z : M, IsPrimitiveRoot z (rootOrder G)) ↔ rootField G ≤ M := by
  let : NeZero (rootOrder G) := ⟨rootOrder_ne_zero G⟩
  have hz := Complex.isPrimitiveRoot_exp _ (rootOrder_ne_zero G)
  change (∃ z : M, IsPrimitiveRoot z (rootOrder G)) ↔ IntermediateField.adjoin ℚ {_} ≤ M
  rw [IntermediateField.adjoin_le_iff]
  simp only [Set.singleton_subset_iff]
  constructor
  · rintro ⟨y, hy⟩
    have hy := hy.map_of_injective M.val.injective
    obtain ⟨d, -, hd⟩ := hy.eq_pow_of_pow_eq_one hz.pow_eq_one
    rw [← hd]
    exact M.pow_mem y.property d
  · intro h
    exact ⟨⟨_, h⟩, IsPrimitiveRoot.of_map_of_injective (f := M.val) hz M.val.injective⟩

/-- The roots clause alone, independent of any character values. -/
theorem rootField_le_iff_roots (G : GridData Lc sc) (M : IntermediateField ℚ ℂ) :
    rootField G ≤ M ↔ ∀ v ∈ G.pl.S0, ∃ z : M, IsPrimitiveRoot z (Ideal.absNorm v.asIdeal ^ G.pl.depth sc v) :=
  (primitiveRoot_iff_rootField_le G M).symm.trans <|
    exists_primitiveRoot_lcm_iff G.pl.S0 (fun v => Ideal.absNorm v.asIdeal ^ G.pl.depth sc v)
      (fun v _ => pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot))

theorem FieldHas.rootField_le_iff {G : GridData Lc sc} (M : IntermediateField ℚ ℂ) :
    FieldHas G M.val.toRingHom ↔
      (∀ i, 1 ≤ i → i ≤ D.R.m → (G.ch.chiH i).ValuesIn 0 M.val.toRingHom) ∧
        rootField G ≤ M := by
  rw [FieldHas.iff_values_and_primitiveRoot]
  apply and_congr_right'
  exact primitiveRoot_iff_rootField_le G M

theorem lambdaGrid_apply (G : GridData Lc sc) (l : ℕ) (j a : Fin D.R.m) :
    (lamOf G).lam0 l j a = Lc.C.mu0 j * Lc.C.delAt l / G.ch.chiH (a.1 + 1) := (div_eq_mul_inv _ _).symm

theorem lamOf_hasInfQ (G : GridData Lc sc) (a : Fin D.R.m) :
    ((lamOf G).chi a).HasInfQ (embPsi D.host) fun g => ((lamOf G).c a g : ℚ) := by
  refine ⟨fun g => 2 * cen D sc.cGap (D.eTau.symm g) (a.1 + 1), fun g => by simp [lamOf], fun k => ?_⟩
  refine (G.ch.inf (a.1 + 1) (by omega) a.2 k).trans (Fintype.prod_equiv D.eTau _ _ fun τ => ?_)
  simp only [Equiv.symm_apply_apply]
  rfl

theorem lamOf_teich (G : GridData Lc sc) : (lamOf G).Teich := fun a w hw x hx =>
  G.ch.wild (a.1 + 1) (by omega) a.2 w hw x (by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hx)

theorem FieldHas.map {G : GridData Lc sc} {K K' : Type} [Field K] [Field K'] {e' : K' →+* ℂ} (j : K →+* K')
    (h : FieldHas G (e'.comp j)) : FieldHas G e' :=
  ⟨fun i h1 h2 v hv => (h.values i h1 h2 v hv).elim fun y hy => ⟨j y, hy⟩,
    fun v hv => (h.roots v hv).elim fun z hz => ⟨j z, hz.map_of_injective j.injective⟩⟩

theorem exists_fieldHas (G : GridData Lc sc) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ FieldHas G M.val.toRingHom := by
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have h1 : ∀ a : Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      (G.ch.chiH (a.1 + 1)).ValuesIn 0 M.val.toRingHom := fun a => by
    obtain ⟨n, hn, hi⟩ := lamOf_hasInfQ G a
    have := GlobalTheory.T.algebraicHeckeChar_values_in_numberField D.host.F D.host.E c (D.R.Psi) (embPsi D.host) hcm _ n 0 hi fun g => by
      have h3 : (n g : ℚ) = 2 * ((lamOf G).c a g : ℚ) := hn g
      have h2 : n g = 2 * (lamOf G).c a g := by exact_mod_cast h3
      exact ⟨(lamOf G).c a g, by rw [h2]; ring⟩
    rw [Int.cast_zero, zero_div] at this
    exact this
  choose Mc hMc hMc' using h1
  let : NeZero (rootOrder G) := ⟨rootOrder_ne_zero G⟩
  let : IsCyclotomicExtension {rootOrder G} ℚ (rootField G) :=
    (Complex.isPrimitiveRoot_exp _ (rootOrder_ne_zero G)).intermediateField_adjoin_isCyclotomicExtension ℚ
  have : FiniteDimensional ℚ (rootField G) := IsCyclotomicExtension.finite_of_singleton (rootOrder G) ℚ (rootField G)
  refine ⟨(⨆ a, Mc a) ⊔ rootField G, inferInstance, (FieldHas.rootField_le_iff _).mpr ⟨?_, le_sup_right⟩⟩
  intro i a b
  obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact GlobalTheory.Mem.FrameVal.valuesIn_mono (hMc' ⟨i, b⟩) ((le_iSup Mc _).trans le_sup_left)


def TwistedPlaceChoiceLiesOverPair (D : D7) (c : NChoice D) : Prop :=
  (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (c.twI w) = D.what₂.places.resChar w ∧
    (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (c.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (c.twI w) (D.what₂.places.conj w))) ∧
  ∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → c.Q w ≠ ∅ → c.twI w = c.twI w'

theorem TwistedPlaceChoiceLiesOverPair.inW1 {D : D7} {c : NChoice D} (h : TwistedPlaceChoiceLiesOverPair D c) {w : D.what₂.places.Pl} (hw : GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w) :
    D.ntw.NonzeroIndexPlace (c.twI w) :=
  (h.1 w hw).2.elim (fun h1 => ⟨w, hw, h1⟩) fun h1 => ⟨_, (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw, h1⟩

structure GridFit (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) : Prop where

  frame : ValLL0 D p.R.C

  field : FieldHas G (embLL0 D)

  setting : TwistedPlaceChoiceLiesOverPair D ex.nch

  cond : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w)

  powers : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
    BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w))

  psi : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp

  list : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G)

end Fit

abbrev FldT := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (G : Grid p CF), G.Weil → Prop

def HasGrid (Fld : FldT) (p : PtAt ex Csz) (CF : ℝ) : Prop :=
  ∃ (G : Grid p CF) (W : G.Weil), W.Over p.R.toRealDat ∧ GridFit p G ∧ Fld p CF G W

def Fitted (Comparison₂ : TieT) : TieT := fun p CF d => GridFit p d.G ∧ Comparison₂ p CF d

def Lf (Comparison₂ : TieT) (Q : PropT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, ∀ C, C0 ≤ C → EvPt Fm fun _ _ _ p => ∀ d : FunIn p CF, Comparison₂ p CF d → Q p CF d C CH

def Ex (Fld : FldT) (Comparison₂ : TieT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => DIVinN Fm →
  EvPt Fm fun _ _ _ p => ∀ (G : Grid p CF) (W : G.Weil), W.Over p.R.toRealDat → GridFit p G → Fld p CF G W →
    ∃ d : FunIn p CF, d.G = G ∧ Comparison₂ p CF d

def Wt (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafWt d.O C p.Z.b

def Fun0Fit (Fld : FldT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  EvPt Fm fun _ _ _ p => HasGrid Fld p CF → ∀ C, (p.S false).FUN (p.N C CH)

theorem evPt_imp {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : EvPt Fm P) (h : ∀ x hx i p, p.Rows → P x hx i p → Q x hx i p) : EvPt Fm Q :=
  let ⟨a, ha⟩ := hP
  ⟨a, fun x hx h' i p hp => h x hx i p hp (ha x hx h' i p hp)⟩

end GlobalTheory.BigTop.Fun

end
