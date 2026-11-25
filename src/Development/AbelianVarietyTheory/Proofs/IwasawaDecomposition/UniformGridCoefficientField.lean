module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridCoefficientField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyFinitenessGlobal

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.Mem.LiteralAutomorphy
open GlobalTheory.Mem
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridField

theorem fieldHas_of_gkey {X Y : Stages} {T U : Type} {L : LevCh X.toD7 T} {L' : LevCh Y.toD7 U}
    {sc : Consts} (G : GridData L sc) (G' : GridData L' sc) (hP : X.B.toPre = Y.B.toPre)
    (hk : HEq (gkeyOf G) (gkeyOf G')) {K : Type} [Field K] (e : K →+* ℂ)
    (h : FieldHas G' e) : FieldHas G e := by
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := X
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := Y
  change P = Q at hP
  subst Q
  have hkey := eq_of_heq hk
  have hv : G.pl.v0 = G'.pl.v0 := congrArg Prod.fst hkey
  have hc : ∀ a : Fin P.R.m, G.ch.chiH (a.1 + 1) = G'.ch.chiH (a.1 + 1) :=
    fun a => congrArg (fun k : GKey P => k.2.2 a) hkey
  refine ⟨fun i hi hm => ?_, fun v hS => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i-1, by omega⟩
    rw [hc ⟨a, by change a + 1 ≤ P.R.m at hm; omega⟩]
    exact h.values _ hi hm
  · have hd : G.pl.depth sc v = G'.pl.depth sc v := by
      unfold Places.depth
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (h1.trans hv) h2
      · exact absurd (h2.trans hv.symm) h1
      · rfl
    rw [hd]
    exact h.roots _ (by unfold Places.S0 at hS ⊢; rwa [hv] at hS)

theorem gridCoefficientField_eq_of_gkey {X Y : Stages} {T U : Type}
    {L : LevCh X.toD7 T} {L' : LevCh Y.toD7 U} {sc : Consts}
    (G : GridData L sc) (G' : GridData L' sc) (hP : X.B.toPre = Y.B.toPre)
    (hk : HEq (gkeyOf G) (gkeyOf G')) : gridCoefficientField G = gridCoefficientField G' := by
  apply le_antisymm
  · exact (gridCoefficientField_le_iff ..).2 (fieldHas_of_gkey G G' hP hk _ (gridCoefficientField_has _))
  · exact (gridCoefficientField_le_iff ..).2 (fieldHas_of_gkey G' G hP.symm hk.symm _ (gridCoefficientField_has _))

def gridCoefficientFields (P : Pre) (sc : Consts) : Set (IntermediateField ℚ ℂ) :=
  {M | ∃ (X : Stages), X.B.toPre = P ∧ ∃ (T : Type) (L : LevCh X.toD7 T) (G : GridData L sc),
    gridCoefficientField G = M}

/-- A field for every original grid, with no change of its characters. -/
def uniformGridField (P : Pre) (sc : Consts) : IntermediateField ℚ ℂ :=
  ⨆ M : gridCoefficientFields P sc, M.val

theorem uniformGridField_le_iff (P : Pre) (sc : Consts) (M : IntermediateField ℚ ℂ) :
    uniformGridField P sc ≤ M ↔ ∀ (X : Stages), X.B.toPre = P →
      ∀ (T : Type) (L : LevCh X.toD7 T) (G : GridData L sc), FieldHas G M.val.toRingHom := by
  rw [uniformGridField, iSup_le_iff]
  constructor
  · intro h X hX T L G
    exact (gridCoefficientField_le_iff ..).mp (h ⟨_, X, hX, T, L, G, rfl⟩)
  · rintro h ⟨_, X, hX, T, L, G, rfl⟩
    exact (gridCoefficientField_le_iff ..).mpr (h X hX T L G)

theorem uniformGridField_has {X : Stages} {T : Type} {L : LevCh X.toD7 T} {sc : Consts}
    (G : GridData L sc) : FieldHas G (uniformGridField X.B.toPre sc).val.toRingHom :=
  (uniformGridField_le_iff ..).mp le_rfl X rfl T L G

theorem gridCoefficientFields_finite (P : Pre) (sc : Consts) : (gridCoefficientFields P sc).Finite := by
  classical
  obtain ⟨keys, hkeys, hcovers⟩ := gKeyFin P sc.cGap
  let fields (k : GKey P) : Set (IntermediateField ℚ ℂ) := {M | ∃ (X : Stages), X.B.toPre = P ∧
    ∃ (T : Type) (L : LevCh X.toD7 T) (G : GridData L sc), HEq (gkeyOf G) k ∧ gridCoefficientField G = M}
  have hone (k : GKey P) : (fields k).Subsingleton := by
    rintro _ ⟨X, hX, T, L, G, hG, rfl⟩ _ ⟨Y, hY, U, L', G', hG', rfl⟩
    exact gridCoefficientField_eq_of_gkey G G' (hX.trans hY.symm) (hG.trans hG'.symm)
  refine (hkeys.biUnion (fun k _ => (hone k).finite)).subset ?_
  rintro _ ⟨X, hX, T, L, G, rfl⟩
  obtain ⟨k, hk, hG⟩ := hcovers X T L sc G hX rfl
  exact Set.mem_biUnion hk ⟨X, hX, T, L, G, hG, rfl⟩

instance (P : Pre) (sc : Consts) : FiniteDimensional ℚ (uniformGridField P sc) := by
  have : Finite (gridCoefficientFields P sc) := (gridCoefficientFields_finite P sc).to_subtype
  have (M : gridCoefficientFields P sc) : FiniteDimensional ℚ M.val := by
    rcases M with ⟨_, X, _, T, L, G, rfl⟩
    infer_instance
  exact IntermediateField.finiteDimensional_iSup_of_finite

end GlobalTheory.GridField

end
