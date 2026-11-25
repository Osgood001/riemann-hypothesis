module

public import Mathlib
public import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassSelfDualLatticeFirstSpaceEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeOverColumnBaseLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabiliserSelfDualLatticeLevelIndexFormulaStatement

@[expose] public section

noncomputable section

namespace GlobalTheory.ColClassNumber

open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke
open SelfDualStabiliserIndex SplittingProjection

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

private theorem auxiliaryIndex_pos {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 < LevelIndex.auxiliaryIndex (F := F) hp k := by
  classical
  apply Finset.prod_pos
  intro v _
  apply Nat.cast_pos.mpr
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  apply Finset.prod_pos
  intro j hj
  exact Nat.sub_pos_of_lt (one_lt_pow₀ Finite.one_lt_card (Nat.ne_of_gt (Finset.mem_Icc.mp hj).1))

/-- For a column level admitting a self-dual over-lattice and local frames, its actual
class number is the genus mass times the residue-field level factors. -/
theorem classNumber_residue (L : ColLevel R F E sp gp C A clsLat)
    (hp : ∀ i, (gp i).Prime) (hne : gp 0 ≠ gp 1)
    (hfr : ∀ N, IsSelfDualLat (sp.cm.sig : E →+* E) sp.gram0 N → LevelIndex.HasFrames sp N)
    (H : HasOverLattice L) :
    ∃ M : Submodule (𝓞 E) (sp.X 0).V, Submodule.IsLattice E M ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (sp.X 0).hT M ∧
      (Nat.card (C.cls 0) : ℝ) = LevelIndex.auxiliaryIndex (F := F) (hp 0) R.k *
        LevelIndex.auxiliaryIndex (F := F) (hp 1) R.k *
        ((A.T : ℝ) ^ R.k - 1) ^ Nat.card {v : HeightOneSpectrum (𝓞 F) // (A.T : 𝓞 F) ∈ v.asIdeal} *
        Formalism.HermitianLatticesTheory.mass (sp.X 0).hT M := by
  classical
  obtain ⟨N, ⟨hf, hs, hd, -⟩, -, -, hUK⟩ := H.2
  obtain ⟨M, hM, hu, rfl⟩ := exists_lattice sp N hf hs hd
  have hi := LevelIndex.relIndex_level_residue L hp hne hfr H ⟨hf, hs, hd⟩ hUK
  have hm := (Proof.CosetGroupEquiv.general_clause_iff sp M _).mp
    (Proof.TotallyDefiniteMass.cosetSum sp.cm (sp.X 0) (sp.X_sig 0)
      (baseSpace_posDef _ _ sp) M hM hu)
  rw [Proof.CosetGroupEquiv.stabHat0_eq, Proof.CosetGroupEquiv.cosetSum_iff] at hm
  have hle : levelAfL sp.cm.sig sp.gram0 (sp.crdLat0 M) ≤
      UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) := fun _ h => h.1
  have hrel := Subgroup.relIndex_subgroupOf (H := L.U) hle
  have hidx_ne : L.U.relIndex (levelAfL sp.cm.sig sp.gram0 (sp.crdLat0 M)) ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero] at hi
    have hk : R.k ≠ 0 := by have := R.k_ge; omega
    exact (mul_pos (mul_pos (auxiliaryIndex_pos (F := F) (hp 0) R.k)
      (auxiliaryIndex_pos (F := F) (hp 1) R.k))
      (pow_pos (sub_pos.mpr (one_lt_pow₀ (by exact_mod_cast A.T_prime.one_lt) hk)) _)).ne hi
  have h := card_eq_index_mul_mass _ (Formalism.L2.G.Cmp.KA L) _ _ (Subgroup.comap_mono hUK)
    (hrel.trans_ne hidx_ne) hm (by
      intro x γ hγ hx
      obtain ⟨δ, rfl⟩ := Formalism.L2.G.Cmp.exists_ratA γ hγ
      rw [Formalism.L2.G.Triv.trivStabU L hp hne x δ hx, map_one])
  refine ⟨M, hM, hu, ?_⟩
  rw [Nat.card_eq_of_bijective _ L.y_bij]
  exact h.trans (congrArg (· * Formalism.HermitianLatticesTheory.mass (sp.X 0).hT M)
    ((congrArg (fun n : ℕ => (n : ℝ)) hrel).trans hi))

open Formalism.MainNotions.StandardLattice in
theorem classNumber_all (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv := by
  let := D.host.cmStar
  intro _ hg u hT
  obtain ⟨M, hM, hu, h⟩ := classNumber_residue (Lv u) D.host.g_prime D.host.g_ne
    (fun N hN => ⟨hN.1, hN.2.1, fun v => SelfDualFrame.exists_frame D N v hN⟩)
    (GlobalTheory.T.selfDualLattice_over_columnBaseLattice D Lv u hT)
  rw [LevelIndex.auxiliaryIndex_of_split (D.host.g_prime 0) D.R.k (hg 0).1 (hg 0).2,
    LevelIndex.auxiliaryIndex_of_split (D.host.g_prime 1) D.R.k (hg 1).1 (hg 1).2,
    hT.1, mass_selfDualLattice_firstSpace_eq D M hM hu] at h
  rw [h, idxPi]
  ring

end GlobalTheory.ColClassNumber

end
