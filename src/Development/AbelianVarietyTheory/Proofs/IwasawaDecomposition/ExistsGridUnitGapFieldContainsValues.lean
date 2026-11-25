module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridIntegralGenerator
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaLiftGridDataUnitGapAllStatesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbeddingFixedFieldOfLeComplexImageStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem grid_fieldHas_all : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => Nonempty (GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩) ∧ ∀ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) := by
  intro cDep
  have h := GlobalTheory.T.nonempty_thetaLiftGridData_unit_gap_all_states cDep
  refine EvG.imp h (fun K _ _ _ _ hK => ?_)
  obtain ⟨S₁, P₁, A, S₂, a1, a2, hh⟩ := hK
  let M (P : Pre) := GridField.uniformGridField P ⟨1, cDep, K.s.b⟩
  choose S hSa _ hS using fun B₀ => GridField.exists_minimal_grid_tests B₀ ⟨1, cDep, K.s.b⟩
  refine ⟨fun B f F => S₁ B f F ∪ S B, P₁, A, S₂, ?_, a2, ?_⟩
  · intro B f F z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [a1 B f F z hz, ((hSa B z hz).tower_top : IsIntegral ℚ z).isAlgebraic]
  · intro B f T hO hH hP hA hk hF htriv w hw P x
    have hH' : Has₂ B (S₁ B.toPre f B.KsC) (S₂ B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    refine ⟨hh B f T hO hH' hP hA hk hF htriv w hw P x, fun G => ?_⟩
    have hle : M B.toPre ≤ B.fixedCoefficientFieldInComplex := (hS B.toPre _).2 (fun z hz => hH.1 z (Finset.mem_union_right _ hz))
    obtain ⟨j, hj⟩ := GlobalTheory.T.exists_ringHom_LL0_of_le_fixedCoefficientField (w.st x.o.Z) (M B.toPre) hle
    apply GlobalTheory.BigTop.Fun.FieldHas.map j
    rw [hj]
    exact GridField.uniformGridField_has (X := w.st x.o.Z) G

theorem exists_grid_fieldHas : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) := by
  intro cDep
  refine StepW.trans (grid_fieldHas_all cDep) (StepW.of_all ?_)
  intro K B f T w _ _ h P x
  obtain ⟨⟨G⟩, hG⟩ := h P x
  exact ⟨G, hG G⟩

end GlobalTheory.HeightCounting.Up
