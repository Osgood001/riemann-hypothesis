module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree

@[expose] public section

theorem UpperTheory.V.Pr.globProp : UpperTheory.V.Pr.GlobProp := by
  intro X _ _ M hM
  classical
  -- Group components according to whether they are already known to be good.
  let locus (P : Set X → Prop) := ⋃ Y ∈ {Y | M.CompI Y ∧ P Y}, Y
  have mem_locus {P : Set X → Prop} {x : X} :
      x ∈ locus P ↔ ∃ Y, (M.CompI Y ∧ P Y) ∧ x ∈ Y := by
    simp only [locus, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  have closed_locus (P : Set X → Prop) : IsClosed (locus P) :=
    ((TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)).subset
      (t := {Y | M.CompI Y ∧ P Y}) (fun _ h => h.1.1)).isClosed_biUnion
        (fun Y hY => isClosed_of_mem_irreducibleComponents Y hY.1.1)
  have meets_locus {P : Set X → Prop} {Y : Set X} (hY : M.CompI Y) (hP : P Y) :
      (M.Core ∩ locus P).Nonempty := by
    obtain ⟨x, hx, hc⟩ := hM.meets Y hY
    exact ⟨x, hc, mem_locus.mpr ⟨Y, ⟨hY, hP⟩, hx⟩⟩
  let good := fun Y : Set X => Y ⊆ M.Good
  let bad := fun Y : Set X => ¬good Y
  have cover : M.Core ⊆ locus good ∪ locus bad := by
    refine hM.dense.trans (((closed_locus good).union (closed_locus bad)).closure_subset_iff.mpr ?_)
    intro x hx
    obtain ⟨Y, hY, hxY⟩ := hM.off x hx
    by_cases hg : good Y
    · exact Or.inl (mem_locus.mpr ⟨Y, ⟨hY, hg⟩, hxY⟩)
    · exact Or.inr (mem_locus.mpr ⟨Y, ⟨hY, hg⟩, hxY⟩)
  intro x hx
  let Y := irreducibleComponent x
  have hY : M.CompI Y :=
    ⟨irreducibleComponent_mem_irreducibleComponents x, ⟨x, mem_irreducibleComponent, hx⟩⟩
  suffices hg : good Y from hg mem_irreducibleComponent
  by_contra hbad
  obtain ⟨S, hS, hs⟩ := hM.seed
  obtain ⟨p, hp, hpg, hpb⟩ := isPreconnected_closed_iff.mp hM.conn _ _
    (closed_locus good) (closed_locus bad) cover (meets_locus hS hs) (meets_locus hY hbad)
  -- A point common to both sides yields a closed point where goodness transfers.
  obtain ⟨z, ⟨hzg, hzb⟩, hz⟩ := hM.jac _ ((closed_locus good).inter (closed_locus bad)) ⟨p, ⟨hpg, hpb⟩, hp⟩
  obtain ⟨G, ⟨hG, hg⟩, hzG⟩ := mem_locus.mp hzg
  obtain ⟨B, ⟨hB, hb⟩, hzB⟩ := mem_locus.mp hzb
  exact hb (hM.loc z hz G B hG hB hzG hzB hg)
