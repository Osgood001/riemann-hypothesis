module
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsTateTwistSectionsEquivLocallyConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement

@[expose] public section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace UpperTheory

/-- Tate sections vanish if the coefficient modulus belongs to every maximal ideal. -/
theorem subsingleton_tate_sections_of_mem_maximal (q : ℕ) (i : ℤ) (A : Type) [CommRing A]
    (hq : ∀ m : Ideal A, m.IsMaximal → (q : A) ∈ m) :
    Subsingleton (Sec (tw q i) (Spec (CommRingCat.of A))) := by
  classical
  let X := Spec (CommRingCat.of A)
  have zero (s : Sec (tw q i) X) : s = 0 := by
    let P (V : Scheme) (g : V ⟶ X) := Sec.res g s = 0 ∨ IsUnit (q : Γ(V, ⊤))
    have res_comp {V W : Scheme} (g : V ⟶ X) (k : W ⟶ V) :
        Sec.res (k ≫ g) s = Sec.res k (Sec.res g s) := by simp [Sec.res]
    have hloc : Loc X P := by
      apply GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 _ _ _
        ((GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q) (Scheme.Γ ⋙ twF q i)).1 X s)
      rintro V g ⟨t, ht⟩
      by_cases h : IsUnit (q : Γ(V, ⊤))
      · exact Or.inr h
      · left
        have : IsEmpty (Prim q Γ(V, ⊤)) := ⟨fun ζ => h ζ.2.1⟩
        obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q i Γ(V, ⊤)) t
        have hu : u = 0 := Subsingleton.elim _ _
        refine ht.symm.trans ?_
        rw [hu, Submodule.Quotient.mk_zero]
        exact map_zero _
    have hpts := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover X P (by
      intro V W g k hp
      rcases hp with hz | hu
      · left; rw [res_comp, hz]; exact map_zero _
      · right; simpa using hu.map k.appTop.hom)).1 hloc
    apply (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.2.2.2.2.1
      (ZMod q) (tw q i).obj (tw q i).property X s
    apply (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover X (fun _ g => Sec.res g s = 0) (by
      intro V W g k h; rw [res_comp, h]; exact map_zero _)).2
    intro x
    obtain ⟨m, hm, hxm⟩ := Ideal.exists_le_maximal x.asIdeal x.isPrime.ne_top
    let y : PrimeSpectrum A := ⟨m, hm.isPrime⟩
    obtain ⟨V, g, hV, hg, hy, h⟩ := hpts y
    have hx : x ∈ Set.range g :=
      ((PrimeSpectrum.le_iff_specializes x y).1 hxm).mem_open g.isOpenMap.isOpen_range hy
    refine ⟨V, g, hV, hg, hx, h.resolve_right fun hu => ?_⟩
    have hv : g ⁻¹ᵁ X.basicOpen (q : Γ(X, ⊤)) = ⊤ := by
      rw [Scheme.preimage_basicOpen_top]
      simpa using V.basicOpen_of_isUnit hu
    obtain ⟨v, hvy⟩ := hy
    have hyq : y ∈ X.basicOpen (q : Γ(X, ⊤)) := by
      rw [← hvy]
      change v ∈ g ⁻¹ᵁ X.basicOpen (q : Γ(X, ⊤))
      rw [hv]; trivial
    change y ∈ (Spec (CommRingCat.of A)).basicOpen (q : Γ(Spec (CommRingCat.of A), ⊤)) at hyq
    rw [basicOpen_eq_of_affine'] at hyq
    exact hyq (by simpa using hq m hm)
  exact ⟨fun x y => (zero x).trans (zero y).symm⟩

/-- Over a local base, integrality puts a nonunit modulus in every maximal ideal. -/
theorem subsingleton_tate_H0_of_not_isUnit (q : ℕ) (i : ℤ) (O A : Type) [CommRing O] [IsLocalRing O]
    [CommRing A] [Algebra O A] [Algebra.IsIntegral O A] (hq : ¬ IsUnit (q : O)) :
    Subsingleton (Ht q (sp A) 0 i) := by
  have := subsingleton_tate_sections_of_mem_maximal q i A fun m hm => by
    have h := IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) m)
    have hm' : (q : O) ∈ m.under O := by rw [h]; exact hq
    simpa only [Ideal.under, Ideal.mem_comap, map_natCast] using hm'
  obtain ⟨_, e, _⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)
  exact (e _).symm.injective.subsingleton

end UpperTheory
