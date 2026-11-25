module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSections
public import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoNearOrCentreMeetsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenIntegralOfSmoothOverFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupportStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictOfClosedImmersionNearGenericStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrictStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSncComponentClosureCharZeroStatement

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.WeakRes

theorem isProjOver_comp_closed {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X' ⟶ X) [IsClosedImmersion g]
    {f : X ⟶ Sp R} (hf : IsProjOver f) : IsProjOver (g ≫ f) := by
  obtain ⟨M, k, hk, rfl⟩ := hf
  exact ⟨M, g ≫ k, inferInstance, by simp⟩

theorem isProjOver_seq {F : Type} [Field F] {Y Y' : Scheme.{0}} (f : Y ⟶ Sp F) {B : Set Y} {s : Y' ⟶ Y}
    (h : IsSmoothBlowupSeq f B s) (hf : IsProjOver f) : IsProjOver (s ≫ f) := by
  induction h with
  | id => simpa using hf
  | @step Y₁ Y₂ s J π _ _ _ hb ih =>
    obtain ⟨X', b, hb', hproj, -⟩ := ProjBlowup.exists_blowup (s ≫ f) ih J
    obtain ⟨e, he, heb⟩ := ProjBlowup.exists_iso_of_blowup J π b hb hb'
    rw [← heb, Category.assoc]
    exact isProjOver_comp_closed e hproj

open GlobalTheory

private theorem relDim_zero_generic {F : Type} [Field F] {A : Scheme.{0}} [IsIntegral A] (f : A ⟶ Sp F)
    (hf : SmoothOfRelativeDimension 0 f) (y : A) : y = genericPoint A := by
  have : Smooth f := hf.smooth
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  have hdim := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth f 0 hf
  have : IsLocallyArtinian A := .of_topologicalKrullDim_le_zero (by simpa using hdim.le)
  exact (specializes_iff_eq.1 (genericPoint_specializes y)).symm

private theorem preimage_over_iso {Y A : Scheme.{0}} (s : Y ⟶ A) {y : A} (U : A.Opens)
    (hy : y ∈ U) (hs : IsIso (s ∣_ U)) : ∃ x, s x = y := by
  obtain ⟨x, hx⟩ := (s ∣_ U).homeomorph.surjective ⟨y, hy⟩
  exact ⟨x.1, (morphismRestrict_base_coe s U x).symm.trans (congrArg Subtype.val hx)⟩

/-- A component over the generic point of an integral closed image dominates that image. -/
private theorem exists_component_over_generic {W A Y : Scheme.{0}} [IsIntegral W] (i : W ⟶ A) (s : Y ⟶ A)
    {ι : Type} (z : ι → Y) (h : s ⁻¹' Set.range i = ⋃ a, closure ({z a} : Set Y))
    {x : Y} (hx : s x = i (genericPoint W)) :
    ∃ a, s (z a) = i (genericPoint W) ∧
      ∀ y ∈ closure ({z a} : Set Y), s y ∈ Set.range i := by
  have hx' : x ∈ s ⁻¹' Set.range i := ⟨genericPoint W, hx.symm⟩
  rw [h] at hx'
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx'
  have hsupp : ∀ y ∈ closure ({z a} : Set Y), s y ∈ Set.range i := by
    intro y hy
    change y ∈ s ⁻¹' Set.range i
    rw [h]
    exact Set.mem_iUnion.2 ⟨a, hy⟩
  obtain ⟨w, hw⟩ := hsupp (z a) (subset_closure (Set.mem_singleton _))
  refine ⟨a, ?_, hsupp⟩
  have h₁ : s (z a) ⤳ i (genericPoint W) := hx ▸ (specializes_iff_mem_closure.2 ha).map s.continuous
  have h₂ : i (genericPoint W) ⤳ s (z a) := hw ▸ (genericPoint_specializes w).map i.continuous
  exact (h₁.antisymm h₂).eq

private theorem resolve_from_smooth_subscheme {F : Type} [Field F] (W : Scheme.{0}) [IsIntegral W]
    (p : W ⟶ Sp F) (n : ℕ) (hdim : topologicalKrullDim W = n)
    {A Y Z : Scheme.{0}} (f : A ⟶ Sp F) [LocallyOfFiniteType f]
    (i : W ⟶ A) [IsClosedImmersion i] (hif : i ≫ f = p)
    (s : Y ⟶ A) (hproj : IsProjOver (s ≫ f)) (c : Z ⟶ Y) [IsClosedImmersion c]
    (hsm : Smooth (c ≫ s ≫ f)) (U : A.Opens) (hU : i (genericPoint W) ∈ U) (hiso : IsIso (s ∣_ U))
    (hg : ∀ z, (c ≫ s) z ∈ i.ker.support) (z : Z) (hz : (c ≫ s) z = i (genericPoint W)) :
    ∃ (W' : Scheme.{0}) (h : W' ⟶ W) (V : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (h ≫ p) ∧
      IsProjOver (h ≫ p) ∧ (V : Set W).Nonempty ∧ IsIso (h ∣_ V) := by
  obtain ⟨W', j, _, _, hW', w', rfl⟩ :=
    GlobalTheory.T.exists_clopen_integral_of_smooth_over_field' F Z (c ≫ s ≫ f) hsm z
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support i (j ≫ c ≫ s) (fun t => hg (j t))
  have hw' : h w' = genericPoint W := by
    apply i.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hh]
    exact hz
  obtain ⟨V, hV, hV'⟩ := GlobalTheory.T.exists_nonempty_isIso_restrict_of_generic_mem i h (j ≫ c) s U hiso
    (by rw [hh]; simp) hU ⟨w', hw'⟩
  have hq : h ≫ p = j ≫ c ≫ s ≫ f := by rw [← hif, reassoc_of% hh]
  have hpft : LocallyOfFiniteType p := by rw [← hif]; infer_instance
  have hd := GlobalTheory.T.topologicalKrullDim_eq_of_isIso_restrict' F W W' p (h ≫ p) h hpft
    (by rw [hq]; infer_instance) rfl V hV hV'
  refine ⟨W', h, V, hW', ?_, ?_, hV, hV'⟩
  · rw [hq]
    exact GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq F W' _ n inferInstance (hd.trans hdim)
  · rw [hq, ← Category.assoc]
    exact isProjOver_comp_closed _ hproj

/-- Resolve an integral projective scheme using only its given smooth projective ambient space and defining ideal.
If the blowups are already isomorphisms near its generic point, the SNC output gives a smooth
component above that point; otherwise one of the smooth blowup centres does. -/
theorem weak_resolution_at_embedding (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W]
    (p : W ⟶ Sp F) (n : ℕ) (hdim : topologicalKrullDim W = n)
    (A : Scheme.{0}) [IsIntegral A] (f : A ⟶ Sp F) (N : ℕ)
    (hf : IsProjOver f) (hdf : SmoothOfRelativeDimension N f)
    (i : W ⟶ A) [IsClosedImmersion i] (hif : i ≫ f = p)
    (hP : ¬ Smooth p → i.ker ≠ ⊥ → ∃ (Y : Scheme.{0}) (s : Y ⟶ A),
      IsIntegral Y ∧ SmoothOfRelativeDimension N (s ≫ f) ∧
      IsSmoothBlowupSeq f (i.ker.support : Set A) s ∧
      FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (i.ker.comap s).support)) :
    ∃ (W' : Scheme.{0}) (h : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (h ≫ p) ∧
      IsProjOver (h ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (h ∣_ U) := by
  have : Smooth f := hdf.smooth
  have hi : (i.ker.support : Set A) = Set.range i := by
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  by_cases hsm : Smooth p
  · refine ⟨W, 𝟙 W, ⊤, inferInstance, ?_, ?_, ⟨genericPoint W, Set.mem_univ _⟩, inferInstance⟩
    · simpa using GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq F W p n hsm hdim
    · simpa [← hif] using isProjOver_comp_closed i hf
  have hη : genericPoint A ∉ Set.range i := by
    intro h
    have : Surjective i := ⟨fun y => (genericPoint_specializes y).mem_closed i.isClosedEmbedding.isClosed_range h⟩
    have : IsIso i := isIso_of_isClosedImmersion_of_surjective i
    apply hsm
    rw [← hif]
    infer_instance
  have hne : i.ker ≠ ⊥ := fun he => hη (hi ▸ he ▸ Set.mem_univ _)
  cases N with
  | zero => exact (hη ⟨genericPoint W, relDim_zero_generic f hdf _⟩).elim
  | succ e =>
    obtain ⟨Y, s, hY, hsd, hseq, hsnc⟩ := hP hsm hne
    rcases GlobalTheory.T.isIso_restrict_or_exists_smooth_blowup_centre_over f _ (i (genericPoint W)) s hseq with
      ⟨U, hU, hiso⟩ | ⟨Y₁, s₁, J, U, y₁, hseq₁, hsm, hJB, hU, hiso, hy₁, hs₁⟩
    · have hpY := isProjOver_seq f hseq hf
      obtain ⟨r, z, -, -, hcov, -, hL⟩ := GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points F Y
        (s ≫ f) (e + 1) hpY hsd (i.ker.comap s).support hsnc
      have h : s ⁻¹' Set.range i = ⋃ a, closure ({z a} : Set Y) := by
        rwa [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hi] at hcov
      obtain ⟨x, hx⟩ := preimage_over_iso s U hU hiso
      obtain ⟨a, ha, hsupp⟩ := exists_component_over_generic i s z h hx
      have hcomp := GlobalTheory.T.smooth_snc_component_closure_charZero F Y (s ≫ f) e hpY hsd r z hL a
      have hrange : Set.range (Mix.closι (z a)) = closure ({z a} : Set Y) := by
        change Set.range (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})).subschemeι = _
        rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl
      obtain ⟨w, hw⟩ : z a ∈ Set.range (Mix.closι (z a)) := hrange ▸ subset_closure (Set.mem_singleton _)
      refine resolve_from_smooth_subscheme W p n hdim f i hif s hpY (Mix.closι (z a)) hcomp.smooth U hU hiso
        (fun t => i.range_subset_ker_support (hsupp _ (hrange.le (Set.mem_range_self t)))) w ?_
      change s (Mix.closι (z a) w) = _
      rwa [hw]
    · obtain ⟨z, hz⟩ : ∃ z, J.subschemeι z = y₁ := by
        rw [← Set.mem_range, Scheme.IdealSheafData.range_subschemeι]; exact hy₁
      refine resolve_from_smooth_subscheme W p n hdim f i hif s₁
        (isProjOver_seq f hseq₁ hf) J.subschemeι hsm U hU hiso
        (fun t => hJB (Scheme.IdealSheafData.range_subschemeι J ▸ Set.mem_range_self t)) z ?_
      change s₁ (J.subschemeι z) = _
      rwa [hz]

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem weak_resolution : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W]
    (p : W ⟶ Sp F) (n : ℕ), IsProjOver p → topologicalKrullDim W = n →
    ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U) := by
  intro hP F _ _ W _ p n hp hdim
  obtain ⟨N, i, hi, hif⟩ := hp
  apply weak_resolution_at_embedding F W p n hdim (PSpace F N) (PSpace.str F N) N
    (ProjSpace.isProjOver_pspace_str F N) (Adelic.smoothOfRelativeDimension_pspace F N) i hif
  intro _ hne
  obtain ⟨Y, s, hY, hsd, -, hseq, -, -, hsnc⟩ := hP F N _ (PSpace.str F N) inferInstance
    (Adelic.smoothOfRelativeDimension_pspace F N) (ProjSpace.isProjOver_pspace_str F N) i.ker hne
  exact ⟨Y, s, hY, hsd, hseq, hsnc⟩

end GlobalTheory.WeakRes
