import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG valR lbPow LBIso)
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open GlobalTheory.QCoh.Qcqs GlobalTheory.ProjSpace GlobalTheory.Points

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.TuplePoint

variable {L : Type} [Field L] {X Y : Scheme.{0}}

theorem le_preimage_of_mem (η : Sp L ⟶ X) [IsDominant η] {W : X.Opens} {x : X} (hx : x ∈ W) :
    ⊤ ≤ η ⁻¹ᵁ W := by
  obtain ⟨q, hq⟩ := η.denseRange.exists_mem_open W.isOpen ⟨x, hx⟩
  intro p _
  obtain rfl : p = q := Subsingleton.elim (α := PrimeSpectrum L) p q
  exact hq

theorem ext_of_dense (η : Sp L ⟶ X) [IsDominant η] [IsReduced X] {W : X.Opens} {s s' : Γ(X, W)}
    (h : ⊤ ≤ η ⁻¹ᵁ W → valR η W s = valR η W s') : s = s' := by
  have key : X.basicOpen (s - s') = ⊥ := by
    by_contra hne
    obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne
    have hW : ⊤ ≤ η ⁻¹ᵁ W := le_preimage_of_mem η (X.basicOpen_le _ hy)
    have hB := le_preimage_of_mem η hy
    rw [le_preimage_basicOpen_iff η hW, sub_eq_add_neg, valR_add η W hW, valR_neg η W hW, h hW,
      add_neg_cancel] at hB
    exact not_isUnit_zero hB
  exact sub_eq_zero.mp ((basicOpen_eq_bot_iff _).mp key)

theorem valMap_injective (η : Sp L ⟶ X) [IsDominant η] [IsReduced X] {W : X.Opens}
    (h : ⊤ ≤ η ⁻¹ᵁ W) : Function.Injective (valMap η W h).hom := by
  intro s s' hss
  exact ext_of_dense η fun _ => by rw [valR_eq η W h, valR_eq η W h]; exact hss

variable {o : Type} [CommRing o] [Algebra o L]

theorem valMap_baseRingHom {η : Sp L ⟶ X} {f : X ⟶ Sp o} (hf : η ≫ f = spMap (algebraMap o L))
    {W : X.Opens} (h : ⊤ ≤ η ⁻¹ᵁ W) (a : o) :
    (valMap η W h).hom ((baseRingHom f W).hom a) = algebraMap o L a := by
  rw [← valR_eq η W h]
  exact valR_constFn_of_over f (algebraMap o L) η hf W h a

theorem valMap_eval₂Hom {σ : Type*} {η : Sp L ⟶ X} {f : X ⟶ Sp o}
    (hf : η ≫ f = spMap (algebraMap o L)) {W : X.Opens} (h : ⊤ ≤ η ⁻¹ᵁ W) (u : σ → Γ(X, W))
    (p : MvPolynomial σ o) :
    (valMap η W h).hom (eval₂Hom (baseRingHom f W).hom u p) =
      aeval (fun k => valR η W (u k)) p := by
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.aeval_def]
  have hc : (valMap η W h).hom.comp (baseRingHom f W).hom = algebraMap o L :=
    RingHom.ext (valMap_baseRingHom hf h)
  have hv : (fun k => (valMap η W h).hom (u k)) = fun k => valR η W (u k) :=
    funext fun k => (valR_eq η W h (u k)).symm
  rw [hc, hv, MvPolynomial.coe_eval₂Hom]

variable {r M : ℕ}

theorem map_irrelevant_eq_top (o : Type) [CommRing o] [Algebra o L] {t : Fin (r + 1) → L}
    (ht : t ≠ 0) : (HomogeneousIdeal.irrelevant (grading o r)).toIdeal.map
      (aeval (R := o) t).toRingHom = ⊤ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (X_mem o r i))) ?_
  simpa using hi

def point (o : Type) [CommRing o] [Algebra o L] (t : Fin (r + 1) → L) (ht : t ≠ 0) :
    Sp L ⟶ PSpace o r :=
  ProjPoint.ofHom (grading o r) (aeval (R := o) t).toRingHom (map_irrelevant_eq_top o ht)

variable {t : Fin (r + 1) → L} {ht : t ≠ 0}

@[reassoc]
theorem point_str : point o t ht ≫ PSpace.str o r = spMap (algebraMap o L) := by
  simp only [point, PSpace.str, spMap, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext a
  simp

theorem le_point_preimage_iff (i : Fin (r + 1)) :
    ⊤ ≤ point o t ht ⁻¹ᵁ chart o r i ↔ t i ≠ 0 := by
  rw [point, ProjPoint.ofHom_preimage_basicOpen _ _ _ Nat.one_pos (X_mem o r i)]
  show (⊤ : Opens (PrimeSpectrum L)) ≤ PrimeSpectrum.basicOpen ((aeval t).toRingHom (X i)) ↔ _
  constructor
  · intro hle h0
    have hm := hle (show (default : PrimeSpectrum L) ∈ (⊤ : Opens (PrimeSpectrum L)) from trivial)
    rw [PrimeSpectrum.mem_basicOpen] at hm
    apply hm
    simp [h0]
  · intro h1 p _
    rw [PrimeSpectrum.mem_basicOpen, Ideal.eq_bot_of_prime p.asIdeal]
    simpa using h1

theorem valR_point_ratio {i : Fin (r + 1)} (hi : t i ≠ 0) (j : Fin (r + 1)) :
    valR (point o t ht) (chart o r i) (ratio o r i j) = t j / t i := by
  have hu : IsUnit ((aeval t).toRingHom (X i : MvPolynomial (Fin (r + 1)) o)) := by simpa using hi
  have hpre : ⊤ ≤ Proj.awayι (grading o r) (X i) (X_mem o r i) Nat.one_pos ⁻¹ᵁ chart o r i := by
    have e1 := Scheme.Hom.preimage_opensRange
      (Proj.awayι (grading o r) (X i) (X_mem o r i) Nat.one_pos)
    rw [Proj.opensRange_awayι] at e1
    exact e1.ge
  have hmem : (X j : MvPolynomial (Fin (r + 1)) o) ∈ grading o r (1 • 1) := by
    simpa using X_mem o r j
  have hA : ratio o r i j = (Proj.awayToSection (grading o r) (X i)).hom
      (HomogeneousLocalization.Away.mk (grading o r) (X_mem o r i) 1 (X j) hmem) := by
    rw [ProjFrac.awayToSection_mk]
    exact ProjFrac.frac_eq (by ring)
  have key : Proj.awayToSection (grading o r) (X i) ≫
      (Proj.awayι (grading o r) (X i) (X_mem o r i) Nat.one_pos).appLE (chart o r i) ⊤ hpre =
      (Scheme.ΓSpecIso _).inv := by
    set A := Proj.awayι (grading o r) (X i) (X_mem o r i) Nat.one_pos
    set e := Proj.basicOpenIsoSpec (grading o r) (X i) (X_mem o r i) Nat.one_pos
    have : IsIso (Proj.awayToSection (grading o r) (X i)) :=
      (Proj.basicOpenIsoAway (grading o r) (X i) (X_mem o r i) Nat.one_pos).isIso_hom
    have hι : e.hom ≫ A = (chart o r i).ι := by
      exact Iso.hom_inv_id_assoc e _
    have gen : ∀ (g : (chart o r i).toScheme ⟶ Proj (grading o r)) (_ : e.hom ≫ A = g)
        (hle : ⊤ ≤ g ⁻¹ᵁ chart o r i),
        g.appLE (chart o r i) ⊤ hle = A.appLE (chart o r i) ⊤ hpre ≫ e.hom.appLE ⊤ ⊤ le_rfl := by
      rintro g rfl hle
      exact (Scheme.Hom.appLE_comp_appLE e.hom A (chart o r i) ⊤ ⊤ hpre _).symm
    have h1 := gen _ hι (chart o r i).ι_preimage_self.ge
    have F1 : e.hom.appLE ⊤ ⊤ le_rfl = (Scheme.ΓSpecIso _).hom ≫
        Proj.awayToSection (grading o r) (X i) ≫ (chart o r i).topIso.inv := by
      rw [← Proj.basicOpenToSpec_app_top]
      rfl
    have F2 : (chart o r i).ι.appLE (chart o r i) ⊤ (chart o r i).ι_preimage_self.ge =
        (chart o r i).topIso.inv := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    rw [F2, F1] at h1
    have h3 : A.appLE (chart o r i) ⊤ hpre ≫ (Scheme.ΓSpecIso _).hom ≫
        Proj.awayToSection (grading o r) (X i) = 𝟙 _ := by
      rw [← cancel_mono (chart o r i).topIso.inv, Category.id_comp, Category.assoc, Category.assoc]
      exact h1.symm
    rw [← cancel_mono ((Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (grading o r) (X i)),
      Category.assoc, h3, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [point, ProjPoint.ofHom_eq_awayι _ _ _ Nat.one_pos (X_mem o r i) hu,
    ← valR_appLE _ _ hpre (le_preimage_top _), hA, ← CommRingCat.comp_apply, key, valR_specMap]
  apply eq_div_of_mul_eq hi
  simpa using ProjPoint.awayLift_mk_mul (grading o r) ((aeval t).toRingHom) hu (X_mem o r i) 1 (X j) hmem


theorem range_valMap_point {i : Fin (r + 1)} (h : ⊤ ≤ point o t ht ⁻¹ᵁ chart o r i) :
    Set.range (valMap (point o t ht) _ h).hom =
      Algebra.adjoin o (Set.range fun k => t k / t i) := by
  have hi : t i ≠ 0 := (le_point_preimage_iff i).mp h
  have hc : ∀ a : o, (valMap (point o t ht) _ h).hom (algebraMap o Γ(PSpace o r, chart o r i) a) =
      algebraMap o L a :=
    valMap_baseRingHom point_str h
  have hr : ∀ k, (valMap (point o t ht) _ h).hom (ratio o r i k) = t k / t i := fun k => by
    rw [← valR_eq, valR_point_ratio hi]
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨p, rfl⟩ := (chartAlgEquiv o r i).surjective f
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, hc]
      exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq =>
      rw [map_add, map_add]
      exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, map_mul, chartAlgEquiv_X, hr]
      exact mul_mem hp (Algebra.subset_adjoin ⟨j.1, rfl⟩)
  · intro hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨ratio o r i k, hr k⟩
    | algebraMap a => exact ⟨_, hc a⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨g, rfl⟩ := hy
      exact ⟨f + g, map_add _ f g⟩
    | mul x y _ _ hx hy =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨g, rfl⟩ := hy
      exact ⟨f * g, map_mul _ f g⟩

section

variable {η : Sp L ⟶ X} {π : X ⟶ PSpace o r} (hπ : η ≫ π = point o t ht)

include hπ

theorem ne_zero_of_le {W : X.Opens} (hW : ⊤ ≤ η ⁻¹ᵁ W) {i : Fin (r + 1)}
    (hi : W ≤ π ⁻¹ᵁ chart o r i) : t i ≠ 0 := by
  have key := le_preimage_comp η π hi hW
  rw [hπ, le_point_preimage_iff] at key
  exact key

theorem le_preimage_chart {i : Fin (r + 1)} (hi : t i ≠ 0) : ⊤ ≤ η ⁻¹ᵁ (π ⁻¹ᵁ chart o r i) := by
  have key := (le_point_preimage_iff (o := o) (ht := ht) i).mpr hi
  rw [← hπ] at key
  exact key

theorem valR_pullRatio {W : X.Opens} (hW : ⊤ ≤ η ⁻¹ᵁ W) {i : Fin (r + 1)}
    (hi : W ≤ π ⁻¹ᵁ chart o r i) (j : Fin (r + 1)) :
    valR η W (pullRatio π W i hi j) = t j / t i := by
  rw [pullRatio, valR_appLE η π hi hW, hπ, valR_point_ratio (ne_zero_of_le hπ hW hi)]

end



section Units

variable (η : Sp L ⟶ X) {U V : X.Opens}







end Units



end GlobalTheory.TuplePoint
