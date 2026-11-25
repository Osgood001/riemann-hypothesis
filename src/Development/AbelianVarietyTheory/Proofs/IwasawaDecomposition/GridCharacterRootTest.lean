module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridValuesFromOneReference
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SparseRootFieldTests

@[expose] public section
noncomputable section

open NumberField
open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.Host
open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.Mem
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GridInterpolation

/-- An original grid over a specified base: stage, level and grid are retained as evidence. -/
structure GridOver (P : Pre) (sc : Consts) where
  stage : Stages
  base_eq : stage.B.toPre = P
  indexType : Type
  level : LevCh stage.toD7 indexType
  grid : GridData level sc

/-- The prescribed field contains the original unramified character values of this grid. -/
abbrev GridOver.ValuesIn {P : Pre} {sc : Consts} (G : GridOver P sc) (F : IntermediateField ℚ ℂ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ G.stage.toD7.R.m → (G.grid.ch.chiH i).ValuesIn 0 F.val.toRingHom

/-- The grid's indexed character, transported to the common base field. -/
def GridOver.character {P : Pre} {sc : Consts} (G : GridOver P sc) (a : Fin P.R.m) : HChar P.host.E := by
  obtain ⟨X, rfl, T, L, G⟩ := G
  exact G.ch.chiH (a.val+1)

/-- One observable: two original grids, a common character index, and a finite
prime at which both characters are unramified. -/
structure GridRatioSample (P : Pre) (sc : Consts) where
  left : GridOver P sc
  right : GridOver P sc
  index : Fin P.R.m
  prime : IsDedekindDomain.HeightOneSpectrum (𝓞 P.host.E)
  left_unramified : (left.character index).UnrAt prime
  right_unramified : (right.character index).UnrAt prime

/-- The complex quotient of the two unramified values at the chosen prime. -/
def GridRatioSample.value {P : Pre} {sc : Consts} (s : GridRatioSample P sc) : ℂ :=
  ((s.left.character s.index).val s.prime : ℂ) / ((s.right.character s.index).val s.prime : ℂ)

private theorem same_infinity {P : Pre} {sc : Consts} (G J : GridOver P sc) (a : Fin P.R.m)
    (k : P.host.Eˣ) : (G.character a).inf k = (J.character a).inf k := by
  obtain ⟨X, rfl, T, L, G⟩ := G
  obtain ⟨Y, hY, U, H, J⟩ := J
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := X
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := Y
  change Q = P at hY
  subst Q
  exact Units.ext (((actual_specs G a).1 k).trans ((actual_specs J a).1 k).symm)

private theorem ratio_pow (Y : Stages) {sc : Consts} (s : GridRatioSample Y.B.toPre sc) :
    s.value ^ movingRayExponent Y.toD7 = 1 := by
  obtain ⟨⟨X, hX, T, L, G⟩, ⟨Z, hZ, V, H, J⟩, a, p, _, _⟩ := s
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := Y
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := X
  obtain ⟨⟨W⟩, _, _, _, _, _, _⟩ := Z
  change Q = P at hX
  change W = P at hZ
  subst Q W
  exact moving_ratio_pow G.pl.basePlace_over_qZero J.pl.basePlace_over_qZero (actual_specs G a) (actual_specs J a) p

/-- Field containment of all ratios can be tested away from any finite set. -/
private theorem ratios_off_iff {P : Pre} {sc : Consts} (F : IntermediateField ℚ ℂ)
    (bad : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 P.host.E))) :
    (∀ s : GridRatioSample P sc, s.prime ∉ bad → s.value ∈ F) ↔ ∀ s : GridRatioSample P sc, s.value ∈ F := by
  refine ⟨fun h s => ?_, fun h s _ => h s⟩
  apply ratio_mem_of_good_off _ _ (same_infinity s.left s.right s.index) bad F _ s.prime
  exact fun p hp hl hr => h ⟨s.left, s.right, s.index, p, hl, hr⟩ hp

private theorem gridOver_place_mem {P : Pre} {sc : Consts} (G : GridOver P sc)
    (F : IntermediateField ℚ ℂ) (h : G.ValuesIn F) (a : Fin P.R.m) (p) :
    ((G.character a).val p : ℂ) ∈ F := by
  obtain ⟨X, rfl, T, L, G⟩ := G
  exact local_mem_of_values ((lamOf G).chi a) F (h _ (by omega) a.isLt)
    (embPsi _) ((lamOf G).c a) (lamOf_hasInfQ G a) p (atFin p (unif p))

private theorem gridValues_of_all_place {P : Pre} {sc : Consts} (G : GridOver P sc)
    (F : IntermediateField ℚ ℂ) (h : ∀ (a : Fin P.R.m) (p), ((G.character a).val p : ℂ) ∈ F) :
    G.ValuesIn F := by
  obtain ⟨X, rfl, T, L, G⟩ := G
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := X
  intro i hi hm p _
  change i ≤ P.R.m at hm
  obtain ⟨a, rfl⟩ : ∃ a : Fin P.R.m, i = a.val+1 := ⟨⟨i-1, by omega⟩, by simp; omega⟩
  refine ⟨⟨(G.ch.chiH (a.val+1)).val p, ?_⟩, ?_⟩
  · exact h a p
  · simp [HChar.valTw]

/-- Once a reference's unramified values are known, all original values lie in the
field precisely when the ratios at jointly unramified primes do. -/
theorem all_ratios_iff_values {P : Pre} {sc : Consts} (J : GridOver P sc)
    (F : IntermediateField ℚ ℂ) (href : J.ValuesIn F) :
    (∀ s : GridRatioSample P sc, s.value ∈ F) ↔ ∀ G : GridOver P sc, G.ValuesIn F := by
  constructor
  · intro h G
    apply gridValues_of_all_place G F
    intro a p
    have hr := ratio_mem_of_good_off _ _ (same_infinity G J a) ∅ F
      (fun q _ hl hj => h ⟨G,J,a,q,hl,hj⟩) p
    simpa only [div_mul_cancel₀ _ (Units.ne_zero _)] using F.mul_mem hr (gridOver_place_mem J F href a p)
  · intro h s
    exact F.div_mem (gridOver_place_mem s.left F (h s.left) s.index s.prime)
      (gridOver_place_mem s.right F (h s.right) s.index s.prime)


private theorem powers_off_iff {P : Pre} {sc : Consts}
    (bad : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 P.host.E))) (m : ℕ) :
    (∀ s : GridRatioSample P sc, s.prime ∉ bad → s.value ^ m = 1) ↔ ∀ s : GridRatioSample P sc, s.value ^ m = 1 := by
  refine ⟨fun h s => ?_, fun h s _ => h s⟩
  have test := ratio_units_mem_of_good_off _ _ (same_infinity s.left s.right s.index) bad (rootsOfUnity m ℂ)
    (fun p hp h₁ h₂ => (mem_rootsOfUnity' m _).mpr (by
      simpa only [GridRatioSample.value, Units.val_div_eq_div_val] using h ⟨s.left,s.right,s.index,p,h₁,h₂⟩ hp)) s.prime
  simpa only [GridRatioSample.value, Units.val_div_eq_div_val] using (mem_rootsOfUnity' m _).mp test

/-- One root tests every reference and every prescribed field. Its order is the least
common annihilator of the actual ratios, not necessarily the least field conductor.
After any finite set of primes is excluded, at most one original observation per
distinct prime divisor of this order suffices, and their orders have LCM exactly that order. -/
theorem exists_ratio_samples_iff_all_grid_values (Y : Stages) (sc : Consts) :
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧ ∃ ζ : ℂ, IsPrimitiveRoot ζ e ∧
      (∀ m, e ∣ m ↔ ∀ s : GridRatioSample Y.B.toPre sc, s.value ^ m = 1) ∧
      (∀ (J : GridOver Y.B.toPre sc) (F : IntermediateField ℚ ℂ), J.ValuesIn F →
        (ζ ∈ F ↔ ∀ G : GridOver Y.B.toPre sc, G.ValuesIn F)) ∧
      ∀ bad : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 Y.B.toPre.host.E)),
        ∃ menu : Finset (GridRatioSample Y.B.toPre sc), menu.card ≤ e.primeFactors.card ∧
          menu.lcm (orderOf ∘ GridRatioSample.value) = e ∧ (∀ s ∈ menu, s.prime ∉ bad) ∧
          ∀ F : IntermediateField ℚ ℂ, (∀ s ∈ menu, s.value ∈ F) ↔ ζ ∈ F := by
  classical
  let S := Set.range (GridRatioSample.value (P := Y.B.toPre) (sc := sc))
  obtain ⟨e, he, hleast, _, _, _, _, ζ, hζ, hroot⟩ :=
    exists_sparse_root_field_tests S (NeZero.ne (movingRayExponent Y.toD7))
      (fun _ ⟨s, hs⟩ => hs ▸ ratio_pow Y s)
  have allRoots (F : IntermediateField ℚ ℂ) :
      ζ ∈ F ↔ ∀ s : GridRatioSample Y.B.toPre sc, s.value ∈ F :=
    (hroot F).1.trans Set.range_subset_iff
  have least m : e ∣ m ↔ ∀ s : GridRatioSample Y.B.toPre sc, s.value ^ m = 1 := by
    simpa only [S, Set.forall_mem_range] using hleast m
  refine ⟨e, he, ζ, hζ, least, fun J F hJ => (allRoots F).trans (all_ratios_iff_values J F hJ), fun bad => ?_⟩
  let A := {z : ℂ | ∃ s : GridRatioSample Y.B.toPre sc, s.prime ∉ bad ∧ s.value = z}
  have he0 := ne_zero_of_dvd_ne_zero (NeZero.ne _) he
  have bound : ∀ z ∈ A, z ^ e = 1 := by
    rintro _ ⟨s, _, rfl⟩
    exact (hleast e).mp dvd_rfl _ ⟨s,rfl⟩
  obtain ⟨d, hd, hdleast, T, hT, hc, hord, _, _, hTF⟩ := exists_sparse_root_field_tests A he0 bound
  have hde : d = e := Nat.dvd_antisymm hd <| (hleast d).mpr (by
    rintro _ ⟨s, rfl⟩
    exact (powers_off_iff bad d).mp
      (fun s hs => (hdleast d).mp dvd_rfl _ ⟨s, hs, rfl⟩) s)
  rw [hde] at hc hord
  choose pick hoff hval using fun z : T => hT z.property
  let menu := T.attach.image pick
  have him : menu.image GridRatioSample.value = T := by
    ext z
    constructor
    · rintro hz
      obtain ⟨_, hs, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
      exact hval i ▸ i.property
    · intro hz
      exact Finset.mem_image.mpr ⟨pick ⟨z,hz⟩, Finset.mem_image_of_mem _ (T.mem_attach _), hval _⟩
  refine ⟨menu, (Finset.card_image_le.trans_eq Finset.card_attach).trans hc, ?_, ?_, fun F => ?_⟩
  · calc menu.lcm (orderOf ∘ GridRatioSample.value) = (menu.image GridRatioSample.value).lcm orderOf :=
           (Finset.lcm_image (f := orderOf) menu).symm
         _ = e := by rw [him]; exact hord
  · rintro _ hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact hoff i
  · have retained : (∀ s ∈ menu, s.value ∈ F) ↔ (T : Set ℂ) ⊆ F := by
      rw [← him]
      simp only [Finset.coe_image, Set.image_subset_iff]; rfl
    have outside : A ⊆ F ↔ ∀ s : GridRatioSample Y.B.toPre sc, s.prime ∉ bad → s.value ∈ F :=
      ⟨fun h s hs => h ⟨s,hs,rfl⟩, fun h _ ⟨s,hs,heq⟩ => heq ▸ h s hs⟩
    exact retained.trans <| (hTF F).2.trans <| outside.trans <| (ratios_off_iff F bad).trans (allRoots F).symm

/-- A single root of unity tests all original grids at these base data and parameters.
The root is chosen before the reference grid and the prescribed field. For a field already containing
the reference's unramified values, membership of the root is equivalent to containing
every grid's unramified values. Its order divides the common ray
exponent; this need not be the least possible conductor. -/
theorem exists_root_iff_all_grid_values_uniform (Y : Stages) (sc : Consts) :
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧ ∃ ζ : ℂ, IsPrimitiveRoot ζ e ∧
      ∀ (Z : Stages), Z.B.toPre = Y.B.toPre → ∀ (V : Type) (H : LevCh Z.toD7 V)
        (G₀ : GridData H sc) (F : IntermediateField ℚ ℂ),
        (∀ i, 1 ≤ i → i ≤ Z.toD7.R.m → (G₀.ch.chiH i).ValuesIn 0 F.val.toRingHom) →
        (ζ ∈ F ↔ ∀ (X : Stages), X.B.toPre = Y.B.toPre → ∀ (T : Type) (L : LevCh X.toD7 T)
          (G : GridData L sc) (i : ℕ), 1 ≤ i → i ≤ X.toD7.R.m → (G.ch.chiH i).ValuesIn 0 F.val.toRingHom) := by
  obtain ⟨e, he, ζ, hζ, _, h, _⟩ := exists_ratio_samples_iff_all_grid_values Y sc
  refine ⟨e, he, ζ, hζ, fun Z hZ V H J F href => ?_⟩
  exact (h ⟨Z,hZ,V,H,J⟩ F href).trans ⟨fun hg X hX T L G => hg ⟨X,hX,T,L,G⟩,
    fun hall G => hall G.stage G.base_eq G.indexType G.level G.grid⟩

/-- Specialize the uniform test to a given original reference grid. -/
theorem exists_root_iff_all_grid_values {Y : Stages} {U : Type} {L₀ : LevCh Y.toD7 U} {sc : Consts}
    (G₀ : GridData L₀ sc) :
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧ ∃ ζ : ℂ, IsPrimitiveRoot ζ e ∧
      ∀ F : IntermediateField ℚ ℂ,
        (∀ i, 1 ≤ i → i ≤ Y.toD7.R.m → (G₀.ch.chiH i).ValuesIn 0 F.val.toRingHom) →
        (ζ ∈ F ↔ ∀ (X : Stages), X.B.toPre = Y.B.toPre → ∀ (T : Type) (L : LevCh X.toD7 T)
          (G : GridData L sc) (i : ℕ), 1 ≤ i → i ≤ X.toD7.R.m → (G.ch.chiH i).ValuesIn 0 F.val.toRingHom) := by
  obtain ⟨e, he, ζ, hζ, h⟩ := exists_root_iff_all_grid_values_uniform Y sc
  exact ⟨e, he, ζ, hζ, h Y rfl U L₀ G₀⟩

end GridInterpolation
