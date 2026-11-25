module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullOrderCharacterPackets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridSinglePrimeTest

@[expose] public section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 GroundTheory.Global Set Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host
open GlobalTheory.ChiGrid GlobalTheory.Mem GlobalTheory.BigTop.Fun
open GlobalTheory.Mem.LiteralAutomorphy.KeyFiniteness
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GridInterpolation

/-- Degree-one representatives of the prescribed class, outside the common moving level
and any further finite list of forbidden primes. -/
def goodClassPrimes (D : D7) (q : Ideles D.host.E ⧸ movingRayGroup D)
    (bad : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  {p | movingPrimeClass D p = q ∧ p ∉ bad ∧ p ∉ allBad D ∧ p.asIdeal.inertiaDeg ℤ = 1}

/-- Every good degree-one moving ray class has exact density reciprocal to its index. -/
theorem hasDirichletDensity_goodClassPrimes (D : D7) (q : Ideles D.host.E ⧸ movingRayGroup D)
    (bad : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    (goodClassPrimes D q bad).HasDirichletDensity (1 / (movingRayGroup D).index) := by
  classical
  have h := chosen_ray_class_density _ (movingRayGroup_isOpen D) le_sup_left q
    (fun v => atFin v (unif v)) (fun v => unif_spec v) (bad ∪ (allBad_finite D).toFinset)
  have he (v : HeightOneSpectrum (𝓞 D.host.E)) :
      localIdele D.host.E v (atFin v (unif v)) = IdeleGroup.finiteEmbedding v (atFin v (unif v)) := by
    apply Units.ext
    rfl
  simpa [goodClassPrimes, movingPrimeClass, he, and_assoc] using h

open private HasDirichletDensity.eq_1 from Mathlib.NumberTheory.NumberField.DirichletDensity in
private theorem density_union {K : Type*} [Field K] [NumberField K]
    {A B : Set (HeightOneSpectrum (𝓞 K))} {a b : ℝ} (hdisj : Disjoint A B)
    (ha : A.HasDirichletDensity a) (hb : B.HasDirichletDensity b) :
    (A ∪ B).HasDirichletDensity (a+b) := by
  simp only [HasDirichletDensity.eq_1] at ha hb ⊢
  apply (ha.add hb).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [primeIdealZetaSum_union hdisj hs, add_div]

/-- A finite packet of distinct moving classes has density its cardinality divided by
the index. Only good degree-one primes remain, even after an additional finite exclusion. -/
theorem hasDirichletDensity_goodClassPacket (D : D7) (C : Finset (Ideles D.host.E ⧸ movingRayGroup D))
    (bad : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    {p | movingPrimeClass D p ∈ C ∧ p ∉ bad ∧ p ∉ allBad D ∧ p.asIdeal.inertiaDeg ℤ = 1
      }.HasDirichletDensity (C.card / (movingRayGroup D).index) := by
  classical
  let P (C : Finset (Ideles D.host.E ⧸ movingRayGroup D)) :=
    {p | movingPrimeClass D p ∈ C ∧ p ∉ bad ∧ p ∉ allBad D ∧ p.asIdeal.inertiaDeg ℤ = 1}
  change (P C).HasDirichletDensity _
  induction C using Finset.induction_on with
  | empty => simpa [P] using (NumberField.Set.hasDirichletDensity_empty (K := D.host.E))
  | @insert c C hc ih =>
    have hd : Disjoint (P C) (goodClassPrimes D c bad) := by
      apply Set.disjoint_left.mpr
      intro p hp hpc
      exact hc (hpc.1 ▸ hp.1)
    have hu : P (insert c C) = P C ∪ goodClassPrimes D c bad := by
      ext p
      simp only [P, goodClassPrimes, Set.mem_ofPred_eq, Finset.mem_insert, Set.mem_union]
      tauto
    rw [hu, Finset.card_insert_of_notMem hc, Nat.cast_add, Nat.cast_one, add_div]
    exact density_union hd ih (hasDirichletDensity_goodClassPrimes _ _ _)

private def menuHom (Y : Stages) {sc : Consts} (menu : Finset (GridRatioColumn Y.B.toPre sc)) :
    (Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7) →* (menu → ℂˣ) :=
  MonoidHom.pi fun c => c.1.rayChar Y

private theorem menuHom_read (Y : Stages) {sc : Consts} (menu : Finset (GridRatioColumn Y.B.toPre sc))
    (p : HeightOneSpectrum (𝓞 Y.toD7.host.E)) (c : menu) :
    (((menuHom Y menu) (movingPrimeClass Y.toD7 p) c : ℂˣ) : ℂ) = c.1.read p :=
  c.1.rayChar_read Y p

private theorem menuHom_order (Y : Stages) {sc : Consts} (menu : Finset (GridRatioColumn Y.B.toPre sc))
    (p : HeightOneSpectrum (𝓞 Y.toD7.host.E)) :
    orderOf (menuHom Y menu (movingPrimeClass Y.toD7 p)) = menu.lcm (fun c => orderOf (c.read p)) := by
  classical
  let f := menuHom Y menu (movingPrimeClass Y.toD7 p)
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_iff_pow_eq_one.mpr
    ext1 i
    change (f i) ^ _ = 1
    rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_units, menuHom_read]
    exact Finset.dvd_lcm i.2
  · apply Finset.lcm_dvd
    intro c hc
    rw [← menuHom_read Y menu p (⟨c, hc⟩ : menu), orderOf_units]
    exact orderOf_apply_dvd_orderOf (x := f) ⟨c, hc⟩

private theorem exists_good_class_rep (D : D7) (q : Ideles D.host.E ⧸ movingRayGroup D) :
    ∃ p : HeightOneSpectrum (𝓞 D.host.E), p ∉ allBad D ∧ movingPrimeClass D p = q := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨p, _, hg, _, hd⟩ := exists_good_prime_in_moving_class D x ∅ Set.finite_empty
  exact ⟨p, hg, (QuotientGroup.eq_iff_div_mem).mpr (by simpa only [div_eq_mul_inv] using hd)⟩

/-- One fixed sparse menu works on a packet of degree-one primes of density at
least `φ(e)/e`, uniformly after every finite exclusion. The field test at each
prime in the packet compares every original grid against any given reference. -/
theorem exists_totient_density_single_prime_grid_tests (Y : Stages) (sc : Consts) :
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧
    (∀ m : ℕ, e ∣ m ↔ ∀ s : GridRatioSample Y.B.toPre sc, s.value ^ m = 1) ∧
    ∃ menu : Finset (GridRatioColumn Y.B.toPre sc), menu.card ≤ e.primeFactors.card ∧
    ∃ C : Finset (Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7),
    (e.totient : ℝ) / e ≤ (C.card : ℝ) / (movingRayGroup Y.toD7).index ∧
    (∀ p, movingPrimeClass Y.toD7 p ∈ C ↔ menu.lcm (fun c => orderOf (c.read p)) = e) ∧
    ∀ bad : Finset (HeightOneSpectrum (𝓞 Y.toD7.host.E)),
      let P := {p | movingPrimeClass Y.toD7 p ∈ C ∧ p ∉ bad ∧ p ∉ allBad Y.toD7 ∧
        p.asIdeal.inertiaDeg ℤ = 1}
      P.HasDirichletDensity ((C.card : ℝ) / (movingRayGroup Y.toD7).index) ∧
      ∀ p ∈ P,
        (∀ (G : GridOver Y.B.toPre sc) (a : Fin Y.B.toPre.R.m), (G.character a).UnrAt p) ∧
        menu.lcm (fun c => orderOf (c.read p)) = e ∧
        ∀ (J : GridOver Y.B.toPre sc) (F : IntermediateField ℚ ℂ), J.ValuesIn F →
          ((∀ c ∈ menu, c.read p ∈ F) ↔ ∀ G : GridOver Y.B.toPre sc, G.ValuesIn F) := by
  classical
  obtain ⟨q₀, e, he, hann, menu, hsize, _, htest⟩ := exists_single_prime_grid_tests_exact Y sc
  let D := Y.toD7
  let Q := Ideles D.host.E ⧸ movingRayGroup D
  have : (movingRayGroup D).FiniteIndex :=
    GlobalTheory.T.rayClassGroup_idelic_finiteIndex _ _ 2 (allBad_finite D)
  let _ := Fintype.ofFinite Q
  let f := menuHom Y menu
  obtain ⟨p₀, hg₀, hq₀⟩ := exists_good_class_rep D q₀
  obtain ⟨_, ho₀, ht₀⟩ := htest _ hg₀ hq₀
  have obs (q : Q) (p : HeightOneSpectrum (𝓞 D.host.E))
      (hp : movingPrimeClass D p = q) : orderOf (f q) = menu.lcm (fun c => orderOf (c.read p)) :=
    hp ▸ menuHom_order Y menu p
  have hpeak : orderOf (f q₀) = e := (obs _ _ hq₀).trans ho₀
  have hkill (q : Q) : f q ^ e = 1 := by
    obtain ⟨p, hg, hq⟩ := exists_good_class_rep D q
    rw [← orderOf_dvd_iff_pow_eq_one, obs _ _ hq]
    apply Finset.lcm_dvd
    intro c _
    apply orderOf_dvd_of_pow_eq_one
    exact (hann e).mp dvd_rfl
      ⟨c.left, c.right, c.index, p, unr_of_not_allBad Y _ hg _, unr_of_not_allBad Y _ hg _⟩
  have hE : Monoid.exponent f.range = e := menu_range_exponent_eq f hkill hpeak
  let C := Finset.univ.filter (fun q : Q => orderOf (f q) = e)
  refine ⟨e, he, hann, menu, hsize, C, ?_, ?_, ?_⟩
  · have h := totient_mul_card_le_card_full_image_order_mul_exponent f
    rw [hE] at h
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos he (NeZero.pos (movingRayExponent Y.toD7))
    have hidx : 0 < (movingRayGroup D).index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    apply (div_le_div_iff₀ (Nat.cast_pos.mpr hepos) (Nat.cast_pos.mpr hidx)).mpr
    have hC : Nat.card {q : Q // orderOf (f q) = e} = C.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hC] at h
    exact_mod_cast (h : e.totient * (movingRayGroup D).index ≤ C.card * e)
  · intro p
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show orderOf (f (movingPrimeClass Y.toD7 p)) = _ from menuHom_order Y menu p]
  · intro bad
    refine ⟨hasDirichletDensity_goodClassPacket D C bad, ?_⟩
    rintro p ⟨hm, _, hg, _⟩
    have ho : orderOf (f (movingPrimeClass D p)) = e := (Finset.mem_filter.mp hm).2
    refine ⟨fun G a => unr_of_not_allBad Y G hg a, (menuHom_order Y menu p).symm.trans ho, ?_⟩
    intro J F href
    rw [← ht₀ J F href]
    have ht (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : orderOf (f (movingPrimeClass D v)) = e) :
        (∀ c ∈ menu, c.read v ∈ F) ↔ ∀ y i, (((f y) i : ℂˣ) : ℂ) ∈ F := by
      refine Iff.trans ?_ (full_order_input_tests_subfields f (hv.trans hE.symm) F.toSubfield)
      constructor
      · intro h i
        change (((menuHom Y menu) (movingPrimeClass D v) i : ℂˣ) : ℂ) ∈ F
        rw [menuHom_read]
        exact h i.1 i.2
      · intro h c hc
        rw [← menuHom_read Y menu v (⟨c, hc⟩ : menu)]
        exact h ⟨c, hc⟩
    exact (ht p ho).trans (ht p₀ (hq₀ ▸ hpeak)).symm

end GridInterpolation
