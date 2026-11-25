module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridCharacterRootTest
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovingRayPrimeRepresentatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommonCharacterInput

@[expose] public section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host
open GlobalTheory.ChiGrid GlobalTheory.Mem GlobalTheory.BigTop.Fun
open GlobalTheory.Mem.LiteralAutomorphy.KeyFiniteness
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GridInterpolation

/-- The two original grids and the common character column to read at a prime. -/
structure GridRatioColumn (P : Pre) (sc : Consts) where
  left : GridOver P sc
  right : GridOver P sc
  index : Fin P.R.m

namespace GridRatioColumn

variable {P : Pre} {sc : Consts}

/-- The ratio of the actual uniformizer values, evaluated at the same prime. -/
def read (c : GridRatioColumn P sc) (p : HeightOneSpectrum (𝓞 P.host.E)) : ℂ :=
  ((c.left.character c.index).val p : ℂ) / ((c.right.character c.index).val p : ℂ)

private def ideleChar (c : GridRatioColumn P sc) : Ideles P.host.E →* ℂˣ :=
  ((c.left.character c.index) * (c.right.character c.index)⁻¹).1

private theorem eval_read (c : GridRatioColumn P sc) (p : HeightOneSpectrum (𝓞 P.host.E)) :
    (c.ideleChar (localIdele P.host.E p (atFin p (unif p))) : ℂ) = c.read p := by
  simp [ideleChar, read, HChar.val, HChar.locK, HChar.loc, div_eq_mul_inv]

private theorem ray_le_ker (Y : Stages) (c : GridRatioColumn Y.B.toPre sc) :
    movingRayGroup Y.toD7 ≤ c.ideleChar.ker := by
  obtain ⟨⟨X, hX, T, L, G⟩, ⟨Z, hZ, U, H, J⟩, a⟩ := c
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := Y
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := X
  obtain ⟨⟨W⟩, _, _, _, _, _, _⟩ := Z
  change Q = P at hX
  change W = P at hZ
  subst Q W
  exact movingRayGroup_le_ratio_ker G.pl.basePlace_over_qZero J.pl.basePlace_over_qZero
    (actual_specs G a) (actual_specs J a)

end GridRatioColumn

theorem unr_of_not_allBad (Y : Stages) {sc : Consts} (G : GridOver Y.B.toPre sc)
    {p : HeightOneSpectrum (𝓞 Y.B.toPre.host.E)} (hp : p ∉ allBad Y.toD7) (a : Fin Y.B.toPre.R.m) :
    (G.character a).UnrAt p := by
  obtain ⟨X, hX, T, L, G⟩ := G
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := Y
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := X
  change Q = P at hX
  subst Q
  exact (actual_specs G a).2.1 p fun h => hp (Set.mem_biUnion G.pl.basePlace_over_qZero h)

/-- The class of the specified local uniformizer, not an arbitrary prime above its norm. -/
def movingPrimeClass (D : D7) (p : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideles D.host.E ⧸ movingRayGroup D :=
  QuotientGroup.mk (localIdele D.host.E p (atFin p (unif p)))

/-- The ratio of an original column pair, descended to the common moving ray quotient. -/
def GridRatioColumn.rayChar (Y : Stages) {sc : Consts} (c : GridRatioColumn Y.B.toPre sc) :
    (Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7) →* ℂˣ :=
  QuotientGroup.lift _ ((c.left.character c.index) * (c.right.character c.index)⁻¹).1
    (by exact c.ray_le_ker Y)

theorem GridRatioColumn.rayChar_read (Y : Stages) {sc : Consts} (c : GridRatioColumn Y.B.toPre sc)
    (p : HeightOneSpectrum (𝓞 Y.toD7.host.E)) :
    ((c.rayChar Y (movingPrimeClass Y.toD7 p) : ℂˣ) : ℂ) = c.read p :=
  c.eval_read p

private theorem movingPrimeClass_eq_iff (D : D7) (p : HeightOneSpectrum (𝓞 D.host.E))
    (x : Ideles D.host.E) : movingPrimeClass D p = QuotientGroup.mk x ↔
      localIdele D.host.E p (atFin p (unif p)) / x ∈ movingRayGroup D :=
  QuotientGroup.eq_iff_div_mem

/-- Fix a base stage and grid parameters. A single ray class and a menu of at most
one column pair per prime divisor of the test order work independently of all excluded
primes, reference grids and fields. Any finite exclusion leaves a residue-degree-one
prime in that class, unramified for every original grid, at which the entire menu is read. -/
theorem exists_single_prime_grid_tests_exact (Y : Stages) (sc : Consts) :
    ∃ q : Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7,
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧
    (∀ m : ℕ, e ∣ m ↔ ∀ s : GridRatioSample Y.B.toPre sc, s.value ^ m = 1) ∧
    ∃ menu : Finset (GridRatioColumn Y.B.toPre sc), menu.card ≤ e.primeFactors.card ∧
    (∀ bad : Finset (HeightOneSpectrum (𝓞 Y.toD7.host.E)),
      ∃ p : HeightOneSpectrum (𝓞 Y.toD7.host.E), p ∉ bad ∧ p ∉ allBad Y.toD7 ∧
        p.asIdeal.inertiaDeg ℤ = 1 ∧
        movingPrimeClass Y.toD7 p = q) ∧
    ∀ p : HeightOneSpectrum (𝓞 Y.toD7.host.E), p ∉ allBad Y.toD7 →
        movingPrimeClass Y.toD7 p = q →
        (∀ (G : GridOver Y.B.toPre sc) (a : Fin Y.B.toPre.R.m), (G.character a).UnrAt p) ∧
        menu.lcm (fun c => orderOf (c.read p)) = e ∧
        ∀ (J : GridOver Y.B.toPre sc) (F : IntermediateField ℚ ℂ), J.ValuesIn F →
          ((∀ c ∈ menu, c.read p ∈ F) ↔ ∀ G : GridOver Y.B.toPre sc, G.ValuesIn F) := by
  classical
  let R := movingRayExponent Y.toD7
  let C := GridRatioColumn Y.B.toPre sc
  let χ (c : C) : (Ideles Y.toD7.host.E) →* ℂ := (Units.coeHom ℂ).comp c.ideleChar
  have powR (c : C) (y : Ideles Y.toD7.host.E) : χ c y ^ R = 1 := by
    have h : y ^ R ∈ movingRayGroup Y.toD7 :=
      (QuotientGroup.eq_one_iff _).mp (Monoid.pow_exponent_eq_one (y : Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7))
    have h' := MonoidHom.mem_ker.mp (c.ray_le_ker Y h)
    calc
      χ c y ^ R = χ c (y ^ R) := (map_pow _ _ _).symm
      _ = 1 := congrArg Units.val h'
  obtain ⟨x, hx, hpowers⟩ := exists_common_character_tests χ
    (Nat.pos_of_ne_zero (NeZero.ne R)) powR
  let S := Set.range fun c : C => χ c x
  obtain ⟨e, he, hleast, A, hA, hcard, horder, _, _, htest⟩ :=
    exists_sparse_root_field_tests S (NeZero.ne R) (fun _ ⟨c, hc⟩ => hc ▸ powR c x)
  choose pick hval using fun z : A => hA z.property
  let menu := A.attach.image pick
  have himg : menu.image (fun c => χ c x) = A := by
    ext z
    constructor
    · rintro hz
      obtain ⟨_, hm, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hm
      simpa only [show χ (pick a) x = a.val from hval a] using a.property
    · intro hz
      exact Finset.mem_image.mpr ⟨pick ⟨z, hz⟩, Finset.mem_image_of_mem _ (A.mem_attach _), hval _⟩
  have agree (p : HeightOneSpectrum (𝓞 Y.toD7.host.E))
      (hp : movingPrimeClass Y.toD7 p = QuotientGroup.mk x) (c : C) : c.read p = χ c x := by
    have h := c.ideleChar.div_mem_ker_iff.mp (c.ray_le_ker Y ((movingPrimeClass_eq_iff Y.toD7 p x).mp hp))
    exact (c.eval_read p).symm.trans (congrArg Units.val h)
  have primes (bad : Finset (HeightOneSpectrum (𝓞 Y.toD7.host.E))) :
      ∃ p : HeightOneSpectrum (𝓞 Y.toD7.host.E), p ∉ bad ∧ p ∉ allBad Y.toD7 ∧
        p.asIdeal.inertiaDeg ℤ = 1 ∧ movingPrimeClass Y.toD7 p = QuotientGroup.mk x := by
    obtain ⟨p, hp, hg, hd, hr⟩ := exists_good_prime_in_moving_class Y.toD7 x (bad : Set _) bad.finite_toSet
    exact ⟨p, hp, hg, hd, (movingPrimeClass_eq_iff Y.toD7 p x).mpr (by simpa only [div_eq_mul_inv] using hr)⟩
  refine ⟨QuotientGroup.mk x, e, he, ?_, menu,
    (Finset.card_image_le.trans_eq Finset.card_attach).trans hcard, primes, ?_⟩
  · intro m
    rw [hleast m]
    constructor
    · intro bound s
      let c : C := ⟨s.left, s.right, s.index⟩
      change c.read s.prime ^ m = 1
      rw [← c.eval_read]
      exact (hpowers m).mp (fun i => bound _ ⟨i, rfl⟩) _ c
    · rintro h _ ⟨c, rfl⟩
      obtain ⟨p, _, hg, _, hp⟩ := primes ∅
      have hr := h ⟨c.left, c.right, c.index, p, unr_of_not_allBad Y _ hg _, unr_of_not_allBad Y _ hg _⟩
      change c.read p ^ m = 1 at hr
      rwa [agree p hp] at hr
  intro p hg hclass
  have himp : menu.image (fun c => c.read p) = A := by simpa only [agree p hclass] using himg
  refine ⟨fun G a => unr_of_not_allBad Y G hg a, ?_, ?_⟩
  · rw [← himp, Finset.lcm_image] at horder
    exact horder
  · intro J F href
    rw [← all_ratios_iff_values J F href]
    constructor
    · intro h s
      have hAF : (A : Set ℂ) ⊆ F := by
        intro z hz
        rw [← himp] at hz
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
        exact h c hc
      have hS := ((htest F).2).mp hAF
      have hall := (hx F.toSubfield).mp (fun c => hS ⟨c, rfl⟩)
      let c : C := ⟨s.left, s.right, s.index⟩
      change c.read s.prime ∈ F
      rw [← c.eval_read]
      exact hall _ c
    · intro h c _
      exact h ⟨c.left, c.right, c.index, p, unr_of_not_allBad Y _ hg _, unr_of_not_allBad Y _ hg _⟩

/-- Fix a base stage and grid parameters. A single ray class and a menu of at most
one column pair per prime divisor of the test order work independently of all excluded
primes, reference grids and fields. Any finite exclusion leaves a residue-degree-one
prime in that class, unramified for every original grid, at which the entire menu is read. -/
theorem exists_single_prime_grid_tests (Y : Stages) (sc : Consts) :
    ∃ q : Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7,
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧
    ∃ menu : Finset (GridRatioColumn Y.B.toPre sc), menu.card ≤ e.primeFactors.card ∧
    (∀ bad : Finset (HeightOneSpectrum (𝓞 Y.toD7.host.E)),
      ∃ p : HeightOneSpectrum (𝓞 Y.toD7.host.E), p ∉ bad ∧ p ∉ allBad Y.toD7 ∧
        p.asIdeal.inertiaDeg ℤ = 1 ∧
        movingPrimeClass Y.toD7 p = q) ∧
    ∀ p : HeightOneSpectrum (𝓞 Y.toD7.host.E), p ∉ allBad Y.toD7 →
        movingPrimeClass Y.toD7 p = q →
        (∀ (G : GridOver Y.B.toPre sc) (a : Fin Y.B.toPre.R.m), (G.character a).UnrAt p) ∧
        menu.lcm (fun c => orderOf (c.read p)) = e ∧
        ∀ (J : GridOver Y.B.toPre sc) (F : IntermediateField ℚ ℂ), J.ValuesIn F →
          ((∀ c ∈ menu, c.read p ∈ F) ↔ ∀ G : GridOver Y.B.toPre sc, G.ValuesIn F) := by
  obtain ⟨q, e, he, _, menu, hc, primes, test⟩ := exists_single_prime_grid_tests_exact Y sc
  exact ⟨q, e, he, menu, hc, primes, test⟩

end GridInterpolation
end
