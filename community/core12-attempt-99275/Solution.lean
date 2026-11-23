import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement



namespace CyclotomicProof

open PowerSeries IsLocalRing LevelStatements.Lv

theorem evalPoly {O T : Type} [CommRing O] [CommRing T] [Algebra O T]
    (f : PowerSeries O →ₐ[O] T) (r : Polynomial O) :
    f (r : PowerSeries O) = Polynomial.aeval (f X) r := by
  have h : f.comp (Polynomial.coeToPowerSeries.algHom O) = Polynomial.aeval (f X) := by
    apply Polynomial.algHom_ext
    simp [Polynomial.coeToPowerSeries.algHom_apply]
  simpa [Polynomial.coeToPowerSeries.algHom_apply] using DFunLike.congr_fun h r

theorem ccEval {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (x : PowerSeries S) (r : Polynomial O) :
    constantCoeff (Polynomial.aeval x r) = Polynomial.aeval (constantCoeff x) r := by
  let c : PowerSeries S →ₐ[O] S := { __ := constantCoeff, commutes' := fun _ => rfl }
  exact (Polynomial.aeval_algHom_apply c x r).symm

private theorem division {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    {P : Polynomial O} (h : P.Monic) (a : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), a = (P : PowerSeries O) * q + r := by
  obtain ⟨q, r, hd⟩ := exists_isWeierstrassDivision (f := a) (g := (P : PowerSeries O))
    (by rw [← Polynomial.polynomial_map_coe, Ne, Polynomial.coe_eq_zero_iff]; exact (h.map _).ne_zero)
  exact ⟨q, r, hd.2⟩

theorem unique : RhoUniqueStatement := by
  intro O S _ _ _ _ _ P hP f g hx h0
  have hp (r : Polynomial O) : f (r : PowerSeries O) = g r := by rw [evalPoly, evalPoly, hx]
  have hx' : X ∣ f (P : PowerSeries O) := X_dvd_iff.mpr (by rwa [evalPoly])
  ext a n
  obtain ⟨q, r, e⟩ := division (hP.monic.pow (n + 1)) a
  rw [Polynomial.coe_pow] at e
  have en : f a - g a = f (P : PowerSeries O) ^ (n+1) * (f q - g q) := by
    rw [e]; simp only [map_add, map_mul, map_pow, hp]; ring
  have h := X_pow_dvd_iff.mp (en ▸ (pow_dvd_pow_of_dvd hx' (n+1)).mul_right (f q - g q)) n (by omega)
  simpa [sub_eq_zero] using h

/-- One division argument works simultaneously for any family of expansions.
    Its only input about the family is that the joint residue evaluations detect multiples of P. -/
theorem family {O S I : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing S] [Algebra O S] (P : Polynomial O) (mon : P.Monic)
    (f : I → (PowerSeries O →ₐ[O] PowerSeries S))
    (units : ∀ i, ∃ w : (PowerSeries S)ˣ, f i (P : PowerSeries O) = (w : PowerSeries S) * X)
    (roots : ∀ r : Polynomial O, (∀ i, Polynomial.aeval (constantCoeff (f i X)) r = 0) → P ∣ r)
    (k : ℕ) (a : PowerSeries O) (ha : ∀ i, X ^ k ∣ f i a) : (P : PowerSeries O) ^ k ∣ a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    obtain ⟨q, r, he⟩ := division mon a
    have hr : P ∣ r := roots r fun i => by
      obtain ⟨w, hw⟩ := units i
      have h := X_dvd_iff.mp ((dvd_pow_self _ (Nat.succ_ne_zero k)).trans (ha i))
      simpa [he, hw, evalPoly, ccEval] using h
    obtain ⟨b, hb⟩ : (P : PowerSeries O) ∣ a := he ▸ dvd_add (dvd_mul_right _ _) (by
      obtain ⟨s,rfl⟩ := hr
      exact ⟨s, Polynomial.coe_mul _ _⟩)
    rw [hb, pow_succ']
    apply mul_dvd_mul_left
    apply ih
    intro i
    obtain ⟨w, hw⟩ := units i
    obtain ⟨c, hc⟩ := ha i
    apply w.isUnit.dvd_mul_left.mp
    refine ⟨c, X_mul_cancel ?_⟩
    rw [hb, map_mul, hw] at hc
    linear_combination hc

theorem complete : RhoComplStatement := by
  intro O L S _ _ _ _ _ _ _ _ _ _ _ P hP f hw hann k a ha
  refine family P hP.monic (fun _ : Unit => f) (fun _ => hw) ?_ k a (fun _ => ha)
  intro r hr
  apply (Polynomial.map_dvd_map _ (IsFractionRing.injective O L) hP.monic).mp
  apply hann
  simpa [Polynomial.aeval_map_algebraMap] using hr ()

theorem distinguished : CycloDistStatement := by
  intro O _ _ l s hl hlm
  let _ : Fact l.Prime := ⟨hl⟩
  have h := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt (p := l) s
  let P := (Polynomial.cyclotomic (l ^ (s+1)) ℤ).comp (Polynomial.X + 1)
  have mon : P.Monic := (Polynomial.cyclotomic.monic _ _).comp_X_add_C 1
  suffices (P.map (Int.castRingHom O)).IsDistinguishedAt (maximalIdeal O) by
    simpa [P, Polynomial.map_comp] using this
  refine { monic := mon.map _, mem := fun {i} hi => ?_ }
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (h.mem (by rwa [mon.natDegree_map] at hi))
  rw [Polynomial.coeff_map, ← hb, smul_eq_mul, map_mul]
  exact Ideal.mul_mem_left _ _ (by simpa using hlm)

theorem simple : CycloSimpleStatement := by
  intro L S _ _ _ _ m hm ζ E hζ hE0 hE
  let Φ := Polynomial.cyclotomic m L
  let _ : NeZero (m : L) := ⟨by exact_mod_cast hm.ne'⟩
  have rootUnit : IsUnit ζ := by
    apply IsUnit.of_pow_eq_one _ hm.ne'
    obtain ⟨q,hq⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one m L
    simpa [hζ, sub_eq_zero] using congrArg (Polynomial.aeval ζ) hq
  have sep : IsCoprime Φ Φ.derivative := Polynomial.separable_cyclotomic _ _
  have unitDeriv : IsUnit (Polynomial.aeval ζ Φ.derivative) := by
    simpa [Φ, hζ, isCoprime_zero_left] using sep.map (Polynomial.aeval ζ).toRingHom
  let y := C ζ * E
  have y0 : constantCoeff y = ζ := by simp [y, hE0]
  have dy : PowerSeries.derivative y = y := by
    simp [y, Derivation.leibniz, hE, smul_eq_mul]
  obtain ⟨G,hG⟩ := X_dvd_iff.mpr (by rw [ccEval y Φ, y0]; exact hζ)
  have hu : IsUnit G := by
    rw [isUnit_iff_constantCoeff]
    have eq := congrArg (fun f => constantCoeff (PowerSeries.derivative f)) hG
    rw [← Polynomial.aeval_map_algebraMap S y Φ, Derivation.map_aeval, dy, smul_eq_mul, map_mul,
      ccEval, y0, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap] at eq
    simpa [Derivation.leibniz, smul_eq_mul] using (show IsUnit (constantCoeff (PowerSeries.derivative (X * G))) by rw [← eq]; exact unitDeriv.mul rootUnit)
  exact ⟨hu.unit, by rw [hu.unit_spec, hG, mul_comm]⟩

theorem exponential : ExpRescaleStatement := by
  intro S _ _ E h0 hd
  let _ := IsAddTorsionFree.of_module_rat S
  obtain rfl := exp_unique_of_derivative_eq_self hd h0
  exact ⟨rfl, exp_pow_eq_rescale_exp⟩

/-- Divisibility by the translate of a split cyclotomic polynomial is detected
    by evaluating at its translated primitive roots. -/
private theorem allRoots {L : Type} [Field L] {n : ℕ} (hn : 0 < n) {u : L}
    (hu : IsPrimitiveRoot u n) (r : Polynomial L) (hr : ∀ z, IsPrimitiveRoot z n → r.eval (z-1) = 0) :
    (Polynomial.cyclotomic n L).comp (Polynomial.X + 1) ∣ r := by
  classical
  have h : Polynomial.cyclotomic n L ∣ r.comp (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hu]
    apply Finset.prod_dvd_of_coprime ((Polynomial.pairwise_coprime_X_sub_C Function.injective_id).set_pairwise _)
    intro z hz
    simpa [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot] using hr z ((mem_primitiveRoots hn).mp hz)
  obtain ⟨q,hq⟩ := h
  refine ⟨q.comp (Polynomial.X+1), ?_⟩
  calc r = (r.comp (Polynomial.X-1)).comp (Polynomial.X+1) := by rw [Polynomial.comp_assoc]; simp
       _ = _ := by rw [hq, Polynomial.mul_comp]

theorem split : SplitComplStatement := by
  intro O L _ _ _ _ _ _ _ _ l s hl hlm ⟨u, hu⟩ ρ hρ k a ha
  let n := l ^ (s+1)
  have hn : 0 < n := pow_pos hl.pos _
  let _ : NeZero (n : L) := ⟨by exact_mod_cast hn.ne'⟩
  let P := (Polynomial.cyclotomic n O).comp (Polynomial.X+1)
  have mon : P.Monic := (distinguished O l s hl hlm).monic
  let I := {z : L // IsPrimitiveRoot z n}
  refine family P mon (fun i : I => ρ i.1) ?_ ?_ k a (fun i => ha _ i.2)
  · intro i
    have root : Polynomial.aeval i.1 (Polynomial.cyclotomic n L) = 0 := by
      rw [Polynomial.coe_aeval_eq_eval]
      exact Polynomial.isRoot_cyclotomic_iff.mpr i.2
    obtain ⟨w, hw⟩ := simple L L n hn i.1 (exp L) root constantCoeff_exp (derivative_exp L)
    refine ⟨w, ?_⟩
    dsimp only [P]
    rw [evalPoly, Polynomial.aeval_comp, map_add, Polynomial.aeval_X, map_one, add_comm, hρ _ i.2]
    rwa [← Polynomial.map_cyclotomic n (algebraMap O L), Polynomial.aeval_map_algebraMap] at hw
  · intro r hr
    apply (Polynomial.map_dvd_map _ (IsFractionRing.injective O L) mon).mp
    simp only [P, Polynomial.map_comp, Polynomial.map_cyclotomic, Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]
    apply allRoots hn hu
    intro z hz
    have h := congrArg constantCoeff (hρ z hz)
    have e : constantCoeff (ρ z X) = z - 1 := by
      simp at h
      linear_combination h
    rw [← e, ← Polynomial.coe_aeval_eq_eval, Polynomial.aeval_map_algebraMap]
    exact hr ⟨z,hz⟩

variable {O : Type} [CommRing O]

/-- Discard the first block of coefficients. -/
private noncomputable def tail (m : ℕ) : PowerSeries O →ₗ[O] PowerSeries O where
  toFun f := mk fun n => coeff (n + m) f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem descent : DescendDvdStatement := by
  intro O _ ι m hm ⟨w, hw⟩
  let D := (LinearMap.mulLeft O (↑w⁻¹ : PowerSeries O)).comp (tail m)
  have shift (b : PowerSeries O) : D (ι X * b) = b := by
    change ↑w⁻¹ * tail m (ι X * b) = b
    rw [hw, mul_comm (↑w : PowerSeries O) _, mul_assoc]
    have h (f : PowerSeries O) : tail m (X ^ m * f) = f := by
      ext n
      simp [tail]
    simp [h]
  let π : PowerSeries O →ₗ[O] PowerSeries O :=
    { toFun := fun f => mk fun n => constantCoeff ((D ^ n) f)
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun c b => by ext; simp only [coeff_mk, RingHom.id_apply, ← coeff_zero_eq_constantCoeff_apply, map_smul] }
  have shiftπ (b : PowerSeries O) : π (ι X * b) = X * π b := by
    ext n
    cases n with
    | zero => simp [π, hw, zero_pow hm.ne']
    | succ n => simp [π, pow_succ, shift, Module.End.mul_apply, coeff_succ_X_mul]
  have π1 : π 1 = 1 := by
    have h : D 1 = 0 := by
      change (↑w⁻¹ : PowerSeries O) * tail m 1 = 0
      suffices tail m (1 : PowerSeries O) = 0 by simp [this]
      ext n
      simp [tail, coeff_one, hm.ne']
    ext n
    cases n <;> simp [π, pow_succ, Module.End.mul_apply, h, coeff_one]
  have constants (c : O) : ι (C c) = C c := ι.commutes c
  have linear (b p : PowerSeries O) : π (ι p * b) = p * π b := by
    ext n
    induction n generalizing p with
    | zero =>
      conv_lhs => rw [eq_X_mul_shift_add_const p]
      conv_rhs => rw [eq_X_mul_shift_add_const p]
      simp only [map_add, map_mul, add_mul, mul_assoc, shiftπ, constants,
        ← smul_eq_C_mul, map_smul, coeff_zero_eq_constantCoeff_apply, constantCoeff_X,
        zero_mul, zero_add]
    | succ n ih =>
      conv_lhs => rw [eq_X_mul_shift_add_const p]
      conv_rhs => rw [eq_X_mul_shift_add_const p]
      simp only [map_add, map_mul, add_mul, mul_assoc, shiftπ, constants,
        ← smul_eq_C_mul, map_smul, coeff_succ_X_mul, ih]
  have retract (p : PowerSeries O) : π (ι p) = p := by simpa [π1] using linear 1 p
  exact ⟨Function.LeftInverse.injective retract, fun p a ⟨c,hc⟩ =>
    ⟨π c, by rw [← retract a, hc, linear]⟩⟩

theorem coprime : PsCoprimeStatement := by
  intro O _ l φ h
  let c : PowerSeries O := C (l : O)
  let q := X + c
  have const (s : ℕ) : (φ ^ s) c = c := (φ ^ s).commutes _
  have divX (s : ℕ) : X ∣ (φ ^ s) X := by
    induction s with
    | zero => exact dvd_refl _
    | succ s ih =>
      rw [pow_succ', AlgHom.mul_apply]
      exact ((dvd_mul_right _ _).trans h).trans (map_dvd φ ih)
  have step (t : ℕ) : q ∣ (φ ^ (t+1)) X := by
    rw [pow_succ', AlgHom.mul_apply]
    exact ((dvd_mul_left _ _).trans h).trans (map_dvd φ (divX t))
  have span (a : PowerSeries O) (s : ℕ) (ha : a ∣ (φ ^ s) X) :
      c ∈ Ideal.span {(φ ^ s) q, a} := by
    obtain ⟨d,hd⟩ := ha
    rw [Ideal.mem_span_pair]
    refine ⟨1, -d, ?_⟩
    dsimp [q]
    rw [map_add, const, hd]
    ring
  simp only [← AlgHom.coe_pow]
  refine ⟨fun s => span X s (divX s), ?_⟩
  have lt (s t : ℕ) (hlt : s < t) : c ∈ Ideal.span {(φ ^ s) q, (φ ^ t) q} := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Set.pair_comm]
    apply span
    simpa [pow_add, AlgHom.mul_apply, Nat.add_assoc] using map_dvd (φ ^ s) (step j)
  intro s t hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact lt s t h'
  · rw [Set.pair_comm]; exact lt t s h'

end CyclotomicProof

namespace AlpogeRHCore12

open CyclotomicProof

theorem cyclotomicPowerSeriesRigidity :
    LevelStatements.Lv.RhoUniqueStatement ∧
    LevelStatements.Lv.RhoComplStatement ∧
    LevelStatements.Lv.CycloDistStatement ∧
    LevelStatements.Lv.CycloSimpleStatement ∧
    LevelStatements.Lv.ExpRescaleStatement ∧
    LevelStatements.Lv.DescendDvdStatement ∧
    LevelStatements.Lv.SplitComplStatement ∧
    LevelStatements.Lv.PsCoprimeStatement :=
  ⟨unique, complete, distinguished, simple, exponential, descent, split, coprime⟩

end AlpogeRHCore12
