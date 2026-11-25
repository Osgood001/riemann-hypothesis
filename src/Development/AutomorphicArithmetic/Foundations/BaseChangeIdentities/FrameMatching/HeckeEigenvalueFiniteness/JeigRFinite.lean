module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LinearIndependentEigenvectors

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.HeckeLevelFrameExistence.Ev

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Tail

section Gen

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fix_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (K : Subgroup G) {v : V}
    (hv : v ∈ fixed ρ K) : φ.toLinearEquiv v ∈ fixed σ K := by
  intro h
  have h1 : ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v := hv h
  rw [Representation.Equiv.toLinearEquiv_apply, ← φ.toIntertwiningMap.isIntertwining,
    ← Representation.Equiv.toLinearEquiv_apply, h1, map_smul]
  rfl

theorem hk_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (K : Subgroup G) (f : G → ℂ) (v : V) :
    φ.toLinearEquiv (hkG ρ K f v) = hkG σ K f (φ.toLinearEquiv v) := by
  unfold hkG
  refine (φ.toLinearEquiv.toAddEquiv.map_finsum (fun q : G ⧸ K => f q.out • ρ q.out v)).trans (finsum_congr fun q => ?_)
  change φ.toLinearEquiv (f q.out • ρ q.out v) = f q.out • σ q.out (φ.toLinearEquiv v)
  rw [map_smul, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
    φ.toIntertwiningMap.isIntertwining]

theorem hk_lin (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) : ∃ T : V →ₗ[ℂ] V, ∀ v, hkG ρ K f v = T v := by
  by_cases h : (Function.support fun q : G ⧸ K => f q.out).Finite
  · refine ⟨∑ q ∈ h.toFinset, f q.out • ρ q.out, fun v => ?_⟩
    unfold hkG
    rw [finsum_eq_sum_of_support_subset (s := h.toFinset), LinearMap.sum_apply]
    · rfl
    · intro q hq
      rw [Set.Finite.coe_toFinset]
      intro h0
      apply hq
      simp only [h0, zero_smul]
  · refine ⟨0, fun v => ?_⟩
    unfold hkG
    by_cases hv : v = 0
    · simp [hv]
    · refine finsum_of_infinite_support fun hfin => h (hfin.subset fun q hq h0 => ?_)
      rcases smul_eq_zero.1 h0 with h1 | h1
      · exact hq h1
      · apply hv
        have := congrArg (ρ q.out⁻¹) h1
        rwa [map_zero, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self] at this

theorem li_eig {Ξ P : Type} (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ) (hinj : Function.Injective ev) (v : Ξ → V)
    (h0 : ∀ ξ, v ξ ≠ 0) (hv : ∀ ξ p, T p (v ξ) = ev ξ p • v ξ) : LinearIndependent ℂ v :=
  _root_.UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig T ev hinj v h0 hv

/-- Distinct joint eigencharacters with a nonzero eigenvector in `U` are bounded by its dimension. -/
theorem encard_eig_le_finrank {Ξ P : Type} (U : Submodule ℂ V) [FiniteDimensional ℂ U] (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ)
    (hinj : Function.Injective ev) : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v}.encard ≤ Module.finrank ℂ U := by
  choose v hU h0 hv using fun ξ : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v} => ξ.2
  have h := li_eig T (fun ξ : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v} => ev ξ.1)
    (hinj.comp Subtype.val_injective) v h0 hv
  have h' : LinearIndependent ℂ fun ξ => (⟨v ξ, hU ξ⟩ : U) := LinearIndependent.of_comp U.subtype h
  classical
  have := h'.finite_of_isNoetherian
  let := Fintype.ofFinite {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v}
  rw [Set.encard, ENat.card_eq_coe_fintype_card]
  exact_mod_cast h'.fintype_card_le_finrank

theorem fin_eig {Ξ P : Type} (U : Submodule ℂ V) [FiniteDimensional ℂ U] (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ)
    (hinj : Function.Injective ev) : {ξ | ∃ v ∈ U, v ≠ 0 ∧ ∀ p, T p v = ev ξ p • v}.Finite :=
  Set.finite_of_encard_le_coe (encard_eig_le_finrank U T ev hinj)

end Gen

variable {E : Type} [Field E] [NumberField E] [hCM : IsCMField E] {a b : ℕ}

def JEigR {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E) (ρ : Representation ℂ (GLw a w × GLw b w) V)
    (ϖ : (w.adicCompletion E)ˣ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) : Prop :=
  ∃ v ∈ fixed ρ (I2 a b w), v ≠ 0 ∧
    ∀ x y, Gap x → Gap y → hkG ρ (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v

theorem jeigR_equiv {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {w : Pl E}
    {ρ : Representation ℂ (GLw a w × GLw b w) V} {σ : Representation ℂ (GLw a w × GLw b w) W} (φ : ρ.Equiv σ)
    {ϖ : (w.adicCompletion E)ˣ} {ξa : Fin a → ℂˣ} {ξb : Fin b → ℂˣ} (h : JEigR w ρ ϖ ξa ξb) :
    JEigR w σ ϖ ξa ξb := by
  obtain ⟨v, hv, hv0, he⟩ := h
  refine ⟨φ.toLinearEquiv v, fix_map φ _ hv, fun h0 => hv0 (φ.toLinearEquiv.injective (by rw [h0, map_zero])),
    fun x y hx hy => ?_⟩
  rw [← hk_map, he x y hx hy, map_smul]

theorem qh_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) : qh w ≠ 0 := by
  unfold qh
  rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
  have hq : qV E w ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero hq

theorem pw_ne_zero {m : ℕ} (y : Fin m → ℂˣ) (x : Fin m → ℤ) : pw y x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _

theorem pw_shift {m : ℕ} (y : Fin m → ℂˣ) (x : Fin m → ℤ) (i : Fin m) :
    pw y (fun j => x j + if j = i then 1 else 0) = pw y x * (y i : ℂ) := by
  have key : ∀ j, (((y j ^ (x j + if j = i then 1 else 0) : ℂˣ)) : ℂ) =
      ((y j ^ x j : ℂˣ) : ℂ) * (if j = i then (y i : ℂ) else 1) := by
    intro j
    by_cases h : j = i
    · subst h
      simp [_root_.zpow_add]
    · simp [h]
  simp only [pw, key, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

def g0 (m : ℕ) : Fin m → ℤ := fun i => 2 * ((m : ℤ) - (i : ℕ))

theorem gap0 (m : ℕ) : Gap (g0 m) := by
  intro i j hij
  have := Fin.lt_def.1 hij
  simp only [g0]
  omega

theorem gap1 (m : ℕ) (i : Fin m) : Gap (fun j => g0 m j + if j = i then 1 else 0) := by
  intro j l hjl
  have := Fin.lt_def.1 hjl
  simp only [g0]
  split_ifs <;> omega

private def center (n : ℕ) (i : Fin n) : ℤ := n - 1 - 2 * (i.val : ℤ)

private theorem center_sum (n : ℕ) : ∑ i, center n i = 0 := by
  have h : ∀ i : Fin n, center n (Fin.revPerm i) = -center n i := by
    intro i
    simp only [center, Fin.revPerm_apply, Fin.val_rev]
    omega
  have heq := Equiv.sum_comp Fin.revPerm (center n)
  simp_rw [h] at heq
  rw [Finset.sum_neg_distrib] at heq
  omega

private def weight {n : ℕ} (x : Fin n → ℂˣ) : ℂˣ := ∏ i, x i ^ center n i

private theorem weight_scale {n : ℕ} (u : ℂˣ) (x : Fin n → ℂˣ) :
    weight (fun i => u * x i) = weight x := by
  simp only [weight, mul_zpow, Finset.prod_mul_distrib]
  have prod_const (s : Finset (Fin n)) : ∏ i ∈ s, u ^ center n i = u ^ ∑ i ∈ s, center n i := by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih => simp only [Finset.prod_cons, Finset.sum_cons, _root_.zpow_add, ih]
  rw [prod_const, center_sum, zpow_zero, one_mul]

private def probe {m : ℕ} (i : Option (Fin m)) (j : Fin m) : ℤ :=
  center m j + if some j = i then 1 else 0

private theorem probe_gap {m : ℕ} (i : Option (Fin m)) : Gap (probe i) := by
  intro j k hjk
  have h := Fin.lt_def.mp hjk
  simp only [probe, center]
  split_ifs <;> omega

private theorem pw_probe {m : ℕ} (x : Fin m → ℂˣ) (i : Option (Fin m)) :
    pw x (probe i) = ((weight x * i.elim 1 x : ℂˣ) : ℂ) := by
  cases i with
  | none => simp [pw, probe, weight, Units.coe_prod]
  | some i =>
    simpa [probe, weight, pw, Units.coe_prod] using pw_shift x (center m) i

/-- The two ordered characters can be recovered from exactly one gap-compatible
Hecke evaluation per coordinate. -/
theorem exists_separating_probes (w : Pl E) :
    ∃ (x : Fin a ⊕ Fin b → Fin a → ℤ) (y : Fin a ⊕ Fin b → Fin b → ℤ),
      (∀ p, Gap (x p) ∧ Gap (y p)) ∧ Function.Injective
        (fun u : (Fin a → ℂˣ) × (Fin b → ℂˣ) => fun p => ev2 w u.1 u.2 (x p) (y p)) := by
  let x : Fin a ⊕ Fin b → Fin a → ℤ := fun p => probe p.getLeft?
  let y : Fin a ⊕ Fin b → Fin b → ℤ := fun p => probe p.getRight?
  refine ⟨x, y, fun p => ⟨probe_gap _, probe_gap _⟩, ?_⟩
  have hd {n : ℕ} (z : Fin n → ℤ) : dl w z ≠ 0 := zpow_ne_zero _ (qh_ne_zero w)
  intro u v huv
  have h (p : Fin a ⊕ Fin b) :
      (weight u.1 * weight u.2) * Sum.elim u.1 u.2 p =
      (weight v.1 * weight v.2) * Sum.elim v.1 v.2 p := by
    have he := congrFun huv p
    change dl w (x p) * pw u.1 (x p) * (dl w (y p) * pw u.2 (y p)) =
      dl w (x p) * pw v.1 (x p) * (dl w (y p) * pw v.2 (y p)) at he
    rw [mul_mul_mul_comm, mul_mul_mul_comm (dl w (x p)) (pw v.1 (x p))] at he
    have hh := mul_left_cancel₀ (mul_ne_zero (hd (x p)) (hd (y p))) he
    apply Units.ext
    cases p <;> simpa [x, y, pw_probe, mul_assoc, mul_left_comm, mul_comm] using hh
  have ha : (fun i => (weight u.1 * weight u.2) * u.1 i) =
      (fun i => (weight v.1 * weight v.2) * v.1 i) := funext (fun i => h (.inl i))
  have hb : (fun i => (weight u.1 * weight u.2) * u.2 i) =
      (fun i => (weight v.1 * weight v.2) * v.2 i) := funext (fun i => h (.inr i))
  have wa : weight u.1 = weight v.1 := by simpa only [weight_scale] using congrArg weight ha
  have wb : weight u.2 = weight v.2 := by simpa only [weight_scale] using congrArg weight hb
  rw [wa, wb] at ha hb
  exact Prod.ext (funext fun i => mul_left_cancel (congrFun ha i))
    (funext fun i => mul_left_cancel (congrFun hb i))

omit hCM in
/-- Distinct local torus parameters cannot be separated by fewer than `a + b` fixed
evaluation probes. On the sign cube each monomial has at most two possible values. -/
theorem rank_le_of_evaluation_injective (w : Pl E) {κ : Type*} [Fintype κ]
    (x : κ → Fin a → ℤ) (y : κ → Fin b → ℤ)
    (h : Function.Injective fun u : (Fin a → ℂˣ) × (Fin b → ℂˣ) =>
      fun j => ev2 w u.1 u.2 (x j) (y j)) : a + b ≤ Fintype.card κ := by
  classical
  let f := Units.map (Int.castRingHom ℂ).toMonoidHom
  have hf : Function.Injective f := Units.map_injective Int.cast_injective
  let signs (u : (Fin a → ℤˣ) × (Fin b → ℤˣ)) (j : κ) :=
    (∏ i, (u.1 i) ^ x j i) * ∏ i, (u.2 i) ^ y j i
  have hinj : Function.Injective signs := by
    intro u v huv
    have eq : (f ∘ u.1, f ∘ u.2) = (f ∘ v.1, f ∘ v.2) := by
      apply h
      funext j
      have e := congrArg (fun z => (f z : ℂ)) (congrFun huv j)
      simp only [signs, map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod] at e
      simpa only [ev2, pw, Function.comp_apply, mul_mul_mul_comm] using
        congrArg (fun z => dl w (x j) * dl w (y j) * z) e
    exact Prod.ext (funext fun i => hf (congrFun (congrArg Prod.fst eq) i))
      (funext fun i => hf (congrFun (congrArg Prod.snd eq) i))
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_units_int,
    pow_add] using Fintype.card_le_of_injective signs hinj

theorem ev2_inj (w : Pl E) : Function.Injective (fun (ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ))
    (p : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2}) => ev2 w ξ.1 ξ.2 p.1.1 p.1.2) := by
  obtain ⟨x, y, hgap, hsep⟩ := exists_separating_probes (a := a) (b := b) w
  intro u v h
  apply hsep
  exact funext fun p => congrFun h ⟨(x p, y p), hgap p⟩

/-- The number of distinct joint Hecke eigencharacters is at most the fixed-space dimension. -/
theorem jeigR_encard_le_finrank {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E)
    (ρ : Representation ℂ (GLw a w × GLw b w) V) (ϖ : (w.adicCompletion E)ˣ)
    [FiniteDimensional ℂ (fixed ρ (I2 a b w))] :
    {ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ) | JEigR w ρ ϖ ξ.1 ξ.2}.encard ≤ Module.finrank ℂ (fixed ρ (I2 a b w)) := by
  obtain ⟨x, y, hgap, hsep⟩ := exists_separating_probes (a := a) (b := b) w
  choose T hT using fun p => hk_lin ρ (I2 a b w) (dc2 w ϖ (x p) (y p))
  refine (Set.encard_le_encard ?_).trans (encard_eig_le_finrank (fixed ρ (I2 a b w)) T _ hsep)
  rintro ⟨ξa, ξb⟩ ⟨v, hv, hv0, he⟩
  exact ⟨v, hv, hv0, fun p => by rw [← hT]; exact he _ _ (hgap p).1 (hgap p).2⟩

theorem jeigR_finite {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E)
    (ρ : Representation ℂ (GLw a w × GLw b w) V) (ϖ : (w.adicCompletion E)ˣ)
    [FiniteDimensional ℂ (fixed ρ (I2 a b w))] :
    {ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ) | JEigR w ρ ϖ ξ.1 ξ.2}.Finite :=
  Set.finite_of_encard_le_coe (jeigR_encard_le_finrank w ρ ϖ)

end UpperTheory.HeckeLevelFrameExistence.Ev

end
