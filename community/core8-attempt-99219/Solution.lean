import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs

noncomputable section

open PositivityTheory.PfSWUS.Loc Filter Topology Matrix
open Finset hiding card card_fin card_subtype
open Ideal.Quotient (mk_surjective eq_zero_iff_mem factor factor_mk)
open Nat (card card_congr card_eq_fintype_card card_fun card_fin card_prod)
open Fintype (ofFinite card_subtype card_units sum_equiv card_sigma)
open AddChar (map_add_eq_mul map_zero_eq_one)

namespace C8

abbrev Qk (R : Type) [CommRing R] (ϖ : R) k := R ⧸ lev ϖ k
abbrev mkQ {R : Type} [CommRing R] (ϖ : R) k := Ideal.Quotient.mk $ lev ϖ k
abbrev Mat a b α := Matrix (Fin a) (Fin b) α
abbrev sx := @Subtype.ext
abbrev iqEq := @Ideal.Quotient.eq

def barσ {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) k : Qk R ϖ k →+* Qk R ϖ k :=
  Ideal.Quotient.lift (lev ϖ k) ((mkQ ϖ k).comp σ) fun _ ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul, map_pow, h]
    exact eq_zero_iff_mem.2 $ Ideal.mul_mem_left _ _ $ Ideal.mem_span_singleton_self _

@[simp] lemma barσ_mk {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} (h : σ ϖ = ϖ) k a :
    barσ σ ϖ h k (mkQ ϖ k a) = mkQ ϖ k (σ a) := rfl

lemma barσ_inv {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} (h : σ ϖ = ϖ) (hi : ∀ a, σ (σ a) = a) k a :
    barσ σ ϖ h k (barσ σ ϖ h k a) = a := by
  obtain ⟨_, rfl⟩ := mk_surjective a
  simp [hi]

section MatLemmas
variable {A : Type} [CommRing A]

@[simp] lemma cT_mul (τ : A →+* A) {a b c} (x : Mat a b A) (y : Mat b c A) :
    cT τ (x * y) = cT τ y * cT τ x := by simp [cT, Matrix.map_mul, transpose_mul]
@[simp] lemma cT_one (τ : A →+* A) {a} : cT τ (1 : Mat a a A) = 1 := by
  simp [cT, Matrix.map_one _ (map_zero τ) $ map_one τ]
@[simp] lemma cT_zero (τ : A →+* A) {a b} : cT τ (0 : Mat a b A) = 0 := by
                                                                           ext
                                                                           simp [cT]
@[simp] lemma cT_add (τ : A →+* A) {a b} (x y : Mat a b A) : cT τ (x + y) = cT τ x + cT τ y := by
                                                                                                  ext
                                                                                                  simp [cT]
@[simp] lemma cT_sub (τ : A →+* A) {a b} (x y : Mat a b A) : cT τ (x - y) = cT τ x - cT τ y := by
                                                                                                  ext
                                                                                                  simp [cT]
@[simp] lemma cT_neg (τ : A →+* A) {a b} (x : Mat a b A) : cT τ (-x) = -cT τ x := by
                                                                                     ext
                                                                                     simp [cT]
@[simp] lemma cT_smul (τ : A →+* A) {a b} (c : A) (x : Mat a b A) : cT τ (c • x) = τ c • cT τ x := by
                                                                                                      ext
                                                                                                      simp [cT]
@[simp] lemma cT_single (τ : A →+* A) {n} (i j : Fin n) c : cT τ (single i j c) = single j i (τ c) := by
  simp [cT, map_single, transpose_single]

lemma cT_cT {τ : A →+* A} (hτ : ∀ a, τ (τ a) = a) {a b} (x : Mat a b A) : cT τ (cT τ x) = x := by
  ext
  exact hτ _

@[simp] lemma red_mul (ϖ : A) k {a b c} (x : Mat a b A) (y : Mat b c A) :
    red ϖ k (x * y) = red ϖ k x * red ϖ k y := Matrix.map_mul
@[simp] lemma red_one (ϖ : A) k {a} : red ϖ k (1 : Mat a a A) = 1 :=
  Matrix.map_one _ (map_zero _) $ map_one _
@[simp] lemma red_zero (ϖ) k {a b} : red ϖ k (0 : Mat a b A) = 0 := by
                                                                       ext
                                                                       simp [red]
@[simp] lemma red_add (ϖ : A) k {a b} (x y : Mat a b A) : red ϖ k (x + y) = red ϖ k x + red ϖ k y := by
                                                                                                        ext
                                                                                                        simp [red]
@[simp] lemma red_sub (ϖ : A) k {a b} (x y : Mat a b A) : red ϖ k (x - y) = red ϖ k x - red ϖ k y := by
                                                                                                        ext
                                                                                                        simp [red]
@[simp] lemma red_neg (ϖ : A) k {a b} (x : Mat a b A) : red ϖ k (-x) = -red ϖ k x := by
                                                                                        ext
                                                                                        simp [red]

lemma red_cT {σ : A →+* A} (ϖ : A) (h : σ ϖ = ϖ) k {a b} (x : Mat a b A) :
    red ϖ k (cT σ x) = cT (barσ σ ϖ h k) (red ϖ k x) := by ext; rfl

lemma red_diagonal (ϖ : A) k {n} (d : Fin n → A) :
    red ϖ k (diagonal d) = diagonal fun i => mkQ ϖ k $ d i := diagonal_map $ map_zero _

lemma red_surj (ϖ : A) k {a b} : Function.Surjective (red ϖ k : Mat a b A → _) := fun y =>
  ⟨of fun i j => (mk_surjective $ y i j).choose, by
                                                    ext i j
                                                    exact (mk_surjective $ y i j).choose_spec⟩

lemma red_gram {σ : A →+* A} (ϖ : A) (h : σ ϖ = ϖ) k {m n} (S : Mat m m A) (x : Mat m n A) :
    red ϖ k (cT σ x * S * x) = cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x := by
  simp [red_cT ϖ h]

lemma solImg_eq {σ : A →+* A} (ϖ : A) (h : σ ϖ = ϖ) k {m n} (S : Mat m m A) (T : Mat n n A) :
    red ϖ k '' {x : Mat m n A | red ϖ k (cT σ x * S * x) = red ϖ k T} =
      {y | cT (barσ σ ϖ h k) y * red ϖ k S * y = red ϖ k T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [red_gram ϖ h] using hx
  · intro hy
    obtain ⟨x, rfl⟩ := red_surj ϖ k y
    exact ⟨x, by simpa [red_gram ϖ h] using hy, rfl⟩

lemma mem_lev_iff {ϖ : A} {k} {a : A} : a ∈ lev ϖ k ↔ ∃ c, a = ϖ ^ k * c := by
  rw [lev, Ideal.mem_span_singleton, dvd_def]

lemma lev_le {ϖ : A} {j k} (h : j ≤ k) : lev ϖ k ≤ lev ϖ j :=
  Ideal.span_singleton_le_span_singleton.2 $ pow_dvd_pow ϖ h

lemma unit_notMem {ϖ x : A} (hϖ : ¬ IsUnit ϖ) (hx : IsUnit x) : x ∉ lev ϖ 1 := fun h => by
  obtain ⟨_, rfl⟩ := mem_lev_iff.1 h
  apply hϖ
  simpa using isUnit_of_mul_isUnit_left hx

end MatLemmas

lemma sum_comp_surj {A B : Type} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (π : A →+ B) (hπ : Function.Surjective π) (G : B → ℂ) :
    (Fintype.card B : ℂ) * ∑ a, G (π a) = (Fintype.card A : ℂ) * ∑ b, G b := by
  classical
  have hfib : ∀ b, (univ.filter fun a => π a = b).card = Fintype.card π.ker := fun b => by
    obtain ⟨a₀, rfl⟩ := hπ b
    rw [← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun x => ⟨x.1 - a₀, by simp [ (mem_filter.1 x.2).2]⟩
        invFun := fun y => ⟨a₀ + y.1, mem_filter.2 ⟨mem_univ _, by simp [AddMonoidHom.mem_ker.1 y.2]⟩⟩
        left_inv := fun x => sx $ by
                                     dsimp
                                     abel
        right_inv := fun y => sx $ by
                                      dsimp
                                      abel }
  have h1 : ∑ a, G (π a) = (Fintype.card π.ker) * ∑ b, G b := by
    rw [← sum_fiberwise_of_maps_to (g := π) $ fun _ _ => mem_univ _, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [sum_congr rfl fun a ha => by rw [(mem_filter.1 ha).2], sum_const, hfib b, nsmul_eq_mul]
  have h2 : (Fintype.card A : ℂ) = (Fintype.card B) * Fintype.card π.ker := by
    have := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup π.ker
    rw [card_congr (QuotientAddGroup.quotientKerEquivOfSurjective π hπ).toEquiv] at this
    simp only [card_eq_fintype_card] at this
    exact_mod_cast this
  rw [h1, h2]
  ring

section UnrQuadBasic
variable {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}

lemma card_quot_lev (hR : IsUnrQuad R σ ϖ q ε) (k : ℕ) : card (Qk R ϖ k) = q ^ (2 * k) := by
  induction k with
  | zero => exact Nat.card_eq_one_iff_unique.2 ⟨Ideal.Quotient.subsingleton_iff.2 $ by simp, ⟨0⟩⟩
  | succ k ih =>
    let φ : Qk R ϖ (k + 1) →+ Qk R ϖ k := (factor $ lev_le $ Nat.le_succ k).toAddMonoidHom
    let ψ : R →+ Qk R ϖ (k + 1) := (mkQ ϖ $ k + 1).toAddMonoidHom.comp $ AddMonoidHom.mulLeft $ ϖ ^ k
    have hker : φ.ker = ψ.range := by
      ext x
      obtain ⟨a, rfl⟩ := mk_surjective x
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, φ, ψ, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply, AddMonoidHom.coe_mulLeft,
        factor_mk, eq_zero_iff_mem]
      refine ⟨fun ha => let ⟨c, hc⟩ := mem_lev_iff.1 ha; ⟨c, by rw [hc]⟩, ?_⟩
      rintro ⟨c, hc⟩
      simpa using sub_mem (mem_lev_iff.2 ⟨c, rfl⟩) $ lev_le (Nat.le_succ k) $ iqEq.1 hc
    have hkerψ : ψ.ker = (lev ϖ 1).toAddSubgroup := by
      ext a
      simp only [AddMonoidHom.mem_ker, ψ, AddMonoidHom.coe_comp, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe, Function.comp_apply, AddMonoidHom.coe_mulLeft, eq_zero_iff_mem,
        Submodule.mem_toAddSubgroup, mem_lev_iff]
      refine ⟨fun ⟨c, hc⟩ => ⟨c, hR.reg.pow k $ by
                                                   show ϖ ^ k * a = ϖ ^ k * (ϖ ^ 1 * c)
                                                   rw [hc]
                                                   ring⟩,
        fun ⟨c, hc⟩ => ⟨c, by rw [hc]; ring⟩⟩
    have e1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
    rw [card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ $ fun y => let ⟨a, ha⟩ := mk_surjective y; ⟨mkQ ϖ (k + 1) a, ha⟩).toEquiv, hker,
      ← card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv, hkerψ] at e1
    change card (Qk R ϖ $ k + 1) = card (Qk R ϖ k) * card (Qk R ϖ 1) at e1
    rw [e1, ih, hR.card]
    ring

lemma finite_quot (hR : IsUnrQuad R σ ϖ q ε) k : Finite $ Qk R ϖ k :=
  Nat.finite_of_card_ne_zero $ by rw [card_quot_lev hR k]; have := hR.one_lt; positivity

lemma exists_trace_one (hR : IsUnrQuad R σ ϖ q ε) : ∃ c : R, c + σ c = 1 := by
  obtain ⟨u, hu, -⟩ := hR.basis
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : (u - σ u) * σ v = -1 := by
    have := congrArg σ hv; simp only [map_mul, map_sub, hR.inv, map_one] at this; linear_combination -this
  exact ⟨u * v, by rw [map_mul, show σ v = -v by linear_combination v * h1 - σ v * hv]; linear_combination hv⟩

lemma mem_of_trace_mem (hR : IsUnrQuad R σ ϖ q ε) {k y} (h : ∀ t, t * y + σ (t * y) ∈ lev ϖ k) : y ∈ lev ϖ k := by
  obtain ⟨u, hu, -⟩ := hR.basis
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  rw [show y = v * ((u - σ u) * y) by rw [← mul_assoc, hv, one_mul]]
  exact Ideal.mul_mem_left _ _ (by
    rw [show (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y)) by
                                                                                simp
                                                                                ring]
    exact Ideal.sub_mem _ (h u) (Ideal.mul_mem_left _ _ (h 1)))

lemma card_hermMod (hR : IsUnrQuad R σ ϖ q ε) (n k : ℕ) : card (hermMod σ ϖ n k) = q ^ (k * n ^ 2) := by
  classical
  have := finite_quot hR k
  let FixQ := Set.range fun x : {a : R // σ a = a} => mkQ ϖ k x.1
  obtain ⟨u, hu, hbas⟩ := hR.basis
  have hFix : card FixQ = q ^ k := by
    let φ : FixQ × FixQ → Qk R ϖ k := fun p => p.1.1 + p.2.1 * mkQ ϖ k u
    have hbij : Function.Bijective φ := by
      refine ⟨fun ⟨⟨_, x₁, rfl⟩, ⟨_, y₁, rfl⟩⟩ ⟨⟨_, x₂, rfl⟩, ⟨_, y₂, rfl⟩⟩ h => ?_, fun z => ?_⟩
      · have hd : (x₁.1 - x₂.1) + (y₁.1 - y₂.1) * u ∈ lev ϖ k := by
                                                                    convert iqEq.1 h using 1
                                                                    ring
        have hsd : σ ((x₁.1 - x₂.1) + (y₁.1 - y₂.1) * u) ∈ lev ϖ k := by
          obtain ⟨t, ht⟩ := mem_lev_iff.1 hd
          exact mem_lev_iff.2 ⟨σ t, by rw [ht, map_mul, map_pow, hR.fix_ϖ]⟩
        have hy : y₁.1 - y₂.1 ∈ lev ϖ k := by
          have hsub := Ideal.sub_mem _ hd hsd
          simp only [map_add, map_sub, map_mul, x₁.2, x₂.2, y₁.2, y₂.2] at hsub
          obtain ⟨v, hv⟩ := hu.exists_right_inv
          simpa [mul_assoc, hv] using Ideal.mul_mem_right v _ (by
                                                                  convert hsub using 1
                                                                  ring : (y₁.1 - y₂.1) * (u - σ u) ∈ lev ϖ k)
        exact Prod.ext (sx $ iqEq.2 $ by
                                         convert Ideal.sub_mem _ hd (Ideal.mul_mem_right u _ hy) using 1
                                         ring)
          (sx $ iqEq.2 hy)
      · obtain ⟨a, rfl⟩ := mk_surjective z
        obtain ⟨x, y, hx, hy, rfl⟩ := hbas a
        exact ⟨⟨⟨mkQ ϖ k x, ⟨x, hx⟩, rfl⟩, ⟨mkQ ϖ k y, ⟨y, hy⟩, rfl⟩⟩, by simp [φ]⟩
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) $ by
      dsimp only
      rw [sq, sq, ← card_prod, card_congr $ Equiv.ofBijective φ hbij, card_quot_lev hR k, ← pow_add, two_mul]
  let Up := {p : Fin n × Fin n // p.1 < p.2}
  let fromH : hermMod σ ϖ n k → (Fin n → FixQ) × (Up → Qk R ϖ k) := fun ⟨B, hB⟩ =>
    (fun i => ⟨B i i, let ⟨H₀, hH₀, hB'⟩ := hB; ⟨⟨H₀ i i, congrFun (congrFun hH₀ i) i⟩, congrFun (congrFun hB' i) i⟩⟩,
     fun p => B p.1.1 p.1.2)
  have hbij : Function.Bijective fromH := by
    refine ⟨fun ⟨B₁, H₁, hH₁, hB₁⟩ ⟨B₂, H₂, hH₂, hB₂⟩ h => sx ?_, fun ⟨d, U⟩ => ?_⟩
    · subst hB₁ hB₂
      ext i j
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact congrFun (congrArg Prod.snd h) ⟨(i, j), hij⟩
      · exact congrArg Subtype.val $ congrFun (congrArg Prod.fst h) i
      · have hji : mkQ ϖ k (H₁ j i) = mkQ ϖ k (H₂ j i) := congrFun (congrArg Prod.snd h) ⟨(j, i), hij⟩
        have hH1 : σ (H₁ j i) = H₁ i j := congrFun (congrFun hH₁ i) j
        have hH2 : σ (H₂ j i) = H₂ i j := congrFun (congrFun hH₂ i) j
        simpa [red, hH1, hH2] using (congrArg (barσ σ ϖ hR.fix_ϖ k) hji)
    · let d' i := (d i).2.choose
      let U' p := (mk_surjective $ U p).choose
      let H := of fun i j =>
        if h : i < j then U' ⟨(i, j), h⟩ else if h' : j < i then σ (U' ⟨(j, i), h'⟩) else (d' i).1
      have hH : cT σ H = H := by
        ext i j
        show σ (H j i) = H i j
        rcases lt_trichotomy i j with h | rfl | h
        · simp [H, h, not_lt.2 h.le, hR.inv]
        · simp [H, (d' i).2]
        · simp [H, h, not_lt.2 h.le]
      refine ⟨⟨red ϖ k H, H, hH, rfl⟩, Prod.ext (funext fun i => sx ?_) $ funext fun ⟨⟨i, j⟩, hij⟩ => ?_⟩
      · simpa [fromH, red, H] using (d i).2.choose_spec
      · simpa [fromH, red, H, hij] using (mk_surjective $ U ⟨(i, j), hij⟩).choose_spec
  have hUp : 2 * card Up + n = n ^ 2 := by
    let e : Fin n × Fin n ≃ (Up ⊕ Up) ⊕ Fin n :=
      { toFun := fun p => if h : p.1 < p.2 then .inl (.inl ⟨p, h⟩) else if h' : p.2 < p.1 then .inl (.inr ⟨p.swap, h'⟩) else .inr p.1
        invFun := Sum.elim (Sum.elim Subtype.val $ Prod.swap ∘ Subtype.val) fun i => (i, i)
        left_inv := fun ⟨i, j⟩ => by
          rcases lt_trichotomy i j with h | rfl | h
          · simp [h]
          · simp
          · simp [h, not_lt.2 h.le]
        right_inv := by
          rintro ((⟨⟨i, j⟩, h⟩ | ⟨⟨i, j⟩, h⟩) | i)
          · simp [h]
          · simp [h, not_lt.2 h.le]
          · simp }
    have := card_congr e
    simp only [card_prod, card_fin, Nat.card_sum] at this
    nlinarith
  rw [card_congr $ Equiv.ofBijective fromH hbij, card_prod, card_fun, card_fun, card_fin, hFix,
    card_quot_lev hR k, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  nlinarith

end UnrQuadBasic

structure ResAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ) : Prop where
  inv : ∀ a, τ (τ a) = a
  fixedUnit : ∀ a, τ a = a → a ≠ 0 → IsUnit a
  basis : ∃ u : E, IsUnit (u - τ u) ∧ ∀ a, ∃ x y, τ x = x ∧ τ y = y ∧ a = x + y * u
  one_lt : 1 < q
  card : card E = q ^ 2
  eps : (ε = -1 ∧ IsField E) ∨ (ε = 1 ∧ ¬ IsField E)

lemma resAlg_of_isUnrQuad {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (hR : IsUnrQuad R σ ϖ q ε) : ResAlg (Qk R ϖ 1) (barσ σ ϖ hR.fix_ϖ 1) q ε := by
  obtain ⟨u, hu, hbas⟩ := hR.basis
  obtain ⟨c, hc⟩ := exists_trace_one hR
  refine ⟨barσ_inv hR.fix_ϖ hR.inv 1, fun a ha hne => ?_, ⟨mkQ ϖ 1 u, by simpa using hu.map $ mkQ ϖ 1, fun a => ?_⟩,
    hR.one_lt, hR.card, hR.eps⟩
  · obtain ⟨x, rfl⟩ := mk_surjective a
    let y := c * x + σ (c * x)
    have hxy : mkQ ϖ 1 y = mkQ ϖ 1 x := by
      have h1 : mkQ ϖ 1 (σ x) = mkQ ϖ 1 x := ha
      change mkQ ϖ 1 (c * x + σ (c * x)) = mkQ ϖ 1 x
      rw [map_add, map_mul, map_mul, map_mul, h1, ← add_mul, ← map_add, hc, map_one, one_mul]
    rw [← hxy]
    exact (hR.fixLocal y (by simp [y, hR.inv, add_comm]) fun hm => hne $ hxy.symm.trans $ eq_zero_iff_mem.2 hm).map _
  · obtain ⟨x, rfl⟩ := mk_surjective a
    obtain ⟨x₁, y₁, hx₁, hy₁, rfl⟩ := hbas x
    exact ⟨mkQ ϖ 1 x₁, mkQ ϖ 1 y₁, by simp [hx₁], by simp [hy₁], by simp⟩

section ResAlgTheory
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

lemma resAlg_finite (h : ResAlg E τ q ε) : Finite E :=
  Nat.finite_of_card_ne_zero $ by rw [h.card]; have := h.one_lt; positivity

lemma resAlg_nontrivial (h : ResAlg E τ q ε) : Nontrivial E := by
  have := resAlg_finite h; have := h.one_lt
  apply Finite.one_lt_card_iff_nontrivial.1
  rw [h.card]
  nlinarith

def fixSub (τ : E →+* E) : Subring E where
  carrier := {x | τ x = x}
  mul_mem' {a b} ha hb := show τ (a * b) = a * b by rw [map_mul, ha, hb]
  one_mem' := map_one τ
  add_mem' {a b} ha hb := show τ (a + b) = a + b by rw [map_add, ha, hb]
  zero_mem' := map_zero τ
  neg_mem' {a} ha := show τ (-a) = -a by rw [map_neg, ha]

@[simp] lemma fixSub_eq (x : fixSub τ) : τ x.1 = x.1 := x.2

lemma resAlg_card_fixed (h : ResAlg E τ q ε) : card (fixSub τ) = q := by
  obtain ⟨u, hu, hbas⟩ := h.basis
  let φ : fixSub τ × fixSub τ → E := fun p => p.1.1 + p.2.1 * u
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) $ by
    dsimp only
    rw [sq, ← card_prod, card_congr $ Equiv.ofBijective φ $ by
      refine ⟨fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ heq => ?_, fun a => let ⟨x, y, hx, hy, hxy⟩ := hbas a; ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy.symm⟩⟩
      have hτ := congrArg τ heq; simp only [φ, map_add, map_mul, fixSub_eq] at hτ
      have hy0 : y₁.1 = y₂.1 := sub_eq_zero.1 $ hu.mul_left_eq_zero.1 $ by linear_combination heq - hτ
      exact Prod.ext (sx $ by linear_combination heq - u * hy0) $ sx hy0, h.card]

lemma resAlg_fix_field (h : ResAlg E τ q ε) : IsField (fixSub τ) := by
  have := resAlg_nontrivial h
  refine ⟨⟨0, 1, by simp⟩, mul_comm, fun {x} hx => ?_⟩
  obtain ⟨v, hv⟩ := (h.fixedUnit x.1 x.2 fun h0 => hx $ sx h0).exists_right_inv
  have h1 : x.1 * τ v = 1 := by simpa using congrArg τ hv
  exact ⟨⟨v, show τ v = v by linear_combination v * h1 - τ v * hv⟩, sx hv⟩

lemma resAlg_split_equiv (h : ResAlg E τ q ε) (hnf : ¬ IsField E) :
    ∃ e : fixSub τ × fixSub τ ≃+* E, (∀ x y, τ (e (x, y)) = e (y, x)) ∧ ∀ x, e (x, x) = x.1 := by
  have := resAlg_finite h
  have := resAlg_nontrivial h
  obtain ⟨u, hu, -⟩ := h.basis
  have hnu : ∃ z : E, z ≠ 0 ∧ ¬ IsUnit z := by
    by_contra hall
    push Not at hall
    exact hnf ⟨exists_pair_ne E, mul_comm, fun {a} ha => (hall a ha).exists_right_inv⟩
  obtain ⟨z, hz0, hzu⟩ := hnu
  have hzτ : z * τ z = 0 := by
    by_contra hne
    exact hzu $ isUnit_of_mul_isUnit_left $ h.fixedUnit _ (by rw [map_mul, h.inv, mul_comm]) hne
  obtain ⟨t, ht⟩ := (h.fixedUnit (z + τ z) (by rw [map_add, h.inv, add_comm]) $ fun h0 => by
    have hτz : τ z = -z := eq_neg_of_add_eq_zero_right h0
    exact hzu $ isUnit_of_mul_isUnit_left $ h.fixedUnit (z * (u - τ u)) (by rw [map_mul, map_sub, hτz, h.inv]; ring)
      fun h' => hz0 $ hu.mul_left_eq_zero.1 h').exists_right_inv
  have hτt : τ t = t := by
    have h1 : (z + τ z) * τ t = 1 := by simpa [map_add, h.inv, add_comm] using congrArg τ ht
    linear_combination t * h1 - τ t * ht
  let e := z * t
  have he_add : e + τ e = 1 := by simp only [e, map_mul, hτt, ← add_mul]; exact ht
  have he_mul : e * τ e = 0 := by simp only [e, map_mul, hτt]; linear_combination t * t * hzτ
  have he_sq : e * e = e := by linear_combination e * he_add - he_mul
  have hτe_sq : τ e * τ e = τ e := by rw [← map_mul, he_sq]
  have he0 : e ≠ 0 := fun h0 => hz0 $ by
    have h1 : e * (z + τ z) = 0 := by rw [h0, zero_mul]
    linear_combination h1 - z * ht
  let ψ : fixSub τ × fixSub τ →+* E :=
    { toFun := fun p => p.1.1 * e + p.2.1 * τ e
      map_one' := by simp [he_add]
      map_mul' := fun p₁ p₂ => by
        show (p₁.1.1 * p₂.1.1) * e + (p₁.2.1 * p₂.2.1) * τ e = (p₁.1.1 * e + p₁.2.1 * τ e) * (p₂.1.1 * e + p₂.2.1 * τ e)
        linear_combination -(p₁.1.1 * p₂.1.1) * he_sq - (p₁.2.1 * p₂.2.1) * hτe_sq - (p₁.1.1 * p₂.2.1 + p₁.2.1 * p₂.1.1) * he_mul
      map_zero' := by simp
      map_add' := fun p₁ p₂ => by
                                  show (p₁.1.1 + p₂.1.1) * e + (p₁.2.1 + p₂.2.1) * τ e = _
                                  ring }
  let : Fintype E := ofFinite E
  let : Fintype (fixSub τ) := ofFinite _
  exact ⟨RingEquiv.ofBijective ψ ((Fintype.bijective_iff_injective_and_card ψ).2 ⟨(fun p₁ p₂ hp => by
    have h1 : (p₁.1.1 - p₂.1.1) * e = 0 := by
      have := congrArg (· * e) hp; dsimp [ψ] at this
      linear_combination this - (p₁.1.1 - p₂.1.1) * he_sq - (p₁.2.1 - p₂.2.1) * he_mul
    have h2 : (p₁.2.1 - p₂.2.1) * τ e = 0 := by
      have := congrArg (· * τ e) hp; dsimp [ψ] at this
      linear_combination this - (p₁.2.1 - p₂.2.1) * hτe_sq - (p₁.1.1 - p₂.1.1) * he_mul
    exact Prod.ext
      (sx $ sub_eq_zero.1 $ by
                               by_contra hne
                               exact he0 $ (h.fixedUnit _ (by simp) hne).mul_right_eq_zero.1 h1)
      (sx $ sub_eq_zero.1 $ by
        by_contra hne
        exact (fun h' => he0 $ by simpa [h.inv] using congrArg τ h') $ (h.fixedUnit _ (by simp) hne).mul_right_eq_zero.1 h2)), by
    rw [Fintype.card_prod, ← card_eq_fintype_card, ← card_eq_fintype_card, resAlg_card_fixed h, h.card, sq]⟩), fun x y => by
                                                                                                                             change τ (x.1 * e + y.1 * τ e) = y.1 * e + x.1 * τ e
                                                                                                                             simp [h.inv, add_comm],
    fun x => by
                change x.1 * e + x.1 * τ e = x.1
                rw [← mul_add, he_add, mul_one]⟩

lemma norm_fibre_card_nonzero (h : ResAlg E τ q ε) {b : E} (hb : τ b = b) (hb0 : b ≠ 0) :
    (card {a : E // a * τ a = b} : ℤ) = (q : ℤ) - ε := by
  classical
  have := resAlg_finite h
  have := resAlg_nontrivial h
  let : Fintype E := ofFinite E
  let : Fintype (fixSub τ) := ofFinite _
  let : Field (fixSub τ) := (resAlg_fix_field h).toField
  have hq := h.one_lt
  have hcardF : card (fixSub τ)ˣ = q - 1 := by rw [card_eq_fintype_card, card_units, ← card_eq_fintype_card, resAlg_card_fixed h]
  rcases h.eps with ⟨rfl, hF⟩ | ⟨rfl, hnf⟩
  · let : Field E := hF.toField
    have hτ0 : ∀ {x : E}, x ≠ 0 → τ x ≠ 0 := fun hx h0 => hx $ by simpa using congrArg τ h0
    let N : Eˣ →* (fixSub τ)ˣ :=
      { toFun := fun x => Units.mk0 ⟨x.1 * τ x.1, show τ (x.1 * τ x.1) = _ by rw [map_mul, h.inv, mul_comm]⟩
          fun h0 => mul_ne_zero x.ne_zero (hτ0 x.ne_zero) $ congrArg Subtype.val h0
        map_one' := by
                       ext
                       simp
        map_mul' := fun x y => by
                                  ext
                                  show x.1 * y.1 * τ (x.1 * y.1) = _; simp; ring }
    let φ : Eˣ →* Eˣ :=
      { toFun := fun y => y * (Units.map τ.toMonoidHom y)⁻¹
        map_one' := by
                       ext
                       simp
        map_mul' := fun x y => by
                                  ext
                                  show x.1 * y.1 * τ (y.2 * x.2) = x.1 * τ x.2 * (y.1 * τ y.2); simp; ring }
    obtain ⟨u, hu, -⟩ := h.basis
    have hrg : φ.range = N.ker := by
      ext z
      refine ⟨?_, fun hz => ?_⟩
      · rintro ⟨y, rfl⟩
        rw [MonoidHom.mem_ker]
        ext
        show (y.1 * τ y.2) * τ (y.1 * τ y.2) = 1
        simp only [map_mul, h.inv]
        calc y.1 * τ y.2 * (τ y.1 * y.2) = (y.1 * y.2) * τ (y.1 * y.2) := by rw [map_mul]; ring
          _ = 1 := by rw [y.val_inv, map_one, mul_one]
      · have hzN : z.1 * τ z.1 = 1 := congrArg (fun u : (fixSub τ)ˣ => (u.1 : E)) hz
        by_cases h1z : 1 + z.1 = 0
        · refine ⟨hu.unit, Units.ext ?_⟩
          show (u - τ u) * τ (hu.unit⁻¹ : Eˣ) = z.1
          have hinv : τ (hu.unit⁻¹ : Eˣ) * -(u - τ u) = 1 := by
            rw [← show τ (u - τ u) = -(u - τ u) by rw [map_sub, h.inv]; ring, ← map_mul,
              show ((hu.unit⁻¹ : Eˣ) : E) * (u - τ u) = 1 from hu.unit.inv_mul, map_one]
          rw [eq_neg_of_add_eq_zero_right h1z]
          linear_combination -hinv
        · refine ⟨Units.mk0 (1 + z.1) h1z, Units.ext ?_⟩
          show (1 + z.1) * τ ((1 + z.1)⁻¹) = z.1
          rw [map_inv₀, mul_inv_eq_iff_eq_mul₀ $ hτ0 h1z, map_add, map_one, mul_add, mul_one, hzN, add_comm]
    have hkerφ : card φ.ker = q - 1 := by
      have e : φ.ker ≃ (fixSub τ)ˣ :=
        { toFun := fun ⟨y, hy⟩ =>
            have hτy : τ y.1 = y.1 := by
              have h2 : τ y.1 * τ y.2 = 1 := by rw [← map_mul, y.val_inv, map_one]
              exact mul_right_cancel₀ (hτ0 y⁻¹.ne_zero) $ h2.trans (congrArg Units.val hy).symm
            Units.mk0 ⟨y.1, hτy⟩ fun h0 => y.ne_zero $ congrArg Subtype.val h0
          invFun := fun x => ⟨Units.mk0 x.1.1 fun h0 => x.ne_zero $ sx h0, by
            rw [MonoidHom.mem_ker]
            ext
            show x.1.1 * τ (x.1.1⁻¹) = 1
            rw [map_inv₀, fixSub_eq, mul_inv_cancel₀ fun h0 => x.ne_zero $ sx h0]⟩
          left_inv := fun ⟨y, _⟩ => sx $ Units.ext rfl
          right_inv := fun x => Units.ext $ sx rfl }
      rw [card_congr e, hcardF]
    have hcardE : card Eˣ = q ^ 2 - 1 := by rw [card_eq_fintype_card, card_units, ← card_eq_fintype_card, h.card]
    have hq2 : 1 ≤ q ^ 2 := by nlinarith
    have hkerN : card N.ker = q + 1 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
      rw [card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrg, hcardE, hkerφ,
        show q ^ 2 - 1 = (q + 1) * (q - 1) by zify [le_of_lt hq, hq2]; ring] at h1
      exact Nat.eq_of_mul_eq_mul_right (by omega) h1.symm
    have hNsurj : Function.Surjective N := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N.ker
      rw [card_congr (QuotientGroup.quotientKerEquivRange N).toEquiv, hcardE, hkerN,
        show q ^ 2 - 1 = (q - 1) * (q + 1) by zify [le_of_lt hq, hq2]; ring] at h1
      exact fun y => ((Subgroup.eq_top_of_card_eq _ $ by rw [hcardF]; exact Nat.eq_of_mul_eq_mul_right (by omega) h1.symm) ▸ Subgroup.mem_top y : y ∈ N.range)
    let bU : (fixSub τ)ˣ := Units.mk0 ⟨b, hb⟩ fun h0 => hb0 $ congrArg Subtype.val h0
    obtain ⟨a₀, ha₀⟩ := hNsurj bU
    have e : {a : E // a * τ a = b} ≃ N.ker :=
      { toFun := fun ⟨a, ha⟩ =>
          have ha0 : a ≠ 0 := fun h0 => hb0 $ by simpa [h0] using ha.symm
          ⟨Units.mk0 a ha0 * a₀⁻¹, by
            rw [MonoidHom.mem_ker, map_mul, map_inv, ha₀, show N (Units.mk0 a ha0) = bU from Units.ext (sx ha), mul_inv_cancel]⟩
        invFun := fun ⟨z, hz⟩ => ⟨(z * a₀).1, by
          have : N (z * a₀) = bU := by rw [map_mul, hz.out, one_mul, ha₀]
          exact congrArg (fun u : (fixSub τ)ˣ => (u.1 : E)) this⟩
        left_inv := fun ⟨_, _⟩ => sx $ by simp
        right_inv := fun ⟨_, _⟩ => sx $ Units.ext $ by simp }
    rw [card_congr e, hkerN]
    omega
  · obtain ⟨e, he, hdiag⟩ := resAlg_split_equiv h hnf
    let bF : fixSub τ := ⟨b, hb⟩
    have hbF0 : bF ≠ 0 := fun h0 => hb0 $ congrArg Subtype.val h0
    have hprod : ∀ {a : E}, a * τ a = b → (e.symm a).1 * (e.symm a).2 = bF := fun {a} ha => by
      set p := e.symm a
      exact (Prod.mk.inj $ e.injective $ by
        rw [hdiag bF]
        show e (p.1 * p.2, p.2 * p.1) = b
        rw [← ha, show (p.1 * p.2, p.2 * p.1) = (p.1, p.2) * (p.2, p.1) from rfl, e.map_mul, ← he p.1 p.2,
          show (p.1, p.2) = e.symm a from rfl, e.apply_symm_apply]).1
    have heq : {a : E // a * τ a = b} ≃ (fixSub τ)ˣ :=
      { toFun := fun ⟨a, ha⟩ => Units.mk0 (e.symm a).1 fun h0 => hbF0 $ by simpa [h0] using (hprod ha).symm
        invFun := fun u => ⟨e (u.1, u.1⁻¹ * bF), by
          rw [he, ← e.map_mul]
          show e (u.1 * (u.1⁻¹ * bF), u.1⁻¹ * bF * u.1) = b
          rw [mul_inv_cancel_left₀ u.ne_zero, mul_comm $ u.1⁻¹ * bF, mul_inv_cancel_left₀ u.ne_zero, hdiag]⟩
        left_inv := fun ⟨a, ha⟩ => sx $ by
          have hp := hprod ha
          show e ((e.symm a).1, (e.symm a).1⁻¹ * bF) = a
          rw [← hp, inv_mul_cancel_left₀ fun h0 => hbF0 $ by simpa [h0] using hp.symm]
          exact e.apply_symm_apply a
        right_inv := fun u => Units.ext $ by
                                             show (e.symm $ e (u.1, u.1⁻¹ * bF)).1 = u.1
                                             rw [e.symm_apply_apply] }
    rw [card_congr heq, hcardF]
    omega

lemma norm_fibre_card_zero (h : ResAlg E τ q ε) :
    (card {a : E // a * τ a = 0} : ℤ) = (q : ℤ) ^ 2 - ((q : ℤ) - 1) * ((q : ℤ) - ε) := by
  classical
  have := resAlg_finite h
  let : Fintype E := ofFinite E
  let : Fintype (fixSub τ) := ofFinite _
  have hpart : Fintype.card E = ∑ b : fixSub τ, (univ.filter fun a => a * τ a = b.1).card := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := fun a => (⟨a * τ a, show τ (a * τ a) = _ by rw [map_mul, h.inv, mul_comm]⟩ : fixSub τ))
      (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun b _ => ?_; congr 1; ext a; simp [Subtype.ext_iff]
  rw [← add_sum_erase _ _ $ mem_univ (0 : fixSub τ)] at hpart
  have hZ : (Fintype.card E) = (card {a : E // a * τ a = 0}) +
      ∑ b ∈ univ.erase (0 : fixSub τ), (card {a : E // a * τ a = b.1} : ℤ) := by
    have := congrArg (Nat.cast (R := ℤ)) hpart; push_cast at this; rw [this]; congr 1
    · rw [card_eq_fintype_card, card_subtype]
    · refine sum_congr rfl fun b _ => ?_
      rw [card_eq_fintype_card, card_subtype]
  have hnz : ∀ b ∈ univ.erase (0 : fixSub τ), (card {a : E // a * τ a = b.1} : ℤ) = (q : ℤ) - ε := fun b hb =>
    norm_fibre_card_nonzero h b.2 fun h0 => (mem_erase.1 hb).1 $ sx h0
  rw [sum_congr rfl hnz, sum_const, card_erase_of_mem $ mem_univ _, card_univ, nsmul_eq_mul,
    ← card_eq_fintype_card, ← card_eq_fintype_card, h.card, resAlg_card_fixed h, Nat.cast_sub h.one_lt.le] at hZ
  push_cast at hZ
  linear_combination -hZ

end ResAlgTheory


section CharsGauss
variable {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}

lemma psi_pow {ψ : ∀ k, AddChar (Qk R ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (k j : ℕ) (a : R) :
    ψ (k + j) (mkQ ϖ (k + j) (ϖ ^ j * a)) = ψ k (mkQ ϖ k a) := by
  induction j with
  | zero => simp
  | succ j ih => rw [← ih, ← add_assoc, pow_succ', mul_assoc]; exact hψ.compat (k + j) $ ϖ ^ j * a

lemma fixed_nondeg {ψ : ∀ k, AddChar (Qk R ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (hfix : σ ϖ = ϖ)
    (hreg : IsSMulRegular R ϖ) (k : ℕ) (a : R) (ha : σ a = a)
    (h : ∀ b, σ b = b → ψ k (mkQ ϖ k (a * b)) = 1) : a ∈ lev ϖ k := by
  induction k generalizing a with
  | zero => simp [lev]
  | succ k ih =>
    obtain ⟨c, rfl⟩ := mem_lev_iff.1 $ ih a ha fun b hb => by
      have := h (ϖ * b) $ by simp [hfix, hb]
      rwa [show a * (ϖ * b) = ϖ * (a * b) by ring, hψ.compat] at this
    obtain ⟨d, rfl⟩ := mem_lev_iff.1 $ hψ.prim c (hreg.pow k $ by simpa [  hfix] using ha) fun b hb => by
      have h2 := psi_pow hψ 1 k $ c * b
      rw [add_comm 1 k, ← mul_assoc] at h2
      rw [← h2]
      exact h b hb
    exact mem_lev_iff.2 ⟨d, by ring⟩

lemma trace_nondeg (hR : IsUnrQuad R σ ϖ q ε) {ψ : ∀ k, AddChar (Qk R ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (k : ℕ) (y : R) (h : ∀ t, ψ k (mkQ ϖ k (t * y + σ (t * y))) = 1) : y ∈ lev ϖ k :=
  mem_of_trace_mem hR fun t =>
    fixed_nondeg hψ hR.fix_ϖ hR.reg k _ (by simp [hR.inv, add_comm]) fun b hb => by
      convert h (b * t) using 3
      simp only [map_mul, hb]
      ring

lemma sum_addChar_eq_zero {G : Type} [AddCommGroup G] [Fintype G] (f : G → ℂ)
    (hf : ∀ x y, f (x + y) = f x * f y) {g₀ : G} (hg : f g₀ ≠ 1) : ∑ x : G, f x = 0 := by
  have h1 : ∑ x : G, f x = f g₀ * ∑ x : G, f x := by
    calc ∑ x : G, f x = ∑ x : G, f (g₀ + x) := (sum_equiv (Equiv.addLeft g₀) _ _ fun _ => rfl).symm
      _ = ∑ x : G, f g₀ * f x := sum_congr rfl fun x _ => hf g₀ x
      _ = f g₀ * ∑ x : G, f x := (mul_sum ..).symm
  exact (mul_eq_zero.1 $ by linear_combination -h1).resolve_left $ sub_ne_zero.2 hg

lemma gauss_level_one (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (Qk R ϖ k)]
    {ψ : ∀ k, AddChar (Qk R ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    {a : R} (ha : σ a = a) (ha1 : a ∉ lev ϖ 1) :
    (∑ w : Qk R ϖ 1, ψ 1 (mkQ ϖ 1 a * (barσ σ ϖ hR.fix_ϖ 1 w * w))) = (ε : ℂ) * q := by
  classical
  let E := Qk R ϖ 1
  let τ := barσ σ ϖ hR.fix_ϖ 1
  have hE := resAlg_of_isUnrQuad hR
  let : Fintype (fixSub τ) := ofFinite _
  let N w : fixSub τ := ⟨w * τ w, show τ (w * τ w) = _ by rw [map_mul, hE.inv, mul_comm]⟩
  have hsum : ∑ w : E, ψ 1 (mkQ ϖ 1 a * (τ w * w)) =
      ∑ b : fixSub τ, ((univ.filter fun w => w * τ w = b.1).card) * ψ 1 (mkQ ϖ 1 a * b.1) := by
    rw [← sum_fiberwise_of_maps_to (g := N) $ fun _ _ => mem_univ _]
    refine sum_congr rfl fun b _ => ?_
    have hfilt : univ.filter (fun w => N w = b) = univ.filter (fun w => w * τ w = b.1) := by
      ext w
      simp [N, Subtype.ext_iff]
    rw [hfilt, sum_congr rfl fun w hw => by rw [mul_comm (τ w) w, (mem_filter.1 hw).2], sum_const, nsmul_eq_mul]
  have hchar0 : ∑ b : fixSub τ, ψ 1 (mkQ ϖ 1 a * b.1) = 0 := by
    have hnt : ∃ b₀ : fixSub τ, ψ 1 (mkQ ϖ 1 a * b₀.1) ≠ 1 := by
      by_contra hall
      push Not at hall
      exact ha1 $ hψ.prim a ha fun b hb => by
        simpa [map_mul] using hall ⟨mkQ ϖ 1 b, show τ (mkQ ϖ 1 b) = _ by simp [τ, hb]⟩
    obtain ⟨b₀, hb₀⟩ := hnt
    exact sum_addChar_eq_zero (fun b : fixSub τ => ψ 1 $ mkQ ϖ 1 a * b.1)
      (fun x y => by
                     show ψ 1 (mkQ ϖ 1 a * (x.1 + y.1)) = _
                     rw [mul_add, map_add_eq_mul]) hb₀
  rw [hsum, ← add_sum_erase _ _ $ mem_univ 0]
  have h0 : ((univ.filter fun w => w * τ w = (0 : fixSub τ).1).card : ℂ) =
      (q : ℂ) ^ 2 - ((q : ℂ) - 1) * ((q : ℂ) - ε) := by
    rw [← card_subtype, ← card_eq_fintype_card]
    exact_mod_cast norm_fibre_card_zero hE
  have hnz : ∀ b ∈ univ.erase (0 : fixSub τ),
      ((univ.filter fun w => w * τ w = b.1).card : ℂ) * ψ 1 (mkQ ϖ 1 a * b.1) =
        ((q : ℂ) - ε) * ψ 1 (mkQ ϖ 1 a * b.1) := fun b hb => by
    congr 1
    rw [← card_subtype, ← card_eq_fintype_card]
    exact_mod_cast norm_fibre_card_nonzero hE b.2 fun h' => (mem_erase.1 hb).1 $ sx h'
  rw [h0, sum_congr rfl hnz, ← mul_sum]
  have herase : ∑ b ∈ univ.erase (0 : fixSub τ), ψ 1 (mkQ ϖ 1 a * b.1) = -1 := by
    rw [← add_sum_erase _ _ $ mem_univ (0 : fixSub τ)] at hchar0
    simp only [ZeroMemClass.coe_zero, mul_zero, map_zero_eq_one] at hchar0
    linear_combination hchar0
  rw [herase]
  simp
  ring

lemma gauss_recursion (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (Qk R ϖ k)]
    {ψ : ∀ k, AddChar (Qk R ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (j : ℕ)
    {a : R} (ha : σ a = a) (ha1 : a ∉ lev ϖ 1) :
    (∑ w : Qk R ϖ (j + 2), ψ (j + 2) (mkQ ϖ (j + 2) a * (barσ σ ϖ hR.fix_ϖ (j + 2) w * w))) =
      (q : ℂ) ^ 2 * ∑ w : Qk R ϖ j, ψ j (mkQ ϖ j a * (barσ σ ϖ hR.fix_ϖ j w * w)) := by
  classical
  let Q1 := Qk R ϖ 1; let Q2 := Qk R ϖ (j + 2)
  let q1 := mkQ ϖ 1; let q2 := mkQ ϖ (j + 2); let τ1 := barσ σ ϖ hR.fix_ϖ 1; let τ2 := barσ σ ϖ hR.fix_ϖ (j + 2)
  let g := fun w => ψ (j + 2) $ q2 a * (τ2 w * w)
  let δ : Q1 →+ Q2 :=
    QuotientAddGroup.lift (lev ϖ 1).toAddSubgroup
      (q2.toAddMonoidHom.comp $ AddMonoidHom.mulLeft $ ϖ ^ (j + 1))
      fun _ hy => let ⟨c, hc⟩ := mem_lev_iff.1 hy; eq_zero_iff_mem.2 $ mem_lev_iff.2 ⟨c, by
                                                                                            dsimp
                                                                                            rw [hc]; ring⟩
  have hshift : ∀ x y : R, g (q2 x + δ (q1 y)) = g (q2 x) * ψ 1 (q1 (a * (σ x * y + σ y * x))) := fun x y => by
    have hmul : q2 (a * (σ (x + ϖ ^ (j + 1) * y) * (x + ϖ ^ (j + 1) * y))) =
        q2 (a * (σ x * x)) + q2 (ϖ ^ (j + 1) * (a * (σ x * y + σ y * x))) := by
      rw [← map_add, iqEq]
      rw [show a * (σ (x + ϖ ^ (j + 1) * y) * (x + ϖ ^ (j + 1) * y)) -
          (a * (σ x * x) + ϖ ^ (j + 1) * (a * (σ x * y + σ y * x))) =
          (ϖ ^ (j + 1) * ϖ ^ (j + 1)) * (a * (σ y * y)) by simp only [map_add, map_mul, map_pow, hR.fix_ϖ]; ring]
      exact Ideal.mul_mem_right _ _ $ mem_lev_iff.2 ⟨ϖ ^ j, by ring⟩
    have h1 : g (q2 x + δ (q1 y)) = ψ (j + 2) (q2 (a * (σ (x + ϖ ^ (j + 1) * y) * (x + ϖ ^ (j + 1) * y)))) := by
      change ψ (j + 2) (q2 a * (τ2 (q2 x + q2 (ϖ ^ (j + 1) * y)) * (q2 x + q2 (ϖ ^ (j + 1) * y)))) = _
      simp only [q2, τ2, ← map_add, barσ_mk, ← map_mul]
    rw [h1, hmul, map_add_eq_mul]
    have h2 : g (q2 x) = ψ (j + 2) (q2 (a * (σ x * x))) := by simp only [g, q2, τ2, barσ_mk, ← map_mul]
    have h3 := psi_pow hψ 1 (j + 1) $ a * (σ x * y + σ y * x)
    rw [add_comm 1 $ j + 1] at h3
    rw [← h2, h3]
  have hcard1 : (Fintype.card Q1 : ℂ) = (q : ℂ) ^ 2 := by rw [← card_eq_fintype_card, hR.card]; push_cast; rfl
  have havg : (q : ℂ) ^ 2 * ∑ w : Q2, g w = ∑ w : Q2, ∑ y : Q1, g (w + δ y) := by
    rw [sum_comm, ← hcard1, ← card_univ (α := Q1), ← nsmul_eq_mul, ← sum_const]
    exact sum_congr rfl fun y _ => (sum_equiv (Equiv.addRight $ δ y) _ _ fun _ => rfl).symm
  let π : Qk R ϖ (j + 1) →+ Q2 :=
    QuotientAddGroup.lift (lev ϖ (j + 1)).toAddSubgroup
      (q2.toAddMonoidHom.comp (AddMonoidHom.mulLeft ϖ))
      fun _ hz => let ⟨c, hc⟩ := mem_lev_iff.1 hz
      eq_zero_iff_mem.2 $ mem_lev_iff.2 ⟨c, by
                                                                                            dsimp
                                                                                            rw [hc]
                                                                                            ring⟩
  have hπinj : Function.Injective π := fun v₁ v₂ hv => by
    obtain ⟨z₁, rfl⟩ := mk_surjective v₁; obtain ⟨z₂, rfl⟩ := mk_surjective v₂
    obtain ⟨c, hc⟩ := mem_lev_iff.1 (by rw [mul_sub]; exact iqEq.1 hv : ϖ * (z₁ - z₂) ∈ lev ϖ (j + 2))
    exact iqEq.2 $ mem_lev_iff.2 ⟨c, hR.reg $ by
                                                 show ϖ * (z₁ - z₂) = ϖ * (ϖ ^ (j + 1) * c)
                                                 rw [hc]; ring⟩
  have hinner : ∀ w : Q2, ∑ y : Q1, g (w + δ y) = if w ∈ π.range then (q : ℂ) ^ 2 * g w else 0 := fun w => by
    obtain ⟨x, rfl⟩ := mk_surjective w
    let χx y := ψ 1 $ q1 a * (q1 (σ x) * y + τ1 y * q1 x)
    have hrw : ∑ y : Q1, g (q2 x + δ y) = g (q2 x) * ∑ y : Q1, χx y := by
      rw [mul_sum]; refine sum_congr rfl fun y _ => ?_
      obtain ⟨r, rfl⟩ := mk_surjective y
      rw [hshift x r]
      simp only [χx, q1, τ1, barσ_mk, ← map_mul, ← map_add]
    rw [hrw]
    by_cases hmem : q2 x ∈ π.range
    · rw [ite_eq_left hmem]
      obtain ⟨v, hv⟩ := hmem; obtain ⟨z, rfl⟩ := mk_surjective v
      have hx1 : x ∈ lev ϖ 1 := by
        simpa using sub_mem (mem_lev_iff.2 ⟨z, by ring⟩ : ϖ * z ∈ lev ϖ 1) $ lev_le (by omega) $ iqEq.1 hv
      have hsx1 : σ x ∈ lev ϖ 1 := let ⟨c, hc⟩ := mem_lev_iff.1 hx1; mem_lev_iff.2 ⟨σ c, by rw [hc]; simp [hR.fix_ϖ]⟩
      simp only [χx, q1, eq_zero_iff_mem.2 hx1, eq_zero_iff_mem.2 hsx1, zero_mul, mul_zero, add_zero, map_zero_eq_one,
        sum_const, card_univ, nsmul_eq_mul, mul_one, hcard1]; ring
    · rw [ite_eq_right hmem]
      have hx1 : x ∉ lev ϖ 1 := fun hx => hmem $
        let ⟨z, hz⟩ := mem_lev_iff.1 hx; ⟨mkQ ϖ (j + 1) z, by
                                                              change q2 (ϖ * z) = _
                                                              rw [hz, pow_one]⟩
      have hax1 : a * σ x ∉ lev ϖ 1 := fun h => hx1 $ by
        obtain ⟨u, hu⟩ := (hR.fixLocal a ha ha1).exists_left_inv
        have h1 : σ x ∈ lev ϖ 1 := by rw [show σ x = u * (a * σ x) by rw [← mul_assoc, hu, one_mul]]; exact Ideal.mul_mem_left _ _ h
        obtain ⟨c, hc⟩ := mem_lev_iff.1 h1
        exact mem_lev_iff.2 ⟨σ c, by rw [← hR.inv x, hc, map_mul, map_pow, hR.fix_ϖ]⟩
      have hnt : ∃ y₀ : Q1, χx y₀ ≠ 1 := by
        by_contra hall
        push Not at hall
        exact hax1 $ trace_nondeg hR hψ 1 (a * σ x) fun t => by
          convert hall (q1 t) using 2
          simp only [q1, τ1, barσ_mk, ← map_mul, ← map_add]
          congr 1
          simp only [map_mul, ha, hR.inv]
          ring
      obtain ⟨y₀, hy₀⟩ := hnt
      rw [sum_addChar_eq_zero χx (fun _ _ => by dsimp only [χx]; rw [← map_add_eq_mul]; congr 1; simp only [map_add]; ring) hy₀, mul_zero]
  rw [sum_congr rfl fun w _ => hinner w, ← sum_filter, ← mul_sum] at havg
  have hq0 : (q : ℂ) ≠ 0 := by
                               have := hR.one_lt
                               exact_mod_cast (by omega)
  have hbij : ∑ w ∈ univ.filter (· ∈ π.range), g w = ∑ v : Qk R ϖ (j + 1), g (π v) :=
    (sum_bij (fun v _ => π v) (fun v _ => mem_filter.2 ⟨mem_univ _, ⟨v, rfl⟩⟩)
      (fun _ _ _ _ h => hπinj h) (fun _ hw => let ⟨v, hv⟩ := (mem_filter.1 hw).2; ⟨v, mem_univ _, hv⟩)
      fun _ _ => rfl).symm
  let φ : Qk R ϖ (j + 1) →+ Qk R ϖ j := (factor $ lev_le $ Nat.le_succ j).toAddMonoidHom
  let G := fun u => ψ j $ mkQ ϖ j a * (barσ σ ϖ hR.fix_ϖ j u * u)
  have hgπ : ∀ v : Qk R ϖ (j + 1), g (π v) = G (φ v) := fun v => by
    obtain ⟨z, rfl⟩ := mk_surjective v
    have h1 : g (π (mkQ ϖ (j + 1) z)) = ψ (j + 2) (q2 (ϖ ^ 2 * (a * (σ z * z)))) := by
      change ψ (j + 2) (q2 a * (τ2 (q2 (ϖ * z)) * q2 (ϖ * z))) = _
      simp only [q2, τ2, barσ_mk, ← map_mul]
      congr 2
      simp only [map_mul, hR.fix_ϖ]
      ring
    rw [h1, psi_pow hψ j 2]
    change ψ j (mkQ ϖ j (a * (σ z * z))) = ψ j (mkQ ϖ j a * (barσ σ ϖ hR.fix_ϖ j (mkQ ϖ j z) * mkQ ϖ j z))
    simp
  have hsc := sum_comp_surj φ (fun u => let ⟨z, hz⟩ := mk_surjective u; ⟨mkQ ϖ (j + 1) z, hz⟩) G
  have hcj : ∀ t, (Fintype.card (Qk R ϖ t) : ℂ) = (q : ℂ) ^ (2 * t) := fun t => by
    rw [← card_eq_fintype_card, card_quot_lev hR t]
    push_cast
    rfl
  rw [mul_left_cancel₀ (pow_ne_zero 2 hq0) havg, hbij, sum_congr rfl fun v _ => hgπ v]
  rw [hcj j, hcj $ j + 1] at hsc
  apply mul_left_cancel₀ $ pow_ne_zero (2 * j) hq0
  rw [hsc]
  ring

lemma gauss1 (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (Qk R ϖ k)]
    {ψ : ∀ k, AddChar (Qk R ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) (j : ℕ) {a : R} (ha : σ a = a) (ha1 : a ∉ lev ϖ 1) :
    (∑ w : Qk R ϖ j, ψ j (mkQ ϖ j a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j := by
  induction j using Nat.twoStepInduction with
  | zero =>
    have : Subsingleton (Qk R ϖ 0) := subsingleton_iff.2 $ by simp
    rw [Fintype.sum_subsingleton _ 0]
    simp
  | one => simpa using gauss_level_one hR hψ ha ha1
  | more j ih _ => rw [gauss_recursion hR hψ j ha ha1, ih, pow_add, mul_pow (ε : ℂ) (q : ℂ) 2, hε]; ring

lemma fixed_decomp (hR : IsUnrQuad R σ ϖ q ε) (k : ℕ) (d : R) (hd : σ d = d) :
    d ∈ lev ϖ k ∨ ∃ a₀ e c, k = e + a₀ ∧ σ c = c ∧ c ∉ lev ϖ 1 ∧ d = ϖ ^ a₀ * c := by
  induction k with
  | zero => left; simp [lev]
  | succ k ih =>
    rcases ih with h | ⟨a₀, e, c, hk, hc, hc1, hdc⟩
    · obtain ⟨c, rfl⟩ := mem_lev_iff.1 h
      by_cases h1 : c ∈ lev ϖ 1
      · left
        obtain ⟨t, rfl⟩ := mem_lev_iff.1 h1
        exact mem_lev_iff.2 ⟨t, by ring⟩
      · right
        exact ⟨k, 1, c, by omega, (hR.reg.pow k $ by simpa [  hR.fix_ϖ] using hd), h1, rfl⟩
    · right
      exact ⟨a₀, e + 1, c, by omega, hc, hc1, hdc⟩

lemma mul_mem_lev_iff (hreg : IsSMulRegular R ϖ) {c : R} (hc : IsUnit c) (e a₀ : ℕ) (y : R) :
    ϖ ^ a₀ * c * y ∈ lev ϖ (e + a₀) ↔ y ∈ lev ϖ e := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := mem_lev_iff.1 h
    have h1 := hreg.pow a₀ $ by
                                show ϖ ^ a₀ * (c * y) = ϖ ^ a₀ * (ϖ ^ e * t)
                                rw [← mul_assoc, ht, pow_add]
                                ring
    obtain ⟨v, hv⟩ := hc.exists_left_inv
    exact mem_lev_iff.2 ⟨v * t, by rw [← one_mul y, ← hv, mul_assoc, h1]; ring⟩
  · intro h
    obtain ⟨t, rfl⟩ := mem_lev_iff.1 h
    exact mem_lev_iff.2 ⟨c * t, by rw [pow_add]; ring⟩

lemma card_range_mul (hreg : IsSMulRegular R ϖ) {c : R} (hc : IsUnit c) (e a₀ : ℕ) :
    card (Set.range fun w : Qk R ϖ (e + a₀) => w * mkQ ϖ (e + a₀) (ϖ ^ a₀ * c)) = card (Qk R ϖ e) := by
  let s := Function.surjInv $ mk_surjective (I := lev ϖ e)
  have hs : ∀ x, mkQ ϖ e (s x) = x := Function.surjInv_eq _
  let φ : Qk R ϖ e → Qk R ϖ (e + a₀) := fun x => mkQ ϖ (e + a₀) $ ϖ ^ a₀ * c * s x
  have hrange : (Set.range fun w : Qk R ϖ (e + a₀) => w * mkQ ϖ (e + a₀) (ϖ ^ a₀ * c)) = Set.range φ := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨y, rfl⟩ := mk_surjective w
      refine ⟨mkQ ϖ e y, ?_⟩
      have h1 := (mul_mem_lev_iff hreg hc e a₀ _).2 $ iqEq.1 $ hs $ mkQ ϖ e y
      rw [mul_sub] at h1
      simp only [φ]
      rw [iqEq.2 h1, ← map_mul, mul_comm]
    · rintro ⟨x, rfl⟩
      exact ⟨mkQ ϖ (e + a₀) $ s x, by simp only [φ]; rw [← map_mul, mul_comm]⟩
  rw [hrange]
  exact card_congr (Equiv.ofInjective φ $ fun x x' hxx => by
    rw [← hs x, ← hs x']
    exact iqEq.2 $ (mul_mem_lev_iff hreg hc e a₀ _).1 $ by rw [mul_sub]; exact iqEq.1 hxx).symm

lemma gauss_image_level (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (Qk R ϖ k)]
    {ψ : ∀ k, AddChar (Qk R ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (hε : (ε : ℂ) ^ 2 = 1)
    (k : ℕ) (d : R) (hd : σ d = d) :
    ∃ e : ℕ, e ≤ k ∧ card (Set.range fun w : Qk R ϖ k => w * mkQ ϖ k d) = (q ^ 2) ^ e ∧
      ∀ a : R, σ a = a → a ∉ lev ϖ 1 →
        (∑ w : Qk R ϖ k, ψ k (mkQ ϖ k (a * d) * (barσ σ ϖ hR.fix_ϖ k w * w))) =
          (q : ℂ) ^ (2 * k) * ((ε : ℂ) / q) ^ e := by
  have hq : q ≠ 0 := by
                        have := hR.one_lt
                        exact_mod_cast (by omega)
  have hcard : ∀ j, Fintype.card (Qk R ϖ j) = q ^ (2 * j) := fun j => by rw [← card_eq_fintype_card, card_quot_lev hR j]
  rcases fixed_decomp hR k d hd with h0 | ⟨a₀, e, c, rfl, hc, hc1, rfl⟩
  · have hz : mkQ ϖ k d = 0 := eq_zero_iff_mem.2 h0
    refine ⟨0, Nat.zero_le _, by rw [show (Set.range fun w => w * mkQ ϖ k d) = {0} by
                                                                                      ext z
                                                                                      simp [hz]]; simp,
      fun _ _ _ => by simp only [map_mul, hz, mul_zero, zero_mul, map_zero_eq_one, sum_const, card_univ, hcard, nsmul_eq_mul, mul_one, pow_zero]; push_cast; rfl⟩
  · have hcu : IsUnit c := hR.fixLocal c hc hc1
    refine ⟨e, by omega, by rw [card_range_mul hR.reg hcu e a₀, card_quot_lev hR e, pow_mul], fun a ha ha1 => ?_⟩
    let π : Qk R ϖ (e + a₀) →+ Qk R ϖ e := (factor $ lev_le $ by omega).toAddMonoidHom
    let G := fun v => ψ e $ mkQ ϖ e (a * c) * (barσ σ ϖ hR.fix_ϖ e v * v)
    have hF : ∀ w : Qk R ϖ (e + a₀),
        ψ (e + a₀) (mkQ ϖ (e + a₀) (a * (ϖ ^ a₀ * c)) * (barσ σ ϖ hR.fix_ϖ (e + a₀) w * w)) = G (π w) := fun w => by
      obtain ⟨y, rfl⟩ := mk_surjective w
      change ψ (e + a₀) (mkQ ϖ (e + a₀) (a * (ϖ ^ a₀ * c)) * (mkQ ϖ (e + a₀) (σ y) * mkQ ϖ (e + a₀) y)) =
        ψ e (mkQ ϖ e (a * c) * (mkQ ϖ e (σ y) * mkQ ϖ e y))
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← psi_pow hψ e a₀ $ a * c * (σ y * y)]
      congr 2
      ring
    rw [sum_congr rfl fun w _ => hF w]
    have h2 := sum_comp_surj π (fun x => let ⟨y, hy⟩ := mk_surjective x; ⟨mkQ ϖ (e + a₀) y, hy⟩) G
    rw [gauss1 hR hψ hε e (by rw [map_mul, ha, hc]) $ unit_notMem hR.notUnit $ (hR.fixLocal a ha ha1).mul hcu, hcard, hcard] at h2
    push_cast at h2
    have h4 : ∑ w, G (π w) = q ^ (2 * (e + a₀)) * ((ε) * q) ^ e / q ^ (2 * e) := by rw [← h2]; field_simp
    rw [h4, mul_pow, div_pow]
    field_simp
    ring

end CharsGauss

section HermDiag
variable {R : Type} [CommRing R]

private def ct (σ : R →+* R) {a b : Type} (x : Matrix a b R) : Matrix b a R := (x.map σ).transpose
private def Hm (σ : R →+* R) {ι : Type} (h : Matrix ι ι R) : Prop := ∀ i j, σ (h i j) = h j i
private def Diagble (σ : R →+* R) {ι : Type} [Fintype ι] [DecidableEq ι] (h : Matrix ι ι R) : Prop :=
  ∃ (g g' : Matrix ι ι R) (d : ι → R), g * g' = 1 ∧ g' * g = 1 ∧ (∀ i, σ (d i) = d i) ∧ ct σ g * h * g = diagonal d

private lemma ct_mul (σ : R →+* R) {a b c : Type} [Fintype b] (x : Matrix a b R) (y : Matrix b c R) :
    ct σ (x * y) = ct σ y * ct σ x := by simp [ct, Matrix.map_mul, transpose_mul]

private lemma diagble_of_congr {σ : R →+* R} {ι : Type} [Fintype ι] [DecidableEq ι]
    {h p p' : Matrix ι ι R} (h1 : p * p' = 1) (h2 : p' * p = 1)
    (hd : Diagble σ (ct σ p * h * p)) : Diagble σ h := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  exact ⟨p * g, g' * p', d,
    by simp only [Matrix.mul_assoc, ← Matrix.mul_assoc g g' p', hg, Matrix.one_mul, h1],
    by simp only [Matrix.mul_assoc, ← Matrix.mul_assoc p' p g, h2, Matrix.one_mul, hg'],
    hfix, by rw [ct_mul, ← hdiag]; simp only [Matrix.mul_assoc]⟩

private lemma diagble_schur {σ : R →+* R} {ι : Type} [Fintype ι] [DecidableEq ι]
    (ih : ∀ h : Matrix ι ι R, Hm σ h → Diagble σ h)
    {h : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R} (hh : Hm σ h)
    (hu : IsUnit (h (Sum.inl ()) (Sum.inl ()))) : Diagble σ h := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  set a := h (Sum.inl ()) (Sum.inl ()) with ha
  have hfa : σ a = a := hh _ _
  have hfv : σ v = v := by
    have h1 : a * σ v = 1 := by simpa [hfa] using congrArg σ hv
    linear_combination v * h1 - σ v * hv
  let B := h.toBlocks₁₂; let C := h.toBlocks₂₁; let D := h.toBlocks₂₂
  have hblocks : h = fromBlocks (diagonal fun _ => a) B C D := by
    rw [← show h.toBlocks₁₁ = diagonal fun _ => a by
                                                     ext ⟨⟩ ⟨⟩
                                                     simp [toBlocks₁₁, ha]]
    exact (fromBlocks_toBlocks h).symm
  have hCB : ∀ i, σ (B () i) = C i () := fun i => hh _ _
  have hCB' : ∀ i, σ (C i ()) = B () i := fun i => hh _ _
  let p : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R := fromBlocks 1 (-(v • B)) 0 1
  let p' : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R := fromBlocks 1 (v • B) 0 1
  let E := D - v • (C * B)
  have hct : ct σ p = fromBlocks 1 0 (-(v • C)) 1 := by
    ext (i | i) (j | j)
    · simp [p, ct]
    · simp [p, ct]
    · cases j
      simp [p, ct, hfv, hCB]
    · by_cases hij : i = j <;> simp [p, ct, hij, Ne.symm]
  have hav : ∀ {c : Type} (X : Matrix Unit c R), (diagonal fun _ : Unit => a) * (v • X) = X := fun X => by
    ext ⟨⟩ j
    rw [diagonal_mul]
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination X () j * hv
  have hva : ∀ {c : Type} (X : Matrix c Unit R), (v • X) * (diagonal fun _ : Unit => a) = X := fun X => by
    ext i ⟨⟩
    rw [mul_diagonal]
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination X i () * hv
  apply diagble_of_congr (by simp [p, p', fromBlocks_multiply] : p * p' = 1) $ by simp [p, p', fromBlocks_multiply]
  rw [show ct σ p * h * p = fromBlocks (diagonal fun _ : Unit => a) 0 0 E by
    rw [hct, hblocks]
    simp only [p]
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [hva, hav, E, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, sub_eq_add_neg, add_comm]]
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := ih E $ fun i j => by
    have hD : σ (D i j) = D j i := hh _ _
    simp only [E, Matrix.sub_apply, Matrix.smul_apply, mul_apply, univ_unique, sum_singleton, smul_eq_mul,
      map_sub, map_mul, hfv, hD, hCB, hCB', PUnit.default_eq_unit]; ring
  refine ⟨fromBlocks 1 0 0 g, fromBlocks 1 0 0 g', Sum.elim (fun _ => a) d,
    by rw [fromBlocks_multiply]; simp [hg], by rw [fromBlocks_multiply]; simp [hg'],
    by rintro (i | i); exact hfa; exact hfix i, ?_⟩
  rw [show ct σ (fromBlocks 1 0 0 g) = fromBlocks 1 0 0 (ct σ g) by ext (i | i) (j | j) <;> simp [ct],
    fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_diagonal]
  simp [hdiag]

lemma herm_diag {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    (n : ℕ) (h : Mat n n R) (hh : cT σ h = h) :
    ∃ (g g' : Mat n n R) (d : Fin n → R), g * g' = 1 ∧ g' * g = 1 ∧
      (∀ i, σ (d i) = d i) ∧ cT σ g * h * g = diagonal d := by
  have hmain : ∀ m (h : Mat m m R), Hm σ h → Diagble σ h := by
    intro m; induction m with
    | zero => intro _ _; exact ⟨1, 1, 0, by simp, by simp, by simp, by ext i; exact i.elim0⟩
    | succ m ih =>
      intro h hh
      by_cases h0 : h = 0
      · exact ⟨1, 1, 0, by simp, by simp, by simp, by simp [h0]⟩
      · classical
        have hex : ∃ k, ∃ i j, h i j ∉ lev ϖ k := by
          by_contra hc; push Not at hc; apply h0; ext i j; exact hR.sep _ fun k => hc k i j
        have hk0 : Nat.find hex ≠ 0 := fun h00 => by
          obtain ⟨i, j, hij⟩ := Nat.find_spec hex; rw [h00] at hij; exact hij $ by simp [lev]
        obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        obtain ⟨i₀, j₀, hij₀⟩ := Nat.find_spec hex
        rw [ha] at hij₀
        have hall : ∀ i j, h i j ∈ lev ϖ a := by
          have := Nat.find_min hex (m := a) (by omega); push Not at this; exact this
        choose c hc using fun i j => mem_lev_iff.1 $ hall i j
        let h' := of c
        have hh' : Hm σ h' := fun x y => by
          show σ (c x y) = c y x; apply hR.reg.pow a
          have := hh x y; rw [hc x y, hc y x, map_mul, map_pow, hR.fix_ϖ] at this; simpa using this
        have hy : h' i₀ j₀ ∉ lev ϖ 1 := fun hm => hij₀ $ by
          obtain ⟨d, hd⟩ := mem_lev_iff.1 hm
          exact mem_lev_iff.2 ⟨d, by rw [hc i₀ j₀, show c i₀ j₀ = ϖ ^ 1 * d from hd, Nat.succ_eq_add_one]; ring⟩
        have hdiag' : Diagble σ h' := by
          have hpiv : ∃ (k : Fin (m + 1)) (p p' : Mat (m + 1) (m + 1) R), p * p' = 1 ∧ p' * p = 1 ∧ (ct σ p * h' * p) k k ∉ lev ϖ 1 := by
            by_cases h1 : ∃ k, h' k k ∉ lev ϖ 1
            · obtain ⟨k, hk⟩ := h1
              exact ⟨k, 1, 1, by simp, by simp, by simpa [ct, Matrix.map_one _ (map_zero σ) $ map_one σ] using hk⟩
            · push Not at h1
              have hij : i₀ ≠ j₀ := by
                                       rintro rfl
                                       exact hy $ h1 i₀
              have hs : ∃ s, s * h' i₀ j₀ + σ (s * h' i₀ j₀) ∉ lev ϖ 1 := by
                by_contra hcon
                push Not at hcon
                exact hy $ mem_of_trace_mem hR hcon
              obtain ⟨s, hs⟩ := hs
              have hctt : ct σ (transvection j₀ i₀ s) = transvection i₀ j₀ (σ s) := by
                show cT σ (1 + single j₀ i₀ s) = 1 + single i₀ j₀ (σ s); simp
              refine ⟨i₀, transvection j₀ i₀ s, transvection j₀ i₀ $ -s,
                by rw [transvection_mul_transvection_same _ _ hij.symm]; simp,
                by rw [transvection_mul_transvection_same _ _ hij.symm]; simp, fun hmem => hs ?_⟩
              rw [hctt, mul_transvection_apply_same, transvection_mul_apply_same, transvection_mul_apply_same] at hmem
              rw [show s * h' i₀ j₀ + σ (s * h' i₀ j₀) =
                (h' i₀ i₀ + σ s * h' j₀ i₀ + s * (h' i₀ j₀ + σ s * h' j₀ j₀)) - h' i₀ i₀ - s * σ s * h' j₀ j₀ by
                rw [map_mul, hh' i₀ j₀]
                ring]
              exact Ideal.sub_mem _ (Ideal.sub_mem _ hmem $ h1 i₀) $ Ideal.mul_mem_left _ _ $ h1 j₀
          obtain ⟨k, p, p', h1, h2, hp⟩ := hpiv
          apply diagble_of_congr h1 h2
          have hh2 : Hm σ (ct σ p * h' * p) := fun x y => by
            have hc1 : ct σ h' = h' := by
                                          ext i j
                                          exact hh' j i
            have hc2 : ct σ (ct σ p) = p := by
                                               ext i j
                                               exact hR.inv _
            have hc3 : ct σ (ct σ p * h' * p) = ct σ p * h' * p := by rw [ct_mul, ct_mul, hc1, hc2, Matrix.mul_assoc]
            exact congrFun (congrFun hc3 y) x
          let e0 := Fintype.equivFinOfCardEq $ show Fintype.card (Unit ⊕ Fin m) = m + 1 by
                                                                                           simp
                                                                                           omega
          let e := e0.trans $ Equiv.swap (e0 $ Sum.inl ()) k
          have he : e (Sum.inl ()) = k := by simp [e]
          obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := diagble_schur ih (h := (ct σ p * h' * p).submatrix e e)
            (fun x y => hh2 _ _) $ by simp only [submatrix_apply, he]; exact hR.fixLocal _ (hh2 _ _) hp
          refine ⟨g.submatrix e.symm e.symm, g'.submatrix e.symm e.symm, fun i => d $ e.symm i,
            by rw [submatrix_mul_equiv, hg]; simp, by rw [submatrix_mul_equiv, hg']; simp, fun i => hfix _, ?_⟩
          have hsub : ct σ p * h' * p = ((ct σ p * h' * p).submatrix e e).submatrix e.symm e.symm := by
                                                                                                        ext i j
                                                                                                        simp
          rw [show ct σ (g.submatrix e.symm e.symm) = (ct σ g).submatrix e.symm e.symm from rfl,
            hsub, submatrix_mul_equiv, submatrix_mul_equiv, hdiag]
          ext i j
          simp [diagonal_apply]
        obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hdiag'
        refine ⟨g, g', fun i => ϖ ^ a * d i, hg, hg', fun i => by simp [hR.fix_ϖ, hfix], ?_⟩
        rw [show h = (ϖ ^ a) • h' by
                                     ext x y
                                     exact hc x y,
          show diagonal (fun i => ϖ ^ a * d i) = (ϖ ^ a) • diagonal d by
                                                                         ext i j
                                                                         by_cases hij : i = j <;> simp [hij], ← hdiag]
        simp
  exact hmain n h fun i j => congrFun (congrFun hh j) i

lemma herm_diag_unimod {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    (n : ℕ) (S : Mat n n R) (hS : IsUnimod σ S) :
    ∃ (g g' : Mat n n R) (d : Fin n → R), g * g' = 1 ∧ g' * g = 1 ∧
      (∀ i, σ (d i) = d i) ∧ cT σ g * S * g = diagonal d ∧ ∀ i, IsUnit (d i) := by
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := herm_diag hR n S hS.1
  refine ⟨g, g', d, hgg, hgg', hd, hgd, fun i => ?_⟩
  have h3 : IsUnit (diagonal d).det := by
    rw [← hgd, det_mul, det_mul]
    exact ((isUnit_det_of_right_inverse $ by rw [← cT_mul, hgg', cT_one]).mul hS.2).mul $ isUnit_det_of_right_inverse hgg
  rw [det_diagonal] at h3
  exact isUnit_of_dvd_unit (dvd_prod_of_mem _ $ mem_univ i) h3

end HermDiag

section SeriesEqDensSec
variable {R : Type} [CommRing R]

private lemma chi_sum {ι Q : Type} [AddCommMonoid Q] (χ : AddChar Q ℂ) (s : Finset ι) (g : ι → Q) :
    χ (∑ i ∈ s, g i) = ∏ i ∈ s, χ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, map_add_eq_mul, ih]

private lemma gauss_prod (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) [Fintype (Qk R ϖ k)]
    (χ : AddChar (Qk R ϖ k) ℂ) (m n : ℕ) (D : Fin n → R) (E : Fin m → R) :
    (∑ y : Mat m n (Qk R ϖ k),
      χ (trace (red ϖ k (diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (diagonal E) * y)))) =
      ∏ i : Fin n, ∏ l : Fin m, ∑ w : Qk R ϖ k, χ (mkQ ϖ k (E l * D i) * (barσ σ ϖ hf k w * w)) := by
  let f := fun i l w => χ $ mkQ ϖ k (E l * D i) * (barσ σ ϖ hf k w * w)
  have hterm : ∀ y : Mat m n (Qk R ϖ k),
      χ (trace $ red ϖ k (diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (diagonal E) * y)) =
        ∏ l, ∏ i, f i l (y l i) := fun y => by
    have htr : trace (red ϖ k (diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (diagonal E) * y)) =
        ∑ i, ∑ l, mkQ ϖ k (E l * D i) * (barσ σ ϖ hf k (y l i) * y l i) := by
      simp only [trace, diag_apply, red_diagonal]
      refine sum_congr rfl fun i _ => ?_
      rw [diagonal_mul, mul_apply, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [mul_diagonal]
      simp only [cT, transpose_apply, map_apply, map_mul]
      ring
    rw [htr, chi_sum, prod_comm (s := univ) (t := univ)]
    exact prod_congr rfl fun _ _ => chi_sum χ univ _
  have hfp : (∑ y : Fin m → Fin n → Qk R ϖ k, ∏ l, ∏ i, f i l (y l i)) = ∏ i, ∏ l, ∑ w, f i l w := by
    have h2 : ∑ y : Fin m → Fin n → Qk R ϖ k, ∏ l, ∏ i, f i l (y l i) = ∏ l, ∑ v : Fin n → Qk R ϖ k, ∏ i, f i l (v i) := by
      rw [prod_univ_sum, Fintype.piFinset_univ]
    simp only [show ∀ l, ∑ v : Fin n → Qk R ϖ k, ∏ i, f i l (v i) = ∏ i, ∑ w, f i l w from fun _ => by rw [prod_univ_sum, Fintype.piFinset_univ]] at h2
    rw [prod_comm (s := univ) (t := univ)]
    exact h2
  exact (sum_equiv Matrix.of.symm _ _ hterm).trans hfp

private lemma eq_of_conj {A : Type} [CommRing A] (τ : A →+* A) {n : ℕ} {h D g g' : Mat n n A}
    (hg : g * g' = 1) (hD : cT τ g * h * g = D) : h = cT τ g' * D * g' := by
  rw [← hD]
  calc h = (cT τ g' * cT τ g) * h * (g * g') := by rw [← cT_mul, hg, cT_one, Matrix.one_mul, Matrix.mul_one]
    _ = cT τ g' * (cT τ g * h * g) * g' := by simp only [Matrix.mul_assoc]

private lemma gauss_cov (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (hσ : ∀ a, σ (σ a) = a)
    (k : ℕ) [Fintype (Qk R ϖ k)] (χ : AddChar (Qk R ϖ k) ℂ) (m n : ℕ)
    (h D g g' : Mat n n R) (S E p p' : Mat m m R)
    (hg : g * g' = 1) (hg' : g' * g = 1) (hp : p * p' = 1) (hp' : p' * p = 1)
    (hD : cT σ g * h * g = D) (hE : cT σ p * S * p = E) :
    (∑ x : Mat m n (Qk R ϖ k), χ (trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)))) =
      ∑ y : Mat m n (Qk R ϖ k), χ (trace (red ϖ k D * (cT (barσ σ ϖ hf k) y * red ϖ k E * y))) := by
  let τ := barσ σ ϖ hf k
  let r {a b} (M : Mat a b R) := red ϖ k M
  have rg : r g * r g' = 1 := by simp [r, ← red_mul, hg]
  have rg' : r g' * r g = 1 := by simp [r, ← red_mul, hg']
  have rp : r p * r p' = 1 := by simp [r, ← red_mul, hp]
  have rp' : r p' * r p = 1 := by simp [r, ← red_mul, hp']
  have hG1 : cT τ (r g') * cT τ (r g) = 1 := by rw [← cT_mul, rg, cT_one]
  have hG2 : cT τ (r g) * cT τ (r g') = 1 := by rw [← cT_mul, rg', cT_one]
  let cov : Mat m n (Qk R ϖ k) ≃ Mat m n (Qk R ϖ k) :=
    { toFun := fun x => r p' * x * cT τ (r g')
      invFun := fun y => r p * y * cT τ (r g)
      left_inv := fun x => by
        calc r p * (r p' * x * cT τ (r g')) * cT τ (r g) = (r p * r p') * x * (cT τ (r g') * cT τ (r g)) := by simp only [Matrix.mul_assoc]
          _ = x := by rw [rp, hG1, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun y => by
        calc r p' * (r p * y * cT τ (r g)) * cT τ (r g') = (r p' * r p) * y * (cT τ (r g) * cT τ (r g')) := by simp only [Matrix.mul_assoc]
          _ = y := by rw [rp', hG2, Matrix.one_mul, Matrix.mul_one] }
  refine sum_equiv cov _ _ fun x => congrArg (⇑χ) ?_
  rw [eq_of_conj σ hg hD, eq_of_conj σ hp hE]
  simp
  change trace ((cT τ (r g') * r D * r g') * (cT τ x * (cT τ (r p') * r E * r p') * x)) =
    trace (r D * (cT τ (r p' * x * cT τ (r g')) * r E * (r p' * x * cT τ (r g'))))
  rw [cT_mul, cT_mul, cT_cT $ barσ_inv hf hσ k]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm $ cT τ $ r g']
  simp only [Matrix.mul_assoc]

private lemma nuAt_eq_prod (σ : R →+* R) (ϖ : R) (k n : ℕ)
    (h g g' : Mat n n R) (d : Fin n → R) (hgg' : g * g' = 1) (hdiag : cT σ g * h * g = diagonal d) :
    nuAt ϖ (red ϖ k h) = ∏ i : Fin n, card (Set.range fun w : Qk R ϖ k => w * mkQ ϖ k (d i)) := by
  let r {a b} (M : Mat a b R) := red ϖ k M
  have hP : r (cT σ g') * r (cT σ g) = 1 := by simp [r, ← red_mul, ← cT_mul, hgg']
  have hG : r g * r g' = 1 := by simp [r, ← red_mul, hgg']
  have hD : r (cT σ g) * r h * r g = diagonal fun i => mkQ ϖ k (d i) := by
    simp only [r, ← red_mul, hdiag, red_diagonal]
  have hconj : card (Set.range fun z => vecMul z $ r (cT σ g) * r h * r g) =
      card (Set.range fun x => vecMul x $ r h) := by
    have hrange : (Set.range fun z => vecMul z $ r (cT σ g) * r h * r g) =
        (fun y => vecMul y $ r g) '' Set.range fun x => vecMul x (r h) := by
      ext v
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨vecMul (vecMul z $ r $ cT σ g) $ r h, ⟨_, rfl⟩, by simp only [vecMul_vecMul]⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨vecMul x $ r $ cT σ g', by simp only [vecMul_vecMul, ← Matrix.mul_assoc, hP, Matrix.one_mul]⟩
    rw [hrange, Nat.card_image_of_injective $ fun _ _ hy => by
      simpa only [vecMul_vecMul, hG, vecMul_one] using congrArg (fun v => vecMul v $ r g') hy]
  have hdiagCard : card (Set.range fun z => vecMul z $ diagonal fun i => mkQ ϖ k $ d i) =
      ∏ i : Fin n, card (Set.range fun w => w * mkQ ϖ k (d i)) := by
    have hset : (Set.range fun z => vecMul z $ diagonal fun i => mkQ ϖ k $ d i) =
        Set.pi Set.univ fun i => Set.range fun w => w * mkQ ϖ k (d i) := by
      ext v
      simp only [Set.mem_range, Set.mem_univ_pi]
      refine ⟨fun ⟨z, hz⟩ i => ⟨z i, by rw [← hz, vecMul_diagonal]⟩, fun hv => ?_⟩
      choose z hz using hv
      exact ⟨z, funext fun i => by rw [vecMul_diagonal, hz i]⟩
    rw [hset, card_congr $ Equiv.Set.univPi _, Nat.card_pi]
  unfold nuAt
  rw [← hconj, hD, hdiagCard]

private lemma orth_hermMod {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (Qk R ϖ k)] {ψ : ∀ k, AddChar (Qk R ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (n k : ℕ) {Y : Mat n n (Qk R ϖ k)} (hY : Y ∈ hermMod σ ϖ n k) :
    (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (trace (B.1 * Y))) = (card (hermMod σ ϖ n k) : ℂ)) ∧
      (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (trace (B.1 * Y))) = 0) := by
  refine ⟨fun h0 => by
                       subst h0
                       simp, fun hne => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hY
  have hnt : ∃ b : Mat n n R, cT σ b = b ∧ ψ k (trace (red ϖ k b * red ϖ k y)) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hne
    ext i j
    simp only [red, map_apply, Matrix.zero_apply]
    rw [eq_zero_iff_mem]
    refine trace_nondeg hR hψ k (y i j) fun t => ?_
    have hyji : σ (y i j) = y j i := congrFun (congrFun hy j) i
    have htr := hall (single j i t + single i j (σ t)) (by simp [hR.inv, add_comm])
    have htm : trace (red ϖ k (single j i t + single i j (σ t)) * red ϖ k y) =
        mkQ ϖ k (trace ((single j i t + single i j (σ t)) * y)) := by
      unfold red
      rw [← Matrix.map_mul]
      simp only [trace, diag_apply, map_apply, map_sum]
    rw [htm, add_mul, trace_add, trace_single_mul, trace_single_mul, smul_eq_mul, smul_eq_mul] at htr
    rwa [map_mul, hyji]
  obtain ⟨b, hb, hb1⟩ := hnt
  let B₀ := red ϖ k b
  let e : hermMod σ ϖ n k ≃ hermMod σ ϖ n k :=
    { toFun := fun B => ⟨B₀ + B.1, let ⟨a, ha, hBa⟩ := B.2; ⟨b + a, by simp [hb, show cT σ a = a from ha], by rw [red_add, hBa]⟩⟩
      invFun := fun B => ⟨-B₀ + B.1, let ⟨a, ha, hBa⟩ := B.2; ⟨-b + a, by simp [hb, show cT σ a = a from ha], by rw [red_add, red_neg, hBa]⟩⟩
      left_inv := fun _ => sx $ by simp
      right_inv := fun _ => sx $ by simp }
  have key : ∑' B : hermMod σ ϖ n k, ψ k (trace (B.1 * red ϖ k y)) =
      ψ k (trace $ B₀ * red ϖ k y) * ∑' B : hermMod σ ϖ n k, ψ k (trace $ B.1 * red ϖ k y) := by
    calc ∑' B : hermMod σ ϖ n k, ψ k (trace $ B.1 * red ϖ k y)
        = ∑' B : hermMod σ ϖ n k, ψ k (trace $ (e B).1 * red ϖ k y) := (e.tsum_eq _).symm
      _ = ∑' B : hermMod σ ϖ n k, ψ k (trace $ B₀ * red ϖ k y) * ψ k (trace $ B.1 * red ϖ k y) :=
          tsum_congr fun B => by
                                 show ψ k (trace $ (B₀ + B.1) * red ϖ k y) = _
                                 simp [add_mul, trace_add, map_add_eq_mul]
      _ = _ := tsum_mul_left
  exact (mul_eq_zero.1 (by linear_combination -key : (ψ k (trace (B₀ * red ϖ k y)) - 1) * _ = 0)).resolve_left (sub_ne_zero.2 hb1)

private lemma gauss_full {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (Qk R ϖ k)] {ψ : ∀ k, AddChar (Qk R ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) {m n : ℕ} (k : ℕ) (S : Mat m m R) (hS : IsUnimod σ S)
    (B : Mat n n (Qk R ϖ k)) (hB : B ∈ hermMod σ ϖ n k) :
    (∑ x : Mat m n (Qk R ϖ k), ψ k (trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) =
      (card (Mat m n (Qk R ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B)) := by
  obtain ⟨h, hh, rfl⟩ := hB
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := herm_diag hR n h hh
  obtain ⟨p, p', e, hpp, hpp', he, hpe, heu⟩ := herm_diag_unimod hR m S hS
  choose eI _ hcard hsum using fun i => gauss_image_level hR hψ hε k (d i) $ hd i
  rw [gauss_cov σ ϖ hR.fix_ϖ hR.inv k (ψ k) m n h _ g g' S _ p p' hgg hgg' hpp hpp' hgd hpe,
    gauss_prod σ ϖ hR.fix_ϖ k (ψ k) m n d e, nuAt_eq_prod σ ϖ k n h g g' d hgg hgd]
  rw [prod_congr rfl fun i _ => hcard i, prod_pow_eq_pow_sum, Nat.log_pow $ Nat.one_lt_pow (by norm_num) hR.one_lt]
  have hM : (card (Mat m n (Qk R ϖ k)) : ℂ) = ((q : ℂ) ^ (2 * k)) ^ (m * n) := by
    have : card (Mat m n (Qk R ϖ k)) = (q ^ (2 * k)) ^ (m * n) := by
      show card (Fin m → Fin n → Qk R ϖ k) = _
      rw [card_fun, card_fun, card_fin, card_fin, card_quot_lev hR k, ← pow_mul, mul_comm n m]
    rw [this]
    push_cast
    rfl
  rw [hM, show ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m by rw [div_pow, _root_.zpow_neg, zpow_natCast, div_eq_mul_inv]]
  simp only [fun i l => hsum i (e l) (he l) $ unit_notMem hR.notUnit $ heu l, prod_const, card_univ, Fintype.card_fin, mul_pow, prod_mul_distrib]
  rw [← pow_mul, ← pow_mul]
  congr 1
  simp only [show ∀ x, (((ε : ℂ) / q) ^ eI x) ^ m = (((ε : ℂ) / q) ^ m) ^ eI x from fun x => by rw [← pow_mul, ← pow_mul, mul_comm]]
  rw [prod_pow_eq_pow_sum]

lemma seriesEqDens : SeriesEqDens := by
  intro R _ σ ϖ q ε hR ψ hψ m n _ S T hS hT α hα
  classical
  have hfin := finite_quot hR
  let : ∀ k, Fintype (Qk R ϖ k) := fun _ => ofFinite _
  have hε : (ε : ℂ) ^ 2 = 1 := by rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have heq : siegAt ϖ σ ψ q ε m T = fun k => ((densAt σ ϖ S T k : ℝ) : ℂ) := funext fun k => by
    let HM := hermMod σ ϖ n k
    let : Fintype ↥HM := ofFinite _
    let τ := barσ σ ϖ hR.fix_ϖ k
    let r {a b} (M : Mat a b R) := red ϖ k M
    let c := (ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))
    have hsol : (solCount σ ϖ S T k : ℂ) = ∑ x : Mat m n (Qk R ϖ k), if cT τ x * r S * x = r T then (1 : ℂ) else 0 := by
      unfold solCount
      rw [solImg_eq ϖ hR.fix_ϖ k S T, card_eq_fintype_card, card_subtype, natCast_card_filter]
      exact sum_congr rfl fun _ _ => if_congr Iff.rfl rfl rfl
    have hcount : (card HM : ℂ) * (solCount σ ϖ S T k) =
        (card (Mat m n $ Qk R ϖ k) : ℂ) * ∑ B : HM, ψ k (-trace (B.1 * r T)) * c ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
      have hx : ∀ x : Mat m n (Qk R ϖ k), (card HM : ℂ) * (if cT τ x * r S * x = r T then (1 : ℂ) else 0) =
          ∑ B : HM, ψ k (trace $ B.1 * (cT τ x * r S * x)) * ψ k (-trace (B.1 * r T)) := fun x => by
        have hmem : cT τ x * r S * x - r T ∈ HM := by
          obtain ⟨x₀, rfl⟩ := red_surj ϖ k x
          exact ⟨cT σ x₀ * S * x₀ - T, by simp [cT_cT hR.inv, hS.1, hT.1, Matrix.mul_assoc], by simp [r, τ, red_gram ϖ hR.fix_ϖ]⟩
        have ho := orth_hermMod hR hψ n k hmem
        have hts : (∑' B : HM, ψ k (trace (B.1 * (cT τ x * r S * x - r T)))) =
            if cT τ x * r S * x = r T then (card HM : ℂ) else 0 := by
          by_cases hxe : cT τ x * r S * x = r T
          · rw [ite_eq_left hxe]
            exact ho.1 (sub_eq_zero.2 hxe)
          · rw [ite_eq_right hxe]
            exact ho.2 (sub_ne_zero.2 hxe)
        rw [mul_ite, mul_one, mul_zero, ← hts, tsum_fintype]
        exact sum_congr rfl fun _ _ => by rw [Matrix.mul_sub, trace_sub, sub_eq_add_neg, map_add_eq_mul]
      calc (card HM : ℂ) * (solCount σ ϖ S T k : ℂ)
          = ∑ x : Mat m n (Qk R ϖ k), (card HM : ℂ) * (if cT τ x * r S * x = r T then (1 : ℂ) else 0) := by rw [hsol, mul_sum]
        _ = ∑ x : Mat m n (Qk R ϖ k), ∑ B : HM, ψ k (trace (B.1 * (cT τ x * r S * x))) * ψ k (-trace (B.1 * r T)) :=
            sum_congr rfl fun x _ => hx x
        _ = ∑ B : HM, ∑ x : Mat m n (Qk R ϖ k), ψ k (trace (B.1 * (cT τ x * r S * x))) * ψ k (-trace (B.1 * r T)) := sum_comm
        _ = ∑ B : HM, (card (Mat m n (Qk R ϖ k))) * (ψ k (-trace (B.1 * r T)) * c ^ Nat.log (q ^ 2) (nuAt ϖ B.1)) :=
            sum_congr rfl fun B _ => by rw [← sum_mul, gauss_full hR hψ hε k S hS B.1 B.2]; ring
        _ = _ := by rw [mul_sum]
    have hneg : ∑ B : HM, ψ k (-trace (B.1 * r T)) * c ^ Nat.log (q ^ 2) (nuAt ϖ B.1) =
        ∑ B : HM, ψ k (trace (r T * B.1)) * c ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
      have hnm : ∀ {B}, B ∈ HM → -B ∈ HM := fun ⟨a, ha, hBa⟩ => ⟨-a, by simp [show cT σ a = a from ha], by rw [red_neg, hBa]⟩
      refine sum_equiv (⟨fun B => ⟨-B.1, hnm B.2⟩, fun B => ⟨-B.1, hnm B.2⟩, fun _ => sx $ neg_neg _, fun _ => sx $ neg_neg _⟩) _ _ fun B => ?_
      have hnu : nuAt ϖ (-B.1) = nuAt ϖ B.1 := by
        unfold nuAt
        rw [show (Set.range fun x => vecMul x $ -B.1) = Set.range fun x => vecMul x B.1 by
          ext v
          constructor
          · rintro ⟨x, rfl⟩
            exact ⟨-x, by
                                           dsimp only
                                           rw [neg_vecMul, vecMul_neg]⟩
          · rintro ⟨x, rfl⟩
            exact ⟨-x, by
                                           dsimp only
                                           rw [neg_vecMul, vecMul_neg, neg_neg]⟩]
      show _ = ψ k (trace (r T * -B.1)) * c ^ Nat.log (q ^ 2) (nuAt ϖ (-B.1))
      rw [hnu, mul_neg, trace_neg, trace_mul_comm]
    have hM : (card (Mat m n (Qk R ϖ k)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have hcast : ((densAt σ ϖ S T k : ℝ) : ℂ) = (solCount σ ϖ S T k : ℂ) * (card HM : ℂ) / (card (Mat m n (Qk R ϖ k)) : ℂ) := by
      unfold densAt
      push_cast
      rfl
    rw [show siegAt ϖ σ ψ q ε m T k = ∑ B : HM, ψ k (-trace (B.1 * r T)) * c ^ Nat.log (q ^ 2) (nuAt ϖ B.1) by
        unfold siegAt
        rw [tsum_fintype, hneg],
      hcast, eq_div_iff hM]
    linear_combination -hcount
  rw [heq]
  exact (Complex.continuous_ofReal.tendsto α).comp hα

end SeriesEqDensSec

section UnrFormulaSec

structure HermSp (E : Type) [CommRing E] (τ : E →+* E) (V : Type) [AddCommGroup V] [Module E V] where
  h : V → V → E
  add_left : ∀ u v w, h (u + v) w = h u w + h v w
  smul_left : ∀ (a : E) v w, h (a • v) w = a * h v w
  symm : ∀ v w, h w v = τ (h v w)
  nondeg : ∀ v, (∀ w, h v w = 0) → v = 0

namespace HermSp
variable {E : Type} [CommRing E] {τ : E →+* E} {V : Type} [AddCommGroup V] [Module E V] (B : HermSp E τ V)

lemma zero_left (w : V) : B.h 0 w = 0 := by have := B.smul_left 0 0 w; rwa [zero_smul, zero_mul] at this
lemma add_right (v u w : V) : B.h v (u + w) = B.h v u + B.h v w := by
  rw [B.symm (u + w) v, B.add_left, map_add, ← B.symm, ← B.symm]
lemma smul_right (a : E) (v w : V) : B.h v (a • w) = τ a * B.h v w := by
  rw [B.symm (a • w) v, B.smul_left, map_mul, ← B.symm]

def perp (w : V) : Submodule E V where
  carrier := {v | B.h v w = 0}
  add_mem' ha hb := show B.h _ w = 0 by rw [B.add_left, ha, hb, add_zero]
  zero_mem' := B.zero_left w
  smul_mem' _ _ hx := show B.h _ w = 0 by rw [B.smul_left, hx, mul_zero]

def coef {w : V} (hw : IsUnit (B.h w w)) (z : V) : E := B.h z w * (hw.unit⁻¹ : Eˣ)

lemma coef_spec {w : V} (hw : IsUnit (B.h w w)) (z : V) : B.h (z - B.coef hw z • w) w = 0 := by
  have hc : B.coef hw z * B.h w w = B.h z w := by
                                                  unfold coef
                                                  rw [mul_assoc, show ((hw.unit⁻¹ : Eˣ)) * B.h w w = 1 by simp, mul_one]
  have e : B.h z w = B.h (z - B.coef hw z • w) w + B.h (B.coef hw z • w) w := by rw [← B.add_left, sub_add_cancel]
  rw [B.smul_left, hc] at e
  linear_combination -e

def perpForm {w : V} (hw : IsUnit (B.h w w)) : HermSp E τ (B.perp w) where
  h a b := B.h a b
  add_left u v x := B.add_left u v x
  smul_left a v x := B.smul_left a v x
  symm v x := B.symm v x
  nondeg v hv := sx $ B.nondeg v fun z => by
    rw [show z = (z - B.coef hw z • w) + B.coef hw z • w by abel, B.add_right, B.smul_right,
      show B.h v.1 w = 0 from v.2, mul_zero, add_zero]
    exact hv ⟨z - B.coef hw z • w, B.coef_spec hw z⟩

def perpEquiv {w : V} (hw : IsUnit (B.h w w)) : E × B.perp w ≃ V where
  toFun p := p.1 • w + p.2
  invFun z := (B.coef hw z, ⟨z - B.coef hw z • w, B.coef_spec hw z⟩)
  left_inv := fun ⟨a, v⟩ => by
    have hc : B.coef hw (a • w + v.1) = a := by
      unfold coef
      rw [B.add_left, B.smul_left, show B.h v.1 w = 0 from v.2, add_zero, mul_assoc,
        show B.h w w * ((hw.unit⁻¹ : Eˣ) : E) = 1 by simp, mul_one]
    exact Prod.ext hc (sx $ by show a • w + v.1 - B.coef hw (a • w + v.1) • w = v.1; rw [hc]; abel)
  right_inv z := by show B.coef hw z • w + (z - B.coef hw z • w) = z; abel

lemma norm_perp {w v : V} (hv : B.h v w = 0) (a : E) :
    B.h (a • w + v) (a • w + v) = a * τ a * B.h w w + B.h v v := by
  have hwv : B.h w v = 0 := by rw [B.symm v w, hv, map_zero]
  simp only [B.add_left, B.smul_left, B.add_right, B.smul_right, hv, hwv, mul_zero, add_zero]
  ring

end HermSp

def HermSp.std {E : Type} [CommRing E] {τ : E →+* E} (hτ : ∀ a, τ (τ a) = a) (m : ℕ) :
    HermSp E τ (Fin m → E) where
  h v w := ∑ i, v i * τ (w i)
  add_left _ _ _ := by simp [add_mul, sum_add_distrib]
  smul_left _ _ _ := by simp [mul_sum, mul_assoc]
  symm _ _ := by simp [map_sum, hτ, mul_comm]
  nondeg _ hv := funext fun i => by simpa [Pi.single_apply] using hv (Pi.single i 1)

private lemma exists_unit_norm {E V : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
    (hE : ResAlg E τ q ε) [AddCommGroup V] [Module E V] (B : HermSp E τ V) [Nontrivial V] :
    ∃ w : V, IsUnit (B.h w w) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hz : ∃ z, B.h v z ≠ 0 := by
                                   by_contra h
                                   push Not at h
                                   exact hv $ B.nondeg v h
  obtain ⟨z, hne⟩ := hz
  by_cases hvv : B.h v v ≠ 0
  · exact ⟨v, hE.fixedUnit _ (B.symm v v).symm hvv⟩
  by_cases hzz : B.h z z ≠ 0
  · exact ⟨z, hE.fixedUnit _ (B.symm z z).symm hzz⟩
  push Not at hvv hzz
  obtain ⟨u, hu, -⟩ := hE.basis
  have ha : ∃ a : E, a * B.h v z + τ (a * B.h v z) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 := hall 1; have h2 := hall u; simp only [one_mul] at h1
    exact hne $ hu.mul_right_eq_zero.1 $ by
      rw [show (u - τ u) * B.h v z = (u * B.h v z + τ (u * B.h v z)) - τ u * (B.h v z + τ (B.h v z)) by rw [map_mul]; ring,
        h1, h2, mul_zero, sub_self]
  obtain ⟨a, ha⟩ := ha
  refine ⟨a • v + z, hE.fixedUnit _ (B.symm _ _).symm ?_⟩
  rw [B.add_left, B.add_right, B.add_right, B.smul_left, B.smul_right, B.smul_left, B.smul_right,
    hvv, hzz, mul_zero, mul_zero, zero_add, add_zero, B.symm v z, ← map_mul]
  exact ha

private def sphVal (q : ℕ) (ε : ℤ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => (q : ℤ) ^ m * ((q : ℤ) ^ (m + 1) - ε ^ (m + 1))

private lemma sphere_card {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ} (hE : ResAlg E τ q ε) :
    ∀ m (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), card V = q ^ (2 * m) →
      (∀ b : E, τ b = b → b ≠ 0 → (card {v : V // B.h v v = b} : ℤ) = sphVal q ε m) ∧
      (card {v : V // B.h v v = 0} : ℤ) = (q : ℤ) ^ (2 * m) - ((q : ℤ) - 1) * sphVal q ε m := by
  intro m; induction m with
  | zero =>
    intro V _ _ B hV
    have : Subsingleton V := (Nat.card_eq_one_iff_unique.1 $ by simpa using hV).1
    refine ⟨fun b _ hb0 => ?_, ?_⟩
    · have : IsEmpty {v : V // B.h v v = b} := ⟨fun ⟨v, hv⟩ => hb0 $ by rw [Subsingleton.elim v 0, B.zero_left] at hv; exact hv.symm⟩
      simp [sphVal]
    · have : Unique {v : V // B.h v v = 0} := ⟨⟨⟨0, B.zero_left 0⟩⟩, fun ⟨v, _⟩ => sx $ Subsingleton.elim v 0⟩
      simp [sphVal]
  | succ m ih =>
    intro V _ _ B hV
    classical
    have hq := hE.one_lt
    have hfinE := resAlg_finite hE
    have hfinV := Nat.finite_of_card_ne_zero $ by rw [hV]; positivity
    have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 $ by rw [hV]; exact Nat.one_lt_pow (by omega) hq
    obtain ⟨w, hw⟩ := exists_unit_norm hE B
    let P := B.perp w
    obtain ⟨ihS, ihZ⟩ := ih P (B.perpForm hw) $ by
      have h1 : card E * card P = card V := by rw [← card_prod, card_congr $ B.perpEquiv hw]
      rw [hE.card, hV, show 2 * (m + 1) = 2 + 2 * m by omega, pow_add] at h1
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    let : Fintype E := ofFinite E; let : Fintype P := ofFinite P
    let : Fintype V := ofFinite V; let : Fintype (fixSub τ) := ofFinite _
    have hS : ∀ b : E, τ b = b → b ≠ 0 → (card {v : V // B.h v v = b} : ℤ) = sphVal q ε (m + 1) := by
      intro b hb hb0
      have hbij : card {v : V // B.h v v = b} = card {p : E × P // p.1 * τ p.1 * B.h w w + B.h p.2.1 p.2.1 = b} :=
        card_congr (Equiv.subtypeEquiv (B.perpEquiv hw).symm fun v => by
          have : B.h (B.perpEquiv hw ((B.perpEquiv hw).symm v)) (B.perpEquiv hw ((B.perpEquiv hw).symm v)) = B.h v v := by simp
          rw [← this]; exact Iff.of_eq (congrArg (· = b) $ B.norm_perp ((B.perpEquiv hw).symm v).2.2 _))
      rw [hbij, card_eq_fintype_card, card_subtype]
      have hsplit : (univ.filter fun p : E × P => p.1 * τ p.1 * B.h w w + B.h p.2.1 p.2.1 = b).card =
          ∑ a : E, (univ.filter fun v : P => B.h v.1 v.1 = b - a * τ a * B.h w w).card := by
        simp only [card_filter, Fintype.sum_prod_type]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by
          congr 1
          exact propext ⟨fun h => eq_sub_of_add_eq' h, fun h => by rw [h, add_sub_cancel]⟩
      rw [hsplit]; push_cast
      have hterm : ∀ a : E, ((univ.filter fun v : P => B.h v.1 v.1 = b - a * τ a * B.h w w).card) =
          if a * τ a * B.h w w = b then q ^ (2 * m) - (q - 1) * sphVal q ε m else sphVal q ε m := fun a => by
        rw [show ((univ.filter fun v : P => B.h v.1 v.1 = b - a * τ a * B.h w w).card) =
            (card {v : P // (B.perpForm hw).h v v = b - a * τ a * B.h w w}) by rw [card_eq_fintype_card, card_subtype]; rfl]
        by_cases ha : a * τ a * B.h w w = b
        · rw [ite_eq_left ha, ha, sub_self]
          exact ihZ
        · rw [ite_eq_right ha]
          exact ihS _ (by rw [map_sub, map_mul, map_mul, hb, hE.inv, (B.symm w w).symm, mul_comm (τ a) a]) $ sub_ne_zero.2 $ Ne.symm ha
      rw [sum_congr rfl fun a _ => hterm a, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
      let u := (hw.unit⁻¹)
      have hw1 : B.h w w * u = 1 := by simp [u]
      have hw2 : u * B.h w w = 1 := by simp [u]
      have hτu : τ u = u := by
        have h1 : B.h w w * τ u = 1 := by
                                          have := congrArg τ hw1
                                          rwa [map_mul, map_one, (B.symm w w).symm] at this
        linear_combination u * h1 - τ u * hw1
      have hhit : ((univ.filter fun a => a * τ a * B.h w w = b).card) = q - ε := by
        have hiff : ∀ a : E, a * τ a * B.h w w = b ↔ a * τ a = b * u := fun a =>
          ⟨fun h => by rw [← h, mul_assoc, hw1, mul_one], fun h => by rw [h, mul_assoc, hw2, mul_one]⟩
        rw [show (univ.filter fun a => a * τ a * B.h w w = b) = univ.filter fun a => a * τ a = b * u by
                                                                                                        ext a
                                                                                                        simp [hiff],
          ← card_subtype, ← card_eq_fintype_card]
        exact norm_fibre_card_nonzero hE (by rw [map_mul, hb, hτu]) $ fun h0 => hb0 $ by simpa [mul_assoc, hw2] using congrArg (· * B.h w w) h0
      have hmiss : ((univ.filter fun a => ¬a * τ a * B.h w w = b).card) = q ^ 2 - (q - ε) := by
        have htot : (univ.filter fun a => a * τ a * B.h w w = b).card +
            (univ.filter fun a => ¬a * τ a * B.h w w = b).card = (univ : Finset E).card := by
          rw [← card_union_of_disjoint $ disjoint_filter.2 fun _ _ h hn => hn h]
          congr 1
          ext a
          simp [em]
        rw [card_univ, ← card_eq_fintype_card, hE.card] at htot
        have hZ : ((univ.filter fun a => a * τ a * B.h w w = b).card) +
            ((univ.filter fun a => ¬a * τ a * B.h w w = b).card : ℤ) = (q : ℤ) ^ 2 := by exact_mod_cast htot
        linear_combination hZ - hhit
      rw [hhit, hmiss]
      cases m with
      | zero => simp [sphVal]
      | succ k => simp [sphVal]; ring
    have hZ : (card {v : V // B.h v v = 0}) = q ^ (2 * (m + 1)) - (q - 1) * sphVal q ε (m + 1) := by
      have hpart : Fintype.card V = ∑ b : fixSub τ, (univ.filter fun v => B.h v v = b.1).card := by
        rw [← card_univ, card_eq_sum_card_fiberwise (f := fun v => (⟨B.h v v, (B.symm v v).symm⟩ : fixSub τ)) $ fun _ _ => mem_univ _]
        refine sum_congr rfl fun _ _ => ?_; congr 1; ext v; simp [Subtype.ext_iff]
      rw [← add_sum_erase _ _ $ mem_univ 0] at hpart
      have hpartZ : (Fintype.card V) = (card {v : V // B.h v v = 0}) +
          ∑ b ∈ univ.erase (0 : fixSub τ), (card {v : V // B.h v v = b.1} : ℤ) := by
        have := congrArg (Nat.cast (R := ℤ)) hpart; push_cast at this; rw [this]; congr 1
        · rw [card_eq_fintype_card, card_subtype]
        · exact sum_congr rfl fun _ _ => by rw [card_eq_fintype_card, card_subtype]
      have hnz : ∀ b ∈ univ.erase (0 : fixSub τ), (card {v : V // B.h v v = b.1} : ℤ) = sphVal q ε (m + 1) := fun b hb =>
        hS b.1 b.2 fun h0 => (mem_erase.1 hb).1 $ sx h0
      rw [sum_congr rfl hnz, sum_const, card_erase_of_mem $ mem_univ _, card_univ, nsmul_eq_mul,
        ← card_eq_fintype_card, ← card_eq_fintype_card, hV, resAlg_card_fixed hE, Nat.cast_sub hq.le] at hpartZ
      push_cast at hpartZ
      linear_combination -hpartZ
    exact ⟨hS, hZ⟩

private lemma card_orthonormal_tuples {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
    (hE : ResAlg E τ q ε) :
    ∀ n m (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), n ≤ m → card V = q ^ (2 * m) →
      (card {v : Fin n → V // ∀ i j, B.h (v i) (v j) = if i = j then 1 else 0} : ℤ) =
        ∏ i : Fin n, sphVal q ε (m - (i : ℕ)) := by
  intro n; induction n with
  | zero =>
    intro _ V _ _ B _ _
    simp
  | succ n ih =>
    intro m V _ _ B hnm hV
    classical
    have := Nat.finite_of_card_ne_zero $ by rw [hV]; have := hE.one_lt; positivity
    let : Fintype V := ofFinite V
    let S1 := {w : V // B.h w w = 1}
    let F (w : S1) := {u : Fin n → B.perp w.1 // ∀ i j, (B.perpForm $ by rw [w.2]; exact isUnit_one).h (u i) (u j) = if i = j then 1 else 0}
    let e : {v : Fin (n + 1) → V // ∀ i j, B.h (v i) (v j) = if i = j then 1 else 0} ≃ (w : S1) × F w :=
      { toFun := fun ⟨v, hv⟩ =>
          ⟨⟨v 0, by simpa using hv 0 0⟩,
           ⟨fun i => ⟨v i.succ, show B.h (v i.succ) (v 0) = 0 by simpa using hv i.succ 0⟩,
            fun i j => show B.h (v i.succ) (v j.succ) = if i = j then 1 else 0 by simpa using hv i.succ j.succ⟩⟩
        invFun := fun ⟨w, u⟩ =>
          ⟨Fin.cons w.1 fun i => (u.1 i).1, fun i j => by
            refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
            · simp [w.2]
            · simp [(Fin.succ_ne_zero j').symm, B.symm (u.1 j').1 w.1, show B.h (u.1 j').1 w.1 = 0 from (u.1 j').2]
            · simp [ show B.h (u.1 i').1 w.1 = 0 from (u.1 i').2]
            · show (B.perpForm $ by rw [w.2]; exact isUnit_one).h (u.1 i') (u.1 j') = if i'.succ = j'.succ then 1 else 0
              simpa using u.2 i' j'⟩
        left_inv := fun ⟨v, _⟩ => sx $ Fin.cons_self_tail v
        right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => Sigma.ext (sx rfl) $ heq_of_eq $ sx $ funext fun _ => sx rfl }
    have hfib : ∀ w : S1, (card (F w)) = ∏ i : Fin n, sphVal q ε (m - 1 - i) := fun w => by
      have hw : IsUnit (B.h w.1 w.1) := by rw [w.2]; exact isUnit_one
      exact ih (m - 1) (B.perp w.1) (B.perpForm hw) (by omega) $ by
        have h1 : card E * card (B.perp w.1) = card V := by rw [← card_prod, card_congr $ B.perpEquiv hw]
        rw [hE.card, hV, show 2 * m = 2 + 2 * (m - 1) by omega, pow_add] at h1
        exact Nat.eq_of_mul_eq_mul_left (by
                                            have := hE.one_lt
                                            positivity) h1
    have h1 : (card {v : Fin (n + 1) → V // ∀ i j, B.h (v i) (v j) = if i = j then 1 else 0} : ℤ) = ∑ w : S1, (card (F w) : ℤ) := by
      have hcard : card ((w : S1) × F w) = ∑ w : S1, card (F w) := by
        rw [card_eq_fintype_card, Fintype.card_sigma]
        exact sum_congr rfl fun _ _ => card_eq_fintype_card.symm
      rw [card_congr e, hcard]
      push_cast
      rfl
    rw [h1, sum_congr rfl fun w _ => hfib w, sum_const, card_univ, nsmul_eq_mul, ← card_eq_fintype_card]
    have := resAlg_nontrivial hE
    rw [(sphere_card hE m V B hV).1 1 (map_one τ) one_ne_zero, Fin.prod_univ_succ]
    simp only [  Fin.val_succ]
    congr 1
    exact prod_congr rfl fun i _ => by rw [show m - ((i : ℕ) + 1) = m - 1 - (i : ℕ) by omega]

private lemma exists_congr_one_mod1 {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (hR : IsUnrQuad R σ ϖ q ε) {m : ℕ} (S : Mat m m R) (hS : IsUnimod σ S) :
    ∃ U U' : Mat m m (Qk R ϖ 1), U * U' = 1 ∧ U' * U = 1 ∧
      cT (barσ σ ϖ hR.fix_ϖ 1) U * red ϖ 1 S * U = 1 := by
  let E := Qk R ϖ 1
  let τ := barσ σ ϖ hR.fix_ϖ 1
  have hE := resAlg_of_isUnrQuad hR
  have := resAlg_nontrivial hE
  obtain ⟨g, g', d, hgg, hgg', hd, hgd, hdu⟩ := herm_diag_unimod hR m S hS
  have hd_nz : ∀ i, mkQ ϖ 1 (d i) ≠ 0 := fun i h0 => unit_notMem hR.notUnit (hdu i) $ eq_zero_iff_mem.1 h0
  have hex : ∀ i, ∃ a : E, a * τ a = mkQ ϖ 1 (d i) := fun i => by
    have hpos : 0 < card {a : E // a * τ a = mkQ ϖ 1 (d i)} := by
      have : (0 : ℤ) < card {a : E // a * τ a = mkQ ϖ 1 (d i)} := by
        rw [norm_fibre_card_nonzero hE (by simp [hd i]) $ hd_nz i]
        have := hR.one_lt
        rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
      exact_mod_cast this
    exact let ⟨a⟩ := (Nat.card_pos_iff.1 hpos).1; ⟨a.1, a.2⟩
  choose a ha using hex
  have hau : ∀ i, IsUnit (a i) := fun i => isUnit_of_mul_isUnit_left (ha i ▸ hE.fixedUnit _ (by simp [hd i]) (hd_nz i))
  let u i : E := ((hau i).unit⁻¹ : Eˣ)
  let D := diagonal u
  let D' := diagonal a
  have hDD' : D * D' = 1 := by rw [diagonal_mul_diagonal]; ext i j; by_cases h : i = j <;> simp [u, h, one_apply]
  have hD'D : D' * D = 1 := by rw [diagonal_mul_diagonal]; ext i j; by_cases h : i = j <;> simp [u, h, one_apply]
  refine ⟨red ϖ 1 g * D, D' * red ϖ 1 g', ?_, ?_, ?_⟩
  · calc red ϖ 1 g * D * (D' * red ϖ 1 g') = red ϖ 1 g * (D * D') * red ϖ 1 g' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDD', Matrix.mul_one, ← red_mul, hgg, red_one]
  · calc D' * red ϖ 1 g' * (red ϖ 1 g * D) = D' * (red ϖ 1 g' * red ϖ 1 g) * D := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← red_mul, hgg', red_one, Matrix.mul_one, hD'D]
  · have hctD : cT τ D = diagonal fun i => τ (u i) := by
                                                         ext i j
                                                         by_cases h : i = j <;> simp [D, cT, h, eq_comm]
    have h1 : cT τ (red ϖ 1 g) * red ϖ 1 S * red ϖ 1 g = diagonal fun i => mkQ ϖ 1 (d i) := by
      rw [← red_cT ϖ hR.fix_ϖ, ← red_mul, ← red_mul, hgd, red_diagonal]
    calc cT τ (red ϖ 1 g * D) * red ϖ 1 S * (red ϖ 1 g * D)
        = cT τ D * (cT τ (red ϖ 1 g) * red ϖ 1 S * red ϖ 1 g) * D := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal (fun i => τ $ u i) * diagonal (fun i => mkQ ϖ 1 $ d i) * D := by rw [h1, hctD]
      _ = 1 := by
          rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
          ext i j
          by_cases h : i = j
          · subst h
            simp only [diagonal_apply_eq, one_apply_eq]
            have h1 : u i * a i = 1 := (hau i).unit.inv_mul
            have h2 : τ (u i) * τ (a i) = 1 := by rw [← map_mul, h1, map_one]
            rw [← ha i]
            calc τ (u i) * (a i * τ (a i)) * u i = (τ (u i) * τ (a i)) * (u i * a i) := by ring
              _ = 1 := by rw [h1, h2, one_mul]
          · simp [h]

private lemma solCount_one {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (hR : IsUnrQuad R σ ϖ q ε) {m n : ℕ} (hnm : n ≤ m)
    (S : Mat m m R) (T : Mat n n R) (hS : IsUnimod σ S) (hT : IsUnimod σ T) :
    (solCount σ ϖ S T 1 : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  let E := Qk R ϖ 1
  let τ := barσ σ ϖ hR.fix_ϖ 1
  have hE := resAlg_of_isUnrQuad hR
  obtain ⟨US, US', hUS, hUS', hS1⟩ := exists_congr_one_mod1 hR S hS
  obtain ⟨UT, UT', hUT, hUT', hT1⟩ := exists_congr_one_mod1 hR T hT
  have hcongr : {y : Mat m n E | cT τ y * red ϖ 1 S * y = red ϖ 1 T} ≃ {z : Mat m n E | cT τ z * z = 1} :=
    { toFun := fun ⟨y, hy⟩ => ⟨US' * y * UT, by
        show cT τ (US' * y * UT) * (US' * y * UT) = 1
        have h1 : cT τ US' * cT τ US = 1 := by rw [← cT_mul, hUS, cT_one]
        have h2 : cT τ (US' * y * UT) * (cT τ US * red ϖ 1 S * US) * (US' * y * UT) = cT τ UT * (cT τ y * red ϖ 1 S * y) * UT := by
          rw [cT_mul, cT_mul]
          calc cT τ UT * (cT τ y * cT τ US') * (cT τ US * red ϖ 1 S * US) * (US' * y * UT)
              = cT τ UT * cT τ y * ((cT τ US' * cT τ US) * red ϖ 1 S * (US * US')) * y * UT := by simp only [Matrix.mul_assoc]
            _ = cT τ UT * (cT τ y * red ϖ 1 S * y) * UT := by rw [h1, hUS, Matrix.one_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        rw [hS1, Matrix.mul_one, hy, hT1] at h2
        exact h2⟩
      invFun := fun ⟨z, hz⟩ => ⟨US * z * UT', by
        show cT τ (US * z * UT') * red ϖ 1 S * (US * z * UT') = red ϖ 1 T
        have h1 : cT τ UT' * cT τ UT = 1 := by rw [← cT_mul, hUT, cT_one]
        rw [cT_mul, cT_mul]
        calc cT τ UT' * (cT τ z * cT τ US) * red ϖ 1 S * (US * z * UT')
            = cT τ UT' * (cT τ z * (cT τ US * red ϖ 1 S * US) * z) * UT' := by simp only [Matrix.mul_assoc]
          _ = cT τ UT' * (cT τ UT * red ϖ 1 T * UT) * UT' := by rw [hS1, Matrix.mul_one, hz, hT1]
          _ = (cT τ UT' * cT τ UT) * red ϖ 1 T * (UT * UT') := by simp only [Matrix.mul_assoc]
          _ = red ϖ 1 T := by rw [h1, hUT, Matrix.one_mul, Matrix.mul_one]⟩
      left_inv := fun ⟨y, _⟩ => sx $ by
        calc US * (US' * y * UT) * UT' = (US * US') * y * (UT * UT') := by simp only [Matrix.mul_assoc]
          _ = y := by rw [hUS, hUT, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun ⟨z, _⟩ => sx $ by
        calc US' * (US * z * UT') * UT = (US' * US) * z * (UT' * UT) := by simp only [Matrix.mul_assoc]
          _ = z := by rw [hUS', hUT', Matrix.one_mul, Matrix.mul_one] }
  have hcol : {z : Mat m n E | cT τ z * z = 1} ≃
      {v : Fin n → Fin m → E // ∀ i j, (HermSp.std hE.inv m).h (v i) (v j) = if i = j then 1 else 0} :=
    { toFun := fun ⟨z, hz⟩ => ⟨fun j a => z a j, fun i j => by
        have hij := congrFun (congrFun hz j) i
        simp only [mul_apply, cT, transpose_apply, map_apply, one_apply] at hij
        simpa [HermSp.std, eq_comm, mul_comm] using hij⟩
      invFun := fun ⟨v, hv⟩ => ⟨of fun a j => v j a, by
        ext i j
        have hij := hv j i
        simp only [HermSp.std] at hij
        simpa [mul_apply, cT, transpose_apply, map_apply, one_apply, eq_comm, mul_comm] using hij⟩
      left_inv := fun ⟨_, _⟩ => sx rfl
      right_inv := fun ⟨_, _⟩ => sx rfl }
  have hZ : (solCount σ ϖ S T 1) = ∏ i : Fin n, sphVal q ε (m - i) := by
    unfold solCount
    rw [solImg_eq ϖ hR.fix_ϖ 1 S T, card_congr $ hcongr.trans hcol]
    exact card_orthonormal_tuples hE n m (Fin m → E) (HermSp.std hE.inv m) hnm
      (by rw [card_fun, card_fin, hE.card, ← pow_mul])
  rw [show (solCount σ ϖ S T 1 : ℝ) = ∏ i : Fin n, ((sphVal q ε (m - (i : ℕ)) : ℤ) : ℝ) by exact_mod_cast hZ]
  have hq0 : (q : ℝ) ≠ 0 := by
                               have := hR.one_lt
                               positivity
  have hterm : ∀ i : Fin n, ((sphVal q ε (m - (i : ℕ)) : ℤ) : ℝ) =
      (q : ℝ) ^ (2 * (m - (i : ℕ)) - 1) * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := fun i => by
    have hi := i.isLt
    obtain ⟨k, hk⟩ : ∃ k, m - (i : ℕ) = k + 1 := ⟨m - (i : ℕ) - 1, by omega⟩
    rw [hk]
    simp only [sphVal, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_sub]
    rw [div_pow, show 2 * (k + 1) - 1 = k + (k + 1) by omega, pow_add]
    field_simp
    ring
  rw [prod_congr rfl fun i _ => hterm i, prod_mul_distrib, prod_pow_eq_pow_sum]
  congr 1
  congr 1
  clear hcongr hcol hZ hterm hUS hUS' hS1 hUT hUT' hT1 US US' UT UT' T hT
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, Fin.val_last]
    simp only [Fin.val_castSucc]
    rw [ih $ by omega]
    zify [show k ^ 2 ≤ 2 * m * k by nlinarith, show (k + 1) ^ 2 ≤ 2 * m * (k + 1) by nlinarith,
      show 1 ≤ 2 * (m - k) by omega, show k ≤ m by omega]
    ring

private lemma solCount_succ {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (hR : IsUnrQuad R σ ϖ q ε) {m n : ℕ} (hnm : n ≤ m)
    (S : Mat m m R) (T : Mat n n R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    (k : ℕ) (hk : 1 ≤ k) :
    solCount σ ϖ S T (k + 1) = solCount σ ϖ S T k * q ^ (2 * m * n - n ^ 2) := by
  classical
  have := finite_quot hR k; have := finite_quot hR $ k + 1
  let E := Qk R ϖ 1
  let τ := barσ σ ϖ hR.fix_ϖ 1
  let r1 {a b} (M : Mat a b R) := red ϖ 1 M
  let rk {a b} (M : Mat a b R) := red ϖ k M
  let rk1 {a b} (M : Mat a b R) := red ϖ (k + 1) M
  let Sol j := {y : Mat m n (Qk R ϖ j) // cT (barσ σ ϖ hR.fix_ϖ j) y * red ϖ j S * y = red ϖ j T}
  have hSol : ∀ j, solCount σ ϖ S T j = card (Sol j) := fun j => by
                                                                    unfold solCount
                                                                    rw [solImg_eq ϖ hR.fix_ϖ j S T]
                                                                    rfl
  rw [hSol $ k + 1, hSol k]
  let proj : Sol (k + 1) → Sol k := fun ⟨y, hy⟩ =>
    let f := factor (lev_le (ϖ := ϖ) $ Nat.le_succ k)
    ⟨y.map f, by
      obtain ⟨x, rfl⟩ := red_surj ϖ (k + 1) y
      have hmap : ∀ {a b} (M : Mat a b R), (rk1 M).map f = rk M := fun _ => by
                                                                               ext
                                                                               rfl
      rw [hmap, ← red_gram ϖ hR.fix_ϖ]
      have h1 := congrArg (fun M => M.map f) hy
      rwa [← red_gram ϖ hR.fix_ϖ, hmap, hmap] at h1⟩
  have hfib : ∀ s : Sol k, card {t : Sol (k + 1) // proj t = s} = q ^ (2 * m * n - n ^ 2) := fun ⟨s, hs⟩ => by
    obtain ⟨x₀, rfl⟩ := red_surj ϖ k s
    have hΔmem : ∀ i j, (cT σ x₀ * S * x₀ - T) i j ∈ lev ϖ k := fun i j => by
      have := congrFun (congrFun hs i) j; rw [← red_gram ϖ hR.fix_ϖ] at this; exact iqEq.1 this
    choose Δ hΔ using fun i j => mem_lev_iff.1 $ hΔmem i j
    let ΔM : Mat n n R := of Δ
    have hΔeq : cT σ x₀ * S * x₀ - T = (ϖ ^ k) • ΔM := by
                                                          ext i j
                                                          exact hΔ i j
    have hΔH : cT σ ΔM = ΔM := by
      ext i j
      show σ (Δ j i) = Δ i j
      apply hR.reg.pow k
      have hH : cT σ (cT σ x₀ * S * x₀ - T) = cT σ x₀ * S * x₀ - T := by simp [cT_cT hR.inv, hS.1, hT.1, Matrix.mul_assoc]
      have hij := congrFun (congrFun hH i) j; rw [hΔeq] at hij
      simpa [cT, ΔM, map_mul, map_pow, hR.fix_ϖ] using hij
    let X := r1 x₀; let S₁ := r1 S; let T₁ := r1 T
    have hXST : cT τ X * S₁ * X = T₁ := by
      let f := factor $ lev_le (ϖ := ϖ) hk
      have hmap : ∀ {a b} (M : Mat a b R), (rk M).map f = r1 M := fun _ => by
                                                                              ext
                                                                              rfl
      have hf := congrArg (fun M => M.map f) hs
      rw [← red_gram ϖ hR.fix_ϖ k S x₀, hmap, hmap] at hf
      dsimp only [r1] at hf
      rwa [red_gram ϖ hR.fix_ϖ 1 S x₀] at hf
    let P (y : Mat m n R) := x₀ + (ϖ ^ k) • y
    let G (y : Mat m n R) := cT σ y * S * y
    let D (Y : Mat m n E) := cT τ X * S₁ * Y + cT τ Y * S₁ * X
    have hlift : ∀ y : Mat m n R, rk1 (G (P y)) = rk1 T ↔ D (r1 y) = -r1 ΔM := fun y => by
      have h2k : ϖ ^ k * ϖ ^ k ∈ lev ϖ (k + 1) := mem_lev_iff.2 ⟨ϖ ^ (k - 1), by rw [← pow_add, ← pow_add]; congr 1; omega⟩
      let L := ΔM + cT σ x₀ * S * y + cT σ y * S * x₀
      have hL1 : r1 L = r1 ΔM + D (r1 y) := by simp only [L, D, r1, X, S₁, τ, red_add, red_mul, red_cT ϖ hR.fix_ϖ, add_assoc]
      have hexp : G (P y) - T = (ϖ ^ k) • L + (ϖ ^ k * ϖ ^ k) • G y := by
        simp only [G, P, L, cT_add, cT_smul, map_pow, hR.fix_ϖ, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          smul_smul, smul_add, ← hΔeq]; abel
      constructor
      · intro h
        have hred : r1 L = 0 := by
          ext i j
          have hij : (G (P y) - T) i j ∈ lev ϖ (k + 1) := iqEq.1 $ congrFun (congrFun h i) j
          rw [hexp] at hij
          obtain ⟨c, hc⟩ := mem_lev_iff.1 $ by
            simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_right] using
              Ideal.sub_mem _ hij $ Ideal.mul_mem_right (G y i j) _ h2k
          exact eq_zero_iff_mem.2 $ mem_lev_iff.2 ⟨c, hR.reg.pow k $ by
                                                                        show ϖ ^ k * L i j = ϖ ^ k * (ϖ ^ 1 * c)
                                                                        rw [hc]
                                                                        ring⟩
        rw [hL1] at hred
        exact eq_neg_of_add_eq_zero_right hred
      · intro h
        ext i j
        apply iqEq.2
        show (G (P y) - T) i j ∈ lev ϖ (k + 1)
        rw [hexp]
        have h0 : (r1 L) i j = 0 := by rw [hL1, h, add_neg_cancel, Matrix.zero_apply]
        obtain ⟨c, hc⟩ := mem_lev_iff.1 $ eq_zero_iff_mem.1 h0
        exact Ideal.add_mem _ (mem_lev_iff.2 ⟨c, by
                                                    show ϖ ^ k * L i j = _
                                                    rw [hc]
                                                    ring⟩) $ Ideal.mul_mem_right _ _ h2k
    let AddHerm : AddSubgroup (Mat n n E) :=
      { carrier := hermMod σ ϖ n 1
        add_mem' := by
                       rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
                       exact ⟨a + b, by simp [show cT σ a = a from ha, show cT σ b = b from hb], red_add _ _ _ _⟩
        zero_mem' := ⟨0, cT_zero σ, red_zero _ _⟩
        neg_mem' := by
                       rintro _ ⟨a, ha, rfl⟩
                       exact ⟨-a, by simp [show cT σ a = a from ha], red_neg _ _ _⟩ }
    let φ : Mat m n E →+ AddHerm :=
      { toFun := fun Y => ⟨D Y, by
          obtain ⟨y, rfl⟩ := red_surj ϖ 1 Y
          exact ⟨cT σ x₀ * S * y + cT σ y * S * x₀, by simp [cT_cT hR.inv, hS.1, Matrix.mul_assoc, add_comm],
            by simp [D, X, S₁, r1, τ, red_cT ϖ hR.fix_ϖ]⟩⟩
        map_zero' := sx $ by simp [D]
        map_add' := fun _ _ => sx $ by simp only [D, AddSubgroup.coe_add, cT_add, Matrix.mul_add, Matrix.add_mul]; abel }
    have hφsurj : Function.Surjective φ := fun ⟨H, hH⟩ => by
      obtain ⟨c, hc⟩ := exists_trace_one hR
      let c₁ := mkQ ϖ 1 c
      have hc₁ : c₁ + τ c₁ = 1 := by
                                     change mkQ ϖ 1 c + mkQ ϖ 1 (σ c) = 1
                                     rw [← map_add, hc, map_one]
      have hHsym : cT τ H = H := by
                                    obtain ⟨h₀, hh₀, rfl⟩ := hH
                                    rw [← red_cT ϖ hR.fix_ϖ, hh₀]
      let half := of fun i j => if i < j then H i j else if i = j then c₁ * H i i else 0
      have hhalf : half + cT τ half = H := by
        ext i j
        have hji : τ (H j i) = H i j := congrFun (congrFun hHsym i) j
        simp only [Matrix.add_apply, cT, transpose_apply, map_apply, half, of_apply]
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h, not_lt.2 h.le, h.ne']
        · simp only [lt_irrefl, ↓reduceIte, map_mul, hji, ← add_mul, hc₁, one_mul]
        · simp [h, not_lt.2 h.le, h.ne', hji]
      refine ⟨X * T₁⁻¹ * half, sx ?_⟩
      have h1 : cT τ X * S₁ * (X * T₁⁻¹ * half) = half := by
        calc cT τ X * S₁ * (X * T₁⁻¹ * half) = (cT τ X * S₁ * X) * T₁⁻¹ * half := by simp only [Matrix.mul_assoc]
          _ = (T₁ * T₁⁻¹) * half := by rw [hXST, Matrix.mul_assoc]
          _ = half := by rw [mul_nonsing_inv _ $ by
            rw [show T₁.det = mkQ ϖ 1 T.det from (RingHom.map_det (mkQ ϖ 1) T).symm]
            exact hT.2.map _, Matrix.one_mul]
      have h2 : cT τ (X * T₁⁻¹ * half) * S₁ * X = cT τ half := by
        have h3 := congrArg (cT τ) h1
        rwa [cT_mul τ $ cT τ X * S₁, cT_mul τ $ cT τ X, cT_cT $ barσ_inv hR.fix_ϖ hR.inv 1,
          show cT τ S₁ = S₁ by rw [← red_cT ϖ hR.fix_ϖ, hS.1], ← Matrix.mul_assoc] at h3
      show D (X * T₁⁻¹ * half) = H
      dsimp only [D]
      rw [h1, h2, hhalf]
    have hΔin : -r1 ΔM ∈ AddHerm := ⟨-ΔM, by simp [hΔH], red_neg _ _ _⟩
    obtain ⟨Y₀, hY₀⟩ := hφsurj ⟨-r1 ΔM, hΔin⟩
    let Fib := {Y : Mat m n E // φ Y = ⟨-r1 ΔM, hΔin⟩}
    have hfb : card Fib = q ^ (2 * m * n - n ^ 2) := by
      have heq : Fib ≃ φ.ker :=
        { toFun := fun ⟨Y, hY⟩ => ⟨Y - Y₀, by simp [AddMonoidHom.mem_ker, hY, hY₀]⟩
          invFun := fun ⟨Z, hZ⟩ => ⟨Y₀ + Z, by simp [hY₀, AddMonoidHom.mem_ker.1 hZ]⟩
          left_inv := fun ⟨_, _⟩ => sx $ by
                                            dsimp
                                            abel
          right_inv := fun ⟨_, _⟩ => sx $ by
                                             dsimp
                                             abel }
      rw [card_congr heq]
      have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
      rw [card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv] at hcard
      have hM : card (Mat m n E) = q ^ (2 * m * n) := by
        show card (Fin m → Fin n → E) = _
        rw [card_fun, card_fun, card_fin, card_fin, hR.card, ← pow_mul, ← pow_mul]
        congr 1
        ring
      have hH : card AddHerm = q ^ (n ^ 2) := by
                                                 change card (hermMod σ ϖ n 1) = _
                                                 simpa using card_hermMod hR n 1
      rw [hM, hH, show q ^ (2 * m * n) = q ^ (n ^ 2) * q ^ (2 * m * n - n ^ 2) by
        rw [← pow_add, Nat.add_sub_of_le $ by nlinarith]] at hcard
      exact Nat.eq_of_mul_eq_mul_left (by
                                          have := hR.one_lt
                                          positivity) hcard.symm
    have heq2 : Fib ≃ {t : Sol (k + 1) // proj t = ⟨rk x₀, hs⟩} := by
      let liftY Y : Mat m n R := (red_surj ϖ 1 Y).choose
      have hliftY : ∀ Y, r1 (liftY Y) = Y := fun Y => (red_surj ϖ 1 Y).choose_spec
      have hmk_eq : ∀ y₁ y₂ : Mat m n R, r1 y₁ = r1 y₂ → rk1 (P y₁) = rk1 (P y₂) := fun y₁ y₂ hy => by
        ext i j
        apply iqEq.2
        obtain ⟨c, hc⟩ := mem_lev_iff.1 (iqEq.1 (congrFun (congrFun hy i) j))
        exact mem_lev_iff.2 ⟨c, by
          show (x₀ i j + ϖ ^ k * y₁ i j) - (x₀ i j + ϖ ^ k * y₂ i j) = _
          rw [show (x₀ i j + ϖ ^ k * y₁ i j) - (x₀ i j + ϖ ^ k * y₂ i j) = ϖ ^ k * (y₁ i j - y₂ i j) by ring, hc]
          ring⟩
      let g : Fib → {t : Sol (k + 1) // proj t = ⟨rk x₀, hs⟩} := fun ⟨Y, hY⟩ =>
        ⟨⟨rk1 $ P $ liftY Y, by rw [← red_gram ϖ hR.fix_ϖ]; exact (hlift $ liftY Y).2 $ by rw [hliftY]; exact congrArg Subtype.val hY⟩,
         sx $ by
          ext i j
          show factor (lev_le (Nat.le_succ k)) (mkQ ϖ (k + 1) (x₀ i j + ϖ ^ k * liftY Y i j)) = mkQ ϖ k (x₀ i j)
          rw [factor_mk, map_add, eq_zero_iff_mem.2 $ mem_lev_iff.2 ⟨liftY Y i j, rfl⟩, add_zero]⟩
      refine Equiv.ofBijective g ⟨fun ⟨Y₁, _⟩ ⟨Y₂, _⟩ h => sx ?_, fun ⟨⟨t, ht⟩, hpt⟩ => ?_⟩
      · show Y₁ = Y₂
        rw [← hliftY Y₁, ← hliftY Y₂]
        ext i j
        apply iqEq.2
        obtain ⟨c, hc⟩ := mem_lev_iff.1 (by
                                            convert (iqEq.1 (congrArg (fun u : {t : Sol (k + 1) // proj t = ⟨rk x₀, hs⟩} => u.1.1 i j) h)) using 1
                                            simp only [P, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
                                            ring :
          ϖ ^ k * (liftY Y₁ i j - liftY Y₂ i j) ∈ lev ϖ (k + 1))
        exact mem_lev_iff.2 ⟨c, hR.reg.pow k $ by
                                                  show ϖ ^ k * _ = ϖ ^ k * (ϖ ^ 1 * c)
                                                  rw [hc]
                                                  ring⟩
      · obtain ⟨x₁, rfl⟩ := red_surj ϖ (k + 1) t
        choose y hy using fun i j => mem_lev_iff.1 $ iqEq.1 $ congrArg (fun u => u.1 i j) hpt
        let ym := of y
        have hx1 : x₁ = P ym := by
          ext i j
          have h' : x₁ i j - x₀ i j = ϖ ^ k * y i j := hy i j
          show x₁ i j = x₀ i j + ϖ ^ k * y i j
          linear_combination h'
        refine ⟨⟨r1 ym, sx $ (hlift ym).1 $ by dsimp only [rk1, G]; rwa [← hx1, red_gram ϖ hR.fix_ϖ]⟩, sx $ sx ?_⟩
        show rk1 (P $ liftY $ r1 ym) = rk1 x₁
        rw [hmk_eq (liftY $ r1 ym) ym $ hliftY _, ← hx1]
    rw [← card_congr heq2, hfb]
  let : Fintype (Sol k) := ofFinite _
  let : Fintype (Sol (k + 1)) := ofFinite _
  have hsum : card (Sol (k + 1)) = ∑ s : Sol k, card {t : Sol (k + 1) // proj t = s} := by
    rw [card_eq_fintype_card, ← card_univ, card_eq_sum_card_fiberwise (f := proj) $ fun _ _ => mem_univ _]
    exact sum_congr rfl fun _ _ => by rw [card_eq_fintype_card, card_subtype]
  rw [hsum, sum_congr rfl fun s _ => hfib s, sum_const, card_univ, smul_eq_mul, ← card_eq_fintype_card]

lemma unrFormula : UnrFormula := by
  intro R _ σ ϖ q ε hR m n hnm S T hS hT
  have hq : (0 : ℝ) < q := by exact_mod_cast lt_trans zero_lt_one hR.one_lt
  obtain ⟨a, ha⟩ : ∃ a, 2 * m * n - n ^ 2 = a := ⟨_, rfl⟩
  have ha' : a + n ^ 2 = 2 * m * n := by rw [← ha]; exact Nat.sub_add_cancel $ by nlinarith
  have hsol : ∀ j : ℕ, (solCount σ ϖ S T (j + 1) : ℝ) =
      (q : ℝ) ^ a * (∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) * (q : ℝ) ^ (j * a) := fun j => by
    induction j with
    | zero => rw [solCount_one hR hnm S T hS hT, ha]; simp
    | succ j ih => rw [solCount_succ hR hnm S T hS hT (j + 1) $ by omega, ha]; push_cast; rw [ih, add_mul, one_mul, pow_add]; ring
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  symm
  unfold densAt
  have hM : card (Mat m n (Qk R ϖ (j + 1))) = q ^ (2 * (j + 1) * (m * n)) := by
    show card (Fin m → Fin n → Qk R ϖ (j + 1)) = _
    rw [card_fun, card_fun, card_fin, card_fin, card_quot_lev hR $ j + 1, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hsol j, card_hermMod hR n $ j + 1, hM]
  have he : a + j * a + (j + 1) * n ^ 2 = 2 * (j + 1) * (m * n) := by
    calc a + j * a + (j + 1) * n ^ 2 = (j + 1) * (a + n ^ 2) := by ring
      _ = (j + 1) * (2 * m * n) := by rw [ha']
      _ = 2 * (j + 1) * (m * n) := by ring
  push_cast
  rw [div_eq_iff (pow_pos hq _).ne', ← he, pow_add, pow_add]
  ring

end UnrFormulaSec

end C8

namespace AlpogeRHCore8

theorem siegelWeilLocalDensity :
    PositivityTheory.PfSWUS.Loc.SeriesEqDens ∧
    PositivityTheory.PfSWUS.Loc.UnrFormula :=
  ⟨C8.seriesEqDens, C8.unrFormula⟩
