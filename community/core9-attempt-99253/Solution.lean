import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase

namespace AlpogeRHCore9

open Finset Matrix Equiv Formalism.L2.SG.GGMirabolic
open AddChar (map_add_eq_mul map_zero_eq_one ne_one_iff)
open Fin (revPerm rev_lt_rev)
open Fintype (ofFinite sum_equiv)
open Units (val_mul val_one)

noncomputable section

open Classical
open Equiv (mulLeft mulRight)
open LinearMap (congr_fun range)

section Helpers

variable {K : Type} [Field K] {N : ℕ}

abbrev Mat (N : ℕ) (K : Type) := Matrix (Fin N) (Fin N) K
abbrev Gl (N : ℕ) (K : Type) [Field K] := GL (Fin N) K

private lemma isUni_one : IsUni N (1 : Gl N K) := ⟨one_apply_eq, fun _ _ h => one_apply_ne h.ne'⟩

private lemma isUni_mul {a b : Gl N K} (ha : IsUni N a) (hb : IsUni N b) : IsUni N $ a * b :=
  ⟨fun i => by
    rw [val_mul, mul_apply, sum_eq_single i, ha.1, hb.1, one_mul]
    exact fun m _ hm => by rcases lt_or_gt_of_ne hm with h | h <;> simp [ha.2, hb.2, h]
    simp,
   fun i j hij => by
    rw [val_mul, mul_apply]
    exact sum_eq_zero fun m _ => by
      rcases lt_or_ge m i with h | h
      simp [ha.2 i m h]
      simp [hb.2 m j $ lt_of_lt_of_le hij h]⟩

private lemma superdiag_mul {a b : Gl N K} (ha : IsUni N a) (hb : IsUni N b) :
    superdiag N (a * b).1 = superdiag N a.1 + superdiag N b.1 := by
  unfold superdiag
  simp [← sum_add_distrib, val_mul]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  split_ifs with h
  rw [mul_apply, ← add_sum_erase _ _ $ mem_univ i,
    ← add_sum_erase _ _ $ mem_erase.mpr ⟨by grind, mem_univ j⟩,
    ha.1, hb.1, one_mul, mul_one, sum_eq_zero, add_zero, add_comm]
  intro m hm
  simp at hm
  rcases lt_or_ge m i with h1 | h1
  simp [ha.2 i m h1]
  simp [hb.2 m j $ by grind]
  simp

private def flipM (A : Mat N K) : Mat N K := of fun i j => A j.rev i.rev

private lemma flipM_mul (A B : Mat N K) : flipM (A * B) = flipM B * flipM A := by
  ext i j
  simp [flipM, mul_apply]
  exact sum_equiv revPerm _ _ fun _ => by simp [mul_comm]

private lemma flipM_one : flipM (1 : Mat N K) = 1 := by ext i j; simp [flipM, one_apply, eq_comm]

private def flipG (g : Gl N K) : Gl N K :=
  ⟨flipM g.1, flipM g⁻¹.1,
    by rw [← flipM_mul, ← val_mul, inv_mul_cancel, val_one, flipM_one],
    by rw [← flipM_mul, ← val_mul, mul_inv_cancel, val_one, flipM_one]⟩

private lemma flipG_mul (x y : Gl N K) : flipG (x * y) = flipG y * flipG x :=
  Units.ext $ by simp [flipG, flipM_mul]

private lemma superdiag_flip (A : Mat N K) : superdiag N (flipM A) = superdiag N A := by
  unfold superdiag
  rw [sum_comm]
  refine sum_equiv revPerm _ _ fun j => sum_equiv revPerm _ _ fun i => ?_
  have : ((j : ℕ) = i + 1) ↔ ((i.rev : Fin N) : ℕ) = j.rev + 1 := by grind
  simp [flipM, this]

private lemma transv_isUni {p q : Fin N} (h : p < q) (v : K) :
    IsUni N $ GeneralLinearGroup.transvection p q h.ne v :=
  ⟨fun i => by simp [GeneralLinearGroup.transvection, transvection, single_apply]
               grind,
   fun i j hij => by simp [GeneralLinearGroup.transvection, transvection, one_apply_ne hij.ne', single_apply]
                     grind⟩

private lemma superdiag_transv (p q : Fin N) (v : K) :
    superdiag N (transvection p q v) = if q.1 = p.1 + 1 then v else 0 := by
  simp [superdiag, transvection, one_apply, single_apply, show ∀ x c,
    (if c.1 = x.1 + 1 then (if x = c then (1 : K) else 0) + (if p = x ∧ q = c then v else 0) else 0) =
      if x = p then if c = q then if q.1 = p.1 + 1 then v else 0 else 0 else 0 by grind]

private lemma bruhat_exists (g : Gl N K) : ∃ v u : Gl N K,
    IsUni N v ∧ IsUni N u ∧ ∃ (π : Perm $ Fin N) (t : Fin N → K), (∀ j, t j ≠ 0) ∧
      ∃ M : Gl N K, g = v * M * u ∧ ∀ i j, M.1 i j = if i = π j then t j else 0 := by
  have hne (h : Gl N K) j : (univ.filter fun i => h.1 i j ≠ 0).Nonempty := by
    by_contra h0
    rw [not_nonempty_iff_eq_empty] at h0
    exact ((isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero $ det_eq_zero_of_column_eq_zero j fun i => by
      by_contra hi
      exact notMem_empty i $ h0 ▸ mem_filter.mpr ⟨mem_univ _, hi⟩
  let piv (h : Gl N K) j := (univ.filter fun i => h.1 i j ≠ 0).max' $ hne h j
  have hpiv_ne (h : Gl N K) j : h.1 (piv h j) j ≠ 0 := (mem_filter.mp $ max'_mem _ $ hne h j).2
  have hpiv_zero (h : Gl N K) j i (hi : piv h j < i) : h.1 i j = 0 := by
    by_contra h0
    exact absurd hi $ not_lt.mpr $ le_max' _ i $ mem_filter.mpr ⟨mem_univ _, h0⟩
  have hcol : ∀ w, ∀ h, ∑ j, (piv h j).1 = w →
      ∃ u, IsUni N u ∧ Function.Injective (piv $ h * u⁻¹) := by
    intro w
    induction w using Nat.strong_induction_on with
    | h w ih =>
      intro h hw
      by_cases hinj : Function.Injective $ piv h
      exact ⟨1, isUni_one, by simpa using hinj⟩
      unfold Function.Injective at hinj
      push Not at hinj
      obtain ⟨j₁, j₂, heq, hne'⟩ := hinj
      wlog hlt : j₁ < j₂ generalizing j₁ j₂
      exact this j₂ j₁ heq.symm hne'.symm $ lt_of_le_of_ne (not_lt.mp hlt) hne'.symm
      set r := piv h j₁
      let c := -h.1 r j₂ / h.1 r j₁
      let E := GeneralLinearGroup.transvection j₁ j₂ hlt.ne $ -c
      have hE : (h * E⁻¹).1 = h.1 * transvection j₁ j₂ c := by simp [E, GeneralLinearGroup.transvection]
      have hlt_piv : piv (h * E⁻¹) j₂ < r := by
        by_contra hge
        have hnz := hpiv_ne (h * E⁻¹) j₂
        rw [hE, mul_transvection_apply_same] at hnz
        rcases eq_or_lt_of_le (not_lt.mp hge) with hr | hr
        have hr1 : h.1 r j₁ ≠ 0 := hpiv_ne h j₁
        apply hnz
        rw [← hr]
        dsimp [c]
        field_simp
        ring
        rw [hpiv_zero h j₂ _ $ heq ▸ hr, hpiv_zero h j₁ _ hr, mul_zero, add_zero] at hnz
        exact hnz rfl
      have hsame j (hj : j ≠ j₂) : piv (h * E⁻¹) j = piv h j := by
        simp only [piv]
        congr 1
        ext i
        simp [hE, hj]
      obtain ⟨u, hu, hpinj⟩ := ih _ (by
        rw [← hw]
        refine sum_lt_sum (fun j _ => ?_) ⟨j₂, mem_univ _, heq ▸ hlt_piv⟩
        by_cases hj : j = j₂; · subst hj; exact (heq ▸ hlt_piv).le
        rw [hsame j hj]) (h * E⁻¹) rfl
      exact ⟨u * E, isUni_mul hu $ transv_isUni hlt $ -c, by rwa [_root_.mul_inv_rev, ← mul_assoc]⟩
  obtain ⟨u, hu, hinj⟩ := hcol _ g rfl
  set h := g * u⁻¹
  let π := ofBijective (piv h) $ Finite.injective_iff_bijective.mp hinj
  let t j := h.1 (π j) j
  have ht j : t j ≠ 0 := hpiv_ne h j
  let M : Gl N K :=
    ⟨of fun i j => if i = π j then t j else 0, of fun j i => if j = π.symm i then (t j)⁻¹ else 0,
     by ext i j
        simp [mul_apply, mul_ite, one_apply, mul_inv_cancel₀ $ ht _],
     by ext i j
        by_cases h : i = j <;> simp [h, mul_apply, mul_ite, one_apply, inv_mul_cancel₀ $ ht _]⟩
  exact ⟨h * M⁻¹, u, ⟨fun i => by simpa [val_mul, M, mul_apply, mul_ite, t] using mul_inv_cancel₀ $ ht $ π.symm i,
    fun i j hij => by
      simp [val_mul, M, mul_apply, mul_ite,
        hpiv_zero h (π.symm j) i $ by rwa [show piv h (π.symm j) = j from π.apply_symm_apply j]]⟩,
    hu, π, t, ht, M, by dsimp [h]
                        group, fun _ _ => rfl⟩

omit [Field K] in
private lemma mono_symm {α : Type} (π : Perm $ Fin N) (t : Fin N → α)
    (hadm : ∀ i j, j.1 = i.1 + 1 → π i < π j → (π j).1 = (π i).1 + 1 ∧ t i = t j) :
    ∀ i, π (π i).rev = i.rev ∧ t (π i).rev = t i := by
  suffices ∀ B ≤ N, (∀ x, N - B ≤ x.1 ↔ (π x).1 < B) →
      ∀ i, N - B ≤ i.1 → π (π i).rev = i.rev ∧ t (π i).rev = t i from
    fun i => this N le_rfl (fun _ => by simp) i $ by simp
  intro B; induction B using Nat.strong_induction_on with
  | h B ih =>
    intro hBN hinv i hi
    set s := N - B; have hsN : s < N := by omega
    set m := (π ⟨s, hsN⟩).1
    have hmB := (hinv ⟨s, hsN⟩).mp le_rfl
    set L := B - m
    have hblk : ∀ k < L, ∀ x, x.1 = s + k → (π x).1 = m + k ∧ t x = t ⟨s, hsN⟩ := by
      intro k; induction k using Nat.strong_induction_on with
      | h k ihk =>
        intro hk x hx
        rcases k with _ | k
        obtain rfl : x = ⟨s, hsN⟩ := Fin.ext hx; exact ⟨rfl, rfl⟩
        have hprev := ihk k (by omega) (by omega) ⟨s + k, by omega⟩ rfl
        have hgt : m + k < (π x).1 := by
          by_contra hle
          have hall : ∀ d, ∀ y, y.1 = s + k + 1 + d → (π y).1 ≤ m + k := by
            intro d; induction d with
            | zero => intro y hy; obtain rfl : y = x := Fin.ext (by omega); omega
            | succ d ihd =>
              intro y hy
              let y' : Fin N := ⟨s + k + 1 + d, by omega⟩
              have h1 := ihd y' rfl
              have hne : (π y').1 ≠ m + k := fun he => by
                have := congrArg Fin.val $ π.injective $ Fin.ext $ he.trans hprev.1.symm
                grind
              by_cases hlt : π y' < π y
              have := (hadm y' y (by grind) hlt).1; omega
              omega
          obtain ⟨z, hz⟩ := π.surjective ⟨m + k + 1, by omega⟩
          have hzs := (hinv z).mpr $ by rw [hz]
                                        grind
          have hzgt : s + k < z.1 := by
            by_contra; have := (ihk (z.1 - s) (by omega) (by omega) z $ by omega).1; rw [hz] at this; grind
          have := hall (z.1 - (s + k + 1)) z (by omega); rw [hz] at this; grind
        constructor
        grind
        exact (hadm ⟨s + k, by omega⟩ x (by grind) $ by grind).2.symm.trans hprev.2
    by_cases hiL : i.1 < s + L
    have h1 := hblk (i.1 - s) (by omega) i $ by omega
    have h2 := hblk ((π i).rev.1 - s) (by grind) (π i).rev $ by grind
    exact ⟨Fin.ext (by grind), h2.2.trans h1.2.symm⟩
    refine ih m hmB (by omega) (fun x => ⟨fun hx => ?_, fun hx => ?_⟩) i $ by omega
    have hxB := (hinv x).mp $ by omega
    by_contra
    have heq : π ⟨s + ((π x).1 - m), by omega⟩ = π x :=
      Fin.ext (by have := (hblk ((π x).1 - m) (by omega) ⟨s + ((π x).1 - m), by omega⟩ rfl).1; omega)
    have := congrArg Fin.val $ π.injective heq; grind
    have hxs := (hinv x).mpr $ by omega
    by_contra; have := (hblk (x.1 - s) (by omega) x $ by omega).1; omega

private lemma hecke_flip_inv (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (f : Gl N K → ℂ)
    (hf : ∀ u v g, IsUni N u → IsUni N v → f (u * g * v) = (psiU ψ₀ u)⁻¹ * (psiU ψ₀ v)⁻¹ * f g)
    (g : Gl N K) : f (flipG g) = f g := by
  have hflipU (u : Gl N K) (hu : IsUni N u) : IsUni N (flipG u) ∧ psiU ψ₀ (flipG u) = psiU ψ₀ u :=
    ⟨⟨fun _ => hu.1 _, fun _ _ hij => hu.2 _ _ $ rev_lt_rev.mpr hij⟩, by simp [psiU, flipG, superdiag_flip]⟩
  obtain ⟨v, u, hv, hu, π, t, ht, n, rfl, hn⟩ := bruhat_exists g
  let du := hflipU u hu; let dv := hflipU v hv
  rw [flipG_mul, flipG_mul, ← mul_assoc, hf _ _ _ du.1 dv.1, hf _ _ _ hv hu, du.2, dv.2, mul_comm (psiU ψ₀ u)⁻¹]
  congr 1
  by_cases hadm : ∀ i j, j.1 = i.1 + 1 → π i < π j → (π j).1 = (π i).1 + 1 ∧ t i = t j
  suffices flipG n = n by rw [this]
  refine Units.ext ?_
  ext i j
  change n.1 j.rev i.rev = n.1 i j
  rw [hn, hn]
  have hs := mono_symm π t hadm
  by_cases hij : i = π j
  rw [ite_eq_left hij, hij, (hs j).1, ite_eq_left rfl, (hs j).2]
  rw [ite_eq_right hij, ite_eq_right fun h3 => hij $ by grind]
  push Not at hadm
  obtain ⟨i, j, hij, hlt, hbad⟩ := hadm
  obtain ⟨a0, ha0⟩ := ne_one_iff.mp hψ
  have hilt : i < j := by grind
  let s := if (π j).1 = (π i).1 + 1 then t i / t j else 0
  have hs1 : 1 - s ≠ 0 := by grind
  let a := a0 / (1 - s)
  let c0 := a * t i / t j
  let u₁ := GeneralLinearGroup.transvection (π i) (π j) hlt.ne $ -c0
  let u₂ := GeneralLinearGroup.transvection i j hilt.ne a
  have hu₁ := transv_isUni hlt $ -c0
  have hu₂ := transv_isUni hilt a
  have hfix : u₁ * n * u₂ = n := Units.ext $ by
    ext x c
    simp [val_mul, u₁, u₂, GeneralLinearGroup.transvection]
    by_cases hc : c = j
    subst hc
    rw [mul_transvection_apply_same]
    by_cases hx : x = π i
    subst hx
    simp [hn, hlt.ne, hlt.ne', c0]
    field_simp [ht c]
    ring
    simp [hx, hn]
    by_cases hx : x = π i
    subst hx
    simp [hc, hn, show π j ≠ π c from fun h => hc (π.injective h).symm]
    simp [hc, hx]
  have hchi : psiU ψ₀ u₁ * psiU ψ₀ u₂ ≠ 1 := fun h => ha0 $ by
    simp [psiU, u₁, u₂, ← map_add_eq_mul, superdiag_transv, hij] at h
    rwa [show (if (π j).1 = (π i).1 + 1 then -c0 else 0) + a = a0 by
      have : (if (π j).1 = (π i).1 + 1 then -c0 else 0) = -(a * s) := by grind
      rw [this]
      dsimp [a]
      field_simp
      ring] at h
  have hzero (m v₁ v₂ : Gl N K) (hv₁ : IsUni N v₁) (hv₂ : IsUni N v₂)
      (hm : v₁ * m * v₂ = m) (hne : psiU ψ₀ v₁ * psiU ψ₀ v₂ ≠ 1) : f m = 0 := by
    by_contra h0; exact hne $ inv_eq_one.mp $ by rw [mul_inv]; exact mul_right_cancel₀ h0 $ by rw [one_mul, ← hf v₁ v₂ m hv₁ hv₂, hm]
  rw [hzero n u₁ u₂ hu₁ hu₂ hfix hchi,
    hzero (flipG n) (flipG u₂) (flipG u₁) (hflipU u₂ hu₂).1 (hflipU u₁ hu₁).1
      (by rw [← flipG_mul, ← flipG_mul, ← mul_assoc, hfix]) $ by grind]

end Helpers

open Submodule Module.End

theorem gelfandGraevMultOne : GelfandGraevMultOne := by
  intro F _ _ k ψ₀ hψ V _ _ _ π hπ ℓ₁ ℓ₂ h1 h2 hne
  have : Fintype $ Gl k F := ofFinite _
  let χ : Gl k F → ℂ := psiU ψ₀
  have hχne g : χ g ≠ 0 := left_ne_zero_of_mul_eq_one $
    show ψ₀ (superdiag k g.1) * ψ₀ (-superdiag k g.1) = 1 by rw [← map_add_eq_mul, add_neg_cancel, map_zero_eq_one]
  have hUinv {a : Gl k F} (ha : IsUni k a) : IsUni k a⁻¹ := by
    obtain ⟨⟨b, hb⟩, h⟩ := (Finite.injective_iff_surjective (f := fun x => ⟨a * x.1, isUni_mul ha x.2⟩)).mp
      (fun _ _ h => Subtype.ext $ mul_left_cancel $ congrArg Subtype.val h) ⟨1, isUni_one⟩
    exact eq_inv_of_mul_eq_one_right (congrArg Subtype.val h) ▸ hb
  have hχmul {a b : Gl k F} (ha : IsUni k a) (hb : IsUni k b) : χ (a * b) = χ a * χ b := by
    simp only [χ, psiU, superdiag_mul ha hb, map_add_eq_mul]
  let nU : ℂ := ((univ : Finset $ Gl k F).filter $ IsUni k).card
  have hnU : nU ≠ 0 := Nat.cast_ne_zero.mpr (card_pos.mpr ⟨1, by simp [isUni_one]⟩).ne'
  let e g : ℂ := if IsUni k g then nU⁻¹ * (χ g)⁻¹ else 0
  have heL {u : Gl k F} (hu : IsUni k u) x : e (u * x) = (χ u)⁻¹ * e x := by
    by_cases hx : IsUni k x
    simp [e, hx, isUni_mul hu hx, hχmul hu hx, mul_comm, mul_left_comm]
    simp [e, hx, show ¬IsUni k (u * x) from fun h => hx $ by simpa using isUni_mul (hUinv hu) h]
  have heR {v : Gl k F} (hv : IsUni k v) x : e (x * v) = (χ v)⁻¹ * e x := by
    by_cases hx : IsUni k x
    simp [e, hx, isUni_mul hx hv, hχmul hx hv, mul_comm, mul_left_comm]
    simp [e, hx, show ¬IsUni k (x * v) from fun h => hx $ by simpa using isUni_mul h $ hUinv hv]
  let P : Module.End ℂ V := ∑ g, e g • π g
  have hmul (a b : Gl k F → ℂ) : (∑ x, a x • π x) * (∑ y, b y • π y) = ∑ z, (∑ x, a x * b (x⁻¹ * z)) • π z := by
    simp only [sum_mul, mul_sum, sum_smul, smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, ← map_mul]
    rw [sum_comm]
    conv_rhs => rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_equiv (mulLeft x) _ _ fun _ => by simp [mul_comm]
  have hPP : P * P = P := by
    rw [hmul]
    refine sum_congr rfl fun z _ => congrArg (· • π z) ?_
    rw [sum_congr rfl fun x _ => show e x * e (x⁻¹ * z) = if IsUni k x then nU⁻¹ * e z else 0 by
        by_cases hx : IsUni k x
        have h := heL hx $ x⁻¹ * z
        rw [mul_inv_cancel_left] at h
        rw [show e x = nU⁻¹ * (χ x)⁻¹ by simp [e, hx], mul_assoc, ← h, ite_eq_left hx]
        simp [e, hx],
      ← sum_filter, sum_const, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hnU, one_mul]
  have hσσ (x : Gl k F) : flipG (flipG x) = x := Units.ext $ by ext; simp [flipG, flipM]
  have hcomm (g g' : Gl k F) : P * π g * P * (P * π g' * P) = P * π g' * P * (P * π g * P) := by
    let f (h z) := ∑ x, e (x * h⁻¹) * e (x⁻¹ * z)
    have hf h : P * π h * P = ∑ z, f h z • π z := by
      rw [← hmul]
      congr 1
      simp only [P, sum_mul, smul_mul_assoc, ← map_mul]
      exact sum_equiv (mulRight h) _ _ fun _ => by simp
    have hfL h {u} (hu : IsUni k u) z : f h (u * z) = (χ u)⁻¹ * f h z := by
      simp [f, mul_sum]; refine (sum_equiv (mulLeft u) _ _ fun x => ?_).symm
      rw [coe_mulLeft, show u * x * h⁻¹ = u * (x * h⁻¹) by group, show (u * x)⁻¹ * (u * z) = x⁻¹ * z by group, heL hu]; ring
    have hfR h {v} (hv : IsUni k v) z : f h (z * v) = (χ v)⁻¹ * f h z := by
      simp [f, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [← mul_assoc, heR hv]
      ring
    have hfFlip h : ∀ z, f h (flipG z) = f h z := hecke_flip_inv ψ₀ hψ (f h) fun u v z hu hv => by rw [hfR h hv, hfL h hu]
                                                                                                   ring
    rw [hf g, hf g', hmul, hmul]
    refine sum_congr rfl fun z _ => congrArg (· • π z) ?_
    rw [← hecke_flip_inv ψ₀ hψ (fun z => ∑ x, f g x * f g' (x⁻¹ * z)) (fun u v z hu hv => by
      simp [mul_sum]; refine (sum_equiv (mulLeft u) _ _ fun x => ?_).symm
      rw [coe_mulLeft, show (u * x)⁻¹ * (u * z * v) = x⁻¹ * z * v by group, hfL g hu, hfR g' hv]; ring) z]
    refine (sum_equiv (((Equiv.inv $ Gl k F).trans $ mulRight z).trans ⟨flipG, flipG, hσσ, hσσ⟩) _ _ fun w => ?_).symm
    change f g' w * f g (w⁻¹ * z) = f g (flipG $ w⁻¹ * z) * f g' ((flipG $ w⁻¹ * z)⁻¹ * flipG z)
    rw [hfFlip, show (flipG $ w⁻¹ * z)⁻¹ * flipG z = flipG w from inv_mul_eq_iff_eq_mul.mpr $ by rw [← flipG_mul, mul_inv_cancel_left], hfFlip, mul_comm]
  let W := range P
  have hPfix w (hw : w ∈ W) : P w = w := by rcases hw with ⟨v, rfl⟩
                                            exact congr_fun hPP v
  have cyc (w : V) (hw : w ≠ 0) (S : Submodule ℂ V) (hf : ∀ g, P (π g w) ∈ S) v : P v ∈ S := by
    let M := span ℂ $ Set.range fun g => π g w
    have hM : M = ⊤ := congrArg Subrepresentation.toSubmodule $
      (IsSimpleOrder.eq_bot_or_eq_top (⟨M, fun g x hx =>
        (span_le.mpr $ by rintro _ ⟨g', rfl⟩; exact subset_span ⟨g * g', by simp⟩ : M ≤ M.comap (π g)) hx⟩ :
        Subrepresentation π)).resolve_left fun h =>
        hw $ (mem_bot ℂ).mp $ (show M = ⊥ from congrArg Subrepresentation.toSubmodule h) ▸ subset_span ⟨1, by simp⟩
    exact (hM ▸ span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hf g) : (⊤ : Submodule ℂ V) ≤ S.comap P) mem_top
  have hℓP (ℓ : Module.Dual ℂ V) (hℓ : IsWhit ψ₀ π ℓ) v : ℓ (P v) = ℓ v := by
    simp only [P, e, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul, ite_mul, zero_mul, ← sum_filter]
    rw [sum_congr rfl fun x hx => by rw [hℓ x (mem_filter.mp hx).2, ← mul_assoc, mul_assoc nU⁻¹, inv_mul_cancel₀ $ hχne x, mul_one],
      sum_const, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hnU, one_mul]
  obtain ⟨v₀, hv₀⟩ : ∃ v, ℓ₁ (P v) ≠ 0 := by
    by_contra h
    push Not at h; exact hne $ LinearMap.ext fun v => by rw [← hℓP ℓ₁ h1 v]
                                                         exact h v
  let w₀ := P v₀
  have hw₀_ne : w₀ ≠ 0 := fun h0 => hv₀ $ by simp [show P v₀ = 0 from h0]
  have hscal h : ∃ μ : ℂ, ∀ x ∈ W, (P * π h * P) x = μ • x := by
    have : Nontrivial W := ⟨⟨⟨w₀, v₀, rfl⟩, 0, fun h => hw₀_ne $ congrArg Subtype.val h⟩⟩
    obtain ⟨μ, hμ⟩ := exists_eigenvalue $ (P * π h * P).restrict (p := W) fun x _ => ⟨(π h * P) x, rfl⟩
    obtain ⟨w, hwv⟩ := hμ.exists_hasEigenvector
    have hw2 : (P * π h * P) w = μ • w := congrArg Subtype.val hwv.apply_eq_smul
    exact ⟨μ, fun x hx => by have := mem_eigenspace_iff.mp $ (cyc w (fun h0 => hwv.2 $ Subtype.ext h0) ((P * π h * P).eigenspace μ) fun g => by rw [mem_eigenspace_iff, show P (π g w) = (P * π g * P) w by simp [hPfix _ w.2], ← Module.End.mul_apply, hcomm h g, Module.End.mul_apply, hw2, map_smul]) x
                             rwa [hPfix x hx] at this⟩
  have key := cyc w₀ hw₀_ne (ℂ ∙ w₀) fun g => by
    obtain ⟨μ, hμ⟩ := hscal g
    rw [show P (π g w₀) = (P * π g * P) w₀ by simp [hPfix w₀ ⟨v₀, rfl⟩], hμ w₀ ⟨v₀, rfl⟩]
    exact smul_mem _ _ $ mem_span_singleton_self _
  refine ⟨ℓ₂ w₀ / ℓ₁ w₀, LinearMap.ext fun v => ?_⟩
  obtain ⟨t, ht⟩ := mem_span_singleton.mp $ key v
  rw [LinearMap.smul_apply, ← hℓP ℓ₂ h2 v, ← hℓP ℓ₁ h1 v, ← ht]
  simp
  field_simp [show ℓ₁ w₀ ≠ 0 from hv₀]

end

end AlpogeRHCore9
