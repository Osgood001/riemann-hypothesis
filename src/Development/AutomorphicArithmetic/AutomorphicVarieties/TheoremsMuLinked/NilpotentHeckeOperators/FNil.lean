module

public import Mathlib

@[expose] public section

namespace UpperTheory.V.Th

/-- One-place factor of the discriminant used for the Hecke relations. -/
def heckeDiscriminant {S : Type*} [CommRing S] {n : ℕ} (q : S) (U : Fin n → S) : S :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, (U i - U j) * (U i - q * U j)

variable {S : Type*} [CommRing S] {n : ℕ} {q a : S} {U : Fin n → S} {i j : Fin n} {r s : ℕ}

private theorem sub_pow_zero {x y c a : S} (hx : (x - c * a) ^ r = 0)
    (hy : (y - a) ^ s = 0) : (x - c * y) ^ (r + s - 1) = 0 := by
  have hneg : (-c * (y - a)) ^ s = 0 := by rw [mul_pow, hy, mul_zero]
  rw [show x - c * y = (x - c * a) + (-c * (y - a)) by ring]
  exact (Commute.all _ _).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero hx hneg (by omega)

private theorem factor_dvd_row (hij : i ≠ j) :
    (U i - U j) * (U i - q * U j) ∣ ∏ k ∈ Finset.univ.erase i, (U i - U k) * (U i - q * U k) :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩)

/-- A collision after multiplication by q requires nilpotence at just the two colliding roots. -/
theorem heckeDiscriminant_pow_of_shift (hij : i ≠ j) (hi : (U i - q * a) ^ r = 0)
    (hj : (U j - a) ^ s = 0) : heckeDiscriminant q U ^ (r + s - 1) = 0 := by
  have hd : U i - q * U j ∣ heckeDiscriminant q U :=
    ((dvd_mul_left _ _).trans (factor_dvd_row hij)).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact zero_dvd_iff.mp (sub_pow_zero hi hj ▸ pow_dvd_pow_of_dvd hd (r + s - 1))

/-- When the roots themselves coincide, the ordered product contains the difference twice. -/
theorem heckeDiscriminant_pow_of_eq (hij : i ≠ j) (hi : (U i - a) ^ r = 0)
    (hj : (U j - a) ^ s = 0) : heckeDiscriminant q U ^ ((r + s) / 2) = 0 := by
  let row := fun i => ∏ k ∈ Finset.univ.erase i, (U i - U k) * (U i - q * U k)
  have h1 : U i - U j ∣ row i := (dvd_mul_right _ _).trans (factor_dvd_row hij)
  have h2 : U i - U j ∣ row j := by
    rw [← neg_sub (U j) (U i), neg_dvd]
    exact (dvd_mul_right _ _).trans (factor_dvd_row hij.symm)
  have hd : (U i - U j) ^ 2 ∣ heckeDiscriminant q U := by
    refine (show (U i - U j) ^ 2 ∣ row i * row j by simpa [pow_two] using mul_dvd_mul h1 h2).trans ?_
    simpa [row, heckeDiscriminant, hij] using
      Finset.prod_dvd_prod_of_subset {i,j} Finset.univ row (Finset.subset_univ _)
  have hz : (U i - U j) ^ (r + s - 1) = 0 := by
    simpa using sub_pow_zero (c := 1) (a := a) (by simpa using hi) hj
  have hzero : ((U i - U j) ^ 2) ^ ((r + s) / 2) = 0 := by
    rw [← pow_mul]
    exact pow_eq_zero_of_le (by omega) hz
  exact zero_dvd_iff.mp (hzero ▸ pow_dvd_pow_of_dvd hd ((r + s) / 2))

-- The ideal of deviations of a finite cluster has a quantified nilpotence order.
private theorem sum_ideals_pow {S ι : Type*} [CommRing S] (s : Finset ι)
    (J : ι → Ideal S) (r : ι → ℕ) (h : ∀ i ∈ s, J i ^ (r i + 1) = 0) :
    (∑ i ∈ s, J i) ^ ((∑ i ∈ s, r i) + 1) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    apply (Commute.all _ _).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
      (h i (Finset.mem_insert_self ..)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    omega

/-- In a collision cluster, every ordered pair contributes one factor in the
ideal of deviations. Count those factors against the nilpotence order of that ideal. -/
theorem heckeDiscriminant_pow_of_cluster {m k : ℕ} (e : Fin m ↪ Fin n) (r : Fin m → ℕ)
    (hnil : ∀ i, (U (e i) - a) ^ (r i + 1) = 0)
    (horder : (∑ i, r i) < m * (m - 1) * k) : heckeDiscriminant q U ^ k = 0 := by
  classical
  let I := fun i => Ideal.span ({U (e i) - a} : Set S)
  let J := ∑ i, I i
  have hJ : J ^ ((∑ i, r i) + 1) = 0 := by
    apply sum_ideals_pow
    intro i _
    simp [I, Ideal.span_singleton_pow, hnil]
  have mem (i : Fin m) : U (e i) - a ∈ J := by
    have le : I i ≤ J := by
      change I i ≤ ∑ j, I j
      exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
    exact le (Ideal.subset_span (Set.mem_singleton _))
  let A := fun i j => (U i - U j) * (U i - q * U j)
  let row := fun i => ∏ j ∈ Finset.univ.erase i, A i j
  have hrow (i : Fin m) : row (e i) ∈ J ^ (m - 1) := by
    let t := (Finset.univ.erase i).map e
    have hprod : (∏ j ∈ t, A (e i) j) ∈ ∏ _j ∈ t, J := by
      apply Ideal.prod_mem_prod
      intro j hj
      obtain ⟨l, _, rfl⟩ := Finset.mem_map.mp hj
      apply J.mul_mem_right
      simpa only [sub_sub_sub_cancel_right] using J.sub_mem (mem i) (mem l)
    have hs : t ⊆ Finset.univ.erase (e i) := by
      rintro j hj
      obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hj
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hl).1 (e.injective h), Finset.mem_univ _⟩
    apply (J ^ (m - 1)).mem_of_dvd (Finset.prod_dvd_prod_of_subset _ _ (A (e i)) hs)
    simpa [t, Finset.card_erase_of_mem] using hprod
  have hprod := Ideal.prod_mem_prod (s := Finset.univ) (I := fun _ : Fin m => J ^ (m-1))
    (x := fun i => row (e i)) (fun i _ => hrow i)
  have hd : (∏ i : Fin m, row (e i)) ∣ heckeDiscriminant q U := by
    rw [← Finset.prod_map]
    exact Finset.prod_dvd_prod_of_subset _ _ row (Finset.subset_univ _)
  have hm : heckeDiscriminant q U ∈ J ^ (m * (m-1)) := by
    apply (J ^ (m * (m-1))).mem_of_dvd hd
    simpa [← pow_mul, Nat.mul_comm] using hprod
  have hk := Ideal.pow_mem_pow hm k
  rw [← pow_mul] at hk
  simpa [hJ] using (Ideal.pow_le_pow_right (Nat.succ_le_of_lt horder)) hk

/-- A cluster larger than the common nilpotence order already kills the discriminant. -/
theorem heckeDiscriminant_eq_zero_of_cluster {m N : ℕ} (e : Fin m ↪ Fin n)
    (hm : N < m) (hU : ∀ i, (U (e i) - a) ^ N = 0) :
    heckeDiscriminant q U = 0 := by
  cases N with
  | zero =>
    have h : (1 : S) = 0 := by simpa using hU ⟨0, hm⟩
    exact (subsingleton_of_zero_eq_one h.symm).elim _ _
  | succ N =>
    have hlt : m * N < m * (m - 1) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    simpa using heckeDiscriminant_pow_of_cluster (q := q) (k := 1) e (fun _ => N) hU (by simpa using hlt)

/-- Uniform discriminant bound when either an equal or a shifted pair collides. -/
theorem fNil_order :
    ∀ (K S : Type) [CommRing K] [IsDomain K] [CommRing S] (f : K →+* S) (n N q : ℕ) (α : Fin n → K) (U : Fin n → S), (∀ k, (U k - f (α k)) ^ N = 0) → ¬ (∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (q : K) * α i') → (∏ i : Fin n, ∏ i' ∈ Finset.univ.erase i, (U i - U i') * (U i - (q : S) * U i')) ^ (2 * N - 1) = 0 := by
  intro K S _ _ _ f n N q α U hU hne
  simp only [not_forall] at hne
  obtain ⟨i, j, hij, hα⟩ := hne
  change heckeDiscriminant (q : S) U ^ (2 * N - 1) = 0
  by_cases h : α i = α j
  · have hi := hU i
    rw [h] at hi
    exact pow_eq_zero_of_le (by omega) (heckeDiscriminant_pow_of_eq hij hi (hU j))
  · have e : α i = (q : K) * α j := not_not.mp fun h' => hα ⟨h, h'⟩
    have hi := hU i
    rw [e, map_mul, map_natCast] at hi
    simpa [two_mul] using heckeDiscriminant_pow_of_shift hij hi (hU j)

theorem fNil :
    ∀ (K S : Type) [CommRing K] [IsDomain K] [CommRing S] (f : K →+* S) (n N q : ℕ) (α : Fin n → K) (U : Fin n → S), (∀ k, (U k - f (α k)) ^ N = 0) → ¬ (∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (q : K) * α i') → (∏ i : Fin n, ∏ i' ∈ Finset.univ.erase i, (U i - U i') * (U i - (q : S) * U i')) ^ (2 * N) = 0 := by
  intro K S _ _ _ f n N q α U hU hne
  exact pow_eq_zero_of_le (Nat.sub_le _ _) (fNil_order K S f n N q α U hU hne)

end UpperTheory.V.Th
