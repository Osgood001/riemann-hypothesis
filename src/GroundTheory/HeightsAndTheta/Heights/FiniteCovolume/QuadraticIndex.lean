module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

open AddSubgroup

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

/-- The integer span of 1 and a complex generator. -/
def quadraticSpan (v : ℂ) : AddSubgroup ℂ := zmultiples 1 ⊔ zmultiples v

theorem mem_quadraticSpan {z v : ℂ} :
    z ∈ quadraticSpan v ↔ ∃ a b : ℤ, z = (a : ℂ) + b * v := by
  constructor
  · intro hz
    obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, rfl⟩ := AddSubgroup.mem_sup.1 hz
    exact ⟨a, b, by simp [zsmul_eq_mul]⟩
  · rintro ⟨a, b, rfl⟩
    apply AddSubgroup.add_mem_sup
    · exact ⟨a, by simp [zsmul_eq_mul]⟩
    · exact ⟨b, by simp [zsmul_eq_mul]⟩

theorem quadraticSpan_index {ω v : ℂ} {n : ℕ} {a : ℤ} (hω : ω.im ≠ 0)
    (hv : (n : ℂ) * v = ω - a) :
    quadraticSpan ω ≤ quadraticSpan v ∧ (quadraticSpan ω).relIndex (quadraticSpan v) = n := by
  have hvω : ω = (a : ℂ) + n * v := by rw [hv]; ring
  have hvim : v.im ≠ 0 := by
    intro h
    apply hω
    simp [hvω, Complex.mul_im, h]
  have hle : quadraticSpan ω ≤ quadraticSpan v :=
    sup_le le_sup_left (zmultiples_le.mpr (mem_quadraticSpan.2 ⟨a, n, by simpa using hvω⟩))
  refine ⟨hle, ?_⟩
  have hsup : quadraticSpan v = (quadraticSpan ω) ⊔ zmultiples v :=
    le_antisymm (sup_le (le_trans le_sup_left le_sup_left) le_sup_right) (sup_le hle le_sup_right)
  rw [hsup, relIndex_sup_left, ← range_zmultiplesHom, ← index_comap]
  have hker : (quadraticSpan ω).comap (zmultiplesHom ℂ v) = zmultiples (n : ℤ) := by
    ext k
    change k • v ∈ quadraticSpan ω ↔ _
    rw [mem_quadraticSpan, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨s, t, he⟩
      have him := congrArg Complex.im he
      simp [hvω, zsmul_eq_mul, Complex.mul_im] at him
      refine ⟨t, ?_⟩
      exact_mod_cast (mul_right_cancel₀ hvim (show (k : ℝ) * v.im = ((n : ℝ) * t) * v.im by
        linear_combination him))
    · rintro ⟨t, rfl⟩
      refine ⟨-t * a, t, ?_⟩
      push_cast
      rw [zsmul_eq_mul, hvω]
      push_cast
      ring
  rw [hker, Int.index_zmultiples]
  simp

/-- A coordinate-wise minimum estimate makes 1 a shortest vector of the overgroup. -/
theorem one_shortest_quadraticSpan {v : ℂ}
    (h : ∀ i j : ℤ, i ≠ 0 ∨ j ≠ 0 → 1 ≤ ‖(i : ℂ) + j * v‖) :
    (1 : ℂ) ∈ quadraticSpan v ∧ ∀ z ∈ quadraticSpan v, z ≠ 0 → 1 ≤ ‖z‖ := by
  refine ⟨mem_quadraticSpan.2 ⟨1, 0, by simp⟩, ?_⟩
  intro z hz hz0
  obtain ⟨i, j, rfl⟩ := mem_quadraticSpan.1 hz
  apply h
  contrapose! hz0
  simp [hz0.1, hz0.2]

end GroundTheory.Heights₂.Heights.FiniteCovolume

namespace QuadraticOverlattice

private theorem horizontal {L : AddSubgroup ℂ} (h1 : (1 : ℂ) ∈ L)
    (hs : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) {z : ℂ} (hz : z ∈ L) (him : z.im = 0) :
    ∃ a : ℤ, z = (a : ℂ) := by
  let a := round z.re
  refine ⟨a, ?_⟩
  have ha : (a : ℂ) ∈ L := by simpa using L.zsmul_mem h1 a
  have he : z - (a : ℂ) = ((z.re - (a : ℝ) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  by_contra h
  have hlo := hs _ (L.sub_mem hz ha) (sub_ne_zero.mpr h)
  rw [he, Complex.norm_real, Real.norm_eq_abs] at hlo
  linarith [abs_sub_round z.re]

private theorem integral_multiple {L : AddSubgroup ℂ} (h1 : (1 : ℂ) ∈ L)
    (hs : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) {n : ℕ} (hn : 0 < n)
    {z : ℂ} (hz : z ∈ L) {b : ℤ} (h : (n : ℂ) * z = b) : ∃ a : ℤ, z = (a : ℂ) := by
  apply horizontal h1 hs hz
  have hi := congrArg Complex.im h
  simp [Complex.mul_im] at hi
  rcases hi with h | h
  · exact False.elim (hn.ne' h)
  · exact h

/-- In an overlattice containing a shortest unit, the vertical coordinate modulo the index
already separates the cosets of the quadratic order. -/
private theorem exists_generator {L : AddSubgroup ℂ} (B : AddSubgroup L) {ω : ℂ} {n : ℕ}
    (hn : 0 < n) (hi : B.index = n) (h1 : (1 : ℂ) ∈ L) (hw : ω ∈ L)
    (hB : ∀ x : L, x ∈ B ↔ ∃ a b : ℤ, (x : ℂ) = (a : ℂ) + b * ω)
    (hs : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) :
    ∃ a : ℤ, (ω - (a : ℂ)) / n ∈ L ∧
      ∀ x ∈ L, ∃ c d : ℤ, x = (c : ℂ) + d * ((ω - (a : ℂ)) / n) := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have coords (x : L) : ∃ a b : ℤ, (n : ℂ) * x = (a : ℂ) + b * ω := by
    simpa [← hi, nsmul_eq_mul] using (hB (B.index • x)).mp (B.nsmul_index_mem x)
  choose A D hd using coords
  let Q := L ⧸ B
  let f (q : Q) : ZMod n := D q.out
  have hinj : Function.Injective f := by
    intro x y hxy
    let X := x.out
    let Y := y.out
    have hmod : ((D X - D Y : ℤ) : ZMod n) = 0 := by simpa [f, X, Y] using sub_eq_zero.mpr hxy
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
    have he : (D X : ℂ) - D Y = (n : ℂ) * t := by exact_mod_cast ht
    have hw' : (t : ℂ) * ω ∈ L := by simpa [zsmul_eq_mul] using L.zsmul_mem hw t
    have hscale : (n : ℂ) * ((X : ℂ) - Y - t * ω) = ((A X - A Y : ℤ) : ℂ) := by
      push_cast
      linear_combination hd X - hd Y + ω * he
    obtain ⟨u, hu⟩ := integral_multiple h1 hs hn (L.sub_mem (L.sub_mem X.2 Y.2) hw') hscale
    have hB' : X - Y ∈ B := (hB _).2 ⟨u, t, by
      change (X : ℂ) - Y = (u : ℂ) + t * ω
      linear_combination hu⟩
    exact x.out_eq.symm.trans ((QuotientAddGroup.eq_iff_sub_mem.mpr hB').trans y.out_eq)
  have hc : Nat.card Q = Nat.card (ZMod n) := by rw [Nat.card_zmod, ← hi, B.index_eq_card]
  obtain ⟨q, hq⟩ := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hc⟩).surjective 1
  let X := q.out
  have hmod : ((D X - 1 : ℤ) : ZMod n) = 0 := by simpa [X, f] using sub_eq_zero.mpr hq
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
  have he : (D X : ℂ) - 1 = (n : ℂ) * t := by exact_mod_cast ht
  let v := (ω - ((-A X : ℤ) : ℂ)) / n
  have hv : (n : ℂ) * v = (A X : ℂ) + ω := by dsimp [v]; push_cast; field_simp; ring
  have hv' : v = (X : ℂ) - t * ω := by
    apply mul_left_cancel₀ hnC
    linear_combination hv - hd X - ω * he
  have hL : v ∈ L := hv' ▸ L.sub_mem X.2 (by simpa [zsmul_eq_mul] using L.zsmul_mem hw t)
  refine ⟨-A X, hL, ?_⟩
  intro x hx
  let Y : L := ⟨x, hx⟩
  have hz : (n : ℂ) * (x - D Y * v) = ((A Y - D Y * A X : ℤ) : ℂ) := by
    change (n : ℂ) * ((Y : ℂ) - D Y * v) = _
    push_cast
    linear_combination hd Y - (D Y : ℂ) * hv
  have hy : (D Y : ℂ) * v ∈ L := by simpa [zsmul_eq_mul] using L.zsmul_mem hL (D Y)
  obtain ⟨c, h⟩ := integral_multiple h1 hs hn (L.sub_mem hx hy) hz
  exact ⟨c, D Y, sub_eq_iff_eq_add.mp h⟩

end QuadraticOverlattice

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

/-- A finite-index overgroup with shortest unit is generated by one divided translate. -/
theorem quadraticSpan_overgroup_normalForm {ω : ℂ} {L : AddSubgroup ℂ} {n : ℕ}
    (hL : quadraticSpan ω ≤ L) (hn : 0 < n) (hi : (quadraticSpan ω).relIndex L = n)
    (hs : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) :
    ∃ a : ℤ, L = quadraticSpan ((ω - (a : ℂ)) / n) := by
  have h1 : (1 : ℂ) ∈ L := hL <| mem_quadraticSpan.mpr ⟨1, 0, by simp⟩
  have hw : ω ∈ L := hL <| mem_quadraticSpan.mpr ⟨0, 1, by simp⟩
  obtain ⟨a, hv, h⟩ := QuadraticOverlattice.exists_generator ((quadraticSpan ω).addSubgroupOf L)
    hn hi h1 hw (fun _ => mem_quadraticSpan) hs
  refine ⟨a, le_antisymm (fun x hx => mem_quadraticSpan.mpr (h x hx)) ?_⟩
  intro x hx
  obtain ⟨c, d, rfl⟩ := mem_quadraticSpan.mp hx
  exact L.add_mem (by simpa using L.zsmul_mem h1 c) (by simpa [zsmul_eq_mul] using L.zsmul_mem hv d)

end GroundTheory.Heights₂.Heights.FiniteCovolume

namespace QuadraticIndex

/-- Clearing the denominator of the quadratic integer basis identifies its integral binary
quadratic form with the squared Euclidean length of exactly the same vector. -/
theorem form_iff_norm {n d t a : ℤ} {v : ℂ} (hn : 0 < n)
    (hre : 2 * (n : ℝ) * v.re = (t : ℝ) - 2 * (a : ℝ))
    (him : (2 * (n : ℝ) * v.im) ^ 2 = (d : ℝ)) (x y : ℤ) :
    4 * n ^ 2 ≤ (2 * (n * x) + (t - 2 * a) * y) ^ 2 + d * y ^ 2 ↔
      1 ≤ ‖(x : ℂ) + y • v‖ := by
  let z := (x : ℂ) + y • v
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hzr : z.re = (x : ℝ) + (y : ℝ) * v.re := by simp [z]
  have hzi : z.im = (y : ℝ) * v.im := by simp [z]
  have hr : 2 * ((n : ℝ) * x) + ((t : ℝ) - 2 * a) * y = 2 * n * z.re := by
    rw [hzr, ← hre]
    ring
  have he : (2 * ((n : ℝ) * x) + ((t : ℝ) - 2 * a) * y) ^ 2 + d * (y : ℝ) ^ 2 =
      (2 * (n : ℝ)) ^ 2 * ‖z‖ ^ 2 := by
    rw [hr, ← him, hz, hzi]
    ring
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : 0 < (2 * (n : ℝ)) ^ 2 := by positivity
  have hi : 4 * n ^ 2 ≤ (2 * (n * x) + (t - 2 * a) * y) ^ 2 + d * y ^ 2 ↔
      (2 * (n : ℝ)) ^ 2 * 1 ≤ (2 * (n : ℝ)) ^ 2 * ‖z‖ ^ 2 := by
    rw [← he, mul_one, show (2 * (n : ℝ)) ^ 2 = 4 * n ^ 2 by ring]
    norm_cast
  rw [hi, mul_le_mul_iff_right₀ hp]
  change 1 ≤ ‖z‖ ^ 2 ↔ 1 ≤ ‖z‖
  constructor
  · intro hh
    by_contra! hlt
    have hs := sq_lt_sq' (by linarith [norm_nonneg z] : -(1 : ℝ) < ‖z‖) hlt
    linarith
  · intro hh
    have hs := sq_le_sq' (by linarith [norm_nonneg z] : -‖z‖ ≤ (1 : ℝ)) hh
    linarith

/-- Choose the nearest horizontal translate. Its doubled coordinate has the parity of
the trace, so an endpoint of the centered interval is impossible in the opposite parity. -/
private theorem centered_index_bound {n d t a : ℤ} (hn : 0 < n)
    (hmin : ∀ k : ℤ, 4 * n ^ 2 ≤ (t - 2 * a + 2 * (n * k)) ^ 2 + d) :
    3 * n ^ 2 + (if t % 2 = n % 2 then 0 else 2 * n - 1) ≤ d := by
  let u := t - 2 * a + n
  let k := -(u / (2 * n))
  let r := t - 2 * a + 2 * (n * k)
  have hmod : r + n = u % (2 * n) := by
    rw [Int.emod_def]
    dsimp [r, k, u]
    ring
  have hl : -n ≤ r := by have := Int.emod_nonneg u (by omega : 2 * n ≠ 0); omega
  have hu : r < n := by have := Int.emod_lt_of_pos u (by omega : 0 < 2 * n); omega
  have h := hmin k
  change 4 * n ^ 2 ≤ r ^ 2 + d at h
  split
  · have hs := sq_le_sq' hl hu.le
    linarith
  · rename_i hne
    have hr : r % 2 = t % 2 := by dsimp [r]; omega
    have hl' : -(n - 1) ≤ r := by omega
    have hu' : r ≤ n - 1 := by omega
    have hs := sq_le_sq' hl' hu'
    nlinarith

/-- The lower bound on lengths in an actual complex overgroup supplies the normalized
integer inequalities, by testing all horizontal translates of one period. -/
theorem translate_norms {L : AddSubgroup ℂ} {n d t a : ℤ} {v : ℂ}
    (hn : 0 < n) (hd : 0 < d) (h1 : (1 : ℂ) ∈ L) (hv : v ∈ L)
    (hmin : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖)
    (hre : 2 * (n : ℝ) * v.re = (t : ℝ) - 2 * (a : ℝ))
    (him : (2 * (n : ℝ) * v.im) ^ 2 = (d : ℝ)) :
    ∀ k : ℤ, 4 * n ^ 2 ≤ (t - 2 * a + 2 * (n * k)) ^ 2 + d := by
  intro k
  let z := (k : ℂ) + (1 : ℤ) • v
  have hi : z.im = v.im := by simp [z]
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  have hz : z ≠ 0 := by
    intro h
    have hv0 : v.im = 0 := by simpa [h] using hi.symm
    rw [hv0] at him
    linarith
  have hk : (k : ℂ) ∈ L := by simpa using L.zsmul_mem h1 k
  have h := hmin z (L.add_mem hk (L.zsmul_mem hv 1)) hz
  simpa [add_comm] using (form_iff_norm hn hre him k 1).mpr h

/-- Once the first basis vector of a reduced integral binary form has value A,
no nonzero vector has smaller value. -/
theorem reduced_form_min {A B C : ℤ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ A)
    (hAC : A ≤ C) (x y : ℤ) (hne : x ≠ 0 ∨ y ≠ 0) :
    A ≤ A * x ^ 2 + B * (x * y) + C * y ^ 2 := by
  have one_le_sq (z : ℤ) (hz : z ≠ 0) : 1 ≤ z ^ 2 := Int.add_one_le_iff.mpr (sq_pos_of_ne_zero hz)
  have hcy := mul_nonneg (sub_nonneg.mpr hAC) (sq_nonneg y)
  by_cases hxy : 0 ≤ x * y
  · have hb := mul_nonneg hB hxy
    rcases hne with hx | hy
    · nlinarith [mul_nonneg hA (sub_nonneg.mpr (one_le_sq x hx)),
        mul_nonneg hA (sq_nonneg y)]
    · nlinarith [mul_nonneg hA (sub_nonneg.mpr (one_le_sq y hy)),
        mul_nonneg hA (sq_nonneg x)]
  · have hxy' : 0 ≤ -(x * y) - 1 := by omega
    nlinarith [mul_nonneg hA (sq_nonneg (x + y)),
      mul_nonneg (show 0 ≤ 2 * A - B by omega) hxy']

/-- Clearing denominators in the squared norm of x + yv gives the displayed form.
The nearest half-step allowed by parity is attained by this explicit shift. -/
theorem sharp_index_shift {n d t : ℤ} (hn : 0 < n)
    (hd : 3 * n ^ 2 + (if t % 2 = n % 2 then 0 else 2 * n - 1) ≤ d) :
    let b := if t % 2 = n % 2 then n else n - 1
    let a := (t - b) / 2
    t - 2 * a = b ∧ ∀ x y : ℤ, x ≠ 0 ∨ y ≠ 0 →
      4 * n ^ 2 ≤ (2 * (n * x) + (t - 2 * a) * y) ^ 2 + d * y ^ 2 := by
  dsimp only
  let b := if t % 2 = n % 2 then n else n - 1
  have h0 : 0 ≤ b := by dsimp [b]; split <;> omega
  have h1 : b ≤ n := by dsimp [b]; split <;> omega
  have hshift : t - 2 * ((t - b) / 2) = b := by dsimp [b]; split <;> omega
  refine ⟨hshift, fun x y hxy => ?_⟩
  change 4 * n ^ 2 ≤ (2 * (n * x) + (t - 2 * ((t - b) / 2)) * y) ^ 2 + d * y ^ 2
  rw [hshift]
  have hC : 4 * n ^ 2 ≤ b ^ 2 + d := by
    dsimp [b]; split <;> rename_i h <;> simp [h] at hd <;> nlinarith
  have h := reduced_form_min (A := 4 * n ^ 2) (B := 4 * n * b) (C := b ^ 2 + d)
    (by positivity) (by positivity) (by nlinarith [mul_nonneg hn.le (sub_nonneg.mpr h1)])
    hC x y hxy
  linarith only [h]

end QuadraticIndex

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open QuadraticIndex

private theorem im_ne_zero {ω : ℂ} {d : ℤ} (hd : 0 < d) (him : (2 * ω.im) ^ 2 = (d : ℝ)) :
    ω.im ≠ 0 := by
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  rintro h
  rw [h] at him
  linarith

/-- A quadratic lattice admits an overgroup of index n retaining 1 as a shortest vector
exactly when its discriminant clears the parity-corrected threshold. The trace t and
absolute discriminant d are the doubled real part and squared doubled imaginary part. -/
theorem exists_overgroup_index_iff {ω : ℂ} {n : ℕ} {t d : ℤ}
    (hn : 0 < n) (hd : 0 < d) (hre : 2 * ω.re = (t : ℝ))
    (him : (2 * ω.im) ^ 2 = (d : ℝ)) :
    (∃ L : AddSubgroup ℂ, quadraticSpan ω ≤ L ∧ (quadraticSpan ω).relIndex L = n ∧
      ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) ↔
    3 * (n : ℤ) ^ 2 + (if t % 2 = (n : ℤ) % 2 then 0 else 2 * (n : ℤ) - 1) ≤ d := by
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hni : 0 < (n : ℤ) := by exact_mod_cast hn
  have hω := im_ne_zero hd him
  have coords (a : ℤ) (v : ℂ) (hv : (n : ℂ) * v = ω - a) :
      2 * ((n : ℤ) : ℝ) * v.re = (t : ℝ) - 2 * (a : ℝ) ∧
      (2 * ((n : ℤ) : ℝ) * v.im) ^ 2 = (d : ℝ) := by
    have h₁ := congrArg Complex.re hv
    have h₂ := congrArg Complex.im hv
    simp [Complex.mul_re] at h₁
    simp [Complex.mul_im] at h₂
    push_cast
    exact ⟨by linarith only [h₁, hre],
      by rw [mul_assoc, h₂, him]⟩
  have hdiv (a : ℤ) : (n : ℂ) * ((ω - a) / n) = ω - a := by field_simp
  constructor
  · rintro ⟨L, hL, hidx, hmin⟩
    obtain ⟨a, heq⟩ := quadraticSpan_overgroup_normalForm hL hn hidx hmin
    let v : ℂ := (ω - a) / n
    obtain ⟨hr, hi⟩ := coords a v (hdiv a)
    have h1 : (1 : ℂ) ∈ L := hL (mem_quadraticSpan.2 ⟨1, 0, by simp⟩)
    have hv : v ∈ L := heq ▸ mem_quadraticSpan.2 ⟨0, 1, by simp [v]⟩
    exact centered_index_bound hni (translate_norms hni hd h1 hv hmin hr hi)
  · intro hbound
    let a := (t - (if t % 2 = (n : ℤ) % 2 then (n : ℤ) else (n : ℤ) - 1)) / 2
    have ha := (sharp_index_shift hni hbound).2
    let v : ℂ := (ω - a) / n
    obtain ⟨hle, hidx⟩ := quadraticSpan_index hω (hdiv a)
    obtain ⟨hr, hi⟩ := coords a v (hdiv a)
    refine ⟨quadraticSpan v, hle, hidx, (one_shortest_quadraticSpan ?_).2⟩
    intro x y hxy
    simpa only [zsmul_eq_mul] using (form_iff_norm hni hr hi x y).mp (ha x y hxy)

end GroundTheory.Heights₂.Heights.FiniteCovolume

namespace QuadraticIndex

/-- Exact maximum: test the integer square-root candidate once. -/
def maximum (d : ℕ) (t : ℤ) : ℕ :=
  let k := (d / 3).sqrt
  if 3 * (k : ℤ) ^ 2 + (if t % 2 = (k : ℤ) % 2 then 0 else 2 * (k : ℤ) - 1) ≤ d
    then k else k - 1

/-- Every positive index up to the returned maximum is feasible; there are no gaps. -/
theorem threshold_iff_le_maximum {n d : ℕ} {t : ℤ} (hn : 0 < n) :
    3 * (n : ℤ) ^ 2 + (if t % 2 = (n : ℤ) % 2 then 0 else 2 * (n : ℤ) - 1) ≤ d ↔
      n ≤ maximum d t := by
  let k := (d / 3).sqrt
  have hbase : 3 * (k : ℤ) ^ 2 ≤ (d : ℤ) := by
    have h := (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mp (Nat.sqrt_le' (d / 3))
    exact_mod_cast (by simpa [mul_comm, k] using h : 3 * k ^ 2 ≤ d)
  have hnext : (d : ℤ) < 3 * ((k : ℤ) + 1) ^ 2 := by
    have h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mp (Nat.lt_succ_sqrt' (d / 3))
    exact_mod_cast (by simpa [mul_comm, Nat.succ_eq_add_one, k] using h : d < 3 * (k+1) ^ 2)
  let p (m : ℕ) := 3 * (m : ℤ) ^ 2 + (if t % 2 = (m : ℤ) % 2 then 0 else 2 * (m : ℤ) - 1) ≤ d
  change p n ↔ n ≤ (if p k then k else k - 1)
  by_cases heq : n = k
  · subst n
    by_cases hk : p k
    · simp [hk]
    · simp [hk]; omega
  by_cases hlt : n < k
  · have hn' : ((n : ℤ) + 1) ≤ k := by exact_mod_cast hlt
    have hs := sq_le_sq' (by omega : -(k : ℤ) ≤ (n : ℤ) + 1) hn'
    constructor
    · intro _
      by_cases hk : p k <;> simp [hk] <;> omega
    · intro _
      dsimp [p]
      split <;> nlinarith
  · have hk' : ((k : ℤ) + 1) ≤ n := by omega
    have hs := sq_le_sq' (by omega : -(n : ℤ) ≤ (k : ℤ) + 1) hk'
    constructor
    · intro h
      exfalso
      dsimp [p] at h
      split at h <;> nlinarith
    · by_cases hk : p k <;> simp [hk] <;> omega

end QuadraticIndex

open Submodule

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

/-- In the nondegenerate plane, the shortest-vector condition excludes infinite index. -/
theorem quadraticSpan_index_pos {ω : ℂ} {L : AddSubgroup ℂ} (hω : ω.im ≠ 0)
    (hle : quadraticSpan ω ≤ L) (hmin : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) :
    0 < (quadraticSpan ω).relIndex L := by
  let A := L.toIntSubmodule
  let B := (quadraticSpan ω).toIntSubmodule
  have hBA : B ≤ A := hle
  have : DiscreteTopology A := DiscreteTopology.of_forall_le_norm (by norm_num : (0:ℝ)<1)
    fun x hx => hmin x x.2 (by simpa using hx)
  have : DiscreteTopology B := DiscreteTopology.of_forall_le_norm (by norm_num : (0:ℝ)<1)
    fun x hx => hmin x (hle x.2) (by simpa using hx)
  have hs : span ℝ (B : Set ℂ) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have h1 : (1 : ℂ) ∈ span ℝ (B : Set ℂ) :=
      subset_span (mem_quadraticSpan.mpr ⟨1, 0, by simp⟩)
    have hw : ω ∈ span ℝ (B : Set ℂ) :=
      subset_span (mem_quadraticSpan.mpr ⟨0, 1, by simp⟩)
    let s := z.im / ω.im
    let r := z.re - s * ω.re
    have he : z = r • (1 : ℂ) + s • ω := by
      apply Complex.ext
      · simp [r]
      · simp [s, div_mul_cancel₀ _ hω]
    rw [he]
    exact add_mem (smul_mem _ r h1) (smul_mem _ s hw)
  let : IsZLattice ℝ B := ⟨hs⟩
  let : IsZLattice ℝ A := ⟨top_le_iff.mp (hs ▸ span_mono (R := ℝ) (show (B : Set ℂ) ⊆ A from hBA))⟩
  have heq := ZLattice.covolume_div_covolume_eq_relIndex' B A hBA
  have hp := div_pos (ZLattice.covolume_pos B MeasureTheory.volume)
    (ZLattice.covolume_pos A MeasureTheory.volume)
  rw [heq] at hp
  exact_mod_cast hp

/-- The complete spectrum of indices is the initial interval from one to the computed
maximum. Index zero (Mathlib's infinite-index convention) cannot occur. -/
theorem exists_overgroup_index_le_maximum_iff {ω : ℂ} {n d : ℕ} {t : ℤ}
    (hd : 0 < d) (hre : 2 * ω.re = (t : ℝ)) (him : (2 * ω.im) ^ 2 = (d : ℝ)) :
    (∃ L : AddSubgroup ℂ, quadraticSpan ω ≤ L ∧ (quadraticSpan ω).relIndex L = n ∧
      ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) ↔ 0 < n ∧ n ≤ QuadraticIndex.maximum d t := by
  have hdi : 0 < (d : ℤ) := by exact_mod_cast hd
  have hi : (2 * ω.im) ^ 2 = ((d : ℤ) : ℝ) := by simpa using him
  constructor
  · rintro ⟨L, hL, hidx, hs⟩
    have hn : 0 < n := hidx ▸ quadraticSpan_index_pos (im_ne_zero hdi hi) hL hs
    exact ⟨hn, (QuadraticIndex.threshold_iff_le_maximum hn).mp
      ((exists_overgroup_index_iff hn hdi hre hi).mp ⟨L, hL, hidx, hs⟩)⟩
  · rintro ⟨hn, hmax⟩
    exact (exists_overgroup_index_iff hn hdi hre hi).mpr
      ((QuadraticIndex.threshold_iff_le_maximum hn).mpr hmax)

end GroundTheory.Heights₂.Heights.FiniteCovolume
