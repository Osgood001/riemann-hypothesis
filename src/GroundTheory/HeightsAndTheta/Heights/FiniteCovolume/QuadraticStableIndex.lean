module
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.QuadraticIndex

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

/-- The horizontal coordinate is unique once the second generator has nonzero imaginary part. -/
private theorem intCoordinates_unique {v : ℂ} (hv : v.im ≠ 0) {i j k l : ℤ}
    (h : (i : ℂ) + j * v = k + l * v) : i = k ∧ j = l := by
  have him := congrArg Complex.im h
  simp [Complex.mul_im] at him
  have hj : j = l := him.resolve_right hv
  subst l
  exact ⟨by exact_mod_cast add_right_cancel h, rfl⟩

/-- For an overgroup with basis `1,v`, stability under the quadratic generator
is equivalent to divisibility of the norm of the shift. -/
theorem quadraticSpan_mul_stable_iff {ω v : ℂ} {n : ℕ} {a t q : ℤ}
    (hn : 0 < n) (hω : ω.im ≠ 0) (hv : (n : ℂ) * v = ω - a)
    (hpoly : ω ^ 2 = (t : ℂ) * ω - q) :
    (∀ z ∈ quadraticSpan v, ω * z ∈ quadraticSpan v) ↔
      (n : ℤ) ∣ a ^ 2 - t * a + q := by
  let D := a ^ 2 - t * a + q
  have e : (n : ℂ) * (ω * v) = (-D : ℤ) + (((n : ℤ) * (t - a) : ℤ) : ℂ) * v := by
    dsimp [D]
    push_cast
    linear_combination (ω - t + a) * hv + hpoly
  have hvω : ω = (a : ℂ) + n * v := by rw [hv]; ring
  have hvim : v.im ≠ 0 := by
    intro h
    apply hω
    simp [hvω, Complex.mul_im, h]
  constructor
  · intro h
    have hvA : v ∈ quadraticSpan v := AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples v)
    obtain ⟨i, j, hij⟩ := mem_quadraticSpan.mp (h v hvA)
    have hcoord : (((n : ℤ) * i : ℤ) : ℂ) + (((n : ℤ) * j : ℤ) : ℂ) * v =
        (-D : ℤ) + (((n : ℤ) * (t - a) : ℤ) : ℂ) * v := by
      rw [← e, hij]
      push_cast
      ring
    have hfirst := (intCoordinates_unique hvim hcoord).1
    refine ⟨-i, ?_⟩
    change D = (n : ℤ) * -i
    linear_combination hfirst
  · rintro ⟨k, hk⟩ z hz
    have hωA : ω ∈ quadraticSpan v := mem_quadraticSpan.mpr ⟨a, n, by simpa using hvω⟩
    have hωv : ω * v ∈ quadraticSpan v := by
      refine mem_quadraticSpan.mpr ⟨-k, t - a, ?_⟩
      apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn.ne' : (n : ℂ) ≠ 0)
      rw [e, show D = (n : ℤ) * k from hk]
      push_cast
      ring
    obtain ⟨i, j, rfl⟩ := mem_quadraticSpan.mp hz
    have hh := (quadraticSpan v).add_mem ((quadraticSpan v).zsmul_mem hωA i)
      ((quadraticSpan v).zsmul_mem hωv j)
    convert hh using 1
    simp only [zsmul_eq_mul]
    ring

/-- Testing the quadratic generator suffices for stability under the whole order. -/
theorem quadraticSpan_order_stable_iff {w : ℂ} {L : AddSubgroup ℂ} :
    (∀ u ∈ quadraticSpan w, ∀ z ∈ L, u * z ∈ L) ↔ ∀ z ∈ L, w * z ∈ L := by
  constructor
  · exact fun h => h w (mem_quadraticSpan.mpr ⟨0, 1, by simp⟩)
  · intro h u hu z hz
    obtain ⟨i, j, rfl⟩ := mem_quadraticSpan.mp hu
    have hs := L.add_mem (L.zsmul_mem hz i) (L.zsmul_mem (h z hz) j)
    convert hs using 1
    simp only [zsmul_eq_mul]
    ring

/-- The norm congruence in the centered binary quadratic form coordinates. -/
theorem shift_norm_dvd_iff_discriminant (n a t q : ℤ) :
    n ∣ a ^ 2 - t * a + q ↔ 4 * n ∣ (t - 2 * a)^2 + (4 * q - t ^ 2) := by
  rw [show (t - 2 * a)^2 + (4 * q - t ^ 2) = 4 * (a^2 - t*a + q) by ring,
    mul_dvd_mul_iff_left (by decide : (4 : ℤ) ≠ 0)]

open QuadraticIndex

/-- Coordinates of the divided period. -/
private theorem dividedPeriod_coords {ω : ℂ} {n : ℕ} {t d : ℤ}
    (hn : 0 < n) (hre : 2 * ω.re = (t : ℝ)) (him : (2 * ω.im) ^ 2 = (d : ℝ)) (a : ℤ) :
    let v := (ω - a) / n
    (n : ℂ) * v = ω - a ∧
      2 * ((n : ℤ) : ℝ) * v.re = (t : ℝ) - 2 * (a : ℝ) ∧
      (2 * ((n : ℤ) : ℝ) * v.im) ^ 2 = (d : ℝ) := by
  let v := (ω - (a : ℂ)) / n
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hv : (n : ℂ) * v = ω - a := by dsimp [v]; field_simp
  refine ⟨hv, ?_⟩
  have hr := congrArg Complex.re hv
  have hi := congrArg Complex.im hv
  simp [Complex.mul_re] at hr
  simp [Complex.mul_im] at hi
  change 2 * ((n : ℤ) : ℝ) * v.re = _ ∧ (2 * ((n : ℤ) : ℝ) * v.im) ^ 2 = _
  push_cast
  exact ⟨by linarith only [hr, hre], by rw [mul_assoc, hi, him]⟩

/-- A stable shortest-unit overgroup yields a reduced integral form whose leading
coefficient is its actual index. The congruence is extra data beyond the additive bound. -/
theorem stable_overgroup_index_conditions {ω : ℂ} {L : AddSubgroup ℂ} {n : ℕ} {t d q : ℤ}
    (hn : 0 < n) (hd : 0 < d) (hre : 2 * ω.re = (t : ℝ))
    (him : (2 * ω.im) ^ 2 = (d : ℝ)) (hpoly : ω ^ 2 = (t : ℂ) * ω - (q : ℂ))
    (hdq : d = 4 * q - t ^ 2) (hle : quadraticSpan ω ≤ L) (hidx : (quadraticSpan ω).relIndex L = n)
    (hmin : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) (hstable : ∀ z ∈ L, ω * z ∈ L) :
    ∃ b : ℤ, |b| ≤ (n : ℤ) ∧ b % 2 = t % 2 ∧ 4 * (n : ℤ) ^ 2 ≤ b ^ 2 + d ∧
      (4 * (n : ℤ)) ∣ b ^ 2 + d := by
  obtain ⟨a, he⟩ := quadraticSpan_overgroup_normalForm hle hn hidx hmin
  let v : ℂ := (ω - a) / n
  obtain ⟨hv, hr, hi⟩ := dividedPeriod_coords hn hre him a
  have hω : ω.im ≠ 0 := by
    have h : 0 < (d : ℝ) := by exact_mod_cast hd
    intro hz; rw [hz] at him; linarith
  have hst : ∀ z ∈ quadraticSpan v, ω * z ∈ quadraticSpan v := he ▸ hstable
  have hdiv := (quadraticSpan_mul_stable_iff hn hω hv hpoly).mp hst
  have hdisc := (shift_norm_dvd_iff_discriminant (n : ℤ) a t q).mp hdiv
  rw [← hdq] at hdisc
  have hone : (1 : ℂ) ∈ L := hle (mem_quadraticSpan.mpr ⟨1, 0, by simp⟩)
  have hvL : v ∈ L := he ▸ mem_quadraticSpan.mpr ⟨0, 1, by simp [v]⟩
  have hall := translate_norms (by exact_mod_cast hn : 0 < (n : ℤ)) hd hone hvL hmin hr hi
  let x := t - 2 * a
  let b := x.bmod (2 * n)
  obtain ⟨hl, hu, k, hk⟩ := (Int.bmod_eq_iff (a := x) (b := 2*n) (c := b) (by omega)).mp rfl
  push_cast at hk
  have hb : b = x + 2 * ((n : ℤ) * k) := by linarith only [hk]
  refine ⟨b, abs_le.mpr ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · rw [hb]; dsimp [x]; omega
  · simpa only [hb, x] using hall k
  · obtain ⟨j, hj⟩ := hdisc
    refine ⟨j + k * x + (n : ℤ) * k ^ 2, ?_⟩
    rw [hb]
    dsimp [x] at *
    linear_combination hj

/-- The norm of the centered second basis vector and the unit horizontal vector
control every integral combination in a reduced binary quadratic form. -/
private theorem centered_form_min {n b d : ℤ} (hn : 0 < n) (hb : |b| ≤ n)
    (hd : 4 * n ^ 2 ≤ b ^ 2 + d) (x y : ℤ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    4 * n ^ 2 ≤ (2 * (n * x) + b * y) ^ 2 + d * y ^ 2 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  rcases le_total 0 b with h0 | h0
  · have h := reduced_form_min (A := 4 * n ^ 2) (B := 4 * n * b) (C := b ^ 2 + d)
      (by positivity) (by positivity) (by nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hu)]) hd x y hxy
    linarith only [h]
  · have h := reduced_form_min (A := 4 * n ^ 2) (B := 4 * n * (-b)) (C := b ^ 2 + d)
      (by positivity) (mul_nonneg (by positivity) (neg_nonneg.mpr h0))
      (by nlinarith [mul_nonneg hn.le (show 0 ≤ n + b by omega)]) hd (-x) y (by simpa using hxy)
    linarith only [h]

/-- A stable shortest-unit overgroup of index n exists exactly when one reduced middle
coefficient meets the norm bound and integral discriminant congruence. Unlike the purely
additive spectrum, the stable spectrum can have gaps. -/
theorem exists_stable_overgroup_index_iff {ω : ℂ} {n : ℕ} {t d q : ℤ}
    (hn : 0 < n) (hd : 0 < d) (hre : 2 * ω.re = (t : ℝ))
    (him : (2 * ω.im) ^ 2 = (d : ℝ)) (hpoly : ω ^ 2 = (t : ℂ) * ω - (q : ℂ))
    (hdq : d = 4 * q - t ^ 2) :
    (∃ L : AddSubgroup ℂ, quadraticSpan ω ≤ L ∧ (quadraticSpan ω).relIndex L = n ∧
      (∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) ∧ (∀ z ∈ L, ω * z ∈ L)) ↔
    ∃ b : ℤ, |b| ≤ (n : ℤ) ∧ b % 2 = t % 2 ∧ 4 * (n : ℤ) ^ 2 ≤ b ^ 2 + d ∧
      (4 * (n : ℤ)) ∣ b ^ 2 + d := by
  constructor
  · rintro ⟨L, hle, hidx, hmin, hs⟩
    exact stable_overgroup_index_conditions hn hd hre him hpoly hdq hle hidx hmin hs
  · rintro ⟨b, hb, hpar, hred, hcong⟩
    let a := (t - b) / 2
    have ha : t - 2 * a = b := by dsimp [a]; omega
    let v : ℂ := (ω - a) / n
    obtain ⟨hv, hr, hi⟩ := dividedPeriod_coords hn hre him a
    have hω : ω.im ≠ 0 := by
      have h : 0 < (d : ℝ) := by exact_mod_cast hd
      intro hz; rw [hz] at him; linarith
    obtain ⟨hle, hidx⟩ := quadraticSpan_index hω hv
    refine ⟨quadraticSpan v, hle, hidx, (one_shortest_quadraticSpan ?_).2, ?_⟩
    · intro x y hxy
      have hni : 0 < (n : ℤ) := by exact_mod_cast hn
      have h := centered_form_min hni hb hred x y hxy
      rw [← ha] at h
      simpa only [zsmul_eq_mul] using (form_iff_norm hni hr hi x y).mp h
    · apply (quadraticSpan_mul_stable_iff hn hω hv hpoly).mpr
      apply (shift_norm_dvd_iff_discriminant _ _ _ _).mpr
      rwa [ha, ← hdq]

end GroundTheory.Heights₂.Heights.FiniteCovolume

namespace StableQuadraticIndex

/-- Trace coefficients may be taken nonnegative because the two reduction tests only see b². -/
def indices (d : ℕ) : Finset ℕ :=
  (Finset.range ((d / 3).sqrt + 1)).filter fun n =>
    0 < n ∧ ∃ b : Fin (n + 1), 4*n^2 ≤ (b:ℕ)^2 + d ∧ 4*n ∣ (b:ℕ)^2 + d

def maximum (d : ℕ) : ℕ := (indices d).sup id

/-- The finite search includes every reduced stable index; the cutoff is forced by reduction. -/
theorem mem_indices {d n : ℕ} :
    n ∈ indices d ↔ 0 < n ∧ ∃ b : ℕ, b ≤ n ∧ 4*n^2 ≤ b^2+d ∧ 4*n ∣ b^2+d := by
  simp only [indices, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨-,hn,b,hb,hdvd⟩
    exact ⟨hn,b,by omega,hb,hdvd⟩
  · rintro ⟨hn,b,hbn,hb,hdvd⟩
    have hs : b^2 ≤ n^2 := Nat.pow_le_pow_left hbn 2
    have hn2 : n^2 ≤ d/3 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
    exact ⟨Nat.le_sqrt.mpr (by simpa [sq] using hn2), hn, ⟨b,by omega⟩,hb,hdvd⟩

theorem maximum_mem {d : ℕ} (hd : (indices d).Nonempty) : maximum d ∈ indices d := by
  obtain ⟨k,hk,h⟩ := Finset.exists_mem_eq_sup (indices d) hd id
  change (indices d).sup id ∈ indices d
  rw [h]
  exact hk

/-- Computation only for the nine displayed discriminant magnitudes. -/
theorem nine_maxima :
    [3,4,7,8,11,19,43,67,163].map maximum = List.replicate 9 1 := by decide +kernel

theorem criterion_iff_mem {n d : ℕ} {t q : ℤ} (hn : 0 < n)
    (hdq : (d : ℤ) = 4 * q - t^2) :
    (∃ b : ℤ, |b| ≤ (n : ℤ) ∧ b % 2 = t % 2 ∧ 4 * (n : ℤ)^2 ≤ b^2+d ∧
      4 * (n : ℤ) ∣ b^2+d) ↔ n ∈ StableQuadraticIndex.indices d := by
  rw [StableQuadraticIndex.mem_indices]
  constructor
  · rintro ⟨b, hb, _, hred, hdiv⟩
    have he : (b.natAbs : ℤ)^2 = b^2 := by simp
    refine ⟨hn, b.natAbs, ?_, ?_, ?_⟩
    · exact_mod_cast (show (b.natAbs : ℤ) ≤ n by simpa [Int.natCast_natAbs] using hb)
    · rw [← he] at hred; exact_mod_cast hred
    · rw [← he] at hdiv; exact_mod_cast hdiv
  · rintro ⟨_, b, hb, hred, hdiv⟩
    have h : 4 * (n : ℤ) ∣ (b : ℤ)^2 + d := by exact_mod_cast hdiv
    refine ⟨b, by simpa using hb, ?_, by exact_mod_cast hred, h⟩
    obtain ⟨k, hk⟩ := h
    have sqmod (i : ℤ) : i^2 % 2 = i % 2 := by
      rw [pow_two, Int.mul_emod]
      have hh : i % 2 = 0 ∨ i % 2 = 1 := by omega
      rcases hh with hh | hh <;> simp [hh]
    have hr : (b : ℤ)^2 - t^2 = 4 * ((n : ℤ) * k - q) := by linarith only [hk, hdq]
    have h1 := sqmod (b:ℤ)
    have h2 := sqmod t
    omega

end StableQuadraticIndex
