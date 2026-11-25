module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

@[expose] public section

open Formalism.BasicNotions GlobalTheory.EX

/-- Power of the host rank at a fixed epsilon. -/
noncomputable def UpperTheory.Top.rankExponent (eps : ℝ) : ℝ := 797 / 2 + 929 / 16 * eps

/-- The rank growth before any rounding of the powers in the construction. -/
theorem UpperTheory.Top.rank_window_bound {s : Scale} {R : Ranks} (h : RankVal s R) :
    (R.t : ℝ) ≤ 10708 * s.x ^ (797 / 2 + 929 / 16 * s.eps) := by
  let P := fun a : ℝ => s.x ^ a
  have hx := s.one_lt_alt.le
  have hx₀ : 0 < s.x := lt_of_lt_of_le zero_lt_one hx
  have he := s.eps_pos
  have pos (a : ℝ) : 0 < P a := Real.rpow_pos_of_pos hx₀ _
  have mono {a b : ℝ} (hab : a ≤ b) : P a ≤ P b := Real.rpow_le_rpow_of_exponent_le hx hab
  have prod (a b : ℝ) : P a * P b = P (a + b) := (Real.rpow_add hx₀ _ _).symm
  have power (a : ℝ) (n : ℕ) : P a ^ n = P (a * n) := by
    change (s.x ^ a) ^ n = s.x ^ (a * n)
    rw [Real.rpow_mul hx₀.le, Real.rpow_natCast]
  have one {a : ℝ} (ha : 0 ≤ a) : 1 ≤ P a := Real.one_le_rpow hx ha
  let n : ℝ := 2 + 8 * s.eps
  let k : ℝ := 9 / 2 + 10 * s.eps
  let m : ℝ := 1 / 2 - s.eps / 16
  let b := 2 * n + 3 * k + 2 * s.eps - m
  let w := b + k
  have hf : (R.f : ℝ) ≤ 4 * P n := by
    have := h.n_up
    simp only [Ranks.f, Nat.cast_mul, Nat.cast_ofNat]
    change (R.n : ℝ) ≤ 2 * P n at this
    linarith
  have hk : (R.k : ℝ) - 1 ≤ 2 * P k := by linarith [h.2.2.1.2]
  have hk₀ : 0 ≤ (R.k : ℝ) - 1 := by
    have hkm := R.m_add_three_le_k
    have h1 : 1 ≤ R.k := by omega
    exact sub_nonneg.mpr (by exact_mod_cast h1)
  have hm : P m ≤ R.m := by
    apply le_trans _ h.2.1.1
    rw [Real.sqrt_eq_rpow]
    have e : s.x * s.delta1 = P (1 + -(s.eps / 8)) := by
      change s.x * s.x ^ _ = s.x ^ _
      rw [Real.rpow_add hx₀, Real.rpow_one]
    rw [e, ← Real.rpow_mul hx₀.le]
    exact le_of_eq (congrArg (s.x ^ ·) (by dsimp [m]; ring))
  have hL : s.L ^ 2 = P (2 * s.eps) := by
    change P s.eps ^ 2 = _
    rw [power]; congr 1; push_cast; ring
  have hr : (R.r : ℝ) ≤ 4 * P k := by
    have h2 : R.r ≤ 2 * R.k := by
      have := R.m_add_three_le_k
      unfold Ranks.r
      omega
    have h2' : (R.r : ℝ) ≤ 2 * (R.k : ℝ) := by exact_mod_cast h2
    have : (R.k : ℝ) ≤ 2 * P k := h.2.2.1.2
    linarith
  let B := (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m
  have hB : B ≤ 128 * P b := by
    apply (div_le_iff₀ (lt_of_lt_of_le (pos m) hm)).mpr
    calc (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2
        ≤ (4 * P n) ^ 2 * (2 * P k) ^ 3 * P (2 * s.eps) := by rw [hL]; gcongr
      _ = 128 * P b * P m := by
        rw [mul_pow, mul_pow, power, power]
        calc _ = 128 * ((P (n * 2) * P (k * 3)) * P (2 * s.eps)) := by norm_num; ring
          _ = _ := by rw [prod, prod, mul_assoc, prod]; congr 2; dsimp [b]; ring
      _ ≤ 128 * P b * R.m := by gcongr
  have hnb : P n ≤ P b := mono (by dsimp [b,n,k,m]; linarith)
  have hQ : (R.f : ℝ) + B ≤ 132 * P b := by linarith
  have hw0 : 1 ≤ P w := one (by dsimp [w,b,n,k,m]; linarith)
  have hw : (nWv R s : ℝ) ≤ 5288 * P w := by
    have B₀ : 0 ≤ B := by dsimp [B]; positivity
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 10 * (R.r : ℝ) * (R.f + B) / 8 by positivity)
    have H : 10 * (R.r : ℝ) * (R.f + B) ≤ 5280 * P w := calc
      _ ≤ 10 * (4 * P k) * (132 * P b) := by gcongr
      _ = 5280 * (P b * P k) := by ring
      _ = _ := by rw [prod]
    unfold nWv
    push_cast
    change 8 * (⌈10 * (R.r : ℝ) * (R.f + B) / 8⌉₊ : ℝ) ≤ _
    linarith
  have hT : (TOv s : ℝ) ≤ 2 * P 377 := by
    have hc := Nat.ceil_lt_add_one (pos 377).le
    have h1 : 1 ≤ P 377 := one (by norm_num)
    change (⌈P 377⌉₊ : ℝ) ≤ _
    linarith
  have eq : (R.r : ℝ) + R.t = 8 * R.f * R.r + 4 + (TOv s : ℝ) * nWv R s := by
    exact_mod_cast h.2.2.2
  have hfr : 8 * (R.f : ℝ) * R.r ≤ 128 * P (n + k) := calc
    _ ≤ 8 * (4 * P n) * (4 * P k) := by gcongr
    _ = 128 * (P n * P k) := by ring
    _ = _ := by rw [prod]
  have hTw : (TOv s : ℝ) * nWv R s ≤ 10576 * P (377 + w) := calc
    _ ≤ (2 * P 377) * (5288 * P w) := by gcongr
    _ = 10576 * (P 377 * P w) := by ring
    _ = _ := by rw [prod]
  have hsmall : P (n + k) ≤ P (377 + w) := mono (by dsimp [w,b,n,k,m]; linarith)
  have h1 : 1 ≤ P (377 + w) := one (by dsimp [w,b,n,k,m]; linarith)
  have exponent : 377 + w = 797 / 2 + 929 / 16 * s.eps := by dsimp [w,b,n,k,m]; ring
  change (R.t : ℝ) ≤ 10708 * P _
  rw [← exponent]
  linarith [show (0 : ℝ) ≤ R.r by positivity]

theorem UpperTheory.Top.eventually_rank_le_rpow_of_lt_one_div_fiftytwo :
    ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      (R.t : ℝ) ≤ s.x ^ (400 : ℝ) := by
  intro eps _ he
  let a : ℝ := 797 / 2 + 929 / 16 * eps
  have ha : 0 < 400 - a := by dsimp [a]; linarith
  obtain ⟨x₀, h₀⟩ := Filter.eventually_atTop.1 ((tendsto_rpow_atTop ha).eventually_ge_atTop 10708)
  refine ⟨x₀, fun s R hs hx hR => ?_⟩
  have hb := rank_window_bound hR
  rw [hs] at hb
  calc (R.t : ℝ) ≤ 10708 * s.x ^ a := hb
    _ ≤ s.x ^ (400 - a) * s.x ^ a :=
      mul_le_mul_of_nonneg_right (h₀ s.x hx) (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)
    _ = _ := by rw [← Real.rpow_add (by linarith [s.one_lt_alt] : 0 < s.x), sub_add_cancel]
