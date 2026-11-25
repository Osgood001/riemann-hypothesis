module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMorseSectionsMLAddAUniformStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernTopPowerVolumeDensityRatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSupNormBallLeGramDetStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem eventually_poly_mul_pow_le_exp (c C t : ℝ) (n : ℕ) (hC : 1 ≤ C) (ht : Real.log C < t) :
    ∀ᶠ m : ℕ in atTop, c * (m : ℝ) ^ n * C ^ m ≤ Real.exp (t * m) := by
  have hδ : 0 < t - Real.log C := sub_pos.2 ht
  have hc1 : 0 < |c| + 1 := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop n hδ).bound (c := 1 / (|c| + 1)) (by positivity)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  have hCpos : 0 < C := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hm
  have hexp : Real.exp (t * m) = Real.exp ((t - Real.log C) * m) * C ^ m := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCpos, ← Real.exp_add]; ring_nf
  rw [hexp]
  have hmn : (0 : ℝ) ≤ (m : ℝ) ^ n := by positivity
  have hle : c * (m : ℝ) ^ n ≤ Real.exp ((t - Real.log C) * m) := by
    calc c * (m : ℝ) ^ n ≤ (|c| + 1) * (m : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hmn
      _ ≤ (|c| + 1) * (1 / (|c| + 1) * Real.exp ((t - Real.log C) * m)) :=
          mul_le_mul_of_nonneg_left hm hc1.le
      _ = _ := by field_simp
  exact mul_le_mul_of_nonneg_right hle (by positivity)

private theorem scale_log_bound (r m D : ℕ) (R c H K V : ℝ)
    (hH : 1 ≤ H) (hm : 1 ≤ m) (hK : 1 ≤ K) (hV : 1 ≤ V) (hR : 0 < R) (hc : 0 ≤ c)
    (hr : (r : ℝ) ≤ H * (m : ℝ)^D) :
    Real.log (max 2 (1 + Real.sqrt r * c / (2 * R)) * (K * (m : ℝ)^D * V)) ≤
    Real.log (2 * H * K * V) + (2 * D : ℕ) * Real.log m + Real.log (max 1 (c / R)) := by
  have hq : 1 ≤ max 1 (c / R) := le_max_left _ _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hHD : 1 ≤ H * (m : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hH (one_le_pow₀ hm1)
  have hB : 1 ≤ H * (m : ℝ) ^ D * max 1 (c / R) := one_le_mul_of_one_le_of_one_le hHD hq
  have hsr : Real.sqrt (r : ℝ) ≤ (r : ℝ) := Real.sqrt_le_self_iff.2 (by
    rcases Nat.eq_zero_or_pos r with h|h
    · exact .inl (by simp [h])
    · exact .inr (by exact_mod_cast h))
  have hx : Real.sqrt r * c / (2 * R) ≤ H * (m : ℝ) ^ D * max 1 (c / R) := calc
    _ ≤ Real.sqrt r * (c / R) := by rw [← mul_div_assoc]; gcongr; linarith
    _ ≤ _ := mul_le_mul (hsr.trans hr) (le_max_right _ _) (by positivity) (by positivity)
  have hU : max 2 (1 + Real.sqrt r * c / (2 * R)) ≤ 2 * (H * (m : ℝ)^D * max 1 (c/R)) :=
    max_le (by linarith) (by linarith)
  calc
    _ ≤ Real.log (2 * (H * (m : ℝ)^D * max 1 (c/R)) * (K * (m : ℝ)^D * V)) := by
      apply Real.log_le_log
      · exact mul_pos (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_left _ _)) (by positivity)
      · gcongr
    _ = _ := by
      have he : 2 * (H * (m : ℝ)^D * max 1 (c/R)) * (K * (m : ℝ)^D * V) =
          ((2 * H * K * V) * (m : ℝ)^(2*D)) * max 1 (c/R) := by ring
      rw [he, Real.log_mul (by positivity) (ne_of_gt (by linarith)), Real.log_mul (by positivity)
        (by positivity), Real.log_pow]

/-- The normalized Gram error vanishes when the counting radius falls below the generator
radius by at most a subexponential factor. Only a polynomial rank bound is needed. -/
theorem count_ball_asymp_of_radius (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (hS : GenSmooth p D)
    (P : Pair p) (hP : P.L.SemiPos D) (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ)
    (f : ∀ m, Fin (r m) → X.functionField) (hf : ∀ (m : ℕ) i, f m i ∈ P.H m 1)
    (hli : ∀ m, LinearIndependent ℤ (f m)) (H : ℝ) (hH : 1 ≤ H)
    (hr : ∀ᶠ m : ℕ in atTop, (r m : ℝ) ≤ H * (m : ℝ)^D) (S : ℕ → ℝ)
    (hSgen : ∀ᶠ m in atTop, 0 ≤ S m ∧ AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (S m)))
    (R : ℕ → ℝ) (hR : ∀ᶠ m in atTop, 0 < R m)
    (hscale : Tendsto (fun m : ℕ => Real.log (max 1 (S m / R m)) / m) atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => (Real.log ((ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (R m)).ncard : ℝ) -
      (r m * Real.log (R m) - Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re / 2 +
       Real.log (volume {x : Fin (r m) → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)) / (m : ℝ) ^ (D + 1))
      atTop (𝓝 0) := by
  have := hX.finite_emb
  let := Fintype.ofFinite (k →+* ℂ)
  have hρ := fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hS P.L hP σ (ω σ)
  choose ρ hρr hρ0 _ using hρ
  have hbd : ∀ σ, ∃ b : ℝ, ∀ y, ρ σ y ≤ b := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨b, hb⟩ := (isCompact_range (hρr σ).1).bddAbove
    exact ⟨b, fun y => hb ⟨y, rfl⟩⟩
  choose b hb using hbd
  set B : ℝ := ∑ σ, |b σ| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hρB : ∀ σ y, ρ σ y ≤ B := fun σ y => (hb σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |b σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set K : ℝ := B / D.factorial + 1 with hKdef
  have hK : 1 ≤ K := by
    have : 0 ≤ B / D.factorial := by positivity
    linarith
  set V : ℝ := max 1 (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) with hVdef
  have hV : 1 ≤ V := le_max_left _ _
  have hmorse := GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hS P hP ω ρ hρr 1 one_pos
  refine squeeze_zero_norm' (a := fun m : ℕ =>
    2 * H * ((Real.log (2 * H * K * V) + (2 * D : ℕ) * Real.log m) / m +
      Real.log (max 1 (S m / R m)) / m)) ?_ ?_
  · filter_upwards [hmorse, hr, hSgen, hR, eventually_ge_atTop 1] with m hm hrm hgen hRm h1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1
    have hm0 : (0 : ℝ) < m := by linarith
    have hmD : (0 : ℝ) < (m : ℝ) ^ D := pow_pos hm0 D
    have hM : 1 ≤ K * (m : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hm1)
    have hcmb : ∀ (c : Fin (r m) → ℂ) σ y, cmb (vals P m 1 (f m)) c σ y ≤
        K * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c := by
      intro c σ y
      have h := hm (Fin (r m)) (f m) (hf m) c σ y
      have hl2 : 0 ≤ l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c :=
        finsum_nonneg fun σ => integral_nonneg fun y => by unfold cmb; positivity
      refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hmD.le) hl2)
      have : ρ σ y / D.factorial ≤ B / D.factorial :=
        div_le_div_of_nonneg_right (hρB σ y) (by positivity)
      linarith
    have key := GlobalTheory.BallGram.count_ball_gram_of_radius k X p D hX hS P ω (m : ℤ) 1 (r m) (f m)
      (hf m) (hli m) (K * (m : ℝ)^D) V (S m) (R m) hM hV (le_max_right _ _) hgen.1 hRm hcmb hgen.2
    have hlog := scale_log_bound (r m) m D (R m) (S m) H K V hH h1 hK hV hRm hgen.1 hrm
    have hU : 2 ≤ max 2 (1 + Real.sqrt (r m) * S m / (2 * R m)) := le_max_left _ _
    have hlog0 : 0 ≤ Real.log (max 2 (1 + Real.sqrt (r m) * S m / (2 * R m)) *
        (K * (m : ℝ)^D * V)) := Real.log_nonneg
      (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le hM hV))
    have hmD1 : (0 : ℝ) < (m : ℝ)^(D + 1) := pow_pos hm0 _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hmD1, div_le_iff₀ hmD1]
    refine key.trans ?_
    calc
      _ ≤ 2 * (H * (m : ℝ)^D) * (Real.log (2 * H * K * V) + (2 * D : ℕ) * Real.log m +
          Real.log (max 1 (S m / R m))) := by
        exact mul_le_mul (by gcongr) hlog hlog0 (by positivity)
      _ = _ := by rw [pow_succ]; field_simp
  · have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun m : ℕ => (Real.log (2 * H * K * V) + (2 * D : ℕ) * Real.log m) / m) atTop (𝓝 0) := by
      have := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log (2 * H * K * V))).add
        ((hl.comp tendsto_natCast_atTop_atTop).const_mul ((2 * D : ℕ) : ℝ))
      simp only [mul_zero, add_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp_apply]
      ring
    simpa using (h2.add hscale).const_mul (2 * H)

theorem count_ball_asymp : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → ∀ g : ℝ, Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 g) → ∀ C : ℝ, 1 ≤ C → (∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m))) → ∀ t : ℝ, Real.log C < t → Tendsto (fun m : ℕ => (Real.log ((ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (Real.exp (t * m))).ncard : ℝ) - (r m * (t * m) - Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re / 2 + Real.log (volume {x : Fin (r m) → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
  intro k _ X _ p D hX hS P hP ω r f hf hli g hg C hC hball t ht
  have hr : ∀ᶠ m : ℕ in atTop, (r m : ℝ) ≤ max 1 (g + 1) * (m : ℝ) ^ D := by
    filter_upwards [hg.eventually (gt_mem_nhds (lt_add_one g)), eventually_ge_atTop 1] with m hm h1
    have hmD : 0 < (m : ℝ) ^ D := pow_pos (by exact_mod_cast h1) D
    exact ((div_lt_iff₀ hmD).mp hm).le.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hmD.le)
  have hgen : ∀ᶠ m : ℕ in atTop, 0 ≤ C ^ m ∧ AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact ⟨pow_nonneg (by linarith) m, hball m hm⟩
  have he : ∀ᶠ m : ℕ in atTop, C ^ m ≤ Real.exp (t * m) := by
    simpa using eventually_poly_mul_pow_le_exp 1 C t 0 hC ht
  have hscale : (fun m : ℕ => Real.log (max 1 (C ^ m / Real.exp (t * m))) / m) =ᶠ[atTop]
      fun _ => 0 := by
    filter_upwards [he] with m hm
    simp [max_eq_left ((div_le_one (Real.exp_pos _)).2 hm)]
  simpa only [Real.log_exp] using count_ball_asymp_of_radius k X p D hX hS P hP ω r f hf hli
    (max 1 (g + 1)) (le_max_left _ _) hr (fun m => C ^ m) hgen (fun m => Real.exp (t * m))
    (Eventually.of_forall fun _ => Real.exp_pos _) (tendsto_const_nhds.congr' hscale.symm)

end GlobalTheory.HSAmp
