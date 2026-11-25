module

public import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaFunctionalEquation

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace GroundTheory.Global GroundTheory.Global.IdeleGroup
open GlobalTheory.CompanionTheory.PartialZeta GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open Complex Filter Topology
open scoped ComplexOrder nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {F : Type} [Field F] [NumberField F]

/-- Two continuations of the same class Dirichlet series agree away from the pole. -/
theorem isPartialZeta_eqOn {C : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (hW : IsPartialZeta C W) : Set.EqOn Z W {1}ᶜ := by
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  refine (hZ.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (hW.1.analyticOnNhd ho)
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (z₀ := 2) (by norm_num) ?_
  have hh : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hh.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
  exact (hZ.2 s hs).unique (hW.2 s hs)

/-- An ordinary partial zeta is strictly positive real on the real half-ray x > 1. -/
theorem isPartialZeta_pos_right {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ} (hZ : IsPartialZeta C Z)
    (x : ℝ) (hx : 1 < x) : 0 < Z (x : ℂ) := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C
  have h := hZ.2 (x : ℂ) (by simpa using hx)
  have hp (I : {I : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 I = C}) :
      0 < ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-(x : ℂ)) := by
    rw [Complex.cpow_neg]
    exact Complex.inv_natCast_cpow_ofReal_pos (Ideal.absNorm_pos_of_nonZeroDivisors I.1).ne' x
  rw [← h.tsum_eq]
  exact h.summable.tsum_pos (fun I => (hp I).le) ⟨J, hJ⟩ (hp ⟨J, hJ⟩)

private theorem order_inv_Gamma_neg_nat (n : ℕ) :
    analyticOrderAt (fun z : ℂ => (Gamma z)⁻¹) (-(n : ℂ)) = 1 := by
  let γ := fun z : ℂ => (Gamma z)⁻¹
  let t := fun z : ℂ => z + 1
  change analyticOrderAt γ _ = 1
  have ht (x : ℂ) : HasDerivAt t 1 x := by simpa [t] using (hasDerivAt_id x).add_const 1
  have recur (x : ℂ) : analyticOrderAt γ x = analyticOrderAt id x + analyticOrderAt γ (x + 1) := by
    have eq : γ = (id : ℂ → ℂ) * (γ ∘ t) := funext one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
    calc
      _ = analyticOrderAt ((id : ℂ → ℂ) * (γ ∘ t)) x := congrArg (analyticOrderAt · x) eq
      _ = _ := by
        rw [analyticOrderAt_mul analyticAt_id ((differentiable_one_div_Gamma.analyticAt _).comp
          (show AnalyticAt ℂ t x by dsimp [t]; fun_prop)),
          analyticOrderAt_comp_of_deriv_ne_zero (by dsimp [t]; fun_prop) (by rw [(ht x).deriv]; norm_num)]
  induction n with
  | zero =>
      rw [Nat.cast_zero, neg_zero, recur, zero_add]
      have ho : analyticOrderAt (id : ℂ → ℂ) 0 = 1 := by
        simp
      rw [ho, analyticOrderAt_eq_zero.mpr (.inr (by simp [γ, Gamma_one])), add_zero]
  | succ n ih =>
      have hn : (id : ℂ → ℂ) (-(n.succ : ℂ)) ≠ 0 :=
        neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      rw [recur, analyticOrderAt_eq_zero.mpr (.inr hn), zero_add,
        show -(n.succ : ℂ) + 1 = -(n : ℂ) by push_cast; ring]
      exact ih

private theorem order_inv_GammaC_neg_nat (n : ℕ) :
    analyticOrderAt (fun z : ℂ => (Gammaℂ z)⁻¹) (-(n : ℂ)) = 1 := by
  let U := fun s : ℂ => (2 * (2 * (Real.pi : ℂ)) ^ (-s))⁻¹
  have hU : AnalyticAt ℂ U (-(n : ℂ)) :=
    (Differentiable.inv ((differentiable_neg.const_cpow (by simp)).const_mul 2) (by simp)).analyticAt _
  have eq : (fun z : ℂ => (Gammaℂ z)⁻¹) = (fun z : ℂ => (Gamma z)⁻¹) * U :=
    funext fun s => by simp [Gammaℂ_def, U, Pi.mul_apply]
  rw [eq, analyticOrderAt_mul (differentiable_one_div_Gamma.analyticAt _) hU, order_inv_Gamma_neg_nat,
    hU.analyticOrderAt_eq_zero.mpr (by simp [U]), add_zero]

private theorem order_inv_GammaR_neg_even (n : ℕ) :
    analyticOrderAt (fun z : ℂ => (Gammaℝ z)⁻¹) (-(2 * (n : ℂ))) = 1 := by
  let U := fun s : ℂ => ((Real.pi : ℂ) ^ (-s / 2))⁻¹
  let t := fun s : ℂ => s / 2
  have hU : AnalyticAt ℂ U (-(2 * (n : ℂ))) :=
    (Differentiable.inv ((differentiable_neg.div_const (2 : ℂ)).const_cpow (by simp)) (by simp)).analyticAt _
  have ht : AnalyticAt ℂ t (-(2 * (n : ℂ))) := by dsimp [t]; fun_prop
  have eq : (fun z : ℂ => (Gammaℝ z)⁻¹) = ((fun z : ℂ => (Gamma z)⁻¹) ∘ t) * U :=
    funext fun s => by simp [Gammaℝ_def, U, t, Pi.mul_apply]
  rw [eq, analyticOrderAt_mul ((differentiable_one_div_Gamma.analyticAt _).comp ht) hU,
    analyticOrderAt_comp_of_deriv_ne_zero ht (by dsimp [t]; simp),
    hU.analyticOrderAt_eq_zero.mpr (by simp [U]), add_zero,
    show t (-(2 * (n : ℂ))) = -(n : ℂ) by dsimp [t]; ring, order_inv_Gamma_neg_nat]

/-- An analytic numerator nonzero at the target does not cancel any archimedean zero. -/
private theorem orderAt_signature_quotient_eq (r c n : ℕ) (G Z : ℂ → ℂ) (hG : AnalyticAt ℂ G (-(n : ℂ)))
    (hnz : G (-(n : ℂ)) ≠ 0) (hz : Z =ᶠ[𝓝 (-(n : ℂ))] fun z =>
      (Gammaℝ z ^ r * Gammaℂ z ^ c)⁻¹ * G z) :
    analyticOrderAt Z (-(n : ℂ)) = (if Even n then (r : ℕ∞) else 0) + c := by
  let R := fun s : ℂ => (Gammaℝ s)⁻¹
  let C := fun s : ℂ => (Gammaℂ s)⁻¹
  have hR : AnalyticAt ℂ R (-(n : ℂ)) := differentiable_Gammaℝ_inv.analyticAt _
  have hC : AnalyticAt ℂ C (-(n : ℂ)) := differentiable_Gammaℂ_inv.analyticAt _
  have eq : Z =ᶠ[𝓝 (-(n : ℂ))] (R ^ r * C ^ c) * G :=
    hz.trans <| .of_forall fun s => by simp [R, C, Pi.mul_apply, Pi.pow_apply, mul_comm]
  rw [analyticOrderAt_congr eq, analyticOrderAt_mul ((hR.pow r).mul (hC.pow c)) hG,
    hG.analyticOrderAt_eq_zero.mpr hnz, add_zero, analyticOrderAt_mul (hR.pow r) (hC.pow c),
    analyticOrderAt_pow hR, analyticOrderAt_pow hC, order_inv_GammaC_neg_nat, nsmul_one]
  split_ifs with hn
  · obtain ⟨j, rfl⟩ := hn
    rw [show (↑(j + j) : ℂ) = 2 * (j : ℂ) by push_cast; ring, order_inv_GammaR_neg_even, nsmul_one]
  · have hr : R (-(n : ℂ)) ≠ 0 := by
      apply inv_ne_zero
      intro h
      obtain ⟨j, hj⟩ := Gammaℝ_eq_zero_iff.mp h
      apply hn
      refine ⟨j, ?_⟩
      have hj' := neg_inj.mp hj
      rw [two_mul] at hj'
      exact_mod_cast hj'
    rw [hR.analyticOrderAt_eq_zero.mpr hr, nsmul_zero]

private theorem classDiscriminant_ne_zero (F : Type) [Field F] [NumberField F] : (dF F : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F)))

/-- The class gamma factor has no zero in the open right half-plane. -/
theorem classGamma_ne_of_re_pos {s : ℂ} (hs : 0 < s.re) : classGamma F s ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs)) (pow_ne_zero _ ?_)
  rw [Gammaℂ_def]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))) (Gamma_ne_zero_of_re_pos hs)

private theorem normPower_classHecke_eq_zero
    (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) {τ : ℝ}
    (hτ : ∀ x : IdeleGroup F, ((classHecke ψ).toIdele x : ℂ) =
      ((ideleModule F x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) : τ = 0 := by
  let w : InfinitePlace F := Classical.arbitrary _
  have hs (t : {x : ℝ // 0 < x}) : (classHecke ψ).toIdele (moduleSection w t) = 1 :=
    MonoidHom.mem_ker.1 (standardOpenSubgroup_le_ker ψ (moduleSection_mem_standardOpenSubgroup w t))
  have h0 : archExponent w (classHecke ψ) = 0 :=
    archExponent_unique w (classHecke ψ) fun t => by simp [hs t]
  exact (archExponent_eq_of_forall hτ w).symm.trans h0

private theorem classHecke_ne_normPower
    {ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ} (hψ : ψ ≠ 0) :
    ¬ ∃ τ : ℝ, ∀ x : IdeleGroup F, ((classHecke ψ).toIdele x : ℂ) =
      ((ideleModule F x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  rintro ⟨τ, hτ⟩
  have e := normPower_classHecke_eq_zero ψ hτ
  subst τ
  apply hψ
  ext c
  obtain ⟨x, hx⟩ := toClassGroup_surjective (Additive.toMul c)
  have h := hτ x
  rw [classHecke_toIdele, coe_classCircle, hx] at h
  simpa using h

private theorem classHecke_zero :
    classHecke (0 : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) = 1 := by
  ext x
  change ((classCircle (0 : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (IdeleClassGroup.toClassGroup x) : Circle) : ℂ) = 1
  simp [coe_classCircle]

/-- Away from zero, the ordinary class zeta equals the normalized completed function,
including at the other poles of the totalized Gamma factor. -/
theorem zetaOfClass_eq_normalized_of_ne_zero (C : ClassGroup (𝓞 F)) {s : ℂ} (hs : s ≠ 0) :
    zetaOfClass C s = (classGamma F s)⁻¹ * ((dF F : ℂ) ^ (-(s / 2)) * completedZetaOfClass C s) := by
  classical
  rw [zetaOfClass, completedZetaOfClass, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have hU := standardOpenSubgroup_le_ker ψ
  have hL : (classHecke ψ).continuedLFunction s = (classHecke ψ).normalizedLFunction s := by
    by_cases hψ : ψ = 0
    · subst ψ
      rw [classHecke_zero (F := F)]
      exact HeckeCharacter.continuedLFunction_of_ne (HeckeCharacter.one_toIdele_eq_cpow (K := F))
        (by simpa using hs)
    · exact congrFun (HeckeCharacter.continuedLFunction_of_not _ (classHecke_ne_normPower hψ)) s
  rw [hL, HeckeCharacter.normalizedLFunction, classGamma_eq _ hU, discrNormConductor_eq_dF_of_unramified F _ hU]
  ring

/-- On the open left half-plane, normalization is valid even at a pole of the
archimedean Gamma factor. -/
theorem zetaOfClass_eq_normalized_of_re_neg (C : ClassGroup (𝓞 F)) {s : ℂ} (hs : s.re < 0) :
    zetaOfClass C s = (classGamma F s)⁻¹ * ((dF F : ℂ) ^ (-(s / 2)) * completedZetaOfClass C s) :=
  zetaOfClass_eq_normalized_of_ne_zero C (fun e => by simp [e] at hs)

private theorem completedZetaOfClass_ne_of_real_neg (C : ClassGroup (𝓞 F)) (x : ℝ) (hx : x < 0) :
    completedZetaOfClass C (x : ℂ) ≠ 0 := by
  let D : (Ideal (𝓞 F))⁰ := ⟨differentIdeal ℤ (𝓞 F), mem_nonZeroDivisors_of_ne_zero _root_.differentIdeal_ne_bot⟩
  let C' := C⁻¹ * ClassGroup.mk0 D
  have h0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne
  have h1 : (x : ℂ) ≠ 1 := by norm_cast; linarith
  have hr : 1 < 1 - x := by linarith
  have heq : 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by simp
  have hp : 0 < (1 - (x : ℂ)).re := by simp; linarith
  rw [completedZetaOfClass_functionalEquation C C' D rfl (by simp [C']) _ h0 h1,
    completedZetaOfClass_eq C' (classGamma_ne_of_re_pos hp)]
  refine mul_ne_zero (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl (classDiscriminant_ne_zero F))) (classGamma_ne_of_re_pos hp)) ?_
  rw [heq]
  exact (isPartialZeta_pos_right (isPartialZeta_zetaOfClass C') (1 - x) hr).ne'

/-- At every negative real argument the only zeros of a partial zeta function are the
zeros of the totalized archimedean factor. -/
theorem isPartialZeta_eq_zero_iff_of_real_neg {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (x : ℝ) (hx : x < 0) : Z (x : ℂ) = 0 ↔ classGamma F x = 0 := by
  have h1 : (x : ℂ) ≠ 1 := by norm_cast; linarith
  rw [isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C) h1, zetaOfClass_eq_normalized_of_re_neg C hx]
  simp [completedZetaOfClass_ne_of_real_neg C x hx, Complex.cpow_ne_zero_iff.mpr (Or.inl (classDiscriminant_ne_zero F))]

/-- The exact multiplicity of an ordinary partial zeta zero at a strictly negative integer
is one per complex place, and one per real place precisely when the integer is even. -/
theorem isPartialZeta_order_neg_nat {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (n : ℕ) (hn : 0 < n) :
    analyticOrderAt Z (-(n : ℂ)) = (if Even n then (nrRealPlaces F : ℕ∞) else 0) + nrComplexPlaces F := by
  let g := fun t : ℂ => (dF F : ℂ) ^ (-(t / 2)) * completedZetaOfClass C t
  have hr : -(n : ℝ) < 0 := by exact neg_lt_zero.mpr (by exact_mod_cast hn)
  have hs : (-(n : ℂ)).re < 0 := by simpa using hr
  have h0 : -(n : ℂ) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
  have h1 : -(n : ℂ) ≠ 1 := by intro e; rw [e] at hs; norm_num at hs
  have hD : Differentiable ℂ (fun t : ℂ => (dF F : ℂ) ^ (-(t / 2))) :=
    fun _ => DifferentiableAt.const_cpow (by fun_prop) (Or.inl (classDiscriminant_ne_zero F))
  apply orderAt_signature_quotient_eq _ _ n g Z
  · exact (hD.analyticAt _).mul (analyticAt_completedZetaOfClass C h0 h1)
  · apply mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl (classDiscriminant_ne_zero F)))
    simpa using completedZetaOfClass_ne_of_real_neg C _ hr
  · apply Filter.EventuallyEq.trans (Filter.mem_of_superset (isOpen_compl_singleton.mem_nhds h1)
      (isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C)))
    have ho : IsOpen {t : ℂ | t.re < 0} := isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [ho.mem_nhds hs] with t ht
    exact zetaOfClass_eq_normalized_of_re_neg C ht

/-- Removing the trivial character leaves an entire completed class zeta function. -/
theorem completedZetaOfClass_eq_dedekind_add_entire (C : ClassGroup (𝓞 F)) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ s : ℂ,
      completedZetaOfClass C s = (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ *
        completedDedekindZeta F s + E s := by
  classical
  let term (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (s : ℂ) :=
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) *
      (classHecke ψ).completedLFunction s
  refine ⟨fun s => ∑ ψ ∈ Finset.univ.erase 0, term ψ s, ?_, fun s => ?_⟩
  · refine Differentiable.fun_sum fun ψ hψ => ?_
    exact ((classHecke ψ).differentiable_completedLFunction
      (classHecke_ne_normPower (Finset.ne_of_mem_erase hψ))).const_mul _
  · have h := (Finset.sum_erase_add Finset.univ (fun ψ => term ψ s) (Finset.mem_univ 0)).symm
    unfold completedZetaOfClass
    rw [show (∑ ψ, _) = ∑ ψ, term ψ s from rfl, h, add_comm]
    simp [term, classHecke_zero, completedDedekindZeta]

/-- For every class, the completed residue at zero is the completed Dedekind residue
divided by the class number. In particular this residue cannot vanish. -/
theorem tendsto_mul_completedZetaOfClass_zero (C : ClassGroup (𝓞 F)) :
    Tendsto (fun s ↦ s * completedZetaOfClass C s) (𝓝[≠] 0)
      (𝓝 ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ *
        -(((normOneClassMeasure F Set.univ).toReal : ℂ) * ((Real.pi : ℂ) ^ nrComplexPlaces F)⁻¹))) := by
  obtain ⟨E, hE, h⟩ := completedZetaOfClass_eq_dedekind_add_entire C
  have hE' : Tendsto (fun s : ℂ => s * E s) (𝓝[≠] 0) (𝓝 0) := by
    have h0 : Tendsto (fun s : ℂ => s) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_mul] using h0.mul
      ((hE.continuous.continuousAt.tendsto (x := (0 : ℂ))).mono_left nhdsWithin_le_nhds)
  have hh := ((tendsto_const_nhds (x := (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹)).mul (tendsto_mul_completedDedekindZeta_zero_volume F)).add hE'
  rw [add_zero] at hh
  refine hh.congr fun s => ?_
  rw [h s]
  ring


/-- Every ordinary ideal class has the same nonzero residue at one: the Dedekind
residue divided by the class number. -/
theorem tendsto_sub_one_mul_isPartialZeta {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) :
    Tendsto (fun s ↦ (s - 1) * Z s) (𝓝[≠] 1)
      (𝓝 ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (dedekindZeta_residue F : ℂ))) := by
  obtain ⟨E, hE, h⟩ := completedZetaOfClass_eq_dedekind_add_entire C
  let G := fun s : ℂ => (dF F : ℂ) ^ (-(s / 2)) * (classGamma F s)⁻¹ * E s
  have hG : Differentiable ℂ G :=
    (differentiable_discr_cpow_mul_gamma_inv F).mul hE
  have h0 : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have hc : Continuous (fun s : ℂ => s - 1) := by fun_prop
    simpa only [sub_self] using (hc.continuousAt (x := (1 : ℂ))).tendsto.mono_left nhdsWithin_le_nhds
  have hG' : Tendsto (fun s : ℂ => (s - 1) * G s) (𝓝[≠] 1) (𝓝 0) := by
    simpa only [zero_mul] using h0.mul
      ((hG.continuous.continuousAt.tendsto (x := (1 : ℂ))).mono_left nhdsWithin_le_nhds)
  have hh := ((tendsto_const_nhds (x := (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹)).mul
    (tendsto_sub_one_mul_continuedDedekindZeta F)).add hG'
  rw [add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (isOpen_compl_singleton.mem_nhds (one_ne_zero (α := ℂ)))] with s hs1 hs0
  have h1 : s ≠ 1 := hs1
  have hs_ne_zero : s ≠ 0 := hs0
  rw [isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C) h1,
    zetaOfClass_eq_normalized_of_ne_zero C hs_ne_zero, h s,
    continuedDedekindZeta_of_ne_zero F hs_ne_zero]
  unfold normalizedDedekindZeta
  change (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ *
      ((s - 1) * ((dF F : ℂ) ^ (-(s / 2)) * (classGamma F s)⁻¹ * completedDedekindZeta F s)) +
      (s - 1) * G s = _
  dsimp [G]
  ring

/-- The uncompleted ideal-class zeta has exact order r₁ + r₂ − 1 at zero.
Unlike at negative integers, one Gamma zero cancels the pole of the completed zeta. -/
theorem isPartialZeta_order_zero {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) :
    analyticOrderAt Z 0 = ((nrRealPlaces F + nrComplexPlaces F - 1 : ℕ) : ℕ∞) := by
  let R : ℂ := (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ *
    -(((normOneClassMeasure F Set.univ).toReal : ℂ) * ((Real.pi : ℂ) ^ nrComplexPlaces F)⁻¹)
  let P : ℂ → ℂ := Function.update (fun s ↦ s * completedZetaOfClass C s) 0 R
  have hR : R ≠ 0 := mul_ne_zero (inv_ne_zero card_classGroup_ne_zero)
    (neg_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr (normOneClassMeasure_univ_toReal_ne_zero F))
      (inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))))
  have hPon : DifferentiableOn ℂ P ({1}ᶜ : Set ℂ) := by
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (isOpen_compl_singleton.mem_nhds (zero_ne_one (α := ℂ)))).mp ⟨?_, ?_⟩
    · refine DifferentiableOn.congr (fun s hs => ?_) fun s hs =>
        Function.update_of_ne hs.2 _ _
      exact ((differentiableAt_id (x := s)).mul
        (analyticAt_completedZetaOfClass C hs.2 hs.1).differentiableAt).differentiableWithinAt
    · change ContinuousAt (Function.update (fun s ↦ s * completedZetaOfClass C s) 0 R) 0
      rw [continuousAt_update_same]
      exact tendsto_mul_completedZetaOfClass_zero C
  have hP : AnalyticAt ℂ P 0 :=
    hPon.analyticAt (isOpen_compl_singleton.mem_nhds (zero_ne_one (α := ℂ)))
  let G := fun s : ℂ => (dF F : ℂ) ^ (-(s / 2)) * P s
  have hD : Differentiable ℂ (fun t : ℂ => (dF F : ℂ) ^ (-(t / 2))) :=
    fun _ => DifferentiableAt.const_cpow (by fun_prop) (Or.inl (classDiscriminant_ne_zero F))
  have hG : AnalyticAt ℂ G 0 := (hD.analyticAt _).mul hP
  have hGn : G 0 ≠ 0 := by simpa [G, P] using hR
  have horder := orderAt_signature_quotient_eq (nrRealPlaces F) (nrComplexPlaces F) 0
    G (id * Z) (by simpa using hG) (by simpa using hGn) ?_
  · have hZa : AnalyticAt ℂ Z 0 :=
      hZ.1.analyticAt (isOpen_compl_singleton.mem_nhds (zero_ne_one (α := ℂ)))
    have he : 1 + analyticOrderAt Z 0 = (nrRealPlaces F : ℕ∞) + nrComplexPlaces F := by
      simpa [analyticOrderAt_mul analyticAt_id hZa] using horder
    apply ENat.add_right_injective_of_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
    change 1 + analyticOrderAt Z 0 = 1 + ((nrRealPlaces F + nrComplexPlaces F - 1 : ℕ) : ℕ∞)
    rw [he, ← ENat.natCast_add, ← ENat.natCast_one, ← ENat.natCast_add]
    have hn : 0 < nrRealPlaces F + nrComplexPlaces F := by
      rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]
      exact Fintype.card_pos
    exact congrArg (fun n : ℕ => (n : ℕ∞)) (by omega)
  · simp only [Nat.cast_zero, neg_zero]
    refine Filter.EventuallyEq.trans (g := id * zetaOfClass C) ?_ (.of_forall fun s => ?_)
    · filter_upwards [isOpen_compl_singleton.mem_nhds (zero_ne_one (α := ℂ))] with s hs
      simp only [Pi.mul_apply, isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C) hs]
    · change s * zetaOfClass C s = (classGamma F s)⁻¹ * G s
      by_cases hs : s = 0
      · subst s
        simp [classGamma_zero]
      · rw [zetaOfClass_eq_normalized_of_ne_zero C hs]
        dsimp [G, P]
        rw [Function.update_of_ne hs]
        ring

open NumberField.Units

private theorem zero_class_constant (F : Type) [Field F] [NumberField F] :
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ *
      -(((normOneClassMeasure F Set.univ).toReal : ℂ) * ((Real.pi : ℂ) ^ nrComplexPlaces F)⁻¹)) /
      ((2 : ℂ) ^ nrRealPlaces F * 2 ^ nrComplexPlaces F) =
        -(regulator F : ℂ) / torsionOrder F := by
  rw [normOneClassMeasure_univ_toReal_eq, dedekindZeta_residue_def, NumberField.classNumber]
  push_cast
  have hd : Real.sqrt |(discr F : ℝ)| ≠ 0 := (Real.sqrt_pos_of_pos
    (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F)))).ne'
  have hp := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hh : (Fintype.card (ClassGroup (𝓞 F)) : ℂ) ≠ 0 := card_classGroup_ne_zero
  rw [mul_pow]
  field_simp [hp, hh, Complex.ofReal_ne_zero.mpr hd]

/-- At zero every ordinary ideal-class zeta has leading Taylor coefficient
minus the regulator divided by the number of roots of unity, independently of the class. -/
theorem tendsto_isPartialZeta_div_pow_zero {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) :
    Tendsto (fun s ↦ Z s / s ^ (nrRealPlaces F + nrComplexPlaces F - 1)) (𝓝[≠] 0)
      (𝓝 (-(regulator F : ℂ) / torsionOrder F)) := by
  let r := nrRealPlaces F
  let c := nrComplexPlaces F
  have hN : 0 < r + c := by
    change 0 < nrRealPlaces F + nrComplexPlaces F
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hD : (dF F : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F)))
  have ht : Tendsto (fun s : ℂ => (dF F : ℂ) ^ (-(s / 2))) (𝓝[≠] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun s : ℂ => (dF F : ℂ) ^ (-(s / 2))) 0 :=
      ContinuousAt.const_cpow (by fun_prop) (Or.inl hD)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hg := (Gammaℝ_residue_zero.pow r).mul (Gammaℂ_residue_zero.pow c)
  have h := (ht.mul (tendsto_mul_completedZetaOfClass_zero C)).div hg
    (mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero))
  rw [one_mul, zero_class_constant F] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (isOpen_compl_singleton.mem_nhds (zero_ne_one (α := ℂ)))] with s hs0 hs1
  have hs : s ≠ 0 := hs0
  rw [isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C) hs1, zetaOfClass_eq_normalized_of_ne_zero C hs]
  change _ / ((s * Gammaℝ s)^r * (s * Gammaℂ s)^c) =
    (Gammaℝ s ^ r * Gammaℂ s ^ c)⁻¹ * _ / s^(r+c-1)
  rw [mul_pow, mul_pow]
  have hp : s^(r+c) = s^(r+c-1) * s := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  rw [show s^r * Gammaℝ s^r * (s^c * Gammaℂ s^c) =
    (s ^ (r+c)) * (Gammaℝ s^r * Gammaℂ s^c) by rw [pow_add]; ring, hp]
  calc _ = (s * s⁻¹) * ((Gammaℝ s^r * Gammaℂ s^c)⁻¹ *
          ((dF F : ℂ) ^ (-(s / 2)) * completedZetaOfClass C s) / s^(r+c-1)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]; ring
       _ = _ := by rw [mul_inv_cancel₀ hs, one_mul]

/-- The first nonzero derivative, divided by its factorial, is the same arithmetic
constant for every class (also for unit rank zero). -/
theorem isPartialZeta_leading_taylor_zero {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) :
    iteratedDeriv (Units.rank F) Z 0 / (Units.rank F).factorial =
      -(regulator F : ℂ) / torsionOrder F := by
  let k := Units.rank F
  have hk : k = nrRealPlaces F + nrComplexPlaces F - 1 := by
    simp [k, Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces]
  have hZa := hZ.1.analyticAt (isOpen_compl_singleton.mem_nhds (zero_ne_one (α := ℂ)))
  have ho : analyticOrderAt Z 0 = k := by rw [hk, isPartialZeta_order_zero hZ]
  have hz := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hZa).mp ho
  obtain ⟨g, hg, hseries⟩ := hZa.exists_eventuallyEq_sum_add_pow_mul (k+1)
  have ht : Tendsto (fun s : ℂ => iteratedDeriv k Z 0 / k.factorial + s * g s) (𝓝[≠] 0)
      (𝓝 (iteratedDeriv k Z 0 / k.factorial)) := by
    have hi : Tendsto (id : ℂ → ℂ) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := iteratedDeriv k Z 0 / k.factorial)).add
      (hi.mul (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  apply tendsto_nhds_unique (f := fun s : ℂ => Z s / s^k) _ (by
    rw [hk]; exact tendsto_isPartialZeta_div_pow_zero hZ)
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hseries] with s hs h
  have hs0 : s ≠ 0 := hs
  have hsum : ∑ i ∈ Finset.range k, (s ^ i / i.factorial) • iteratedDeriv i Z 0 = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hz.1 i (Finset.mem_range.mp hi), smul_zero])
  rw [h, Finset.sum_range_succ, hsum, zero_add, pow_succ]
  simp only [smul_eq_mul]
  field_simp

/-- The completed poles are identical for every class, so their difference is entire. -/
theorem differentiable_completedZetaOfClass_sub (C B : ClassGroup (𝓞 F)) :
    Differentiable ℂ (fun s => completedZetaOfClass C s - completedZetaOfClass B s) := by
  obtain ⟨E, hE, hC⟩ := completedZetaOfClass_eq_dedekind_add_entire C
  obtain ⟨H, hH, hB⟩ := completedZetaOfClass_eq_dedekind_add_entire B
  simpa only [hC, hB, add_sub_add_left_eq_sub] using hE.fun_sub hH

/-- Ordinary class differences have a global entire factorization, even at zero.
At one this is a statement about the specified canonical representatives. -/
theorem zetaOfClass_sub_eq_normalized (C B : ClassGroup (𝓞 F)) (s : ℂ) :
    zetaOfClass C s - zetaOfClass B s =
      (dF F : ℂ) ^ (-(s / 2)) * (classGamma F s)⁻¹ *
        (completedZetaOfClass C s - completedZetaOfClass B s) := by
  let G := fun t : ℂ => (dF F : ℂ) ^ (-(t / 2)) * (classGamma F t)⁻¹ *
    (completedZetaOfClass C t - completedZetaOfClass B t)
  have away (t : ℂ) (ht : t ≠ 0) : zetaOfClass C t - zetaOfClass B t = G t := by
    rw [zetaOfClass_eq_normalized_of_ne_zero C ht, zetaOfClass_eq_normalized_of_ne_zero B ht]
    dsimp [G]
    ring
  by_cases hs : s ≠ 0
  · exact away s hs
  · obtain rfl := not_not.mp hs
    have hcont (A : ClassGroup (𝓞 F)) : ContinuousAt (zetaOfClass A) 0 :=
      ((isPartialZeta_zetaOfClass A).1.analyticAt
        (isOpen_compl_singleton.mem_nhds (zero_ne_one (α := ℂ)))).continuousAt
    have hG : Differentiable ℂ G := (differentiable_discr_cpow_mul_gamma_inv F).fun_mul
      (differentiable_completedZetaOfClass_sub C B)
    apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] (0 : ℂ))
      (((hcont C).sub (hcont B)).tendsto.mono_left nhdsWithin_le_nhds)
      (hG.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact away t ht

/-- In this normalization subtraction fills the removable singularity of the
ordinary class difference at one without choosing any new point value. -/
theorem differentiable_zetaOfClass_sub (C B : ClassGroup (𝓞 F)) :
    Differentiable ℂ (fun s => zetaOfClass C s - zetaOfClass B s) := by
  simp_rw [zetaOfClass_sub_eq_normalized C B]
  exact (differentiable_discr_cpow_mul_gamma_inv F).fun_mul (differentiable_completedZetaOfClass_sub C B)

/-- At every nonpositive integer the ordinary difference has the full archimedean
order, plus precisely the order of the completed difference. This includes identical classes. -/
theorem isPartialZeta_sub_order_neg_nat {C B : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (hW : IsPartialZeta B W) (n : ℕ) :
    analyticOrderAt (fun s => Z s - W s) (-(n : ℂ)) =
      ((if Even n then (nrRealPlaces F : ℕ∞) else 0) + nrComplexPlaces F) +
        analyticOrderAt (fun s => completedZetaOfClass C s - completedZetaOfClass B s) (-(n : ℂ)) := by
  let G := fun s : ℂ => (dF F : ℂ) ^ (-(s / 2)) * (classGamma F s)⁻¹
  have hG : Differentiable ℂ G := differentiable_discr_cpow_mul_gamma_inv F
  have h1 : -(n : ℂ) ≠ 1 := by
    exact_mod_cast (by omega : -(n : ℤ) ≠ 1)
  have eqn : (fun s => Z s - W s) =ᶠ[𝓝 (-(n : ℂ))]
      G * (fun s => completedZetaOfClass C s - completedZetaOfClass B s) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds h1] with s hs
    rw [isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C) hs,
        isPartialZeta_eqOn hW (isPartialZeta_zetaOfClass B) hs]
    exact zetaOfClass_sub_eq_normalized C B s
  rw [analyticOrderAt_congr eqn, analyticOrderAt_mul (hG.analyticAt _)
    ((differentiable_completedZetaOfClass_sub C B).analyticAt _)]
  congr 1
  apply orderAt_signature_quotient_eq _ _ n (fun s : ℂ => (dF F : ℂ) ^ (-(s / 2))) G
  · exact (show Differentiable ℂ (fun s : ℂ => (dF F : ℂ) ^ (-(s / 2))) from
      fun s => DifferentiableAt.const_cpow (by fun_prop) (Or.inl (classDiscriminant_ne_zero F))).analyticAt _
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (classDiscriminant_ne_zero F))
  · exact .of_forall fun s => mul_comm _ _

/-- Ordinary partial zetas of arbitrary ideal classes have matching derivatives below
the archimedean order at every nonpositive integer. In particular at zero this includes
the first nonzero derivative of every individual partial zeta. -/
theorem isPartialZeta_iteratedDeriv_eq_neg_nat {C B : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (hW : IsPartialZeta B W) (n j : ℕ)
    (hj : j < (if Even n then nrRealPlaces F else 0) + nrComplexPlaces F) :
    iteratedDeriv j Z (-(n : ℂ)) = iteratedDeriv j W (-(n : ℂ)) := by
  have h1 : -(n : ℂ) ≠ 1 := by
    exact_mod_cast (by omega : -(n : ℤ) ≠ 1)
  have hZa := hZ.1.analyticAt (isOpen_compl_singleton.mem_nhds h1)
  have hWa := hW.1.analyticAt (isOpen_compl_singleton.mem_nhds h1)
  have ho : (((if Even n then nrRealPlaces F else 0) + nrComplexPlaces F : ℕ) : ℕ∞) ≤
      analyticOrderAt (fun s => Z s - W s) (-(n : ℂ)) := by
    rw [isPartialZeta_sub_order_neg_nat hZ hW]
    split_ifs <;> simp
  have hj' := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hZa.fun_sub hWa)).mp ho j hj
  simpa only [iteratedDeriv_fun_sub hZa.contDiffAt hWa.contDiffAt, sub_eq_zero] using hj'

/-- The difference of two completed class functions reflects even at the two
poles of the separate functions: the common polar term cancels on both sides. -/
theorem completedZetaOfClass_sub_reflect (C B C' B' : ClassGroup (𝓞 F))
    (D : (Ideal (𝓞 F))⁰) (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F))
    (hC : C * C' = ClassGroup.mk0 D) (hB : B * B' = ClassGroup.mk0 D) :
    (fun s => completedZetaOfClass C s - completedZetaOfClass B s) =
      (fun s => completedZetaOfClass C' (1 - s) - completedZetaOfClass B' (1 - s)) := by
  have h₁ := differentiable_completedZetaOfClass_sub C B
  have h₂ : Differentiable ℂ (fun s => completedZetaOfClass C' (1 - s) - completedZetaOfClass B' (1 - s)) :=
    (differentiable_completedZetaOfClass_sub C' B').comp (show Differentiable ℂ (fun s : ℂ => 1 - s) by fun_prop)
  apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr h₁).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr h₂) (z₀ := 2)
  filter_upwards [eventually_ne_nhds (show (2 : ℂ) ≠ 0 by norm_num),
    eventually_ne_nhds (show (2 : ℂ) ≠ 1 by norm_num)] with s hs₀ hs₁
  exact congrArg₂ (· - ·)
    (completedZetaOfClass_functionalEquation C C' D hD hC s hs₀ hs₁)
    (completedZetaOfClass_functionalEquation B B' D hD hB s hs₀ hs₁)

/-- Any multiplicity beyond the archimedean trivial zeros is the multiplicity
of the reflected ordinary difference. At n = 0 the right side uses the entire
canonical difference at 1, not the arbitrary assigned values of two meromorphic functions. -/
theorem isPartialZeta_sub_order_reflected {C B C' B' : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (hW : IsPartialZeta B W)
    (D : (Ideal (𝓞 F))⁰) (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F))
    (hC : C * C' = ClassGroup.mk0 D) (hB : B * B' = ClassGroup.mk0 D) (n : ℕ) :
    analyticOrderAt (fun s => Z s - W s) (-(n : ℂ)) =
      ((if Even n then (nrRealPlaces F : ℕ∞) else 0) + nrComplexPlaces F) +
        analyticOrderAt (fun s => zetaOfClass C' s - zetaOfClass B' s) (1 + n) := by
  let E := fun s => completedZetaOfClass C' s - completedZetaOfClass B' s
  let u := fun s : ℂ => (dF F : ℂ) ^ (-(s / 2)) * (classGamma F s)⁻¹
  have hu : AnalyticAt ℂ u (1 + n : ℂ) :=
    (differentiable_discr_cpow_mul_gamma_inv F).analyticAt (1 + n : ℂ)
  have hunit : u (1 + n) ≠ 0 := mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (.inl (classDiscriminant_ne_zero F)))
    (inv_ne_zero (classGamma_ne_of_re_pos (by simpa using (show (0 : ℝ) < 1 + n by positivity))))
  have hE : AnalyticAt ℂ E (1 + n : ℂ) :=
    (differentiable_completedZetaOfClass_sub C' B').analyticAt (1 + n : ℂ)
  rw [isPartialZeta_sub_order_neg_nat hZ hW n, completedZetaOfClass_sub_reflect C B C' B' D hD hC hB]
  congr 1
  change analyticOrderAt (E ∘ (fun s : ℂ => 1 - s)) (-(n : ℂ)) = _
  rw [analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
  simp only [sub_neg_eq_add]
  have hmul : (fun s => zetaOfClass C' s - zetaOfClass B' s) = (fun s => u s * E s) :=
    funext (zetaOfClass_sub_eq_normalized C' B')
  rw [hmul, analyticOrderAt_fun_mul hu hE, hu.analyticOrderAt_eq_zero.mpr hunit, zero_add]

/-- Comparing two classes cancels the common leading value at zero. The next
Taylor coefficient is the reflected difference of the finite parts at one,
with the normalization of this field's discriminant and archimedean places. -/
theorem tendsto_isPartialZeta_sub_div_pow_zero {C B C' B' : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (hW : IsPartialZeta B W)
    (D : (Ideal (𝓞 F))⁰) (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F))
    (hC : C * C' = ClassGroup.mk0 D) (hB : B * B' = ClassGroup.mk0 D) :
    Tendsto (fun s => (Z s - W s) / s ^ (nrRealPlaces F + nrComplexPlaces F))
      (𝓝[≠] 0) (𝓝 ((dF F : ℂ) ^ (1 / 2 : ℂ) * (zetaOfClass C' 1 - zetaOfClass B' 1) /
        ((Real.pi : ℂ) ^ nrComplexPlaces F * (2 : ℂ) ^ (nrRealPlaces F + nrComplexPlaces F)))) := by
  let r := nrRealPlaces F
  let c := nrComplexPlaces F
  let E := fun s => completedZetaOfClass C s - completedZetaOfClass B s
  have hE : Tendsto E (𝓝[≠] 0) (𝓝 (E 0)) :=
    ((differentiable_completedZetaOfClass_sub C B).continuous.continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  have hE₀ : E 0 = (dF F : ℂ) ^ (1 / 2 : ℂ) * ((Real.pi : ℂ) ^ c)⁻¹ *
      (zetaOfClass C' 1 - zetaOfClass B' 1) := by
    have e := congrFun (completedZetaOfClass_sub_reflect C B C' B' D hD hC hB) 0
    simp only [sub_zero] at e
    have hγ : classGamma F 1 ≠ 0 := classGamma_ne_of_re_pos (by norm_num)
    change completedZetaOfClass C 0 - completedZetaOfClass B 0 = _
    rw [e, completedZetaOfClass_eq C' hγ, completedZetaOfClass_eq B' hγ, classGamma,
      Gammaℝ_one, Gammaℂ_one]
    simp only [one_pow, one_mul, one_div, inv_pow, c, mul_sub]
  have ht : Tendsto (fun s : ℂ => (dF F : ℂ) ^ (-(s / 2))) (𝓝[≠] 0) (𝓝 1) := by
    have h : ContinuousAt (fun s : ℂ => (dF F : ℂ) ^ (-(s / 2))) 0 :=
      ContinuousAt.const_cpow (by fun_prop) (Or.inl (classDiscriminant_ne_zero F))
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hg := (Gammaℝ_residue_zero.pow r).mul (Gammaℂ_residue_zero.pow c)
  have h := (ht.mul hE).div hg (mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero))
  rw [one_mul, hE₀, ← pow_add] at h
  have hc : (dF F : ℂ) ^ (1 / 2 : ℂ) * ((Real.pi : ℂ) ^ c)⁻¹ *
        (zetaOfClass C' 1 - zetaOfClass B' 1) / (2 : ℂ) ^ (r + c) =
      (dF F : ℂ) ^ (1 / 2 : ℂ) * (zetaOfClass C' 1 - zetaOfClass B' 1) /
        ((Real.pi : ℂ) ^ c * (2 : ℂ) ^ (r + c)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hc] at h
  refine h.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (eventually_ne_nhds (zero_ne_one (α := ℂ)))] with s hs
  rw [isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C) hs,
    isPartialZeta_eqOn hW (isPartialZeta_zetaOfClass B) hs, zetaOfClass_sub_eq_normalized]
  change _ / ((s * Gammaℝ s)^r * (s * Gammaℂ s)^c) =
    _ * (Gammaℝ s ^ r * Gammaℂ s ^ c)⁻¹ * E s / s^(r+c)
  simp only [mul_pow, pow_add, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The value used at one in the reflection formula is the limit for every
choice of the two partial zetas, no matter what values they assign to the pole. -/
theorem isPartialZeta_tendsto_sub_one {C B : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (hW : IsPartialZeta B W) :
    Tendsto (fun s => Z s - W s) (𝓝[≠] 1) (𝓝 (zetaOfClass C 1 - zetaOfClass B 1)) := by
  refine ((differentiable_zetaOfClass_sub C B).continuous.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C) hs,
    isPartialZeta_eqOn hW (isPartialZeta_zetaOfClass B) hs]

end GlobalTheory.CompanionTheory.Hypotheses₂
