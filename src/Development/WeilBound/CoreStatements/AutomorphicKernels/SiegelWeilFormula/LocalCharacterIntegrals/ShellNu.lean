module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.LatticeNormTransport
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.MeasurePreservingOfAddEquiv

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace Shell

variable {v : HeightOneSpectrum (𝓞 F)}

/-- On the ultrametric open ball of contractive perturbations, left multiplication is an isometry. -/
theorem one_add_mul_norm {n : ℕ} {C : ℝ}
    (hm : ∀ a b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v (a * b) ≤ C * nM v a * nM v b)
    {x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)} (hx : C * nM v x < 1) (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    nM v ((1 + x) * b) = nM v b := by
  by_cases hb : b = 0
  · subst b; exact congrArg (nM v) (Matrix.mul_zero _)
  calc
    nM v ((1 + x) * b) = nM v (b + x * b) := by
      apply congrArg (nM v)
      exact (Matrix.add_mul _ _ _).trans (congrArg (fun m => m + x * b) (Matrix.one_mul b))
    _ = nM v b := nM_add_eq_of_lt ?_
  have hp := lt_of_le_of_ne (nM_nonneg b) (fun h => hb (nM_eq_zero.mp h.symm))
  exact (hm x b).trans_lt (by simpa using mul_lt_mul_of_pos_right hx hp)

/-- No determinant-radius hypothesis is needed. The inverse perturbation has exactly the same norm. -/
theorem inverse_of_contractive {n : ℕ} {C : ℝ}
    (hm : ∀ a b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v (a * b) ≤ C * nM v a * nM v b)
    {x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)} (hx : C * nM v x < 1) :
    ∃ y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), (1 + x) * (1 + y) = 1 ∧ (1 + y) * (1 + x) = 1 ∧ nM v y = nM v x := by
  let f := Algebra.lmul (Fv F v) _ (1 + x)
  have hi : Function.Injective f := LinearMap.ker_eq_bot.mp <| by
    rw [LinearMap.ker_eq_bot']
    intro b hb
    apply nM_eq_zero.mp
    exact (one_add_mul_norm hm hx b).symm.trans ((congrArg (nM v) hb).trans nM_zero)
  obtain ⟨u, hu⟩ : IsUnit (1 + x) := IsUnit.isUnit_iff_mulLeft_bijective.mpr
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  let y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := ↑u⁻¹ - 1
  have hy : 1 + y = ↑u⁻¹ := by dsimp [y]; abel
  have hyL : (1 + x) * (1 + y) = 1 := by rw [hy, ← hu, Units.mul_inv]
  refine ⟨y, hyL, by rw [hy, ← hu, Units.inv_mul], ?_⟩
  have e : (1 + x) * y = -x := by
    apply eq_neg_of_add_eq_zero_right
    apply add_left_cancel (a := (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))
    simpa only [add_zero, mul_add, mul_one, add_assoc] using hyL
  exact (one_add_mul_norm hm hx y).symm.trans ((congrArg (nM v) e).trans (nM_neg x))

end Shell

namespace ShNu

variable {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem stable (v : HeightOneSpectrum (𝓞 F)) {L : AddSubgroup (Fin n → Fv F v ⊗[F] E)} (hL : IsCO L) :
    ∃ r > 0, ∀ d : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v d ≤ r → ∀ y ∈ L,
      ((1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) + d).mulVec y ∈ L := by
  obtain ⟨ε, hε, hεL⟩ := exists_ballV_subset (v := v) (U := (L : Set (Fin n → Fv F v ⊗[F] E)))
    (hL.1.mem_nhds L.zero_mem)
  obtain ⟨ρ, hρ⟩ := exists_bound_nV (v := v) hL.2
  obtain ⟨C, hC0, hC⟩ := exists_nM_mulVec v (E := E) n n
  set ρ' := max ρ 0 with hρ'
  have hρ'0 : 0 ≤ ρ' := le_max_right _ _
  refine ⟨ε / (C * ρ' + 1), by positivity, fun g hg y hy => ?_⟩
  have hy' : nV v y ≤ ρ' := (hρ y hy).trans (le_max_left _ _)
  have hsmall : nV v (g.mulVec y) ≤ ε := by
    calc nV v (g.mulVec y) ≤ C * nM v g * nV v y := hC _ _
      _ ≤ C * (ε / (C * ρ' + 1)) * ρ' :=
          mul_le_mul (mul_le_mul_of_nonneg_left hg hC0) hy' (nV_nonneg _) (by positivity)
      _ = ε * (C * ρ' / (C * ρ' + 1)) := by ring
      _ ≤ ε := mul_le_of_le_one_right hε.le (div_le_one_of_le₀ (by linarith) (by positivity))
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  exact L.add_mem hy (hεL hsmall)

theorem nM_transpose (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : nM v xᵀ = nM v x := by
  apply le_antisymm
  · exact (nM_le_iff (nM_nonneg x)).2 fun i j => nA_le_nM x j i
  · exact (nM_le_iff (nM_nonneg (v := v) (xᵀ : Fin n → Fin n → Fv F v ⊗[F] E))).2 fun i j =>
      nA_le_nM (v := v) (xᵀ : Fin n → Fin n → Fv F v ⊗[F] E) j i

theorem inv_small {C : ℝ} (hC : ∀ x y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v (x * y) ≤ C * nM v x * nM v y)
    {x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)} (hx : C * nM v x ≤ 1 / 2) (hu : IsUnit (1 + x).det) :
    nM v (((1 + x)⁻¹ - 1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ≤ nM v x := by
  obtain ⟨y, hxy, _, hy⟩ := Shell.inverse_of_contractive hC (hx.trans_lt (by norm_num))
  rw [Matrix.right_inv_eq_right_inv (Matrix.mul_nonsing_inv _ hu) hxy]
  exact ((congrArg (nM v) (show 1 + y - 1 = y by abel)).trans hy).le

/-- A contractive perturbation maps a lattice onto itself as soon as the same closed ball
maps it into itself. Its inverse perturbation has exactly the same coordinate norm. -/
theorem image_one_add_of_contractive {L : AddSubgroup (Fin n → Fv F v ⊗[F] E)} {r C : ℝ}
    (hstab : ∀ d : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v d ≤ r →
      ∀ z ∈ L, (1 + d).mulVec z ∈ L)
    (hm : ∀ a b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v (a * b) ≤ C * nM v a * nM v b)
    {x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)} (hx : C * nM v x < 1) (hr : nM v x ≤ r) :
    IsUnit (1 + x).det ∧ L.map (Matrix.mulVecLin (1 + x)).toAddMonoidHom = L := by
  obtain ⟨y, hxy, _, hy⟩ := Shell.inverse_of_contractive hm hx
  refine ⟨Matrix.isUnit_det_of_right_inverse hxy, SetLike.ext' (Set.Subset.antisymm ?_ ?_)⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hstab x hr z hz
  · intro z hz
    refine ⟨(1 + y).mulVec z, hstab y (hy.le.trans hr) z hz, ?_⟩
    change (1 + x).mulVec ((1 + y).mulVec z) = z
    rw [Matrix.mulVec_mulVec, hxy, Matrix.one_mulVec]


def cs (σ : E →ₐ[F] E) (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  (x.map (sigR (Fv F v) σ))ᵀ

theorem cs_one_add {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} (σ : E →ₐ[F] E) (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    cs σ (1 + x) = 1 + cs σ x := by
  simp only [cs]
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add,
    Matrix.transpose_one]

theorem isUnit_det_cs {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} (σ : E →ₐ[F] E) {a : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)} (ha : IsUnit a.det) :
    IsUnit (cs σ a).det := by
  simp only [cs, Matrix.det_transpose]
  have : (a.map (sigR (Fv F v) σ)).det = sigR (Fv F v) σ a.det := (RingHom.map_det _ _).symm
  rw [this]
  exact ha.map _

def Sx (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)) (B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    Set (Fin n → Fv F v ⊗[F] E) := {x | ∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + B.mulVec y'}

theorem measurableSet_Sx {L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)} (h₁ : IsCO L₁) (h₂ : IsCO L₂)
    (B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : MeasurableSet (Sx L₁ L₂ B) := by
  have e : Sx L₁ L₂ B = (fun p : (Fin n → Fv F v ⊗[F] E) × (Fin n → Fv F v ⊗[F] E) => p.1 + B.mulVec p.2) ''
      ((L₁ : Set (Fin n → Fv F v ⊗[F] E)) ×ˢ (L₂ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext z
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩; exact ⟨(y, y'), ⟨hy, hy'⟩, rfl⟩
    · rintro ⟨⟨y, y'⟩, ⟨hy, hy'⟩, rfl⟩; exact ⟨y, hy, y', hy', rfl⟩
  rw [e]
  have hc : Continuous fun p : (Fin n → Fv F v ⊗[F] E) × (Fin n → Fv F v ⊗[F] E) => p.1 + B.mulVec p.2 :=
    continuous_fst.add (Continuous.matrix_mulVec continuous_const continuous_snd)
  exact ((h₁.2.prod h₂.2).image hc).isClosed.measurableSet

def mulVecEquiv (P Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (Fin n → Fv F v ⊗[F] E) ≃+ (Fin n → Fv F v ⊗[F] E) where
  toFun := P.mulVec
  invFun := Q.mulVec
  left_inv y := by simp only [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  right_inv y := by simp only [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add P

end ShNu


open ShNu in
theorem lattice_norm_conj_invariant (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) :
    (hcm : IsCMExt F E σ) → {n : ℕ} → (lam : Measure (Fin n → Fv F v ⊗[F] E)) → [lam.IsAddHaarMeasure] →
    (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)) → (h₁ : IsCO L₁) → (h₂ : IsCO L₂) →
    ∃ r > 0, ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r → ∀ B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
      nu2 lam L₁ L₂ (((1 + x).map (sigR (Fv F v) σ))ᵀ * B * (1 + x)) = nu2 lam L₁ L₂ B := fun _ {n} lam _ L₁ L₂ h₁ h₂ => by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_nM_mul v (E := E) n n n
  obtain ⟨Cs, hCs0, hCs⟩ := exists_nM_sig v σ n n
  obtain ⟨r₁, hr₁, hst₁⟩ := stable v h₁
  obtain ⟨r₂, hr₂, hst₂⟩ := stable v h₂
  let u := max 1 Cs
  have hu : 1 ≤ u := le_max_left _ _
  let rh := 1 / (Cm + 1)
  have hrh : 0 < rh := by dsimp [rh]; positivity
  have hsmall {t : ℝ} (ht : t ≤ rh) : Cm * t < 1 :=
    (mul_le_mul_of_nonneg_left ht hCm0).trans_lt (by
      change Cm * (1 / (Cm + 1)) < 1
      rw [mul_one_div]
      exact (div_lt_one (by linarith)).mpr (by linarith))
  refine ⟨min r₂ (min r₁ rh / u), lt_min hr₂ (div_pos (lt_min hr₁ hrh) (by linarith)), fun x hx B => ?_⟩
  have hx₂ := hx.trans (min_le_left _ _)
  have hx' := (le_div_iff₀ (show 0 < u by linarith)).mp (hx.trans (min_le_right _ _))
  have hxm : nM v x ≤ min r₁ rh := (le_mul_of_one_le_right (nM_nonneg x) hu).trans hx'
  have hcs : nM v (cs σ x) ≤ min r₁ rh := by
    calc nM v (cs σ x) = nM v (x.map (sigR (Fv F v) σ)) := nM_transpose _
         _ ≤ Cs * nM v x := hCs x
         _ ≤ u * nM v x := mul_le_mul_of_nonneg_right (le_max_right _ _) (nM_nonneg x)
         _ ≤ min r₁ rh := by rwa [mul_comm]
  have ha := image_one_add_of_contractive hst₂ hCm (hsmall (hxm.trans (min_le_right _ _))) hx₂
  have hs := image_one_add_of_contractive hst₁ hCm (hsmall (hcs.trans (min_le_right _ _))) (hcs.trans (min_le_left _ _))
  rw [← cs_one_add] at hs
  change nu2 lam L₁ L₂ (cs σ (1 + x) * B * (1 + x)) = _
  simpa only [hs.2, ha.2] using
    GlobalTheory.CompanionTheory.SwFinM.lattice_norm_matrix_transport lam L₁ L₂
      (cs σ (1 + x)) _ B (1 + x) (Matrix.mul_nonsing_inv _ hs.1) (Matrix.nonsing_inv_mul _ hs.1)

end PositivityTheory.SiegelWeilFormula.SwLocFin
