module
public import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
public import Mathlib.RingTheory.QuadraticAlgebra
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.QuadraticStableIndex

@[expose] public section

open NumberField NumberField.InfinitePlace QuadraticAlgebra Module
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

/-- Every quadratic number field admits an integral quadratic period, with its actual
field discriminant, not just the discriminant of a smaller order. -/
private theorem exists_integral_period (K : Type*) [Field K] [NumberField K] (hK : finrank ℚ K = 2) :
    ∃ a b : ℤ, ∃ _e : QuadraticAlgebra ℤ a b ≃ₐ[ℤ] 𝓞 K,
      NumberField.discr K = QuadraticAlgebra.discr a b := by
  let : Algebra.IsQuadraticExtension ℤ (𝓞 K) := ⟨(RingOfIntegers.rank K).trans hK⟩
  obtain ⟨a,b,⟨e⟩⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  refine ⟨a,b,e.symm,?_⟩
  let B := QuadraticAlgebra.basis a b
  rw [← NumberField.discr_eq_discr _ (B.map e.symm.toLinearEquiv)]
  change Algebra.discr ℤ (e.symm ∘ B) = _
  rw [← Algebra.discr_eq_discr_of_algEquiv]
  exact Algebra.discr_quadraticAlgebra

/-- A quadratic integral basis yields the period and the complete image of the
integers in any one complex embedding. -/
private theorem period_coordinates {K : Type*} [Field K] [NumberField K]
    {a b : ℤ} (e : QuadraticAlgebra ℤ a b ≃ₐ[ℤ] 𝓞 K) (σ : K →+* ℂ) :
    ∃ w : ℂ, w ^ 2 = (a : ℂ) + b*w ∧
        ∀ z : ℂ, (∃ y : 𝓞 K, σ (y : K) = z) ↔ ∃ i j : ℤ, z = (i : ℂ) + j*w := by
  let f : QuadraticAlgebra ℤ a b →+* ℂ := σ.comp ((algebraMap (𝓞 K) K).comp e.toRingEquiv.toRingHom)
  have hf (x : QuadraticAlgebra ℤ a b) : f x = (x.re : ℂ) + x.im * f ω := by
    calc
      _ = f (x.re • 1 + x.im • ω) := congrArg f (re_smul_add_im_smul x).symm
      _ = _ := by simp [zsmul_eq_mul]
  refine ⟨f ω, ?_, ?_⟩
  · rw [sq, ← map_mul, omega_mul_omega_eq_add]
    simp [zsmul_eq_mul]
  · intro z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨x,rfl⟩ := e.surjective y
      exact ⟨_,_,hf x⟩
    · rintro ⟨i,j,rfl⟩
      exact ⟨e ⟨i,j⟩, hf ⟨i,j⟩⟩

private theorem discr_root_coordinates {a b : ℤ} {z : ℂ}
    (hd : QuadraticAlgebra.discr a b < 0) (hz : z ^ 2 = a + b * z) :
    2 * z.re = b ∧ (2 * z.im) ^ 2 = (|QuadraticAlgebra.discr a b| : ℤ) := by
  have hD : (b : ℝ) ^ 2 + 4 * a < 0 := by
    rw [QuadraticAlgebra.discr_def] at hd
    exact_mod_cast hd
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have hne : z.im ≠ 0 := by
    intro h
    rw [h, mul_zero, sub_zero] at hre
    nlinarith [sq_nonneg (2 * z.re - b)]
  have htrace : 2 * z.re = b := by
    apply (mul_left_cancel₀ hne)
    linarith only [him]
  refine ⟨htrace, ?_⟩
  rw [abs_of_neg hd, QuadraticAlgebra.discr_def]
  push_cast
  nlinarith [congrArg (fun t : ℝ => t ^ 2) htrace]

private theorem discr_abs_mod_two (a b : ℤ) (hd : QuadraticAlgebra.discr a b < 0) :
    |QuadraticAlgebra.discr a b| % 2 = b % 2 := by
  rw [abs_of_neg hd, QuadraticAlgebra.discr_def]
  have h : (b % 2) = 0 ∨ (b % 2) = 1 := by omega
  have hsq : b ^ 2 % 2 = b % 2 := by
    rw [pow_two, Int.mul_emod]
    rcases h with h | h <;> simp [h]
  omega

/-- The ring of integers of any imaginary quadratic field has a complex period
with precisely the actual field discriminant as vertical height squared. -/
theorem integral_period_of_imaginary_quadratic (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (σ : K →+* ℂ) :
    ∃ (w : ℂ) (t q : ℤ), (2 * w.re = (t : ℝ)) ∧
      (2 * w.im) ^ 2 = (|(NumberField.discr K : ℤ)| : ℝ) ∧ t % 2 = |NumberField.discr K| % 2 ∧
      w ^ 2 = (t : ℂ) * w - (q : ℂ) ∧ |NumberField.discr K| = 4 * q - t ^ 2 ∧
      (algebraMap (𝓞 K) K).toAddMonoidHom.range.map σ.toAddMonoidHom = quadraticSpan w := by
  obtain ⟨a,b,e, hd⟩ := exists_integral_period K hK
  obtain ⟨w, hw, he⟩ := period_coordinates e σ
  have hn : nrComplexPlaces K = 1 := by
    have h := card_add_two_mul_card_eq_rank K
    rw [nrRealPlaces_eq_zero_iff.mpr inferInstance, hK] at h
    omega
  have hsign := NumberField.sign_discr K
  rw [hn, pow_one, hd] at hsign
  have hnD := Int.sign_eq_neg_one_iff_neg.mp hsign
  obtain ⟨hr,hi⟩ := discr_root_coordinates hnD hw
  rw [hd]
  refine ⟨w, b, -a, hr, by simpa using hi, (discr_abs_mod_two a b hnD).symm, ?_, ?_, ?_⟩
  · rw [hw]; push_cast; ring
  · rw [abs_of_neg hnD, QuadraticAlgebra.discr_def]; ring
  · ext z
    rw [mem_quadraticSpan, ← he]
    exact ⟨fun ⟨_, ⟨u, rfl⟩, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨_, ⟨u, rfl⟩, hu⟩⟩

theorem weighted_minimum_iff_single_embedding (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (w : InfinitePlace K) (c : InfinitePlace K → ℝ) (hc : 0 < c w)
    (A : AddSubgroup K) :
    (∀ a ∈ A, a ≠ 0 → ∑ v, c v ≤ ∑ v, c v * ‖v.embedding a‖ ^ 2) ↔
    ∀ a ∈ A, a ≠ 0 → 1 ≤ ‖w.embedding a‖ := by
  have hd := card_add_two_mul_card_eq_rank K
  rw [nrRealPlaces_eq_zero_iff.mpr inferInstance, hK] at hd
  have hone : Fintype.card (InfinitePlace K) ≤ 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq_zero_iff.mpr inferInstance]
    omega
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp hone
  have hsum (f : InfinitePlace K → ℝ) : ∑ v, f v = f w :=
    Finset.sum_eq_single_of_mem w (Finset.mem_univ w) (fun i _ h => False.elim (h (Subsingleton.elim i w)))
  have cancel (x : ℝ) : c w ≤ c w * x ↔ 1 ≤ x := by
    simpa only [mul_one] using (mul_le_mul_iff_right₀ hc : c w * 1 ≤ c w * x ↔ 1 ≤ x)
  simp only [hsum, cancel, one_le_sq_iff₀ (norm_nonneg _)]

/-- A finite-index extension of an additive subgroup of a field transports predicates on
its complex image without changing the ambient field of any generator. -/
private theorem finite_index_subgroups_image {E : Type*} [Field E] (e : E →+* ℂ) (O : AddSubgroup E)
    {n : ℕ} (hn : 0 < n) (P : AddSubgroup ℂ → Prop) :
    (∃ A : AddSubgroup E, O ≤ A ∧ O.relIndex A = n ∧ P (A.map e.toAddMonoidHom)) ↔
    (∃ L : AddSubgroup ℂ, O.map e.toAddMonoidHom ≤ L ∧
      (O.map e.toAddMonoidHom).relIndex L = n ∧ P L) := by
  let f := e.toAddMonoidHom
  constructor
  · rintro ⟨A, hOA, hi, hA⟩
    exact ⟨A.map f, AddSubgroup.map_mono hOA,
      (AddSubgroup.relIndex_map_map_of_injective O A (show Function.Injective f from e.injective)).trans hi, hA⟩
  · rintro ⟨L, hOL, hi, hL⟩
    have himage : L ≤ f.range := by
      intro z hz
      let B := (O.map f).addSubgroupOf L
      have hB : B.index = n := hi
      have h := B.nsmul_index_mem (⟨z, hz⟩ : L)
      rw [hB] at h
      obtain ⟨a, _, he⟩ := (show n • z ∈ O.map f from h)
      change e a = n • z at he
      refine ⟨a / n, ?_⟩
      change e (a / n) = z
      rw [map_div₀, map_natCast, show e a = (n : ℂ) * z by simpa [nsmul_eq_mul] using he]
      exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')
    have hm : (L.comap f).map f = L := AddSubgroup.map_comap_eq_self himage
    refine ⟨L.comap f, AddSubgroup.map_le_iff_le_comap.mp hOL, ?_, ?_⟩
    · rw [← AddSubgroup.relIndex_map_map_of_injective O (L.comap f) (show Function.Injective f from e.injective)]
      rwa [hm]
    · exact (congrArg P hm).symm ▸ hL

private theorem image_shortest_iff {E : Type*} [Field E] (e : E →+* ℂ) (A : AddSubgroup E) :
    (∀ z ∈ A.map e.toAddMonoidHom, z ≠ 0 → 1 ≤ ‖z‖) ↔
    ∀ x ∈ A, x ≠ 0 → 1 ≤ ‖e x‖ := by
  constructor
  · intro h x hx h0
    exact h (e x) ⟨x, hx, rfl⟩ ((map_ne_zero e).mpr h0)
  · rintro h _ ⟨x, hx, rfl⟩ h0
    exact h x hx (fun he => h0 (by simp [he]))

private theorem image_stable_iff {E : Type*} [Field E] (e : E →+* ℂ) (O A : AddSubgroup E) :
    (∀ u ∈ O.map e.toAddMonoidHom, ∀ z ∈ A.map e.toAddMonoidHom, u * z ∈ A.map e.toAddMonoidHom) ↔
    ∀ a ∈ O, ∀ x ∈ A, a * x ∈ A := by
  constructor
  · intro h a ha x hx
    obtain ⟨y, hy, he⟩ := h (e a) ⟨a, ha, rfl⟩ (e x) ⟨x, hx, rfl⟩
    exact (e.injective (he.trans (e.map_mul a x).symm)) ▸ hy
  · rintro h _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨a * x, h a ha x hx, e.map_mul _ _⟩

/-- For an imaginary quadratic field the admissible indices are an initial interval determined
by its discriminant alone. The minimum is exactly the weighted condition used by Core 26. -/
theorem imaginary_quadratic_weighted_index_spectrum (K : Type*) [Field K] [NumberField K]
    [IsTotallyComplex K] (hK : finrank ℚ K = 2) (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 < c v)
    (n : ℕ) :
    let O := (algebraMap (𝓞 K) K).toAddMonoidHom.range
    let d := (NumberField.discr K).natAbs
    (∃ A : AddSubgroup K, O ≤ A ∧ O.relIndex A = n ∧
      ∀ a ∈ A, a ≠ 0 → ∑ v, c v ≤ ∑ v, c v * ‖v.embedding a‖ ^ 2) ↔
      0 < n ∧ n ≤ QuadraticIndex.maximum d d := by
  classical
  let O := (algebraMap (𝓞 K) K).toAddMonoidHom.range
  let d := (NumberField.discr K).natAbs
  let v : InfinitePlace K := Classical.arbitrary _
  let e := v.embedding
  obtain ⟨w, t, _, hr, hi, hpar, _, _, hO⟩ := integral_period_of_imaginary_quadratic K hK e
  have hd : 0 < d := Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  have hdi : (d : ℤ) = |NumberField.discr K| := Int.natCast_natAbs _
  have ht : t % 2 = (d : ℤ) % 2 := hdi ▸ hpar
  have hmax : QuadraticIndex.maximum d t = QuadraticIndex.maximum d d := by
    simp only [QuadraticIndex.maximum, ht]
  have hl := exists_overgroup_index_le_maximum_iff (n := n) hd hr
    (show (2 * w.im) ^ 2 = (d : ℝ) by simpa [d, Int.cast_abs] using hi)
  change O.map e.toAddMonoidHom = quadraticSpan w at hO
  rw [← hO, hmax] at hl
  simp_rw [weighted_minimum_iff_single_embedding K hK v c (hc v)]
  constructor
  · rintro ⟨A, hOA, hidx, hs⟩
    refine hl.mp ⟨A.map e.toAddMonoidHom, AddSubgroup.map_mono hOA, ?_, ?_⟩
    · rwa [AddSubgroup.relIndex_map_map_of_injective _ _ e.injective]
    · exact (image_shortest_iff e A).mpr hs
  · intro h
    have ht := finite_index_subgroups_image e O h.1 (fun L => ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖)
    simp_rw [image_shortest_iff] at ht
    exact ht.mpr (hl.mpr h)

/-- The possible indices of integer-stable overgroups in which 1 is shortest,
computed from the field discriminant by the reduced integral quadratic form criterion. -/
theorem imaginary_quadratic_stable_index_spectrum (K : Type*) [Field K] [NumberField K]
    [IsTotallyComplex K] (hK : finrank ℚ K = 2) (c : InfinitePlace K → ℝ)
    (hc : ∀ v, 0 < c v) (n : ℕ) :
    let O := (algebraMap (𝓞 K) K).toAddMonoidHom.range
    (∃ A : AddSubgroup K, O ≤ A ∧ O.relIndex A = n ∧
      (∀ x ∈ A, x ≠ 0 → ∑ v, c v ≤ ∑ v, c v * ‖v.embedding x‖^2) ∧
      (∀ a ∈ O, ∀ x ∈ A, a * x ∈ A)) ↔
      n ∈ StableQuadraticIndex.indices (NumberField.discr K).natAbs := by
  classical
  let O := (algebraMap (𝓞 K) K).toAddMonoidHom.range
  let d := (NumberField.discr K).natAbs
  let v : InfinitePlace K := Classical.arbitrary _
  let e := v.embedding
  obtain ⟨w,t,q,hr,hi,_,hw,hdq,hO⟩ := integral_period_of_imaginary_quadratic K hK e
  have hd : 0 < d := Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  have hdi : (d : ℤ) = |NumberField.discr K| := Int.natCast_natAbs _
  have him : (2 * w.im)^2 = ((d : ℤ) : ℝ) := by simpa [hdi] using hi
  have hp : (d : ℤ) = 4 * q - t^2 := hdi.trans hdq
  change O.map e.toAddMonoidHom = quadraticSpan w at hO
  by_cases hn : 0 < n
  · have geom := exists_stable_overgroup_index_iff hn (by exact_mod_cast hd) hr him hw hp
    have htransport := finite_index_subgroups_image e O hn
      (fun L => (∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) ∧ ∀ u ∈ O.map e.toAddMonoidHom, ∀ z ∈ L, u*z ∈ L)
    simp_rw [image_shortest_iff, image_stable_iff, hO, quadraticSpan_order_stable_iff] at htransport
    simp_rw [weighted_minimum_iff_single_embedding K hK v c (hc v)]
    exact htransport.trans (geom.trans (StableQuadraticIndex.criterion_iff_mem hn hp))
  · constructor
    · rintro ⟨A, hOA, hidx, hmin, _⟩
      have h := (imaginary_quadratic_weighted_index_spectrum K hK c hc n).mp ⟨A, hOA, hidx, hmin⟩
      exact False.elim (hn h.1)
    · intro hx
      exact False.elim (hn (StableQuadraticIndex.mem_indices.mp hx).1)

end GroundTheory.Heights₂.Heights.FiniteCovolume
