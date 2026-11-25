module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeValueInterpolation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterFiniteOrderValuesInField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemField

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.GridField
variable {E : Type} [Field E] [NumberField E]

/-- A single positive rational integer clears the denominator and every finite level. -/
theorem exists_ray_sample_step (b : E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (m : HeightOneSpectrum (𝓞 E) → ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 E)), v ∈ S →
      v.valuation E ((t : E) * M * b) ≤ WithZero.exp (-((m v : ℤ) + 1)) := by
  classical
  have hb : IsAlgebraic ℤ b := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ b)
  obtain ⟨d, a, hd, ha⟩ := hb.exists_nsmul_eq (𝓞 E)
  rw [nsmul_eq_mul, ← RingOfIntegers.coe_eq_algebraMap] at ha
  let J := ∏ v ∈ S, v.asIdeal ^ (m v + 1)
  have hJ : J ≠ ⊥ := Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  refine ⟨d * J.absNorm, Nat.mul_pos (Nat.pos_of_ne_zero hd)
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)), ?_⟩
  intro t v hv
  have hle : J ≤ v.asIdeal ^ (m v + 1) := Ideal.prod_le_inf.trans (Finset.inf_le hv)
  have hmem := (v.asIdeal ^ (m v + 1)).mul_mem_left ((t : 𝓞 E) * a) (hle J.absNorm_mem)
  have heq : (t : E) * (d * J.absNorm : ℕ) * b =
      algebraMap (𝓞 E) E ((t * a) * (J.absNorm : 𝓞 E)) := by
    calc
      _ = (t : E) * (d * b) * J.absNorm := by push_cast; ring
      _ = _ := by rw [ha]; push_cast; rfl
  rw [heq, v.valuation_of_algebraMap]
  simpa using (v.intValuation_le_pow_iff_mem _ _).mpr hmem

/-- At most one integral sample is excluded when turning these elements into units. -/
theorem ray_samples_nonzero {b : E} (M : ℕ) :
    {t : ℕ | 1 + (t : E) * M * b = 0}.Subsingleton := by
  by_cases h : (M : E) * b = 0
  · simp [mul_assoc, h]
  · intro t _ s _
    rename_i ht hs
    change 1 + (t : E) * M * b = 0 at ht
    change 1 + (s : E) * M * b = 0 at hs
    rw [mul_assoc] at ht hs
    exact_mod_cast mul_right_cancel₀ h (add_left_cancel (ht.trans hs.symm))

open Formalism.L2.Host
open HeckeCharacterValueBounds.GlobalTheory.CompanionTheory.CharValues

/-- Enlarge the ray modulus by any finite excluded set; the product formula then
uses only the remaining good uniformizers. -/
theorem exists_ray_samples_inf_mem_off (χ : HChar E) {C : Type} [Field C] (e : C →+* ℂ)
    (bad : Finset (HeightOneSpectrum (𝓞 E)))
    (hval : ∀ v, v ∉ bad → χ.UnrAt v → (χ.val v : ℂ) ∈ e.fieldRange) (k : E) :
    ∃ M : ℕ, 0 < M ∧ ∀ (t : ℕ) (hu : 1 + (t : E) * M * (k - 1) ≠ 0),
      (χ.inf (Units.mk0 _ hu) : ℂ) ∈ e.fieldRange := by
  classical
  let S := bad ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have off (v) (hv : v ∉ S) : v ∉ bad ∧ χ.UnrAt v := by simpa [S, not_or] using hv
  have hunr (v) (hv : v ∉ S) : χ.UnrAt v := (off v hv).2
  choose m hm using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  obtain ⟨M, hM, hstep⟩ := exists_ray_sample_step (k-1) S m
  refine ⟨M, hM, fun t hu => ?_⟩
  let u := Units.mk0 _ hu
  have hloc (v) (hv : v ∈ S) : χ.locK v u = 1 := by
    have h := hstep t v hv
    have heq := locK_eq_of_level χ (hm v) 1 u
    apply (heq ?_).trans (map_one _)
    simpa [u] using h
  let H := GlobalTheory.TameVal.unitsIn e.fieldRange
  have hval' (v) (hv : v ∉ S) : χ.val v ∈ H := hval v (off v hv).1 (hunr v hv)
  have hprod : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v u) ∈ H :=
    finprod_induction (· ∈ H) H.one_mem (fun _ _ => H.mul_mem) fun v =>
      finprod_induction (· ∈ H) H.one_mem (fun _ _ => H.mul_mem) fun hv =>
        H.zpow_mem (hval' v hv) _
  have hpr := GlobalTheory.TypeValues.productRule χ S hunr u
  rw [Finset.prod_eq_one hloc, mul_one] at hpr
  exact (H.mul_mem_cancel_right hprod).mp (hpr ▸ H.one_mem)

/-- Ordinary unramified values suffice when no extra places are excluded. -/
theorem exists_ray_samples_inf_mem (χ : HChar E) {C : Type} [Field C] (e : C →+* ℂ)
    (hval : χ.ValuesIn 0 e) (k : E) :
    ∃ M : ℕ, 0 < M ∧ ∀ (t : ℕ) (hu : 1 + (t : E) * M * (k - 1) ≠ 0),
      (χ.inf (Units.mk0 _ hu) : ℂ) ∈ e.fieldRange := by
  apply exists_ray_samples_inf_mem_off χ e ∅ _ k
  intro v _ hv
  obtain ⟨y, hy⟩ := hval v hv
  exact RingHom.mem_fieldRange.mpr ⟨y, by simpa [HChar.valTw] using hy⟩

end GlobalTheory.GridField

open Formalism.L2.Host

namespace GlobalTheory.RelativeGrid

theorem hasInfQ_rational_line {L : Type} [Field L] [NumberField L] {I : Type} [Fintype I]
    {χ : HChar L} (φ : I → L →+* ℂ) (b : I → ℤ)
    (hinf : χ.HasInfQ φ (fun i => (b i : ℚ))) (k : Lˣ) {M : ℕ} (hM : M ≠ 0) :
    RationalArchLine (fun u => (χ.inf u : ℂ)) k M (∑ i, (b i).natAbs) := by
  obtain ⟨n, hn, hphase⟩ := hinf
  have h : n = (fun i => 2*b i) := funext fun i => by
    have hi : (n i : ℚ) = 2*(b i : ℚ) := hn i
    exact_mod_cast hi
  subst n
  exact rationalArchLine_of_even_phase φ b _ hphase k hM

end GlobalTheory.RelativeGrid

open GlobalTheory.RelativeGrid GlobalTheory.GridField Polynomial

namespace GridInterpolation

private theorem line_values_mem (F : IntermediateField ℚ ℂ) (P Q : ℂ[X]) (s : Set ℕ)
    (hs : s.Infinite) (h : ∀ n ∈ s, Q.eval (n : ℂ) ≠ 0 ∧ P.eval (n : ℂ) / Q.eval (n : ℂ) ∈ F)
    (x : ℚ) (hx : Q.eval (x : ℂ) ≠ 0) : P.eval (x : ℂ) / Q.eval (x : ℂ) ∈ F := by
  let pts := (fun n : ℕ => (n : F)) '' s
  have hinf : pts.Infinite := hs.image Nat.cast_injective.injOn
  have hh (a : F) (ha : a ∈ pts) :
      ∃ c : F, P.eval (algebraMap F ℂ a) = c • Q.eval (algebraMap F ℂ a) := by
    obtain ⟨n, hn, rfl⟩ := ha
    obtain ⟨hq, hf⟩ := h n hn
    refine ⟨⟨_,hf⟩, ?_⟩
    rw [Algebra.smul_def]
    change P.eval ((n : F) : ℂ) = (P.eval (n : ℂ) / Q.eval (n : ℂ)) * Q.eval ((n : F) : ℂ)
    simpa using (div_mul_cancel₀ (P.eval (n : ℂ)) hq).symm
  obtain ⟨c, hc⟩ := value_descends P Q pts hinf hh (x : F) (by simpa using hx)
  have he : P.eval (x : ℂ) / Q.eval (x : ℂ) = (c : ℂ) := by simpa using hc
  exact he ▸ c.property

/-- For even phase weights, good-prime values outside any prescribed finite set
force the principal infinity values to lie in the same field. -/
theorem infinity_mem_of_good_off {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (F : IntermediateField ℚ ℂ) (bad : Finset (HeightOneSpectrum (𝓞 E)))
    (hval : ∀ v, v ∉ bad → χ.UnrAt v → (χ.val v : ℂ) ∈ F)
    {I : Type} [Fintype I] (φ : I → E →+* ℂ) (b : I → ℤ) (hi : χ.HasInfQ φ (fun i => (b i : ℚ)))
    (k : Eˣ) : (χ.inf k : ℂ) ∈ F := by
  obtain ⟨M, hM, hm⟩ := exists_ray_samples_inf_mem_off χ F.val.toRingHom bad
    (fun v hv hu => RingHom.mem_fieldRange.mpr ⟨⟨_, hval v hv hu⟩, rfl⟩) (k:E)
  obtain ⟨P,Q,_,_,hline,_,hQ,hk⟩ := hasInfQ_rational_line φ b hi k hM.ne'
  let S := {t : ℕ | 1 + (t : E) * M * ((k : E) - 1) ≠ 0}
  have hS : S.Infinite :=
    (ray_samples_nonzero (b := (k:E)-1) M).finite.infinite_compl
  dsimp only at hk
  rw [hk]
  have ht (n : ℕ) (hn : n ∈ S) : Q.eval (n : ℂ) ≠ 0 ∧ P.eval (n : ℂ) / Q.eval (n : ℂ) ∈ F := by
    let u := Units.mk0 _ hn
    obtain ⟨_, hq, he⟩ := hline (n : ℚ) u (by simp [u,mul_assoc])
    have hu : (χ.inf u : ℂ) ∈ F := by
      obtain ⟨y,hy⟩ := RingHom.mem_fieldRange.mp (hm n hn)
      exact hy ▸ y.property
    simp only [Rat.cast_natCast] at hq he
    exact ⟨hq, he ▸ hu⟩
  simpa using line_values_mem F P Q S hS ht (M:ℚ)⁻¹ (by simpa using hQ)

theorem infinity_mem_of_values {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (F : IntermediateField ℚ ℂ) (hval : χ.ValuesIn 0 F.val.toRingHom)
    {I : Type} [Fintype I] (φ : I → E →+* ℂ) (b : I → ℤ) (hi : χ.HasInfQ φ (fun i => (b i : ℚ)))
    (k : Eˣ) : (χ.inf k : ℂ) ∈ F := by
  exact infinity_mem_of_good_off χ F ∅
    (fun _ _ hv => GlobalTheory.HeckeValField.val_mem χ (GlobalTheory.Mem.Fld.valueField_le_iff.mpr hval) hv) φ b hi k

open HeckeCharacterValueBounds.GlobalTheory.CompanionTheory.CharValues

/-- All uniformizer values are in the group if this holds for the diagonal infinity values
and at all unramified places outside a prescribed finite set. -/
theorem val_mem_of_good_off {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (G : Subgroup ℂˣ) (hinf : ∀ k : Eˣ, χ.inf k ∈ G)
    (bad : Finset (HeightOneSpectrum (𝓞 E))) (h : ∀ v, v ∉ bad → χ.UnrAt v → χ.val v ∈ G)
    (p : HeightOneSpectrum (𝓞 E)) : χ.val p ∈ G := by
  classical
  let S := bad ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have off (v) (hv : v ∉ S) : v ∉ bad ∧ χ.UnrAt v := by simpa [S, not_or] using hv
  exact locK_mem χ G S (fun v hv => (off v hv).2) (fun v hv => h v (off v hv).1 (off v hv).2)
    hinf p (unif p)

/-- For even algebraic phases, removing any finite set of good primes does not
change the field-membership test: the omitted good-prime values are forced. -/
theorem valuesIn_iff_good_off {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (F : IntermediateField ℚ ℂ) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (b : I → ℤ)
    (hi : χ.HasInfQ φ (fun i => (b i : ℚ))) (bad : Finset (HeightOneSpectrum (𝓞 E))) :
    χ.ValuesIn 0 F.val.toRingHom ↔ ∀ v, v ∉ bad → χ.UnrAt v → (χ.val v : ℂ) ∈ F := by
  constructor
  · intro h _ _ hv
    exact GlobalTheory.HeckeValField.val_mem χ (GlobalTheory.Mem.Fld.valueField_le_iff.mpr h) hv
  · intro h p _
    have hp := val_mem_of_good_off χ (GlobalTheory.HeckeValField.unitsIn F)
      (infinity_mem_of_good_off χ F bad h φ b hi) bad h p
    exact ⟨⟨_, hp⟩, by simp [HChar.valTw]⟩

/-- Removing any finite set of places leaves the actual untwisted character-value field unchanged. -/
theorem adjoin_good_off_eq_valueField {E : Type} [Field E] [NumberField E] (χ : HChar E)
    {I : Type} [Fintype I] (φ : I → E →+* ℂ) (b : I → ℤ) (hi : χ.HasInfQ φ (fun i => (b i : ℚ)))
    (bad : Finset (HeightOneSpectrum (𝓞 E))) :
    IntermediateField.adjoin ℚ {z : ℂ | ∃ v, v ∉ bad ∧ χ.UnrAt v ∧ (χ.val v : ℂ) = z} =
      GlobalTheory.Mem.Fld.valueField χ 0 := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨v, _, hv, rfl⟩
    exact GlobalTheory.HeckeValField.val_mem χ le_rfl hv
  · apply GlobalTheory.Mem.Fld.valueField_le_iff.mpr
    apply (valuesIn_iff_good_off χ _ φ b hi bad).mpr
    intro v hv hu
    exact IntermediateField.subset_adjoin ℚ _ ⟨v, hv, hu, rfl⟩

/-- All finite local values, including those at ramified places, lie in the prescribed field. -/
theorem local_mem_of_values {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (F : IntermediateField ℚ ℂ) (hval : χ.ValuesIn 0 F.val.toRingHom)
    {I : Type} [Fintype I] (φ : I → E →+* ℂ) (b : I → ℤ) (hi : χ.HasInfQ φ (fun i => (b i : ℚ)))
    (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ) : (χ.loc v y : ℂ) ∈ F :=
  GlobalTheory.HeckeValField.loc_mem χ (GlobalTheory.Mem.Fld.valueField_le_iff.mpr hval)
    (infinity_mem_of_values χ F hval φ b hi) v y

/-- The same field contains each idèle value with trivial archimedean component. -/
theorem finite_idele_mem_of_values {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (F : IntermediateField ℚ ℂ) (hval : χ.ValuesIn 0 F.val.toRingHom)
    {I : Type} [Fintype I] (φ : I → E →+* ℂ) (b : I → ℤ) (hi : χ.HasInfQ φ (fun i => (b i : ℚ)))
    (x : (AdeleRing (𝓞 E) E)ˣ) (hx : ∀ w : InfinitePlace E, x.val.1 w = 1) :
    ((χ.1 x : ℂˣ) : ℂ) ∈ F :=
  GlobalTheory.HeckeValField.mem_of_inf_eq_one E χ F (GlobalTheory.Mem.Fld.valueField_le_iff.mpr hval)
    (infinity_mem_of_values χ F hval φ b hi) x hx

/-- For characters with matching infinity values on principal elements, a finite
set of excluded primes and both ramification sets may be skipped when testing ratios. -/
theorem ratio_units_mem_of_good_off {E : Type} [Field E] [NumberField E] (χ ψ : HChar E)
    (hinf : ∀ k : Eˣ, χ.inf k = ψ.inf k) (bad : Finset (HeightOneSpectrum (𝓞 E)))
    (G : Subgroup ℂˣ) (hgood : ∀ p, p ∉ bad → χ.UnrAt p → ψ.UnrAt p →
      χ.val p / ψ.val p ∈ G) (p : HeightOneSpectrum (𝓞 E)) :
    χ.val p / ψ.val p ∈ G := by
  classical
  let S := bad ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset ∪
    (GlobalTheory.Mem.UnrAe.finite_ramified ψ).toFinset
  have off (v) (hv : v ∉ S) : v ∉ bad ∧ χ.UnrAt v ∧ ψ.UnrAt v := by
    simpa [S, not_or, and_assoc] using hv
  let r := χ * ψ⁻¹
  have hin (k : Eˣ) : r.inf k ∈ G := by
    change (χ * ψ⁻¹).inf k ∈ G
    rw [HChar.inf_mul, HChar.inf_inv, hinf k, mul_inv_cancel]
    exact G.one_mem
  have hval (v) (hv : v ∉ S) (_ : r.UnrAt v) : r.val v ∈ G := by
    simpa [r, HChar.val, HChar.locK, HChar.loc, div_eq_mul_inv] using
      hgood v (off v hv).1 (off v hv).2.1 (off v hv).2.2
  have hh := val_mem_of_good_off r G hin S hval p
  simpa [r, HChar.val, HChar.locK, HChar.loc, div_eq_mul_inv] using hh

/-- The subgroup test specialized to the units of a prescribed complex field. -/
theorem ratio_mem_of_good_off {E : Type} [Field E] [NumberField E] (χ ψ : HChar E)
    (hinf : ∀ k : Eˣ, χ.inf k = ψ.inf k) (bad : Finset (HeightOneSpectrum (𝓞 E)))
    (F : IntermediateField ℚ ℂ) (hgood : ∀ p, p ∉ bad → χ.UnrAt p → ψ.UnrAt p →
      (χ.val p : ℂ) / (ψ.val p : ℂ) ∈ F) (p : HeightOneSpectrum (𝓞 E)) :
    (χ.val p : ℂ) / (ψ.val p : ℂ) ∈ F := by
  have h := ratio_units_mem_of_good_off χ ψ hinf bad (GlobalTheory.HeckeValField.unitsIn F)
    (fun v hv hu hw => GlobalTheory.HeckeValField.mem_unitsIn.mpr (by simpa using hgood v hv hu hw)) p
  simpa using GlobalTheory.HeckeValField.mem_unitsIn.mp h

end GridInterpolation
