module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.DefGroup

@[expose] public section

noncomputable section

namespace GlobalTheory.CovTop.LevelIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

theorem index_comap_le {K G : Type*} [Group K] [Group G] [Finite G] (f : K →* G) (H : Subgroup G) :
    (H.comap f).index ≠ 0 ∧ (H.comap f).index ≤ Nat.card G := by
  rw [Subgroup.index_comap, Subgroup.relIndex]
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  exact (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)).trans
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _))

section Gen

variable {E : Type} [Field E] [NumberField E]

instance finite_kP (PP : Pl E) : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

theorem card_GL_le (R : Type) [CommRing R] [Finite R] (r : ℕ) : Nat.card (GL (Fin r) R) ≤ Nat.card R ^ (r ^ 2) := by
  simpa [Matrix.card_matrix, sq] using
    (Nat.card_le_card_of_injective (Units.val : GL (Fin r) R → Matrix (Fin r) (Fin r) R) Units.val_injective)

/-- Exact order of the ambient product of the residue-field level groups. -/
theorem card_levelQuotientGroup_eq (Pg : Finset (Pl E)) (r : ℕ) :
    Nat.card (G0 Pg r) = ∏ P ∈ Pg, ∏ i : Fin r,
      (Ideal.absNorm P.asIdeal ^ r - Ideal.absNorm P.asIdeal ^ (i : ℕ)) := by
  rw [Nat.card_pi, ← Finset.prod_coe_sort Pg]
  apply Finset.prod_congr rfl
  intro P _
  let : Field (kP P.1) := Ideal.Quotient.field _
  let : Fintype (kP P.1) := Fintype.ofFinite _
  simpa [Ideal.absNorm_eq_natCard, Nat.card_eq_fintype_card] using Matrix.card_GL_field (𝔽 := kP P.1) r

theorem card_levelQuotientGroup_le_prod_absNorm_pow_sq (Pg : Finset (Pl E)) (r : ℕ) :
    Nat.card (G0 Pg r) ≤ (∏ PP ∈ Pg, Ideal.absNorm PP.asIdeal) ^ (r ^ 2) := by
  rw [card_levelQuotientGroup_eq, ← Finset.prod_pow]
  refine Finset.prod_le_prod fun P _ => ?_
  calc
    _ ≤ ∏ _ : Fin r, Ideal.absNorm P.asIdeal ^ r := Finset.prod_le_prod fun i _ => Nat.sub_le _ _
    _ = _ := by simp [← pow_mul, sq]

/-- The former unrestricted matrix-count bound is strict at positive rank and nonempty level. -/
theorem card_levelQuotientGroup_lt (Pg : Finset (Pl E)) (hPg : Pg.Nonempty) {r : ℕ} (hr : 0 < r) :
    Nat.card (G0 Pg r) < (∏ P ∈ Pg, Ideal.absNorm P.asIdeal) ^ (r^2) := by
  let : NeZero r := ⟨hr.ne'⟩
  let : Nonempty ↥Pg := hPg.to_subtype
  rw [Nat.card_pi, ← Finset.prod_pow, ← Finset.prod_coe_sort Pg]
  apply Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => Nat.card_pos) _ Finset.univ_nonempty
  intro P _
  calc
    Nat.card (GL (Fin r) (kP P.1)) < Nat.card (Matrix (Fin r) (Fin r) (kP P.1)) :=
      natCard_units_lt _
    _ = Ideal.absNorm P.1.asIdeal ^ (r^2) := by
      simp [Matrix.card_matrix, Ideal.absNorm_eq_natCard, sq]

theorem prod_absNorm_le (Pg : Finset (Pl E)) {N : ℕ} (hN : N ≠ 0) (h : ∀ PP ∈ Pg, ((N : ℕ) : 𝓞 E) ∈ PP.asIdeal) :
    ∏ PP ∈ Pg, Ideal.absNorm PP.asIdeal ≤ N ^ Module.finrank ℚ E := by
  have hd : ∏ PP ∈ Pg, PP.asIdeal ∣ Ideal.span {((N : ℕ) : 𝓞 E)} := by
    refine Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ => ?_) fun PP hP => Ideal.dvd_span_singleton.2 (h PP hP)
    exact Ideal.isCoprime_iff_sup_eq.2 (P.isMaximal.coprime_of_ne Q.isMaximal fun e => hPQ (HeightOneSpectrum.ext e))
  have h2 := map_dvd Ideal.absNorm hd
  rw [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h2
  exact Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hN) _) h2

variable {F : Type} [Field F] [NumberField F] [StarRing E] [Algebra F E] {n : ℕ} {LL : Type} [CommRing LL]


open scoped TensorProduct

/-- Only the image of reduction is relevant: no surjectivity assumption is needed. -/
theorem relIndex_lev_eq_image (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    (lev hc J β L).relIndex (parLev hc J β L) = L.P.H.relIndex (rHom hc J β L).range := by
  have e : (lev hc J β L).subgroupOf (parLev hc J β L) = L.P.H.comap (rHom hc J β L) := by
    ext x
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  rw [Subgroup.relIndex, e, Subgroup.index_comap]

/-- The ambient estimate is divided by the order of the selected residue-level group. -/
theorem relIndex_lev_mul_card_le (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    (lev hc J β L).relIndex (parLev hc J β L) * Nat.card L.P.H ≤
      ∏ P ∈ L.Pg, ∏ i : Fin L.r, (Ideal.absNorm P.asIdeal ^ L.r - Ideal.absNorm P.asIdeal ^ (i : ℕ)) := by
  rw [← card_levelQuotientGroup_eq, relIndex_lev_eq_image, ← L.P.H.index_mul_card]
  gcongr
  rw [← L.P.H.relIndex_top_right]
  exact Subgroup.relIndex_le_of_le_right le_top (by simp [Subgroup.index_ne_zero_of_finite])


/-- When the reduction is onto, the index times the subgroup order is exactly the ambient order. -/
theorem relIndex_lev_mul_card_eq_of_surjective (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n)
    (hf : Function.Surjective (rHom hc J β L)) :
    (lev hc J β L).relIndex (parLev hc J β L) * Nat.card L.P.H =
      ∏ P ∈ L.Pg, ∏ i : Fin L.r, (Ideal.absNorm P.asIdeal ^ L.r - Ideal.absNorm P.asIdeal ^ (i : ℕ)) := by
  rw [relIndex_lev_eq_image, MonoidHom.range_eq_top_of_surjective _ hf, Subgroup.relIndex_top_right,
    Subgroup.index_mul_card, card_levelQuotientGroup_eq]

open scoped TensorProduct in
theorem relIndex_lev_le (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n)
    (B : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (hB : B = parLev hc J β L) :
    (lev hc J β L).relIndex B ≠ 0 ∧ (lev hc J β L).relIndex B ≤ Nat.card (G0 L.Pg L.r) := by
  subst hB
  rw [relIndex_lev_eq_image, ← Subgroup.index_comap]
  exact index_comap_le _ _

open scoped TensorProduct in
theorem lev_full (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    lev hc J β { L with P := LevelP.full L.Pg L.r LL } = parLev hc J β L := by
  ext x
  exact ⟨fun h => h.1, fun h => ⟨h, Subgroup.mem_top _⟩⟩

end Gen

end GlobalTheory.CovTop.LevelIndex

end
