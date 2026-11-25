module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Matrix ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SwFinM

section Scale

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

def mulVecHomeo (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) : (Fin n → R) ≃ₜ (Fin n → R) where
  toFun x := A *ᵥ x
  invFun x := Ai *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, h2]
  right_inv x := by simp [Matrix.mulVec_mulVec, h1]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def mulVecCAE (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) : (Fin n → R) ≃ₜ+ (Fin n → R) :=
  { (mulVecHomeo A Ai h1 h2).toEquiv with
    map_add' := fun x y => Matrix.mulVec_add A x y
    continuous_toFun := (mulVecHomeo A Ai h1 h2).continuous
    continuous_invFun := (mulVecHomeo A Ai h1 h2).symm.continuous }

-- The original public signature includes the ambient measure and topology instances.
theorem image_eq_preimage {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}
    (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) (S : Set (Fin n → R)) :
    (fun x => A *ᵥ x) '' S = (fun x => Ai *ᵥ x) ⁻¹' S := by
  exact (mulVecHomeo A Ai h1 h2).image_eq_preimage_symm S

theorem exists_scale (lam : Measure (Fin n → R)) [lam.IsAddHaarMeasure] (A Ai : Matrix (Fin n) (Fin n) R)
    (h1 : A * Ai = 1) (h2 : Ai * A = 1) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : Set (Fin n → R), lam ((fun x => A *ᵥ x) '' S) = c * lam S := by
  let e : (Fin n → R) ≃ₜ+ (Fin n → R) := mulVecCAE Ai A h2 h1
  have hcoc : Filter.Tendsto (e : (Fin n → R) → (Fin n → R)) (Filter.cocompact _) (Filter.cocompact _) :=
    (mulVecHomeo Ai A h2 h1).isClosedEmbedding.tendsto_cocompact
  have : (lam.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map lam (e : (Fin n → R) →+ (Fin n → R)) e.continuous e.surjective hcoc
  have hsm := Measure.isAddLeftInvariant_eq_smul (lam.map e) lam
  set c : ℝ≥0 := (lam.map e).addHaarScalarFactor lam
  have hmap : ∀ S : Set (Fin n → R), (lam.map e) S = lam ((fun x => Ai *ᵥ x) ⁻¹' S) := fun S =>
    MeasurableEquiv.map_apply (mulVecHomeo Ai A h2 h1).toMeasurableEquiv S
  have key : ∀ S : Set (Fin n → R), lam ((fun x => A *ᵥ x) '' S) = (c : ℝ≥0∞) * lam S := by
    intro S
    rw [image_eq_preimage A Ai h1 h2, ← hmap, hsm]
    rfl
  exact ⟨c, ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (lam.map e) lam).ne',
    ENNReal.coe_ne_top, key⟩

end Scale

section Index

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

/-- Moving the left lattice and multiplying a matrix on the left have the same Haar scale.
Right multiplication can be transferred to the right lattice, even for a singular matrix. -/
theorem lattice_norm_matrix_transport (lam : Measure (Fin n → R)) [lam.IsAddHaarMeasure]
    (L₁ L₂ : AddSubgroup (Fin n → R)) (A Ai B Q : Matrix (Fin n) (Fin n) R)
    (h1 : A * Ai = 1) (h2 : Ai * A = 1) :
    PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (L₁.map (Matrix.mulVecLin A).toAddMonoidHom) L₂ (A * B * Q) =
      PositivityTheory.SiegelWeilFormula.Gen.nu2 lam L₁ (L₂.map (Matrix.mulVecLin Q).toAddMonoidHom) B := by
  obtain ⟨c, hc0, hct, hc⟩ := exists_scale lam A Ai h1 h2
  have hS : {z | ∃ y ∈ L₁.map (Matrix.mulVecLin A).toAddMonoidHom, ∃ y' ∈ L₂, z = y + (A * B * Q).mulVec y'} =
      (fun x => A *ᵥ x) '' {z | ∃ y ∈ L₁, ∃ y' ∈ L₂.map (Matrix.mulVecLin Q).toAddMonoidHom, z = y + B.mulVec y'} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image, AddSubgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, w, hw, rfl⟩
      refine ⟨y + B *ᵥ (Q *ᵥ w), ⟨y, hy, Q *ᵥ w, ⟨w, hw, rfl⟩, rfl⟩, ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · rintro ⟨_, ⟨y, hy, _, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      refine ⟨A *ᵥ y, ⟨y, hy, rfl⟩, w, hw, ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hL : ((L₁.map (Matrix.mulVecLin A).toAddMonoidHom : AddSubgroup (Fin n → R)) : Set _) =
      (fun x => A *ᵥ x) '' (L₁ : Set _) := rfl
  unfold PositivityTheory.SiegelWeilFormula.Gen.nu2
  rw [hS, hL, hc, hc, ENNReal.mul_div_mul_left _ _ hc0 hct]

end Index

end GlobalTheory.CompanionTheory.SwFinM

end
