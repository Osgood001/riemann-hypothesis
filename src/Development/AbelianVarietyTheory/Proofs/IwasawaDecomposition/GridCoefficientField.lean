module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid NumberField IsDedekindDomain

namespace GlobalTheory.BigTop.Fun

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}

/-- The smallest complex number field that can realize a fixed grid. -/
def gridCoefficientField (G : GridData Lc sc) : IntermediateField ℚ ℂ :=
  sInf {M : IntermediateField ℚ ℂ | FieldHas G M.val.toRingHom}

private theorem root_mem_of_contains_primitive {n : ℕ} [NeZero n] (K : IntermediateField ℚ ℂ)
    (h : ∃ y : K, IsPrimitiveRoot y n) {z : ℂ} (hz : z ^ n = 1) : z ∈ K := by
  obtain ⟨y, hy⟩ := h
  have hC := hy.map_of_injective (f := K.val) Subtype.val_injective
  obtain ⟨i, -, rfl⟩ := hC.eq_pow_of_pow_eq_one hz
  exact K.pow_mem y.property i

theorem gridCoefficientField_has (G : GridData Lc sc) : FieldHas G (gridCoefficientField G).val.toRingHom := by
  constructor
  · intro i hi hi' v hv
    refine ⟨⟨_, IntermediateField.mem_sInf.mpr fun M hM => ?_⟩, rfl⟩
    obtain ⟨y, hy⟩ := hM.values i hi hi' v hv
    change (G.ch.chiH i).valTw 0 v ∈ M
    rw [← hy]
    exact y.property
  · intro v hv
    let n := Ideal.absNorm v.asIdeal ^ G.pl.depth sc v
    have hn : 0 < n := pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
    have : NeZero n := ⟨hn.ne'⟩
    have hz := Complex.isPrimitiveRoot_exp n hn.ne'
    refine ⟨⟨_, IntermediateField.mem_sInf.mpr fun M hM => ?_⟩,
      IsPrimitiveRoot.of_map_of_injective (f := IntermediateField.val _) hz Subtype.val_injective⟩
    exact root_mem_of_contains_primitive M (hM.roots v hv) hz.pow_eq_one

theorem gridCoefficientField_le_iff (G : GridData Lc sc) (M : IntermediateField ℚ ℂ) :
    gridCoefficientField G ≤ M ↔ FieldHas G M.val.toRingHom := by
  refine ⟨fun h => ?_, fun h => sInf_le h⟩
  exact (gridCoefficientField_has G).map (IntermediateField.inclusion h).toRingHom

instance (G : GridData Lc sc) : FiniteDimensional ℚ (gridCoefficientField G) := by
  obtain ⟨M, hM, hv⟩ := exists_fieldHas G
  exact FiniteDimensional.of_injective (IntermediateField.inclusion ((gridCoefficientField_le_iff G M).mpr hv)).toLinearMap
    (IntermediateField.inclusion ((gridCoefficientField_le_iff G M).mpr hv)).injective

end GlobalTheory.BigTop.Fun

end
