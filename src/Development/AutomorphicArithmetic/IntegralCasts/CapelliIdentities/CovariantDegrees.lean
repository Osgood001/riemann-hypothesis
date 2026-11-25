module

public import Mathlib

@[expose] public section

noncomputable section

namespace UpperTheory.Reformulated.B.CovariantDegrees

open Pointwise

abbrev G (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] := Ω ≃ₐ[F] Ω

def Dec {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) :
    Subgroup (G F Ω) :=
  A.decompositionSubgroup F

abbrev GQ (l : ℕ) [Fact l.Prime] := PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l

variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  (j : Ω →+* PadicAlgCl l)

def jE : E →+* PadicAlgCl l := j.comp (algebraMap E Ω)

def KwF : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => jE (E := E) j (Module.finBasis ℚ E i))

theorem jE_mem (x : E) : jE j x ∈ KwF (E := E) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (Module.finBasis ℚ E).sum_repr x, map_sum]
  refine IntermediateField.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, eq_ratCast (algebraMap ℚ E), map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin ℚ_[l] _ ⟨i, rfl⟩)

variable [CharZero Ω] [IsAlgClosure ℚ Ω]

omit [Algebra E Ω] [NumberField E] [Field E] in
def resQ (σ : GQ l) : Ω ≃ₐ[ℚ] Ω :=
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  AlgHom.restrictNormal' ((σ.restrictScalars ℚ : PadicAlgCl l ≃ₐ[ℚ] PadicAlgCl l) :
    PadicAlgCl l →ₐ[ℚ] PadicAlgCl l) Ω

omit [Algebra E Ω] [NumberField E] [Field E] in
theorem j_resQ (σ : GQ l) (x : Ω) : j (resQ j σ x) = σ (j x) := by
  let : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  have : IsScalarTower ℚ Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  exact AlgHom.restrictNormal_commutes _ Ω x

def resE (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) : G E Ω :=
  AlgEquiv.ofRingEquiv (f := (resQ j σ).toRingEquiv) fun x => j.injective (by
    show j (resQ j σ (algebraMap E Ω x)) = _
    rw [j_resQ]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ (jE_mem j x))

theorem j_resE (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j (resE j σ hσ x) = σ (j x) := j_resQ j σ x

variable {j} {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

include hj in
theorem resE_mem (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) :
    resE j σ hσ ∈ Dec (F := E) A := by
  have hn : ∀ x, ‖j (resE j σ hσ x)‖ = ‖j x‖ := fun x => by
    rw [j_resE]
    exact (spectralNorm_eq_of_equiv σ (j x)).symm
  refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hj, hj, ← hn]
  simp

def rHom : ↥(KwF (E := E) j).fixingSubgroup →* ↥(Dec (F := E) A) where
  toFun σ := ⟨resE j σ.1 σ.2, resE_mem hj σ.1 σ.2⟩
  map_one' := Subtype.ext (AlgEquiv.ext fun x => j.injective (j_resE j _ (Subgroup.one_mem _) x))
  map_mul' σ τ := Subtype.ext (AlgEquiv.ext fun x => j.injective ((j_resE j _ (σ * τ).2 x).trans
    ((congrArg (σ : GQ l) (j_resE j _ τ.2 x)).symm.trans (j_resE j _ σ.2 _).symm)))

theorem continuous_rHom : Continuous (rHom (E := E) hj) := by
  have h : Continuous ((Dec A).subtype.comp (rHom (E := E) hj)) := by
    apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).1 hs
    let b := Module.finBasis E L
    have hU : ∀ᶠ σ : (KwF (E := E) j).fixingSubgroup in nhds 1, ∀ i, σ.1 (j (b i)) = j (b i) := by
      refine Filter.eventually_all.2 fun i => ?_
      have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) (j (b i))).preimage
        (continuous_subtype_val (p := fun σ => σ ∈ (KwF (E := E) j).fixingSubgroup))
      exact ho.mem_nhds (Subgroup.one_mem (MulAction.stabilizer _ _))
    refine hU.mono fun σ hσ => hLs ?_
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have key : (resE j σ.1 σ.2).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
      b.ext fun i => j.injective ((j_resE j σ.1 σ.2 (b i)).trans (hσ i))
    exact LinearMap.congr_fun key ⟨x, hx⟩
  exact continuous_induced_rng.2 h

end UpperTheory.Reformulated.B.CovariantDegrees
