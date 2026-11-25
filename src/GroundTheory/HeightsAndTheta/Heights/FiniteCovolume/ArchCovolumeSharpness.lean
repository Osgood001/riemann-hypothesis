module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StArchCovolumeBound
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.OfUnfolding
import Mathlib.GroupTheory.IndexNSmul

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic NumberField Module MeasureTheory

variable {F E W : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [AddCommGroup W] [Module E W]

theorem dualLattice_map_nsmul (h : HermitianForm F E W) (L : AddSubgroup W) (n : ℕ) :
    dualLattice h (L.map (nsmulAddMonoidHom n)) =
      (dualLattice h L).comap (nsmulAddMonoidHom n) := by
  ext y
  constructor
  · intro hy x hx
    have hp := hy _ (AddSubgroup.mem_map_of_mem (nsmulAddMonoidHom n) hx)
    simpa only [nsmulAddMonoidHom_apply, map_nsmul, LinearMap.smul_apply] using hp
  · intro hy x hx
    obtain ⟨z, hz, rfl⟩ := hx
    simpa only [nsmulAddMonoidHom_apply, map_nsmul, LinearMap.smul_apply] using hy z hz

variable [NumberField E]

theorem IsLattice.map_nsmul {L : AddSubgroup W} (hL : IsLattice E L)
    (n : ℕ) (hn : n ≠ 0) : IsLattice E (L.map (nsmulAddMonoidHom n)) := by
  have := hL.fg
  refine ⟨?_, inferInstanceAs (IsAddFG _), ?_⟩
  · rintro a x ⟨y, hy, rfl⟩
    exact ⟨(a : E) • y, hL.smul_mem a _ hy, smul_comm n (a : E) y⟩
  · apply top_unique
    rw [← hL.span_eq_top]
    apply Submodule.span_le.mpr
    intro x hx
    have hnx := Submodule.subset_span (R := E)
      (AddSubgroup.mem_map_of_mem (nsmulAddMonoidHom n) hx)
    have hnx' := (Submodule.span E ((L.map (nsmulAddMonoidHom n) : AddSubgroup W) : Set W)).smul_mem
      (n : E)⁻¹ hnx
    simpa [← Nat.cast_smul_eq_nsmul E, hn] using hnx'

theorem hermitian_relIndex_map_nsmul (h : HermitianForm F E W) {L : AddSubgroup W}
    (hint : IsIntegralOn h L) (hfg : L.FG) (n : ℕ) (hn : n ≠ 0) :
    (L.map (nsmulAddMonoidHom n)).relIndex (dualLattice h (L.map (nsmulAddMonoidHom n))) =
      n ^ (2 * finrank ℤ L) * L.relIndex (dualLattice h L) := by
  let f := nsmulAddMonoidHom (α := W) n
  let : Module.Finite ℤ L.toIntSubmodule :=
    Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg _).2 hfg)
  let : Module.IsTorsionFree ℤ W := .trans_faithfulSMul ℤ E W
  have hf := AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree (M := W) hn
  have hs : Function.Surjective f := fun x => ⟨(n : E)⁻¹ • x, by
    simp [f, ← Nat.cast_smul_eq_nsmul E, smul_smul, hn]⟩
  have hff : f.comp f = nsmulAddMonoidHom (α := W) (n ^ 2) := by
    ext x
    simp [f, smul_smul, pow_two]
  rw [dualLattice_map_nsmul]
  change (L.map f).relIndex ((dualLattice h L).comap f) = _
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.map_comap_eq_self_of_surjective hs, AddSubgroup.map_map, hff]
  rw [← AddSubgroup.relIndex_mul_relIndex _ L (dualLattice h L)
    (by rintro _ ⟨x, hx, rfl⟩; exact L.nsmul_mem hx (n ^ 2)) (fun x hx y hy => hint x hx y hy),
    AddSubgroup.relIndex_map_nsmul, pow_mul]

theorem IsDIntegral.map_nsmul {h : HermitianForm F E W} {L : AddSubgroup W}
    {D : ℕ} (hL : IsDIntegral h D L) (n : ℕ) (hn : n ≠ 0) :
    IsDIntegral h (n ^ (2 * finrank ℤ L) * L.relIndex (dualLattice h L)) (L.map (nsmulAddMonoidHom n)) := by
  have hindex := hermitian_relIndex_map_nsmul h hL.integral hL.isLattice.fg n hn
  refine ⟨hL.isLattice.map_nsmul n hn, ?_, ?_, hindex.le⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hL.integral _ (L.nsmul_mem hx n) _ (L.nsmul_mem hy n)
  · rw [hindex]
    exact mul_ne_zero (pow_ne_zero _ hn) hL.index_ne_zero

private theorem covolume_map_nsmul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (n : ℕ) (hn : n ≠ 0)
    (μ : Measure V) [μ.IsAddHaarMeasure] :
    ZLattice.covolume (L.map (DistribSMul.toLinearMap ℤ V n)) μ =
      (n : ℝ) ^ finrank ℤ L * ZLattice.covolume L μ := by
  classical
  let : IsTorsionFree ℤ V := .trans_faithfulSMul ℤ ℝ V
  let f := DistribSMul.toLinearMap ℤ V n
  have hf := AddSubgroup.distribSMulToLinearMap_injective_of_isTorsionFree (M := V) hn
  have hle : L.map f ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact L.nsmul_mem hx n
  let : DiscreteTopology (L.map f) := DiscreteTopology.of_subset
    (inferInstance : DiscreteTopology L) (show (L.map f : Set V) ⊆ L from hle)
  have : IsZLattice ℝ (L.map f) := by
    constructor
    apply top_unique
    rw [← IsZLattice.span_top (K := ℝ) (L := L)]
    apply Submodule.span_le.mpr
    intro x hx
    have hnx := Submodule.subset_span (R := ℝ) (show f x ∈ L.map f from ⟨x, hx, rfl⟩)
    have hi := (Submodule.span ℝ (L.map f : Set V)).smul_mem (n : ℝ)⁻¹ hnx
    change (n : ℝ)⁻¹ • (n • x) ∈ _ at hi
    simpa [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn] using hi
  let e := Submodule.equivMapOfInjective f hf L
  let b := Free.chooseBasis ℤ L
  let a := b.ofZLatticeBasis ℝ L
  rw [ZLattice.covolume_eq_det_mul_measureReal _ μ (b.map e) a,
    ZLattice.covolume_eq_det_mul_measureReal _ μ b a]
  have heq : ((↑) ∘ (b.map e) : _ → V) = (fun i => (n : ℝ) • (b i : V)) := by
    funext i
    change n • (b i : V) = _
    rw [Nat.cast_smul_eq_nsmul]
  rw [heq, a.det.map_smul_univ (fun _ => (n : ℝ)) (fun i => (b i : V))]
  simp [← finrank_eq_card_chooseBasisIndex, abs_mul, mul_assoc, Function.comp_def]

variable {ι : Type*} [Fintype ι]

theorem arch_covolume_homothetic (v : Basis ι E W) (L : AddSubgroup W)
    [DiscreteTopology (archLattice v L)] [IsZLattice ℝ (archLattice v L)] (n : ℕ) (hn : n ≠ 0) :
    ZLattice.covolume (archLattice v (L.map (nsmulAddMonoidHom n))) =
      (n : ℝ) ^ finrank ℤ L * ZLattice.covolume (archLattice v L) := by
  classical
  let V := InfinitePlace E → ι → ℂ
  let Ln := L.map (nsmulAddMonoidHom n)
  let A := archLattice v L
  have hAn : archLattice v Ln = A.map (DistribSMul.toLinearMap ℤ V n) := by
    apply Submodule.toAddSubgroup_injective
    change (Ln.map (vecAtHom v)) =
      (L.map (vecAtHom v)).map (nsmulAddMonoidHom n)
    dsimp only [Ln]
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext x
    simp
  have hv : Function.Injective (vecAtHom v) := by
    intro x y hxy
    apply v.repr.injective
    ext i
    let w : InfinitePlace E := Classical.arbitrary _
    exact w.embedding.injective (congrFun (congrFun hxy w) i)
  have hr := (L.equivMapOfInjective (vecAtHom v) hv).toIntLinearEquiv.finrank_eq
  rw [hAn, hr]
  let : (volume : Measure V).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact covolume_map_nsmul A n hn volume

/-- On the homotheties of any full positive-rank integral lattice the square-root
rate is attained at arbitrarily large *actual* dual indices. -/
theorem ArchCovolumeBound.sqrt_sharp_of_lattice (h : HermitianForm F E W) (v : Basis ι E W) {L : AddSubgroup W}
    {D : ℕ} (hL : IsDIntegral h D L) (hd : 0 < finrank ℤ L)
    [DiscreteTopology (archLattice v L)] [IsZLattice ℝ (archLattice v L)] :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ (M : AddSubgroup W) (I : ℕ), B < I ∧
      IsDIntegral h I M ∧ I = M.relIndex (dualLattice h M) ∧
      ZLattice.covolume (archLattice v M) = c * Real.sqrt I := by
  let J := L.relIndex (dualLattice h L)
  have hJ : 0 < J := Nat.pos_of_ne_zero hL.index_ne_zero
  let : (volume : Measure (InfinitePlace E → ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hJ' : 0 < Real.sqrt J := Real.sqrt_pos.2 (by exact_mod_cast hJ)
  refine ⟨ZLattice.covolume (archLattice v L) / Real.sqrt J,
    div_pos (ZLattice.covolume_pos _ _) hJ', fun B => ?_⟩
  let n := B + 1
  have hn : n ≠ 0 := Nat.succ_ne_zero B
  let M := L.map (nsmulAddMonoidHom n)
  let I := n ^ (2 * finrank ℤ L) * J
  have hI : M.relIndex (dualLattice h M) = I :=
    hermitian_relIndex_map_nsmul h hL.integral hL.isLattice.fg n hn
  refine ⟨M, I, lt_of_lt_of_le (Nat.lt_succ_self B)
    ((Nat.le_pow (by omega : 0 < 2 * finrank ℤ L)).trans
      (Nat.le_mul_of_pos_right _ hJ)), hL.map_nsmul n hn, hI.symm, ?_⟩
  have hsq : Real.sqrt I = (n : ℝ) ^ finrank ℤ L * Real.sqrt J := by
    simp only [I, Nat.cast_mul, Nat.cast_pow, mul_comm 2 _, pow_mul]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsq, arch_covolume_homothetic v L n hn]
  field_simp [hJ'.ne']

/-- The square-root dependence on the true Hermitian dual index is attained
at arbitrarily large indices, starting from any positive-rank integral lattice. -/
theorem ArchCovolumeBound.sqrt_sharp [NumberField.IsTotallyComplex E]
    (h : HermitianForm F E W) (v : Basis ι E W) {L : AddSubgroup W} {D : ℕ}
    (hL : IsDIntegral h D L) (hd : 0 < finrank ℤ L) :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ (M : AddSubgroup W) (I : ℕ), B < I ∧
      IsDIntegral h I M ∧ I = M.relIndex (dualLattice h M) ∧
      ZLattice.covolume (archLattice v M) = c * Real.sqrt I := by
  obtain ⟨_, harch⟩ := ArchCovolumeBound.full h v D
  obtain ⟨_, _, _⟩ := harch L hL
  exact ArchCovolumeBound.sqrt_sharp_of_lattice h v hL hd

end GroundTheory.Heights₂.Heights.FiniteCovolume
