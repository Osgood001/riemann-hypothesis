module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PReducedBasisBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchCovolumeBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordEmbedBasis
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegralFormCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTraceHermNondegenerate
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTraceDualIndex
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDualLatticeMultiple
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordLatticeFullRank
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantTransport
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineNormalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementLattice
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldAlongSubgroup
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHaarParabolicCoordinates
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLatticePointsBelowFinite
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchimedeanUnitaryEquiv
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicLatticeDictionary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDoubleCosetCovolume

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

theorem ReducedBasisBound.full : ReducedBasisBound.Statement := ReducedBasisBound.proof

private theorem discr_dvd_pow_of_clears_traceDual (E : Type*) [Field E] [NumberField E]
    (δ : ℤ) (hdiff : ∀ z : E, (∀ a : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((a : E) * z) = n) →
      IsIntegral ℤ ((δ : E) * z)) :
    (NumberField.discr E).natAbs ∣ δ.natAbs ^ finrank ℚ E := by
  have h : Ideal.span {(δ : 𝓞 E)} ≤ differentIdeal ℤ (𝓞 E) := by
    apply (IsLocalization.coeSubmodule_le_coeSubmodule (S := E) (M := nonZeroDivisors (𝓞 E)) le_rfl).mp
    rw [IsLocalization.coeSubmodule_span_singleton, coeSubmodule_differentIdeal ℤ ℚ,
      Submodule.span_singleton_le_iff_mem, map_intCast, Submodule.mem_div_iff_forall_mul_mem]
    intro z hz
    refine Submodule.mem_one.mpr ⟨⟨_, hdiff z ?_⟩, rfl⟩
    intro a
    obtain ⟨n, hn⟩ := Submodule.mem_traceDual.mp hz (a : E) (Submodule.mem_one.mpr ⟨a, rfl⟩)
    exact ⟨n, by simpa [Algebra.traceForm_apply, mul_comm] using hn.symm⟩
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le h
  rwa [NumberField.absNorm_differentIdeal E, Ideal.absNorm_span_singleton,
    show (δ : 𝓞 E) = algebraMap ℤ (𝓞 E) δ by simp,
    Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow] at hdvd

/-- In coordinates, the trace dual enlarges the Hermitian dual by an index bounded by
the clearing integer for the inverse different to the power of the rational dimension. -/
theorem traceHerm_relIndex_factor {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {W : Type*} [AddCommGroup W] [Module E W]
    {ι : Type*} [Fintype ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hT : (traceHerm h v).Nondegenerate) (hfull : CoordLatticeFullRank.Statement v)
    (δ : ℤ)
    (hdiff : ∀ z : E, (∀ a : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((a : E) * z) = n) →
      IsIntegral ℤ ((δ : E) * z))
    {D : ℕ} (La : AddSubgroup W) (hLa : IsDIntegral h D La) :
    let L := La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
    let B := (traceHerm h v).dualSubmodule L.toIntSubmodule
    L.toIntSubmodule ≤ B ∧ ∃ a : ℕ, a ∣ δ.natAbs ^ finrank ℚ (ι → E) ∧
      L.relIndex B.toAddSubgroup = La.relIndex (dualLattice h La) * a := by
  obtain ⟨hle, heq⟩ := traceHerm_relIndex_eq h v hT hfull La hLa.isLattice hLa.integral
  refine ⟨hle, (NumberField.discr E).natAbs ^ Fintype.card ι, ?_, heq⟩
  rw [← Module.finrank_mul_finrank ℚ E (ι → E), Module.finrank_fintype_fun_eq_card, pow_mul]
  exact pow_dvd_pow_of_dvd (discr_dvd_pow_of_clears_traceDual E δ hdiff) _

section Closed

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

section OneSpace

variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)


omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
/-- For fixed Hermitian form and fixed archimedean coordinates the squared covolume
is exactly proportional to the actual Hermitian dual index, for every integral lattice, without an assumed index bound. -/
theorem ArchCovolumeBound.index_formula :
    ∃ C : ℝ, 0 < C ∧ ∀ (La : AddSubgroup W), IsLattice E La → IsIntegralOn h La →
      ∃ _ : DiscreteTopology (archLattice v La), IsZLattice ℝ (archLattice v La) ∧
        ZLattice.covolume (archLattice v La) ^ 2 =
          C * (La.relIndex (dualLattice h La) : ℝ) := by
  let e := Pi.basis fun _ : ι => integralBasis E
  have hc := CoordEmbedBasis.proof E ι
  have ht := TraceHermNondegenerate.proof h v
  have hf := CoordLatticeFullRank.proof v
  obtain ⟨C, hC, hformula⟩ := IntegralFormCovolume.index_formula _ _ _ (coordEmbed E ι) e
    (traceHerm h v) volume (Measure.pi.isAddHaarMeasure _) ht hc.1
    (by rw [hc.2, finrank_eq_card_basis e])
  refine ⟨C * ((NumberField.discr E).natAbs : ℝ) ^ Fintype.card ι, mul_pos hC
    (pow_pos (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)) _), ?_⟩
  intro La hLa hint
  let φ := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
  have harch : archLattice v La = AddSubgroup.toIntSubmodule ((La.map φ).map (coordEmbed E ι)) := by
    rw [archLattice, AddSubgroup.map_map]
    rfl
  obtain ⟨hfg, hspan⟩ := hf La hLa
  obtain ⟨hint, hidx⟩ := traceHerm_relIndex_eq h v ht hf La hLa hint
  obtain ⟨hd, hZ, hcov⟩ := hformula (La.map φ) hfg hspan hint
  rw [harch]
  refine ⟨hd, hZ, ?_⟩
  rw [hcov, hidx, Nat.cast_mul, Nat.cast_pow]
  ring

omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
/-- The exact normalization recovers the previous finite-factor formulation. -/
theorem ArchCovolumeBound.index_factors :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ) (La : AddSubgroup W), IsDIntegral h D La →
      ∃ _ : DiscreteTopology (archLattice v La), IsZLattice ℝ (archLattice v La) ∧
        ∃ a : ℕ, a ∣ (NumberField.discr E).natAbs ^ finrank ℚ (ι → E) ∧
          ZLattice.covolume (archLattice v La) ^ 2 =
            C * (La.relIndex (dualLattice h La) : ℝ) * a := by
  obtain ⟨C, hC, hformula⟩ := ArchCovolumeBound.index_formula h v
  refine ⟨C, hC, fun D La hLa => ?_⟩
  obtain ⟨hd, hZ, hv⟩ := hformula La hLa.isLattice hLa.integral
  exact ⟨hd, hZ, 1, one_dvd _, by simpa using hv⟩

omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
/-- The old lower and upper estimates can use the same positive normalization. -/
theorem ArchCovolumeBound.index_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (D : ℕ) (La : AddSubgroup W), IsDIntegral h D La →
      ∃ _ : DiscreteTopology (archLattice v La), IsZLattice ℝ (archLattice v La) ∧
        c * (La.relIndex (dualLattice h La) : ℝ) ≤ ZLattice.covolume (archLattice v La) ^ 2 ∧
        ZLattice.covolume (archLattice v La) ^ 2 ≤ C * (La.relIndex (dualLattice h La) : ℝ) := by
  obtain ⟨C, hC, hformula⟩ := ArchCovolumeBound.index_formula h v
  refine ⟨C, C, hC, hC, fun D La hLa => ?_⟩
  obtain ⟨hd, hZ, hv⟩ := hformula La hLa.isLattice hLa.integral
  exact ⟨hd, hZ, hv.ge, hv.le⟩
omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
/-- On integral lattices, the original discriminant cutoff is exactly the archimedean
squared-covolume cutoff for a single normalization. Finiteness of the dual index follows. -/
theorem ArchCovolumeBound.cutoff_iff :
    ∃ C : ℝ, 0 < C ∧ ∀ (La : AddSubgroup W), IsLattice E La → IsIntegralOn h La →
      ∃ _ : DiscreteTopology (archLattice v La), IsZLattice ℝ (archLattice v La) ∧
        ∀ D : ℕ, IsDIntegral h D La ↔ ZLattice.covolume (archLattice v La) ^ 2 ≤ C * D := by
  obtain ⟨C, hC, hformula⟩ := ArchCovolumeBound.index_formula h v
  refine ⟨C, hC, fun La hLa hint => ?_⟩
  obtain ⟨hd, hZ, hv⟩ := hformula La hLa hint
  have : (volume : Measure (InfinitePlace E → ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hne : La.relIndex (dualLattice h La) ≠ 0 := by
    intro hz
    have hp := sq_pos_of_pos (ZLattice.covolume_pos (archLattice v La) volume)
    simp [hv, hz] at hp
  refine ⟨hd, hZ, fun D => ?_⟩
  rw [hv, mul_le_mul_iff_right₀ hC, Nat.cast_le]
  exact ⟨fun hD => hD.index_le, fun hb => ⟨hLa, hint, hne, hb⟩⟩

omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
theorem ArchCovolumeBound.full : ArchCovolumeBound.Statement h v := by
  obtain ⟨C, _, hcutoff⟩ := ArchCovolumeBound.cutoff_iff h v
  intro D
  refine ⟨Real.sqrt (C * D), fun La hLa => ?_⟩
  obtain ⟨hd, hZ, hiff⟩ := hcutoff La hLa.isLattice hLa.integral
  exact ⟨hd, hZ, (le_abs_self _).trans (Real.abs_le_sqrt ((hiff D).mp hLa))⟩

omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem MajorantTransport.full : MajorantTransport.Statement h v := MajorantTransport.proof h v


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem ComplementExtension.full : ComplementExtension.Statement h := ComplementExtension.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LineNormalForm.full : LineNormalForm.Statement h := LineNormalForm.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem ComplementLattice.full [FiniteDimensional E W] : ComplementLattice.Statement h :=
  ComplementLattice.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LatticePointsBelowFinite.full : LatticePointsBelowFinite.Statement h v :=
  LatticePointsBelowFinite.proof h v

theorem ArchimedeanUnitaryEquiv.full : ArchimedeanUnitaryEquiv.Statement h v :=
  ArchimedeanUnitaryEquiv.proof h v

theorem AdelicLatticeDictionary.full : AdelicLatticeDictionary.Statement h v :=
  AdelicLatticeDictionary.proof h v

end OneSpace

theorem LatticeOrbitsFiniteBelow.full (N : ℕ) : LatticeOrbitsFiniteBelow.{u} F E N :=
  LatticeOrbitsFiniteBelow.of_steps ReducedBasisBound.full
    (fun _ _ _ _ h _ v => ArchCovolumeBound.full h v) (fun _ _ _ _ h _ v => MajorantTransport.full h v)
    (fun _ _ _ _ h => ComplementExtension.full h) (fun _ _ _ _ h => LineNormalForm.full h)
    (fun _ _ _ _ h => ComplementLattice.full h) N

section Dimension

variable {W : Type u} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
variable (h : HermitianForm F E W)

theorem LatticeOrbitsFinite.full : LatticeOrbitsFinite.Statement h :=
  LatticeOrbitsFinite.step_of h (LatticeOrbitsFiniteBelow.full _) ReducedBasisBound.full
    (ArchCovolumeBound.full h _) (MajorantTransport.full h _) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h)

theorem LinePairOrbitsFinite.full : LinePairOrbitsFinite.Statement h :=
  LinePairOrbitsFinite.full_of h (LatticeOrbitsFiniteBelow.full _) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h)

theorem ScalingLaw.of_unfolding {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Basis ι E W)
    (hU : UnfoldingIntegral.Statement h v) : ScalingLaw.Statement h v :=
  ScalingLaw.full_of h v (LinePairOrbitsFinite.full h) hU

end Dimension

end Closed

section Adelic

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AdelicCovolumeFinite.of_covolume (h : HermitianForm F E W) (v : Basis ι E W)
    (hC : ArithmeticCovolumeFinite.Statement h v) : AdelicCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  AdelicCovolumeFinite.full_of h v (LatticeOrbitsFinite.full h) hC (ArchimedeanUnitaryEquiv.full h v)
    (AdelicLatticeDictionary.full h v) (DoubleCosetCovolume.proof _ _ _)

theorem HaarParabolicCoordinates.of_open (h : HermitianForm F E W) (v : Basis ι E W)
    (hAU : ArchUnimodular.Statement h v) (hMS : MajorantStabCompact.Statement h v)
    (hLS : LineStabHaar.Statement h v) : HaarParabolicCoordinates.Statement h v :=
  HaarParabolicCoordinates.proof h v (ParabolicDecomposition.full h v) hAU hMS hLS

end Adelic

section Open

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

variable
    (hAU : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchUnimodular.Statement h v)
    (hMS : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantStabCompact.Statement h v)
    (hLS : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), LineStabHaar.Statement h v)
    (hSD : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W) (x₀ w₀ : W)
      (h' : HermitianForm F E (hypComplement h x₀ w₀)) (m : ℕ)
      (v' : Basis (Fin m) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (hSL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), StabilizerLevi.Statement h v)
    (hUM : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentModulus.Statement h v)
    (hUC : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCocompact.Statement h v)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), CongruenceLift.Statement h)

include hAU hMS hLS hSD hSL hUM hUC hCL

theorem CovolumeFiniteBelow.of_open (N : ℕ) : CovolumeFiniteBelow.{u} F E N :=
  CovolumeFiniteBelow.of_steps ReducedBasisBound.full
    (fun _ _ _ _ h _ v => ArchCovolumeBound.full h v) (fun _ _ _ _ h _ v => MajorantTransport.full h v)
    (fun _ _ _ _ h => ComplementExtension.full h) (fun _ _ _ _ h => LineNormalForm.full h)
    (fun _ _ _ _ h => ComplementLattice.full h) (fun _ _ _ _ _ _ _ _ => UnfoldAlongSubgroup.proof _ _)
    (fun W _ _ _ h n v => HaarParabolicCoordinates.of_open h v (hAU W h n v) (hMS W h n v)
      (hLS W h n v))
    (fun W _ _ _ h n v hB => StabilizerCovolumeFinite.proof h v hB (hSD W h n v) (hSL W h n v)
      (hUM W h n v) (hUC W h n v) (hCL W h))
    (fun _ _ _ _ h _ v => LatticePointsBelowFinite.full h v) N

variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)

variable (hSD' : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (m : ℕ)
      (v' : Basis (Fin m) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (hSL' : StabilizerLevi.Statement h v) (hUM' : UnipotentModulus.Statement h v)
    (hUC' : UnipotentCocompact.Statement h v)

include hSD' hSL' hUM' hUC'

theorem StabilizerCovolumeFinite.of_open : StabilizerCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  StabilizerCovolumeFinite.proof h v
    (CovolumeFiniteBelow.of_open hAU hMS hLS hSD hSL hUM hUC hCL _) hSD' hSL' hUM' hUC' (hCL W h)

variable (hAU' : ArchUnimodular.Statement h v) (hMS' : MajorantStabCompact.Statement h v)
    (hLS' : LineStabHaar.Statement h v)

include hAU' hMS' hLS'

theorem UnfoldingIntegral.of_open : UnfoldingIntegral.Statement h v :=
  UnfoldingIntegral.full_of h v (fun _ => UnfoldAlongSubgroup.proof _ _)
    (HaarParabolicCoordinates.of_open h v hAU' hMS' hLS')
    (StabilizerCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC')

theorem ScalingLaw.of_open : ScalingLaw.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  ScalingLaw.of_unfolding h v
    (UnfoldingIntegral.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC' hAU' hMS' hLS')

theorem ArithmeticCovolumeFinite.of_open : ArithmeticCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  ArithmeticCovolumeFinite.step_of h v (LatticeOrbitsFiniteBelow.full _) ReducedBasisBound.full
    (ArchCovolumeBound.full h v) (MajorantTransport.full h v) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h) (fun _ => UnfoldAlongSubgroup.proof _ _)
    (HaarParabolicCoordinates.of_open h v hAU' hMS' hLS')
    (StabilizerCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC')
    (LatticePointsBelowFinite.full h v)

theorem AdelicCovolumeFinite.of_open : AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_covolume h v
    (ArithmeticCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC' hAU' hMS'
      hLS')

end Open

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
