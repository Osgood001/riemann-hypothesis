module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerIsoSmoothSncToroidalModel
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CoeffEqZeroOfMemSpanPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtOfStalkIdEqSpanProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictNormalCrossingsDescentEtaleCompletion
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsC

@[expose] public section

namespace GlobalTheory.RigChart

open GlobalTheory.Toroidal MvPowerSeries

private theorem snd_eq_zero_of_boundary_generators {K k : Type} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] [Field k] {m : ℕ}
    (ρ : ChartRing K m 0 →+* DualNumber k) (h : ∀ i, ρ (bdParam K m 0 i) = 0)
    (r : ChartRing K m 0) : (ρ r).snd = 0 := by
  classical
  let φ := ρ.comp (C : K →+* ChartRing K m 0)
  let : Algebra ℚ (DualNumber k) := (φ.comp (algebraMap ℚ K)).toAlgebra
  have : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  have he := Algebra.FormallyUnramified.ext' (R := ℚ) (A := K) (B := DualNumber k)
    (TrivSqZeroExt.fstHom k k k).toRingHom ⟨2, TrivSqZeroExt.kerIdeal_sq k k⟩ φ.toRatAlgHom
    ((algebraMap k (DualNumber k)).comp ((TrivSqZeroExt.fstHom k k k).toRingHom.comp φ)).toRatAlgHom
    (fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  have hspan : Ideal.span (X '' (↑(Finset.univ : Finset (Fin m ⊕ Fin 0)) : Set _)) ≤ RingHom.ker ρ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i | i, _, rfl⟩
    · exact h i
    · exact Fin.elim0 i
  have hsub : r - C (constantCoeff r) ∈ RingHom.ker ρ := hspan <|
    SocleDet.mem_span_X_of_coeff Finset.univ _ fun d hd => by
      have hz : d = 0 := Finsupp.ext fun i => hd i (Finset.mem_univ _)
      simp [hz, coeff_zero_eq_constantCoeff]
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hsub
  rw [hsub]
  exact congrArg TrivSqZeroExt.snd (DFunLike.congr_fun he (constantCoeff r))

/-- With no smooth coordinates a chart over an algebraic number field is rigid:
the boundary coordinates already generate its tangent directions. -/
private theorem isRigid_of_no_smooth_coordinates {K : Type} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] {m : ℕ}
    (Q : ReciprocityTheory.ChartRestriction.G.Out.DegPre (ChartRing K m 0))
    (gam : Fin m → LinearMap.BilinForm ℤ Q.X) : IsRigid Q (bdParam K m 0) gam :=
  fun _ _ ρ _ _ h _ => snd_eq_zero_of_boundary_generators ρ h

end GlobalTheory.RigChart


open CategoryTheory AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart

namespace GlobalTheory.LogKSAssembly

/-- The coefficient field of a completed chart over a closed point of a scheme of finite
type over a number field is a number field. Only the finite residue clause is needed. -/
private theorem finite_chart_field {F k R : Type} [Field F] [CharZero F] [FiniteDimensional ℚ F]
    [Field k] [CharZero k] [CommRing R] [IsLocalRing R] (C : k →+* R)
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) (φ : X.presheaf.stalk x →+* R) [IsLocalHom φ]
    (hfin : ((residue R).comp φ).Finite) : FiniteDimensional ℚ k := by
  let ι := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom
  let : Algebra F (X.residueField x) := ι.toAlgebra
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ f), HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have : Algebra.FiniteType F (X.residueField x) := RingHom.finiteType_algebraMap.mp h
  have hι : ι.Finite := finite_of_finite_type_of_isJacobsonRing F _
  have hφ : (ResidueField.map φ).Finite := RingHom.Finite.of_comp_finite (f := residue _) hfin
  let c := (residue R).comp C
  have : CharZero (ResidueField R) := charZero_of_injective_ringHom c.injective
  have hr : (algebraMap ℚ (ResidueField R)).Finite := by
    rw [show algebraMap ℚ (ResidueField R) =
      ((ResidueField.map φ).comp ι).comp (algebraMap ℚ F) from Subsingleton.elim _ _]
    exact (hφ.comp hι).comp (RingHom.finite_algebraMap.mpr inferInstance)
  have := RingHom.finite_algebraMap.mp hr
  exact FiniteDimensional.of_injective (c.toRatAlgHom.toLinearMap) c.injective

/-- A flat local map which generates the maximal ideal has zero-dimensional closed
fiber and hence preserves local dimension. -/
private theorem etaleCompletion_dim {A B : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]
    (hφ : IsEtaleCompletion φ) : ringKrullDim B = ringKrullDim A := by
  let := φ.toAlgebra
  have : Module.Flat A B := hφ.1
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom φ)
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := hφ.2.1
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [hm, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim (R := A), h]

/-- At a closed smooth point the boundary and smooth coordinates of a completed
chart together account for the full relative dimension. -/
theorem chart_parameter_count_eq {F k : Type} [Field F] [Field k]
    {X : Scheme.{0}} (p : X ⟶ Sp F) (N : ℕ) [hsm : SmoothOfRelativeDimension N p]
    {m d : ℕ} (ξ : Sp (ChartRing k m d) ⟶ X)
    (hξ : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (hc : IsClosed ({ξ (closedPoint _)} : Set X)) : m + d = N := by
  have : Smooth p := SmoothOfRelativeDimension.smooth N p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have h := (etaleCompletion_dim (Scheme.stalkClosedPointTo ξ).hom hξ).trans
    (CutDegree.ringKrullDim_stalk hsm hc)
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries k (Fin m ⊕ Fin d), ringKrullDim_eq_zero_of_field] at h
  exact_mod_cast (by simpa using h : ((m + d : ℕ) : WithBot ℕ∞) = N)

/-- A full-rank ordinary boundary chart has no transverse coordinate.
At a closed point its coefficient field is algebraic, so it is already rigid. -/
theorem isRigid_of_full_boundary_rank {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F)) {N : ℕ} [SmoothOfRelativeDimension N (genStr Y)]
    {k : Type} [Field k] {m d : ℕ}
    (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hEt : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (hc : IsClosed ({ξ (closedPoint _)} : Set (gen Y))) (hm : N ≤ m)
    (Q : DegPre (ChartRing k m d)) (gam : Fin m → LinearMap.BilinForm ℤ Q.X) :
    IsRigid Q (bdParam k m d) gam := by
  have hmd := chart_parameter_count_eq (genStr Y) N ξ hEt hc
  have hd : d = 0 := by omega
  subst d
  have : CharZero k := GlobalTheory.T.charZero_of_toricChart_to_genericFibre E H Dw l Xo c Y k m 0 ξ
  have := SmoothOfRelativeDimension.smooth N (genStr Y)
  have := c.fin
  have := finite_chart_field (MvPowerSeries.C : k →+* ChartRing k m 0) (genStr Y) _ hc
    (Scheme.stalkClosedPointTo ξ).hom hEt.2.2
  have := Algebra.IsAlgebraic.of_finite ℚ k
  exact isRigid_of_no_smooth_coordinates Q gam

/-- At a boundary point a monomial chart necessarily has a boundary parameter. -/
private theorem pos_of_boundary_point {k : Type} [Field k] {m d : ℕ}
    (h : ∏ i, bdParam k m d i ∈ (closedPoint (ChartRing k m d)).asIdeal) : 0 < m := by
  by_contra! hm
  interval_cases m
  exact (closedPoint (ChartRing k 0 d)).isPrime.one_notMem (by simpa using h)

/-- On a smooth toroidal curve a closed boundary point has no transverse
parameters in an ordinary chart, hence no separate rigidification is needed. -/
theorem hasRigidChart_of_ordinary_curve {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F)) [SmoothOfRelativeDimension 1 (genStr Y)]
    (x : gen Y) (hx : x ∈ genBd Y)
    (hc : IsClosed ({x} : Set (gen Y))) (hchart : GlobalTheory.MumfordChart.HasChart Y x) :
    HasRigidChart Y x := by
  obtain ⟨k, hk, m, d, ξ, t, P, gam, rfl, hEt, hI, hB, ht, hM, hPart⟩ := hchart
  have hm := pos_of_boundary_point ((hB _).mp hx)
  exact ⟨k, hk, m, d, ξ, t, P, gam, rfl, hEt, hI, hB, ht, hM, hPart,
    isRigid_of_full_boundary_rank Y ξ hEt hc hm P.D.toPre (fun i => gam i)⟩

open Set TopologicalSpace in
/-- In dimension at most one the complement of a dense open consists of closed points. -/
private theorem isClosed_singleton_of_not_mem_dense_curve {X : Type*} [TopologicalSpace X]
    [T0Space X] [NoetherianSpace X] (hd : topologicalKrullDim X ≤ 1)
    {U : Set X} (ho : IsOpen U) (hU : Dense U) {x : X} (hx : x ∉ U) :
    IsClosed ({x} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_contra hne
  let A : IrreducibleCloseds X := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let C : IrreducibleCloseds X :=
    ⟨irreducibleComponent x, isIrreducible_irreducibleComponent, isClosed_irreducibleComponent⟩
  have hAB : A < B := by
    refine lt_of_le_not_ge (closure_minimal (singleton_subset_iff.mpr hy) isClosed_closure) fun h => hne ?_
    exact ((specializes_iff_mem_closure.mpr hy).antisymm
      (specializes_iff_mem_closure.mpr (h (subset_closure rfl)))).eq.symm
  have hBC : B < C := by
    refine lt_of_le_not_ge (closure_minimal (singleton_subset_iff.mpr mem_irreducibleComponent)
      isClosed_irreducibleComponent) fun h => ?_
    obtain ⟨V, hV, hVne, hVC⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
    obtain ⟨z, hzV, hzU⟩ := hU.inter_open_nonempty V hV hVne
    exact hx ((specializes_iff_mem_closure.mpr (h (hVC hzV))).mem_open ho hzU)
  let chain : LTSeries (IrreducibleCloseds X) := ⟨2, ![A,B,C], fun i => by fin_cases i <;> assumption⟩
  have hle : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := Order.le_krullDim_iff.mpr ⟨chain, rfl⟩
  exact (by norm_num : ¬ (2 : WithBot ℕ∞) ≤ 1) (hle.trans hd)

/-- On a smooth curve the ordinary monomial boundary is automatically strict normal crossings. -/
theorem snc_of_ordinary_curve {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F)) [hsm : SmoothOfRelativeDimension 1 (genStr Y)]
    (hchart : ∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → GlobalTheory.MumfordChart.HasChart Y x) :
    FinalTheorems.Snc (genBdIdeal Y) := by
  intro x
  have : Nonempty (gen Y) := ⟨x⟩
  have := SmoothOfRelativeDimension.smooth 1 (genStr Y)
  have := isProper_genStr Y
  have : IsLocallyNoetherian (gen Y) := LocallyOfFiniteType.isLocallyNoetherian (genStr Y)
  have : CompactSpace (gen Y) := QuasiCompact.compactSpace_of_compactSpace (genStr Y)
  have : IsNoetherian (gen Y) := {}
  have := Y.jQ_open
  have hreg := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field (genStr Y) x
  by_cases hx : x ∈ genBd Y
  · have hd := HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (genStr Y) 1 hsm
    have hc := isClosed_singleton_of_not_mem_dense_curve (by simpa using hd.le)
      Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense (mem_genBd.mp hx)
    obtain ⟨k, hk, m, d, ξ, _, _, _, rfl, hEt, hI, hB, _⟩ := hchart x hx hc
    have hm := pos_of_boundary_point ((hB _).mp hx)
    have hd := chart_parameter_count_eq (genStr Y) 1 ξ hEt hc
    have hm1 : m = 1 := by omega
    subst m
    obtain ⟨n, r, T, hr, hD⟩ := SncDescent.exists_rsp_of_isEtaleCompletion _ k 1 d _ _ hEt hI
      (fun i j _ => Subsingleton.elim i j)
    exact sncAt_of_stalkId_eq_span_prod _ _ _ hreg n r T hr hD
  · exact sncAt_of_not_mem _ _ hx hreg

/-- For smooth toroidal curves, ordinary charts give
the full log Kodaira–Spencer isomorphism, not just an injection on sections. -/
theorem hasLogKS_of_ordinary_curve {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F)) (hdim : Dw.dim = 1)
    (hsm : SmoothOfRelativeDimension Dw.dim (genStr Y))
    (hchart : ∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → GlobalTheory.MumfordChart.HasChart Y x) :
    HasLogKS Y.t Y.s (interior Y) := by
  have : SmoothOfRelativeDimension 1 (genStr Y) := hdim ▸ hsm
  exact hasLogKS_of_rigid E H Dw l Xo c Y hsm (snc_of_ordinary_curve Y hchart)
    (fun x hx hc => hasRigidChart_of_ordinary_curve Y x hx hc (hchart x hx hc))

end GlobalTheory.LogKSAssembly
