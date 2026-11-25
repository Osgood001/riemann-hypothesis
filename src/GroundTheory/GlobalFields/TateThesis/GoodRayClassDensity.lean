module

public import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
public import GroundTheory.GlobalFields.TateThesis.RayClassDensity

@[expose] public section
noncomputable section

section
open NumberField IsDedekindDomain Filter Topology Set Ideal

namespace GroundTheory.Global

variable {K : Type*} [Field K] [NumberField K]

/-- The relative degree over the ring of integers of ℚ is exactly the absolute degree over ℤ. -/
theorem inertiaDeg_int_eq_rat (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.inertiaDeg ℤ = v.asIdeal.inertiaDeg (𝓞 ℚ) := by
  let u := v.under (𝓞 ℚ)
  have : (u.asIdeal.under ℤ).IsMaximal := IsPrime.isMaximal inferInstance (under_int_ne_bot u)
  have hu : u.asIdeal.inertiaDeg ℤ = 1 := by
    rw [inertiaDeg_eq_of_isMaximal (u.asIdeal.under ℤ)]
    apply Module.finrank_of_bijective_algebraMap
    refine ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective ?_⟩
    exact (show Rat.ringOfIntegersEquiv.symm.toRingHom = algebraMap ℤ (𝓞 ℚ) from Subsingleton.elim ..) ▸
      Rat.ringOfIntegersEquiv.symm.surjective
  have : v.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  rw [inertiaDeg_tower (R := ℤ) u.asIdeal v.asIdeal, hu, one_mul]

theorem hasDirichletDensity_good_degreeOne_iff (S : Set (HeightOneSpectrum (𝓞 K)))
    (bad : Finset (HeightOneSpectrum (𝓞 K))) (δ : ℝ) :
    {v | v ∈ S ∧ v ∉ bad ∧ v.asIdeal.inertiaDeg ℤ = 1}.HasDirichletDensity δ ↔
      S.HasDirichletDensity δ := by
  classical
  let T := S ∩ degreeOnePrimes ℚ K
  apply Iff.trans _ (hasDirichletDensity_inter_degreeOnePrimes_iff ℚ S δ)
  refine hasDirichletDensity_iff_of_subset_of_isBoundedUnder (S := T)
    (T := {v | v ∈ S ∧ v ∉ bad ∧ v.asIdeal.inertiaDeg ℤ = 1}) (fun v h => ⟨h.1, ?_⟩)
    (isBoundedUnder_primeIdealZetaSum_of_finite (bad.finite_toSet.subset ?_)) δ
  · exact (inertiaDeg_int_eq_rat v).symm.trans h.2.2
  · intro v hv
    by_contra hn
    exact hv.2 ⟨hv.1.1, hn, (inertiaDeg_int_eq_rat v).trans hv.1.2⟩

end GroundTheory.Global

end

open NumberField IsDedekindDomain Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Global

/-- An open idelic quotient which kills principal idèles is finite. -/
theorem finiteIndex_of_isOpen_of_diagonal_le {K : Type*} [Field K] [NumberField K]
    (U : Subgroup (IdeleGroup K)) (hU : IsOpen (U : Set (IdeleGroup K)))
    (hdiag : (IdeleGroup.diagonal K).range ≤ U) : U.FiniteIndex := by
  let q := QuotientGroup.mk' U
  let : DiscreteTopology (IdeleGroup K ⧸ U) := QuotientGroup.discreteTopology hU
  have hq : Continuous q := QuotientGroup.continuous_mk
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  let : PreconnectedSpace {r : ℝ // 0 < r} := Subtype.preconnectedSpace isPreconnected_Ioi
  have hlc : IsLocallyConstant (fun t => q (moduleSection w t)) :=
    fun s => (isOpen_discrete s).preimage (hq.comp (continuous_moduleSection w))
  have hsection (t) : q (moduleSection w t) = 1 := by
    simpa using hlc.apply_eq_of_preconnectedSpace t 1
  obtain ⟨D, hD, -, hrep⟩ := exists_isCompact_normOneSubgroup K
  have hfull : q '' D = univ := by
    apply eq_univ_of_forall
    intro c
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective U c
    obtain ⟨k, hk⟩ := hrep _ (mul_inv_moduleSection_mem w x)
    refine ⟨_, hk, ?_⟩
    have he : q (IdeleGroup.diagonal K k) = 1 := (QuotientGroup.eq_one_iff _).2 (hdiag ⟨k, rfl⟩)
    change q _ = q x
    rw [map_mul, he, one_mul, map_mul, map_inv, hsection, inv_one, mul_one]
  have hfin := (hD.image hq).finite_of_discrete
  rw [hfull] at hfin
  let := Finite.of_finite_univ hfin
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Choosing one normalized local uniformizer per place does not alter ray-class density:
outside the finite set of ramified primes, all normalized choices have the same image. -/
theorem hasDirichletDensity_chosen_uniformizers {K G : Type*} [Field K] [NumberField K]
    [CommGroup G] [Finite G] (f : IdeleGroup K →* G)
    (hop : IsOpen (f.ker : Set (IdeleGroup K))) (hK : (IdeleGroup.diagonal K).range ≤ f.ker)
    (hs : Function.Surjective f) (c : G) (u : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (hu : ∀ v, Valued.v (u v : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    {v | f (finiteEmbedding v (u v)) = c}.HasDirichletDensity (1 / Nat.card G) := by
  let A := {v : HeightOneSpectrum (𝓞 K) | ∀ π : (v.adicCompletion K)ˣ,
    Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) → f (finiteEmbedding v π) = c}
  let B := {v | f (finiteEmbedding v (u v)) = c}
  have hAB : A ⊆ B := fun v hv => hv (u v) (hu v)
  have hdiff : B \ A ⊆ ramifiedPrimes f hop hK := by
    intro v hv
    by_contra hvr
    apply hv.2
    intro π hπ
    exact (map_finiteEmbedding_eq_uniformizerClass f hop hK hvr hπ).trans
      ((map_finiteEmbedding_eq_uniformizerClass f hop hK hvr (hu v)).symm.trans hv.1)
  exact (hasDirichletDensity_iff_of_subset_of_isBoundedUnder hAB
    (isBoundedUnder_primeIdealZetaSum_of_finite ((finite_ramifiedPrimes f hop hK).subset hdiff)) _).1
    (hasDirichletDensity_setOf_map_eq f hop hK hs c)

/-- A positive Dirichlet density forces nonemptiness. -/
theorem nonempty_of_density_pos {K : Type*} [Field K] [NumberField K]
    {A : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} (hδ : 0 < δ) (h : A.HasDirichletDensity δ) :
    A.Nonempty := by
  by_contra! hn
  have he := h.dirichletDensity_eq
  rw [hn, NumberField.Set.dirichletDensity_empty] at he
  exact hδ.ne he

/-- Actual chosen-uniformizer representatives of any finite open ray quotient class,
after removing finitely many primes and all primes of absolute residue degree above one. -/
theorem chosen_ray_class_density {K : Type*} [Field K] [NumberField K]
    (U : Subgroup (IdeleGroup K)) (ho : IsOpen (U : Set (IdeleGroup K)))
    (hK : (IdeleGroup.diagonal K).range ≤ U) (c : IdeleGroup K ⧸ U)
    (u : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (hu : ∀ v, Valued.v (u v : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (bad : Finset (HeightOneSpectrum (𝓞 K))) :
    {v | QuotientGroup.mk (finiteEmbedding v (u v)) = c ∧ v ∉ bad ∧ v.asIdeal.inertiaDeg ℤ = 1
      }.HasDirichletDensity (1 / U.index) := by
  have : U.FiniteIndex := finiteIndex_of_isOpen_of_diagonal_le U ho hK
  let f := QuotientGroup.mk' U
  have hk : f.ker = U := QuotientGroup.ker_mk' _
  apply (hasDirichletDensity_good_degreeOne_iff {v | f (finiteEmbedding v (u v)) = c} bad _).2
  exact hasDirichletDensity_chosen_uniformizers f (by rwa [hk]) (by rwa [hk])
    (QuotientGroup.mk'_surjective U) c u hu

end GroundTheory.Global
