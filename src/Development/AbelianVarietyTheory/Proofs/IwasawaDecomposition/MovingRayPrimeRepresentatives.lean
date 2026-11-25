module

public import GroundTheory.GlobalFields.TateThesis.GoodRayClassDensity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridValuesFromOneReference
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen

@[expose] public section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.BasicNotions
open GroundTheory.Global GlobalTheory.LevelChars

namespace GlobalTheory

theorem exists_degree_one_chosen_uniformizer {K : Type} [Field K] [NumberField K]
    (U : Subgroup (Ideles K)) (ho : IsOpen (U : Set (Ideles K)))
    (hk : (diagUnits K).range ≤ U) (u : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (hu : ∀ v, IsUnifAt v (u v))
    (x : Ideles K) (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧
      localIdele K v (u v) * x⁻¹ ∈ U := by
  have : U.FiniteIndex := finiteIndex_of_isOpen_of_diagonal_le U ho hk
  have hδ := chosen_ray_class_density U ho hk (QuotientGroup.mk x) u hu hS.toFinset
  obtain ⟨v, h, hS', hd⟩ := nonempty_of_density_pos
    (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero))) hδ
  exact ⟨v, fun h => hS' (hS.mem_toFinset.2 h), hd, QuotientGroup.eq_iff_div_mem.mp h⟩

open ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual GlobalTheory.HeckeGal

/-- The customary connected-infinite-component hypothesis is not needed. -/
theorem exists_degree_one_uniformizer_in_class {K : Type} [Field K] [NumberField K]
    (U : Subgroup (Ideles K)) (ho : IsOpen (U : Set (Ideles K)))
    (hk : (diagUnits K).range ⊔ infConn K ≤ U)
    (x : Ideles K) (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧
      ∃ π : (v.adicCompletion K)ˣ, IsUnifAt v π ∧ localIdele K v π * x⁻¹ ∈ U := by
  let u := fun v : HeightOneSpectrum (𝓞 K) => (IdeleGroup.exists_uniformizer v).choose
  have hu : ∀ v, IsUnifAt v (u v) := fun v => (IdeleGroup.exists_uniformizer v).choose_spec
  obtain ⟨v, hS', hd, hv⟩ := exists_degree_one_chosen_uniformizer U ho (le_sup_left.trans hk) u hu x S hS
  exact ⟨v, hS', hd, u v, hu v, hv⟩

end GlobalTheory

namespace GridInterpolation

theorem movingRayGroup_isOpen (D : D7) : IsOpen (movingRayGroup D : Set (Ideles D.host.E)) := by
  classical
  have hS := allBad_finite D
  apply Subgroup.isOpen_mono (show levSub D.host.E (allBad D) 2 ≤ movingRayGroup D from le_sup_right)
  convert (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open D.host.E).2 hS.toFinset 2 using 1
  ext a
  refine ⟨fun h => ⟨fun v => (h v).1, fun v hv => (h v).2 (hS.mem_toFinset.1 hv)⟩, ?_⟩
  exact fun h v => ⟨h.1 v, fun hv => h.2 v (hS.mem_toFinset.2 hv)⟩

theorem exists_good_prime_in_moving_class (D : D7) (x : Ideles D.host.E)
    (S : Set (HeightOneSpectrum (𝓞 D.host.E))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.E), v ∉ S ∧ v ∉ allBad D ∧
      v.asIdeal.inertiaDeg ℤ = 1 ∧
      localIdele D.host.E v (atFin v (unif v)) * x⁻¹ ∈ movingRayGroup D := by
  have hS' := allBad_finite D
  obtain ⟨v, hv, hd, h⟩ := GlobalTheory.exists_degree_one_chosen_uniformizer
    _ (movingRayGroup_isOpen D) le_sup_left _ (fun v => unif_spec v) x _ (hS.union hS')
  exact ⟨v, fun h => hv (Or.inl h), fun h => hv (Or.inr h), hd, h⟩

end GridInterpolation
