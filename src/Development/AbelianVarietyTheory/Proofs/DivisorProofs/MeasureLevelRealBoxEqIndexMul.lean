module
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open Formalism.L2.DIV Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolBox

variable {D : D7}

/-- If the coset representatives lift with trivial real part, each finite-level coset
contributes exactly one copy of the smaller box. -/
private theorem measure_level_mul_index {G H R : Type*} [Group G] [Group H] [Group R]
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (π : G →* H) (rp : G →* R) (K K₀ : Subgroup H) (hK : K ≤ K₀) (hi : K.relIndex K₀ ≠ 0)
    (lift : ∀ x : K₀, ∃ g : G, π g = x ∧ rp g = 1) (B : Set R)
    (hB : MeasurableSet {g : G | π g ∈ K ∧ rp g ∈ B}) :
    μ {g : G | π g ∈ K₀ ∧ rp g ∈ B} =
      (K.relIndex K₀ : ℝ≥0∞) * μ {g : G | π g ∈ K ∧ rp g ∈ B} := by
  classical
  let : (K.subgroupOf K₀).FiniteIndex := ⟨hi⟩
  let : Fintype (K₀ ⧸ K.subgroupOf K₀) := Fintype.ofFinite _
  let Q := K₀ ⧸ K.subgroupOf K₀
  let S (q : Q) := {g : G | (∃ h : π g ∈ K₀, QuotientGroup.mk (⟨π g, h⟩ : K₀) = q) ∧ rp g ∈ B}
  have pre (q : Q) : ∃ k : G, S q = (fun g => k⁻¹ * g) ⁻¹' {g : G | π g ∈ K ∧ rp g ∈ B} := by
    obtain ⟨k, hπ, hr⟩ := lift q.out
    refine ⟨k, Set.ext fun g => ?_⟩
    change ((∃ h : π g ∈ K₀, QuotientGroup.mk (⟨π g, h⟩ : K₀) = q) ∧ rp g ∈ B) ↔
      π (k⁻¹ * g) ∈ K ∧ rp (k⁻¹ * g) ∈ B
    simp only [map_mul, map_inv, hπ, hr, inv_one, one_mul]
    apply and_congr_left
    intro _
    constructor
    · rintro ⟨h, he⟩
      exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp ((QuotientGroup.out_eq' q).trans he.symm))
    · intro h
      have h₀ : π g ∈ K₀ := by simpa using K₀.mul_mem q.out.property (hK h)
      exact ⟨h₀, (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr h)).symm.trans (QuotientGroup.out_eq' q)⟩
  have ms (q : Q) : MeasurableSet (S q) := by
    obtain ⟨k, hk⟩ := pre q
    rw [hk]
    exact hB.preimage (measurable_const_mul _)
  have disj : Pairwise (Function.onFun Disjoint S) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    rintro g ⟨⟨_, hp⟩, _⟩ ⟨⟨_, hq⟩, _⟩
    exact hpq (hp.symm.trans hq)
  have cover : {g : G | π g ∈ K₀ ∧ rp g ∈ B} = ⋃ q, S q := by
    ext g
    constructor
    · rintro ⟨h, hr⟩
      exact Set.mem_iUnion.mpr ⟨QuotientGroup.mk (⟨_, h⟩ : K₀), ⟨⟨h, rfl⟩, hr⟩⟩
    · intro hg
      obtain ⟨q, ⟨⟨h, _⟩, hr⟩⟩ := Set.mem_iUnion.mp hg
      exact ⟨h, hr⟩
  have mass (q : Q) : μ (S q) = μ {g : G | π g ∈ K ∧ rp g ∈ B} := by
    obtain ⟨k, hk⟩ := pre q
    rw [hk, measure_preimage_mul]
  rw [cover, measure_iUnion disj ms, tsum_fintype]
  simp only [mass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.relIndex,
    Subgroup.index, Nat.card_eq_fintype_card, Q]

/-- The finite-part projection has a group-homomorphic right inverse with trivial
infinite component on the whole finite unitary group, not only on its level. -/
theorem exists_finE_section (D : D7) (V : HSp D) :
    ∃ j : UA D.sp.cm V.gram →* GA D V, ∀ x, j x ∈ GfC V ∧ finE V (j x) = x := by
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  let t := GlobalTheory.Mass.swapPts (Af D.host.F) D.sp.cm.sig V.gram
  let j := e.symm.toMulEquiv.toMonoidHom.comp ((MonoidHom.inr _ _).comp t.symm.toMonoidHom)
  refine ⟨j, fun x => ?_⟩
  have hj : e (j x) = (1, t.symm x) := e.apply_symm_apply _
  obtain ⟨hf, hinf⟩ := he (j x)
  rw [hj] at hf hinf
  have hfin : finHom V (j x) = HA.mat _ _ _ (t.symm x) := Units.ext hf.symm
  refine ⟨Units.ext hinf.symm, ?_⟩
  rw [finE_eq, hfin]
  exact ((GlobalTheory.Mass.coe_swapPts _ _ _ _).symm.trans (congrArg Subtype.val (t.apply_symm_apply x)))

/-- Haar mass of a full finite-level box; the representatives lifted into the
finite adelic component preserve its real coordinate. -/
theorem meas_level_eq_index_mul (V : HSp D) (θ : InfFam D) (A : Frames V)
    (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V))
    (hV : V.SigOK) (hθ : IsInfFam θ) (hA : IsFrames V A) (hm : ∀ ρ, IsMinf (m ρ))
    (hc : Continuous rp) (hrp : IsRealPart V θ A rp) (hKK : K ≤ K₀) (hi : K.relIndex K₀ ≠ 0)
    (hU : K₀ ≤ UA D.sp.cm V.gram)
    (hK : IsOpen {h : GA D V | finE V h ∈ K}) (hμ : IsMeasLev V K μ)
    (B : Set (∀ ρ, Upq V ρ)) (hB : MeasurableSet B) :
    μ {h | finE V h ∈ K₀ ∧ rp h ∈ B} = (K.relIndex K₀ : ℝ≥0∞) * Measure.pi m B := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have := hμ.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  rw [← meas_level V θ A m rp K μ hV hθ hA hm hc hrp hK hμ B hB]
  apply measure_level_mul_index μ (finE V) rp K K₀ hKK hi _ B (hK.measurableSet.inter (hc.measurable hB))
  intro x
  obtain ⟨j, hj⟩ := exists_finE_section D V
  let y : UA D.sp.cm V.gram := ⟨x, hU x.property⟩
  obtain ⟨hk, hx⟩ := hj y
  exact ⟨j y, hx, rp_eq_one V θ A rp hV hA hrp _ hk⟩

end GlobalTheory.CovTop.VolBox
