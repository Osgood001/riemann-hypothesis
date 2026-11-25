module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BijectiveCmType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalStar

open UpperTheory.GalS (TmW)
open GlobalTheory.ContraPair

/-- A conjugation-invariant integral infinity type of a CM Hecke character is parallel:
restrict to the maximal real subfield, where the exponents double. -/
theorem parallel_of_conjugate_exponents {E : Type} [Field E] [NumberField E] [IsCMField E]
    (ψ : HChar E) (k : (E →+* ℂ) → ℤ) (hk : ∀ τ, expo ψ τ = k τ)
    (hc : ∀ τ, k (ComplexEmbedding.conjugate τ) = k τ) : ∃ w : ℤ, ∀ τ, k τ = w := by
  classical
  let lift := ComplexEmbedding.lift E (k := maximalRealSubfield E)
  let res := fun (τ : E →+* ℂ) => τ.comp (algebraMap (maximalRealSubfield E) E)
  have hl (φ : maximalRealSubfield E →+* ℂ) : res (lift φ) = φ := ComplexEmbedding.lift_comp_algebraMap E φ
  have hcases (τ : E →+* ℂ) := cm_eq_or_conj_of_comp_eq E (lift (res τ)) τ (hl (res τ)).symm
  have hlift : Function.Bijective fun φ => InfinitePlace.mk (lift φ) := by
    constructor
    · intro φ φ' h
      rcases InfinitePlace.mk_eq_iff.1 h with h | h
      · exact (hl φ).symm.trans ((congrArg res h).trans (hl φ'))
      · exact (hl φ).symm.trans ((cm_conj_comp_eq E (lift φ)).symm.trans ((congrArg res h).trans (hl φ')))
    · intro v
      refine ⟨res v.embedding, ?_⟩
      apply Eq.trans _ (InfinitePlace.mk_embedding v)
      exact InfinitePlace.mk_eq_iff.2 ((hcases v.embedding).imp Eq.symm Eq.symm)
  have ha := CuspRep.AlgExpo.isAlgPos_of_expo E ψ k hk
  have hr : IsAlgPos (PolChar.resReal ψ) (fun φ => 2 * k (lift φ)) := by
    intro x hx
    change ((ψ.1 (IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (infDiag x)) : ℂˣ) : ℂ) = _
    rw [InfDiagExt.ideleMap_infDiag]
    change ((ψ.inf (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) : ℂˣ) : ℂ) = _
    rw [ha _ (fun φ => hx (φ.comp (algebraMap _ E))), Mem.CharAlg.prod_split lift hlift]
    refine Finset.prod_congr rfl fun φ _ => ?_
    change (res (lift φ)) (x : maximalRealSubfield E) ^ _ *
      (res (ComplexEmbedding.conjugate (lift φ))) x ^ _ = _
    rw [hc, show res (ComplexEmbedding.conjugate (lift φ)) = res (lift φ) from cm_conj_comp_eq E _, hl]
    change _ = φ (x : maximalRealSubfield E) ^ (2 * k (lift φ))
    rw [mul_comm (2 : ℤ), zpow_mul, zpow_two]
  let φ₀ := Classical.choice (inferInstance : Nonempty (maximalRealSubfield E →+* ℂ))
  refine ⟨k (lift φ₀), fun τ => ?_⟩
  have e := heckeChar_parallel_weight _ _ _ hr (res τ) φ₀
  rcases hcases τ with h | h
  · calc k τ = k (lift (res τ)) := congrArg k h
         _ = _ := by omega
  · calc k τ = k (lift (res τ)) := (congrArg k h).trans (hc _)
         _ = _ := by omega

/-- Regular algebraicity and the polarization give a single integral reflection
weight for the infinitesimal characters of the given representation. -/
theorem infChar_conjugate_of_polarized {E : Type} [Field E] [NumberField E] [IsCMField E]
    {a : ℕ} (ha : 1 ≤ a) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E))
    (hr : (CG.mk π).IsRegAlg) (hp : PolarizedPair π χ) :
    ∃ w : ℤ, ∀ τ, (CG.mk π).infChar ((starRingEnd ℂ).comp τ) =
      ((CG.mk π).infChar τ).map (fun z => (w : ℂ) - z) := by
  have hm (τ : E →+* ℂ) : π.HasInfChar τ ((CG.mk π).infChar τ) :=
    ParLaws.hasInfChar_infChar (CG.mk π) τ
  let ψ := compNorm E χ
  have hmap (τ : E →+* ℂ) : (CG.mk π).infChar (ComplexEmbedding.conjugate τ) =
      ((CG.mk π).infChar τ).map (fun z => expo ψ τ - z) := by
    have h := T.infChar_conjEmbedding_neg_of_invariant_pairing E a (π.twist ψ⁻¹) π hp.dual τ _ _
      ((hm τ).twist ψ⁻¹) (hm (ComplexEmbedding.conjugate τ))
    rw [h, Multiset.map_map, RegAlgCharAlg.expo_inv']
    exact Multiset.map_congr rfl fun z _ => by simp only [Function.comp_apply]; ring
  have hint (τ : E →+* ℂ) : ∃ k : ℤ, expo ψ τ = k := by
    obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ := Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ).1]; omega)
    obtain ⟨n, hn⟩ := (hr τ).2 z hz
    obtain ⟨n', hn'⟩ := (hr _).2 _ (hmap τ ▸ Multiset.mem_map.2 ⟨z, hz, rfl⟩)
    refine ⟨n + n' + ((a : ℤ) - 1), ?_⟩
    push_cast
    linear_combination hn' + hn
  choose k hk using hint
  obtain ⟨w, hw⟩ := parallel_of_conjugate_exponents ψ k hk fun τ => Int.cast_injective (α := ℂ)
    ((hk _).symm.trans ((T.exponent_heckeChar_compNorm_conjEmbedding E χ τ).trans (hk τ)))
  refine ⟨w, fun τ => ?_⟩
  rw [show (starRingEnd ℂ).comp τ = ComplexEmbedding.conjugate τ by ext x; simp]
  simpa only [hk, hw] using hmap τ

/-- The integral Hodge–Tate multiset fixed by a regular algebraic
infinitesimal character in the cohomological normalization. -/
noncomputable def normalizedWeights (a : ℕ) (I : Multiset ℂ) : Multiset ℤ :=
  I.map (fun z => ⌊(((a : ℂ) - 1) / 2 - z).re⌋)

theorem normalizedWeights_spec (a : ℕ) (I : Multiset ℂ)
    (ha : ∀ z ∈ I, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    (normalizedWeights a I).map (fun n : ℤ => (n : ℂ)) =
      I.map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [normalizedWeights, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro z hz
  obtain ⟨n, rfl⟩ := ha z hz
  have h : ((a : ℂ) - 1) / 2 - (n + ((a : ℂ) - 1) / 2) = (-n : ℤ) := by push_cast; ring
  simp only [Function.comp_apply, h, Complex.intCast_re, Int.floor_intCast]

/-- A common purity weight for complex infinitesimal characters gives a
common conjugation weight for their normalized integral Hodge–Tate numbers. -/
theorem conjugate_weights_of_purity {E Q : Type} [Field E] [NumberField E] [IsCMField E]
    [Field Q] (ι : Q ≃+* ℂ) (a : ℕ) (I : (E →+* ℂ) → Multiset ℂ)
    (HT : (E →+* Q) → Multiset ℤ) (w : ℤ)
    (hp : ∀ φ, I ((starRingEnd ℂ).comp φ) = (I φ).map (fun z => (w : ℂ) - z))
    (h : ∀ τ, (HT τ).map (fun n : ℤ => (n : ℂ)) =
      (I (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z)) (τ : E →+* Q) :
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map ((a : ℤ) - 1 - w - ·) := by
  apply Multiset.map_injective (f := fun x : ℤ => (x : ℂ)) Int.cast_injective
  have hj : ι.toRingHom.comp (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) =
      (starRingEnd ℂ).comp (ι.toRingHom.comp τ) := RingHom.ext fun z =>
    IsCMField.complexEmbedding_complexConj E (ι.toRingHom.comp τ) z
  rw [h, hj, hp]
  calc
    _ = (((I (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z))).map
          (fun z => ((a : ℂ) - 1 - w) - z) := by
      rw [Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun z _ => by simp only [Function.comp_apply]; ring
    _ = _ := by
      rw [← h, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun z _ => by simp



variable (Rc : RecNotion) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

/-- The crystalline and de Rham comparisons that must actually be supplied above ℓ. -/
structure NormalizedAbove (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  nice : ∀ σ, π.IsLocComp w σ → ∀ rc, Rc h rc → ((IsQpBig w a ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) → (rc (algNorm σ)).mono0 →
    IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    (∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)) ∧
    AwayB (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

noncomputable def infCharWeights (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (τ : E →+* Qbar l) : Multiset ℤ :=
  normalizedWeights a ((CG.mk π).infChar (ι.toRingHom.comp τ))

theorem infCharWeights_spec (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (hr : (CG.mk π).IsRegAlg)
    (τ : E →+* Qbar l) : (infCharWeights π ι τ).map (fun z : ℤ => (z : ℂ)) =
      ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z) :=
  normalizedWeights_spec _ _ (((CG.isRegAlg_iff _).1 hr _).2)

/-- Local and global properties of the representation, with all Hodge–Tate weights fixed by π. -/
structure NormalizedProps (π : CuspSub E a) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), Rc h rc → ∀ σ, π.IsLocComp w σ → AwayB (wdOf h hl ι r) (rc (algNorm σ))
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), NormalizedAbove Rc π ι r (infCharWeights π ι) P h Bw hj

/-- Only the continuous semisimple representation is existentially quantified. -/
def NormalizedRow : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), NormalizedProps Rc π ι r

/-- The polarization determines a common conjugation weight; Berger recovers
potential semistability at the de Rham places of a continuous representation. -/
theorem row0b_iff_normalizedRow
    (hB : GlobalTheory.Published.DeRhamPotSemistable) : Row0b Rc ↔ NormalizedRow Rc := by
  constructor
  · intro H E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp'
    obtain ⟨r, w, HT, h⟩ := H E Ω l ι a ha π χ hr hp'
    obtain rfl : HT = infCharWeights π ι := funext fun τ =>
      Multiset.map_injective (Int.cast_injective (α := ℂ)) ((h.weights τ).trans (infCharWeights_spec π ι hr τ).symm)
    refine ⟨r, h.cont, h.ss, h.away, ?_⟩
    intro P AI T v A hv Ov _ _ _ Bw hj
    obtain ⟨hc, hn⟩ := h.above P AI T v A hv Ov Bw hj
    exact ⟨fun σ hσ hs => ⟨(hc σ hσ hs).1, (hc σ hσ hs).2.2⟩, fun σ hσ rc hrc hgood hm => by
      obtain ⟨hdr, _, hHT, hwd⟩ := hn σ hσ rc hrc hgood hm
      exact ⟨hdr, hHT, hwd⟩⟩
  · intro H E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp'
    obtain ⟨r, h⟩ := H E Ω l ι a ha π χ hr hp'
    obtain ⟨w, hw⟩ := infChar_conjugate_of_polarized ha π χ hr hp'
    let HT := infCharWeights π ι
    have hHT := infCharWeights_spec π ι hr
    refine ⟨r, (a : ℤ) - 1 - w, HT, h.cont, h.ss, h.away, hHT,
      conjugate_weights_of_purity ι a _ HT w hw hHT, ?_⟩
    intro P AI T v A hv Ov _ _ _ Bw hj
    obtain ⟨hc, hn⟩ := h.above P AI T v A hv Ov Bw hj
    refine ⟨fun σ hσ hs => ?_, fun σ hσ rc hrc hgood hm => ?_⟩
    · obtain ⟨hcr, hj⟩ := hc σ hσ hs
      refine ⟨hcr, ?_, hj⟩
      obtain ⟨L, r', hm, hd⟩ := hcr
      have := L.2
      refine ⟨L, r', hm, ?_⟩
      simpa [IsDR, LocBridge.IsdRE] using
        (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T.some Bw.Kw L _ _ hd).1
    · obtain ⟨hdr, hHT, hwd⟩ := hn σ hσ rc hrc hgood hm
      exact ⟨hdr, hB.isPstAt T.some Bw _ (Units.continuous_val.comp (h.cont.comp continuous_subtype_val)) hdr, hHT, hwd⟩

end UpperTheory.GalStar

namespace UpperTheory.V.Z.Win

/-- The precise Galois assumption used by the window can be supplied by the
representation alone, with its local compatibilities in the normalized weights. -/
theorem rowT_of_normalized
    (hB : GlobalTheory.Published.DeRhamPotSemistable)
    (h : GalStar.NormalizedRow (fun h rc => UpperTheory.Zero.LLC.IsRecT h rc)) : RowT :=
  (GalStar.row0b_iff_normalizedRow _ hB).2 h

end UpperTheory.V.Z.Win
