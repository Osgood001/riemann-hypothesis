module
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterRamifiedValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyFinitenessGlobal
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
@[expose] public section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host
open GlobalTheory.ChiGrid GlobalTheory.Mem GlobalTheory.Mem.LiteralAutomorphy
open GlobalTheory.Mem.LiteralAutomorphy.KeyFiniteness GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GridInterpolation

/-- Union of the possible ramified places as the auxiliary place varies. -/
def allBad (D : D7) : Set (HeightOneSpectrum (𝓞 D.host.E)) := ⋃ v ∈ Q0 D, Sv D v

theorem allBad_finite (D : D7) : (allBad D).Finite := by
  have hQ0 : (Q0 D).Finite := by
    refine (Formalism.L2.DIV.primesOf ((q0 D : ℕ) : 𝓞 D.host.F)).finite_toSet.subset fun v hv => ?_
    exact Formalism.L2.DIV.mem_primesOf.2 ⟨Nat.cast_ne_zero.2 (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero, hv⟩
  refine hQ0.biUnion fun v _ => ?_
  refine ((finite_aboveF (L := D.host.E) D.host.F v).union
    ((S1 D).finite_toSet.biUnion fun u _ => finite_aboveF (L := D.host.E) D.host.F u)).subset ?_
  rintro p (h | h)
  · exact Or.inl h
  · exact Or.inr (Set.mem_biUnion (Finset.mem_coe.2 h) rfl)

/-- The same level-two ray group bounds all grids of the given base. -/
def movingRayGroup (D : D7) :=
  (Units.map (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E)).toMonoidHom).range ⊔
    GlobalTheory.LevelChars.levSub D.host.E (allBad D) 2

/-- The ray quotient's exponent bounds every character ratio. -/
def movingRayExponent (D : D7) := Monoid.exponent (Ideles D.host.E ⧸ movingRayGroup D)

theorem movingRayExponent_dvd_index (D : D7) : movingRayExponent D ∣ (movingRayGroup D).index :=
  Group.exponent_dvd_nat_card

instance (D : D7) : NeZero (movingRayExponent D) := by
  have : (movingRayGroup D).FiniteIndex := GlobalTheory.T.rayClassGroup_idelic_finiteIndex _ _ 2 (allBad_finite D)
  exact ⟨Monoid.exponent_ne_zero_of_finite⟩

theorem actual_specs {X : Stages} {T : Type} {L : LevCh X.toD7 T} {sc : Consts}
    (G : GridData L sc) (a : Fin X.toD7.R.m) : G.ch.chiH (a.val+1) ∈ CS X.toD7 sc.cGap G.pl.v0 a := by
  obtain ⟨v, _, h⟩ := Set.mem_iUnion₂.mp (mem_KS G)
  have hv : G.pl.v0 = v := h.1
  subst v
  exact h.2.2 a (Set.mem_univ _)

private theorem level_global {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {c : ℝ}
    {a : Fin D.R.m} {χ : HChar D.host.E} (hs : χ ∈ CS D c v a) (p : HeightOneSpectrum (𝓞 D.host.E)) :
    χ.LevelLe p 2 := by
  by_cases hp : p ∈ Sv D v
  · exact hs.2.2 p hp
  · exact fun z hz _ => hs.2.1 p hp z hz

/-- Same-index grid ratios factor through the common moving ray quotient. -/
theorem movingRayGroup_le_ratio_ker {D : D7} {v u : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ Q0 D) (hu : u ∈ Q0 D)
    {c : ℝ} {a : Fin D.R.m} {χ ψ : HChar D.host.E} (hχ : χ ∈ CS D c v a) (hψ : ψ ∈ CS D c u a) :
    movingRayGroup D ≤ (χ * ψ⁻¹).1.ker := by
  let r := χ * ψ⁻¹
  refine sup_le ?_ fun y hy => MonoidHom.mem_ker.2
    (GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles D.host.E (allBad D) 2 r
      (fun k => ?_) (fun PP hp z hz => ?_) (fun PP _ z hz hl => ?_) y hy)
  · rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.2 (r.2.2 k)
  · have e : χ.inf k = ψ.inf k := Units.ext ((hχ.1 k).trans (hψ.1 k).symm)
    change (χ * ψ⁻¹).inf k = 1
    rw [HChar.inf_mul, HChar.inf_inv, e, mul_inv_cancel]
  · change χ.loc PP z * (ψ.loc PP z)⁻¹ = 1
    rw [hχ.2.1 PP (fun h => hp (Set.mem_biUnion hv h)) z hz,
      hψ.2.1 PP (fun h => hp (Set.mem_biUnion hu h)) z hz, inv_one, one_mul]
  · change χ.loc PP z * (ψ.loc PP z)⁻¹ = 1
    rw [level_global hχ PP z hz hl, level_global hψ PP z hz hl, inv_one, one_mul]

theorem moving_ratio_pow {D : D7} {v u : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ Q0 D) (hu : u ∈ Q0 D)
    {c : ℝ} {a : Fin D.R.m} {χ ψ : HChar D.host.E} (hχ : χ ∈ CS D c v a) (hψ : ψ ∈ CS D c u a)
    (p : HeightOneSpectrum (𝓞 D.host.E)) :
    ((χ.val p : ℂ) / (ψ.val p : ℂ)) ^ movingRayExponent D = 1 := by
  let r := χ * ψ⁻¹
  have hk := movingRayGroup_le_ratio_ker hv hu hχ hψ
  let x := localIdele D.host.E p (atFin p (unif p))
  have hx : x ^ movingRayExponent D ∈ movingRayGroup D :=
    (QuotientGroup.eq_one_iff _).mp (Monoid.pow_exponent_eq_one (x : Ideles D.host.E ⧸ movingRayGroup D))
  have h := MonoidHom.mem_ker.1 (hk hx)
  rw [map_pow] at h
  simpa [x,r,HChar.val,HChar.locK,HChar.loc,div_eq_mul_inv] using congrArg Units.val h


/-- Fix a single original reference and a field containing its good-prime values.
One root of order equal to the common ray quotient exponent, determined before the target grid is chosen, then
suffices at every target finite place, including its ramified places. -/
theorem all_grids_values_from_reference {Y : Stages} {U : Type} {L' : LevCh Y.toD7 U}
    {sc : Consts} (G₀ : GridData L' sc) (F : IntermediateField ℚ ℂ)
    (hμ : ∃ z : F, IsPrimitiveRoot z (movingRayExponent Y.toD7))
    (href : ∀ i, 1 ≤ i → i ≤ Y.toD7.R.m → (G₀.ch.chiH i).ValuesIn 0 F.val.toRingHom)
    {X : Stages} {T : Type} {L : LevCh X.toD7 T} (G : GridData L sc) (hP : X.B.toPre = Y.B.toPre) :
    ∀ a : Fin X.toD7.R.m, ∀ p, ((G.ch.chiH (a.val+1)).val p : ℂ) ∈ F := by
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := X
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := Y
  change P = Q at hP
  subst Q
  intro a p
  let χ := G.ch.chiH (a.val+1)
  let ψ := G₀.ch.chiH (a.val+1)
  have hr := moving_ratio_pow G.pl.basePlace_over_qZero G₀.pl.basePlace_over_qZero
    (actual_specs G a) (actual_specs G₀ a) p
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨j, _, hj⟩ := (hz.map_of_injective (f := F.val) Subtype.val_injective).eq_pow_of_pow_eq_one hr
  have hm : (χ.val p : ℂ) / (ψ.val p : ℂ) ∈ F := hj ▸ F.pow_mem z.property j
  have hy : (ψ.val p : ℂ) ∈ F := local_mem_of_values ((lamOf G₀).chi a) F
    (href _ (by omega) a.isLt) (embPsi _) ((lamOf G₀).c a) (lamOf_hasInfQ G₀ a) p (atFin p (unif p))
  simpa [χ,ψ] using F.mul_mem hm hy

end GridInterpolation
end
