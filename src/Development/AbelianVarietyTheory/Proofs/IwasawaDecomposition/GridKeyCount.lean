module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyFinitenessGlobal

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB
  GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx
open IsDedekindDomain NumberField
open scoped BigOperators

namespace GlobalTheory.Mem.LiteralAutomorphy.KeyFiniteness

private theorem finite_Q0 (D : D7) : (Q0 D).Finite := by
  refine (Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F)).finite_toSet.subset fun v hv => ?_
  exact Formalism.L2.DIV.mem_primesOf.2
    ⟨Nat.cast_ne_zero.2 (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero, hv⟩

private theorem finite_Sv (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : (Sv D v).Finite := by
  refine ((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).union
    ((GlobalTheory.ChiGrid.S1 D).finite_toSet.biUnion fun u _ =>
      Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F u)).subset ?_
  rintro PP (h | h)
  · exact Or.inl h
  · exact Or.inr (Set.mem_biUnion (Finset.mem_coe.2 h) rfl)

/-- The index of the level-two idele-class subgroup at the allowed places of a grid key. -/
noncomputable def rayIndexAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℕ :=
  ((Units.map (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E)).toMonoidHom).range ⊔
    GlobalTheory.LevelChars.levSub D.host.E (Sv D v) 2).index

theorem rayIndexAt_pos (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : 0 < rayIndexAt D v := by
  have := GlobalTheory.T.rayClassGroup_idelic_finiteIndex D.host.E (Sv D v) 2 (finite_Sv D v)
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

/-- At every finite place, the uniformizer values of two characters in the same
prescribed family differ by a root of unity of order dividing the ray index. -/
theorem val_ratio_pow_rayIndexAt {D : D7} {c : ℝ} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {a : Fin D.R.m} {χ ψ : Formalism.L2.Host.HChar D.host.E} (hχ : χ ∈ CS D c v a)
    (hψ : ψ ∈ CS D c v a) (p : HeightOneSpectrum (𝓞 D.host.E)) :
    ((χ.val p : ℂ) / (ψ.val p : ℂ)) ^ rayIndexAt D v = 1 := by
  have hk := GlobalTheory.LevelChars.raySubgroup_le_ker_ratio
    (GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles D.host.E (Sv D v) 2) hχ hψ
  let x := Neutral.B1.localIdele D.host.E p
    (Formalism.L2.Host.atFin p (Formalism.L2.Host.unif p))
  have h := MonoidHom.mem_ker.1 (hk (Subgroup.pow_index_mem _ x))
  rw [map_pow] at h
  change (χ.1 x * (ψ.1 x)⁻¹) ^ rayIndexAt D v = 1 at h
  rw [← div_eq_mul_inv] at h
  simpa only [Formalism.L2.Host.HChar.val, Formalism.L2.Host.HChar.locK,
    Formalism.L2.Host.HChar.loc, MonoidHom.comp_apply, Units.val_pow_eq_pow_val,
    Units.val_div_eq_div_val, Units.val_one] using congrArg Units.val h

theorem CS_ncard_le (D : D7) (c : ℝ) (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Fin D.R.m) :
    (CS D c v a).ncard ≤ rayIndexAt D v :=
  (GlobalTheory.LevelChars.heckeFin_card_le_of GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles
    GlobalTheory.T.rayClassGroup_idelic_finiteIndex D.host.E _ (Formalism.L2.Host.embTau D)
    (fun τ => 2 * GlobalTheory.ChiGrid.cen D c τ (a.1 + 1)) (Sv D v) 2 (finite_Sv D v)).2

/-- A quantitative bound on the finite cover used by `gKeyFin`. -/
theorem KS_ncard_le (D : D7) (c : ℝ) :
    (KS D c).ncard ≤ ∑ᶠ v ∈ Q0 D,
      {w : HeightOneSpectrum (𝓞 D.host.E) |
        w.under (𝓞 D.host.F) = v}.ncard * rayIndexAt D v ^ D.R.m := by
  classical
  unfold KS
  refine ((finite_Q0 D).ncard_biUnion_le _).trans ?_
  simp only [finsum_mem_eq_finite_toFinset_sum _ (finite_Q0 D)]
  apply Finset.sum_le_sum
  intro v _
  rw [Set.ncard_prod, Set.ncard_singleton, one_mul, Set.ncard_prod]
  apply Nat.mul_le_mul_left
  rw [← Nat.card_coe_set_eq, Nat.card_congr (Equiv.Set.univPi _), Nat.card_pi]
  calc
    (∏ a : Fin D.R.m, Nat.card (CS D c v a)) ≤
        ∏ _ : Fin D.R.m, rayIndexAt D v :=
      Finset.prod_le_prod fun a _ ↦ CS_ncard_le D c v a
    _ = rayIndexAt D v ^ D.R.m := by simp

end GlobalTheory.Mem.LiteralAutomorphy.KeyFiniteness
