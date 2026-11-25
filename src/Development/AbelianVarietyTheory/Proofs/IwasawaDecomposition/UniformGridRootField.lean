module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormula

@[expose] public section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.Mem
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridField

/-- The numerical order depends only on the stage data and the depth parameters,
not on any of the places or characters chosen by the grid. -/
def stageRootOrder (D : D7) (sc : Consts) : ℕ :=
  (q0 D ^ depth0 D sc.cDep sc.b).lcm ((S1 D).lcm fun v => Ideal.absNorm v.asIdeal ^ 2)

theorem rootOrder_eq_stageRootOrder {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    rootOrder G = stageRootOrder D sc := by
  classical
  have h0 := G.ch.basePlace_not_mem_chiGridBadPlaces
  have hbad : (S1 D).lcm (fun v => Ideal.absNorm v.asIdeal ^ G.pl.depth sc v) =
      (S1 D).lcm (fun v => Ideal.absNorm v.asIdeal ^ 2) := by
    apply Finset.lcm_congr rfl
    intro v hv
    have hv0 : v ≠ G.pl.v0 := fun h => h0 (h ▸ hv)
    simp [Places.depth, hv0]
  simp only [rootOrder, Places.S0, Finset.lcm_insert, lcm_eq_nat_lcm, hbad]
  simp [Places.depth, stageRootOrder, LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.absNorm_splitAuxiliaryPlace_eq_prime]

theorem rootOrder_eq_of_same_pre {X Y : Stages} {T U : Type} {L : LevCh X.toD7 T} {H : LevCh Y.toD7 U}
    {sc : Consts} (G : GridData L sc) (J : GridData H sc) (h : X.B.toPre = Y.B.toPre) :
    rootOrder G = rootOrder J := by
  rw [rootOrder_eq_stageRootOrder, rootOrder_eq_stageRootOrder]
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := X
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := Y
  change P = Q at h
  subst Q
  rfl

/-- Realized orders are either a singleton or empty; the empty family's LCM is one. -/
def realizedRootOrders (P : Pre) (sc : Consts) : Set ℕ :=
  {n | ∃ X : Stages, X.B.toPre = P ∧ ∃ (T : Type) (L : LevCh X.toD7 T) (G : GridData L sc),
    rootOrder G = n}

theorem realizedRootOrders_subsingleton (P : Pre) (sc : Consts) : (realizedRootOrders P sc).Subsingleton := by
  rintro _ ⟨X, hX, T, L, G, rfl⟩ _ ⟨Y, hY, U, H, J, rfl⟩
  exact rootOrder_eq_of_same_pre G J (hX.trans hY.symm)

def uniformRootOrder (P : Pre) (sc : Consts) : ℕ :=
  (realizedRootOrders_subsingleton P sc).finite.toFinset.lcm id

theorem uniformRootOrder_dvd_iff (P : Pre) (sc : Consts) (m : ℕ) :
    uniformRootOrder P sc ∣ m ↔ ∀ n ∈ realizedRootOrders P sc, n ∣ m := by
  simp [uniformRootOrder, Finset.lcm_dvd_iff]

theorem uniformRootOrder_eq_of_grid {X : Stages} {T : Type} {L : LevCh X.toD7 T} {sc : Consts}
    (G : GridData L sc) : uniformRootOrder X.B.toPre sc = rootOrder G := by
  let S := realizedRootOrders X.B.toPre sc
  have hg : rootOrder G ∈ S := ⟨X, rfl, T, L, G, rfl⟩
  have hs : (realizedRootOrders_subsingleton X.B.toPre sc).finite.toFinset = {rootOrder G} := by
    ext n
    rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact ⟨fun hn => (realizedRootOrders_subsingleton _ _) hn hg, fun h => h ▸ hg⟩
  simp [uniformRootOrder, hs]

theorem uniformRootOrder_eq_one_of_empty (P : Pre) (sc : Consts)
    (h : realizedRootOrders P sc = ∅) : uniformRootOrder P sc = 1 := by
  have he : (realizedRootOrders_subsingleton P sc).finite.toFinset = ∅ := by
    ext n
    simp [h]
  simp [uniformRootOrder, he]

/-- Least embedded field that satisfies the original roots clause simultaneously. -/
def uniformRootField (P : Pre) (sc : Consts) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / uniformRootOrder P sc)}

theorem uniformRootField_eq_of_grid {X : Stages} {T : Type} {L : LevCh X.toD7 T} {sc : Consts}
    (G : GridData L sc) : uniformRootField X.B.toPre sc = rootField G := by
  rw [uniformRootField, uniformRootOrder_eq_of_grid G, rootField]

theorem uniformRootField_eq_bot_of_empty (P : Pre) (sc : Consts)
    (h : realizedRootOrders P sc = ∅) : uniformRootField P sc = ⊥ := by
  simp [uniformRootField, uniformRootOrder_eq_one_of_empty P sc h, Complex.exp_two_pi_mul_I]

theorem uniformRootField_finrank (P : Pre) (sc : Consts) :
    Module.finrank ℚ (uniformRootField P sc) = (uniformRootOrder P sc).totient := by
  rcases (realizedRootOrders P sc).eq_empty_or_nonempty with h | ⟨_, X, rfl, T, L, G, rfl⟩
  · simp [uniformRootField_eq_bot_of_empty P sc h, uniformRootOrder_eq_one_of_empty P sc h]
  · rw [uniformRootField_eq_of_grid G, uniformRootOrder_eq_of_grid G, rootField_finrank]

/-- A field containing the required roots for one grid contains them for every grid
over the same base and parameters; if there is no grid, every field qualifies. -/
theorem uniformRootField_le_iff (P : Pre) (sc : Consts) (M : IntermediateField ℚ ℂ) :
    uniformRootField P sc ≤ M ↔ ∀ X : Stages, X.B.toPre = P →
      ∀ (T : Type) (L : LevCh X.toD7 T) (G : GridData L sc), ∀ v ∈ G.pl.S0,
        ∃ z : M, IsPrimitiveRoot z (Ideal.absNorm v.asIdeal ^ G.pl.depth sc v) := by
  constructor
  · rintro h X rfl T L G
    exact (rootField_le_iff_roots G M).mp (uniformRootField_eq_of_grid G ▸ h)
  · intro h
    rcases (realizedRootOrders P sc).eq_empty_or_nonempty with he | ⟨_, X, rfl, T, L, G, rfl⟩
    · exact uniformRootField_eq_bot_of_empty P sc he ▸ bot_le
    · rw [uniformRootField_eq_of_grid G]
      exact (rootField_le_iff_roots G M).mpr (h X rfl T L G)

/-- For any embedded number field the same order is the exact torsion divisibility test
for all grids together; the individual characters still have to take their values in it. -/
theorem all_fieldHas_iff_values_and_dvd (P : Pre) (sc : Consts) {K : Type} [Field K] [NumberField K]
    (e : K →+* ℂ) :
    (∀ X : Stages, X.B.toPre = P → ∀ (T : Type) (L : LevCh X.toD7 T) (G : GridData L sc), FieldHas G e) ↔
    (∀ X : Stages, X.B.toPre = P → ∀ (T : Type) (L : LevCh X.toD7 T) (G : GridData L sc),
      ∀ i, 1 ≤ i → i ≤ X.toD7.R.m → (G.ch.chiH i).ValuesIn 0 e) ∧
      uniformRootOrder P sc ∣ NumberField.Units.torsionOrder K := by
  simp only [FieldHas.iff_values_and_dvd_torsionOrder, forall_and, uniformRootOrder_dvd_iff]
  apply and_congr_right'
  constructor
  · rintro h _ ⟨X, hX, T, L, G, rfl⟩
    exact h X hX T L G
  · intro h X hX T L G
    exact h _ ⟨X, hX, T, L, G, rfl⟩

end GlobalTheory.GridField
