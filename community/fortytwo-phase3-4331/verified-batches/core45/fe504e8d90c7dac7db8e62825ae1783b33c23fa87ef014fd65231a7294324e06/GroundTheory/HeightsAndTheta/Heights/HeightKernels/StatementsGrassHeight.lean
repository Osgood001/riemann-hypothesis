import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

abbrev PlIdx (j m : ℕ) : Type := {I : Finset (Fin (j + m)) // I.card = j}

def plAnchor (j m : ℕ) : PlIdx j m :=
  ⟨Finset.univ.map (Fin.castAddEmb m), by simp⟩

abbrev plBlocks (f j m : ℕ) : Fin f → Type := fun _ => PlIdx j m






def IsRootMatrix {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) : Prop :=
  ∀ τ a b, ∃ k : ℕ, 0 < k ∧ ζ τ a b ^ k = 1





def rootAnchorSection (f j m : ℕ) : MRing (plBlocks f j m) :=
  ∏ τ : Fin f, X ⟨τ, plAnchor j m⟩

def coneRatios {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) : Set Ω :=
  Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩





















example : IsRootMatrix (fun _ : Fin 1 => (!![-1] : Matrix (Fin 1) (Fin 1) ℂ)) := by
  intro τ a b
  refine ⟨2, by norm_num, ?_⟩
  fin_cases a; fin_cases b; simp

example : 1 ≤ (1 : ℕ) := le_rfl

def lineExampleCoord : (Σ _ : Unit, Fin 2) → FractionRing (MvPolynomial (Fin 1) ℚ) :=
  fun p => if p.2 = 0 then 1 else algebraMap _ _ (X 0 : MvPolynomial (Fin 1) ℚ)

def lineExampleT : Fin 1 → FractionRing (MvPolynomial (Fin 1) ℚ) :=
  fun _ => algebraMap _ _ (X 0 : MvPolynomial (Fin 1) ℚ)

example : (∀ k : Unit, lineExampleCoord ⟨k, 0⟩ ≠ 0) ∧ AlgebraicIndependent ℚ lineExampleT ∧
    (∀ i, lineExampleT i ∈ IntermediateField.adjoin ℚ (coneRatios lineExampleCoord fun _ => 0)) ∧
    (∀ r ∈ coneRatios lineExampleCoord (fun _ => 0),
      IsAlgebraic (IntermediateField.adjoin ℚ (Set.range lineExampleT)) r) := by
  refine ⟨fun _ => by simp [lineExampleCoord], ?_, ?_, ?_⟩
  · have h := (MvPolynomial.algebraicIndependent_X (Fin 1) ℚ).map'
      (f := (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 1) ℚ) (FractionRing (MvPolynomial (Fin 1) ℚ))))
      (IsFractionRing.injective _ _)
    have e : lineExampleT = (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 1) ℚ)
        (FractionRing (MvPolynomial (Fin 1) ℚ))) ∘ X := by
      funext i; fin_cases i; rfl
    rw [e]; exact h
  · intro i
    apply IntermediateField.subset_adjoin
    refine ⟨⟨(), 1⟩, ?_⟩
    simp [lineExampleCoord, lineExampleT]
  · rintro r ⟨p, rfl⟩
    have hr : lineExampleCoord p / lineExampleCoord ⟨p.1, 0⟩ ∈
        IntermediateField.adjoin ℚ (Set.range lineExampleT) := by
      by_cases h : p.2 = 0
      · simp [lineExampleCoord, h]
      · have : lineExampleCoord p / lineExampleCoord ⟨p.1, 0⟩ = lineExampleT 0 := by
          simp [lineExampleCoord, h, lineExampleT]
        rw [this]
        exact IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩
    exact isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range lineExampleT))
      (A := FractionRing (MvPolynomial (Fin 1) ℚ)) ⟨_, hr⟩

example : IsMultiHomog (rootAnchorSection 2 1 1) (fun _ => 1) := by
  intro μ hμ k
  classical
  simp only [rootAnchorSection, Fin.prod_univ_two] at hμ
  rw [MvPolynomial.support_X_mul] at hμ
  · simp only [Finset.mem_map, MvPolynomial.support_X, Finset.mem_singleton] at hμ
    obtain ⟨ν, rfl, hν⟩ := hμ
    subst hν
    fin_cases k <;> simp [Finsupp.single_apply]

end

end GroundTheory.Heights₂.Heights
