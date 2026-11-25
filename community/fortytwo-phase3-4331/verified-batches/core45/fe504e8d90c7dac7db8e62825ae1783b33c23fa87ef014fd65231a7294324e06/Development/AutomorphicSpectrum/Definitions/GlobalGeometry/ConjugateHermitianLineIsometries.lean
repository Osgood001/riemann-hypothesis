import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def evC (z : (Σ k, ι k) → ℂ) (f : MRing ι) : ℂ := eval z (map (Int.castRingHom ℂ) f)

def conjPt (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun p => starRingEnd ℂ (z p)

def conjLine (A : HermLine ι) : HermLine ι where
  a := A.a
  h z := A.h (conjPt z)
  pos z hz := A.pos _ fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, by simpa [conjPt] using hi⟩
  smul c z hc := by
    have h := A.smul (fun k => starRingEnd ℂ (c k)) (conjPt z) (fun k => by simpa using hc k)
    have e : conjPt (fun p => c p.1 * z p) = fun p => starRingEnd ℂ (c p.1) * conjPt z p := by
      funext p
      simp [conjPt]
    rw [e, h]
    simp





section Join

variable {K₁ K₂ : Type} (ι₁ : K₁ → Type) (ι₂ : K₂ → Type)

def joinIdx : K₁ ⊕ K₂ → Type := Sum.elim ι₁ ι₂

instance instFintypeJoinIdx [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] : ∀ k, Fintype (joinIdx ι₁ ι₂ k)
  | Sum.inl k => inferInstanceAs (Fintype (ι₁ k))
  | Sum.inr k => inferInstanceAs (Fintype (ι₂ k))

def joinInl : (Σ k, ι₁ k) → Σ k, joinIdx ι₁ ι₂ k := fun p => ⟨Sum.inl p.1, p.2⟩


variable {ι₁ ι₂}

def joinVec {Ω : Type} (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) : (Σ k, joinIdx ι₁ ι₂ k) → Ω
  | ⟨Sum.inl k, i⟩ => y₁ ⟨k, i⟩
  | ⟨Sum.inr k, i⟩ => y₂ ⟨k, i⟩

end Join


end GlobalTheory.CompanionTheory.Ar.Cmp
