import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory

def SamePot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P Q : LocPot X) : Prop :=
  ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧
    ∀ y ∈ V, P.φ x y - Q.φ x y = (G y).re


structure AnSys (e : ℕ) (σ : Type) where

  X : Type
  [top : TopologicalSpace X]
  [compact : CompactSpace X]
  [t2 : T2Space X]

  A : FinHolAtlas e X

  Θ : LocPot X

  L : LocPot X

  s : X → X → ℂ

  nb : ℕ

  m : Fin nb → ℕ

  W : Fin nb → Set X
  potΘ : IsPotential A Θ
  posΘ : IsPosPot A Θ
  potL : IsPotential A L
  sec : IsSection A L s
  snc : IsSNC A L s m W
  norm_le : ∀ y, logNormSec L s y ≤ 0

  th : σ → LocPot X

  ph : σ → X → ℝ

  phT : σ → ℝ → X → ℝ

  C₅ : ℝ

  C : ℝ

  t₀ : ℝ
  sing : ∀ a, IsSingWeight A L s (th a) (ph a) C₅
  reg : ∀ a, IsRegFamily A Θ L s (th a) (ph a) (phT a) C t₀
  c2 : ∀ a, IsRegFamilyC2 A s (ph a) (phT a)

attribute [instance] AnSys.top AnSys.compact AnSys.t2

namespace AnSys

variable {e : ℕ} {σ : Type} (S : AnSys e σ)

def open' : Set S.X := (bdry S.s)ᶜ

def potT (a : σ) (t : ℝ) : LocPot S.X := S.th a + LocPot.ofFun (S.phT a t)




def comap {σ' : Type} (f : σ' → σ) : AnSys e σ' :=
  { S with
    th := fun a => S.th (f a), ph := fun a => S.ph (f a), phT := fun a => S.phT (f a)
    sing := fun a => S.sing (f a), reg := fun a => S.reg (f a), c2 := fun a => S.c2 (f a) }

end AnSys

section Period

variable {e : ℕ} {X : Type} [TopologicalSpace X] {Ψ : Type} {N : ℕ}




end Period

section Param

variable {e : ℕ} {X : Type} [TopologicalSpace X]






end Param

end GlobalTheory.CompanionTheory.Ar.PB
