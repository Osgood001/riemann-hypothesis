import Mathlib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix
open scoped ComplexOrder

def gramOf {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  gᴴ * diagonal (fun i => (hd i : ℂ)) * g

def gramHead {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    Matrix {a : Fin N // (a : ℕ) < k} {a : Fin N // (a : ℕ) < k} ℂ :=
  (gramOf hd g).submatrix Subtype.val Subtype.val


def sigForm (N j : ℕ) : Fin N → ℝ := fun a => if (a : ℕ) < N - j then -1 else 1

def InFlagDomain (N j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsUnit g.det ∧ (-gramHead (sigForm N j) (N - j) g).PosDef






end GlobalTheory.CompanionTheory.Ar.PB
