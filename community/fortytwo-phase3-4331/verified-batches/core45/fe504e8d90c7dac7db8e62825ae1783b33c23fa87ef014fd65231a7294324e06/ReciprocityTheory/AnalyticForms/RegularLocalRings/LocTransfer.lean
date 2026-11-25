import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart

namespace ReciprocityTheory.AnForm.R

open MvPolynomial IsLocalRing

noncomputable section

variable {σ : Type} [Fintype σ]

abbrev renC (σ : Type) [Fintype σ] : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin (Fintype.card σ)) ℂ :=
  renameEquiv ℂ (Fintype.equivFin σ)

abbrev renR (σ : Type) [Fintype σ] : MvPolynomial σ ℂ ≃+* MvPolynomial (Fin (Fintype.card σ)) ℂ :=
  (renC σ).toRingEquiv

abbrev renPt (z : σ → ℂ) : Fin (Fintype.card σ) → ℂ := z ∘ (Fintype.equivFin σ).symm

theorem eval_renC (z : σ → ℂ) (h : MvPolynomial σ ℂ) : eval (renPt z) (renC σ h) = eval z h := by
  simp only [renC, renPt, renameEquiv_apply, eval_rename]
  rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

theorem map_primeCompl_renC (z : σ → ℂ) :
    Submonoid.map (renR σ).toMonoidHom (ptIdealOf z).primeCompl = (ptIdeal (renPt z)).primeCompl := by
  have key : ∀ x : MvPolynomial σ ℂ, eval (renPt z) ((renR σ).toMonoidHom x) = eval z x :=
    fun x => eval_renC z x
  have key' : ∀ y, (renR σ).toMonoidHom ((renR σ).symm y) = y := fun y => (renR σ).apply_symm_apply y
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro hy
    apply hx
    change x ∈ RingHom.ker _
    change _ ∈ RingHom.ker _ at hy
    rw [RingHom.mem_ker] at hy ⊢
    rw [← key x]
    exact hy
  · intro hy
    refine ⟨(renR σ).symm y, ?_, key' y⟩
    intro hx
    apply hy
    change y ∈ RingHom.ker _
    change _ ∈ RingHom.ker _ at hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [← key' y, key]
    exact hx

def locPtEquiv (z : σ → ℂ) : Localization.AtPrime (ptIdealOf z) ≃+* locPt (renPt z) :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (ptIdealOf z)) (locPt (renPt z))
    (renR σ) (map_primeCompl_renC z)

theorem locPtEquiv_algebraMap (z : σ → ℂ) (x : MvPolynomial σ ℂ) :
    locPtEquiv z (algebraMap _ _ x) = algebraMap _ (locPt (renPt z)) (renC σ x) := by
  unfold locPtEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq _ x

def locAtEquiv (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) :
    locAt I z ≃+* locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z) :=
  Ideal.quotientEquiv _ _ (locPtEquiv z) (by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    refine RingHom.ext fun x => ?_
    exact (locPtEquiv_algebraMap z x).symm)

theorem mem_map_renR_iff (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial (Fin (Fintype.card σ)) ℂ) :
    h ∈ I.map (renR σ : MvPolynomial σ ℂ →+* _) ↔ (renR σ).symm h ∈ I := by
  rw [Ideal.map_comap_of_equiv]
  exact Iff.rfl

theorem renPt_zero (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) (hz : ∀ h ∈ I, eval z h = 0) :
    ∀ h ∈ I.map (renR σ : MvPolynomial σ ℂ →+* _), eval (renPt z) h = 0 := by
  intro h hh
  rw [mem_map_renR_iff] at hh
  have e := eval_renC z ((renR σ).symm h)
  rw [show renC σ ((renR σ).symm h) = h from (renR σ).apply_symm_apply h] at e
  rw [e]
  exact hz _ hh


end

end ReciprocityTheory.AnForm.R
