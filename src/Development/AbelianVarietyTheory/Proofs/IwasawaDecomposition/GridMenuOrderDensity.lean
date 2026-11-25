module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridPrimeTestDensity

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 GroundTheory.Global Set
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host
open GlobalTheory.ChiGrid GlobalTheory.Mem GlobalTheory.BigTop.Fun
open GlobalTheory.Mem.LiteralAutomorphy.KeyFiniteness
open scoped BigOperators ArithmeticFunction.Moebius
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GridInterpolation

/-- Möbius inversion counts the observations of exact order `e` using only
counts of observations whose order divides the divisors of `e`. -/
theorem card_order_eq_sum_moebius {A : Type*} (s : Finset A) (ord : A → ℕ)
    {e : ℕ} (he : 0 < e) :
    ((s.filter fun a => ord a = e).card : ℤ) =
      ∑ d ∈ e.divisorsAntidiagonal,
        (μ d.1 : ℤ) * ((s.filter fun a => ord a ∣ d.2).card : ℤ) := by
  classical
  let f (d : ℕ) : ℤ := (s.filter fun a => ord a = d).card
  let g (d : ℕ) : ℤ := (s.filter fun a => ord a ∣ d).card
  change f e = _
  refine ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := f) (g := g)).mp ?_ e he).symm
  intro n hn
  simp only [f, g, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hd : ord a ∣ n
  · rw [ite_eq_left hd, Finset.sum_eq_single (ord a)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · exact fun h => (h (Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩)).elim
  · rw [ite_eq_right hd]
    exact Finset.sum_eq_zero fun b hb => ite_eq_right fun (h : ord a = b) =>
      hd (h.symm ▸ (Nat.mem_divisors.mp hb).1)

/-- The order statistic of the readings on a moving ray class. At a prime
representing the class it equals the least common multiple of the observed orders. -/
def menuClassOrder (Y : Stages) {sc : Consts} (menu : Finset (GridRatioColumn Y.B.toPre sc))
    (q : Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7) : ℕ :=
  menu.lcm fun c => orderOf (c.rayChar Y q)

/-- The class statistic agrees with the observed orders at every prime. -/
theorem menuClassOrder_prime (Y : Stages) {sc : Consts} (menu : Finset (GridRatioColumn Y.B.toPre sc))
    (p : HeightOneSpectrum (𝓞 Y.toD7.host.E)) :
    menuClassOrder Y menu (movingPrimeClass Y.toD7 p) = menu.lcm (fun c => orderOf (c.read p)) := by
  classical
  unfold menuClassOrder
  apply Finset.lcm_congr rfl
  intro c _
  rw [← orderOf_units, c.rayChar_read]

/-- The moving ray classes on which all the menu readings are killed by `d`. -/
noncomputable def menuTorsionCount (Y : Stages) {sc : Consts}
    (menu : Finset (GridRatioColumn Y.B.toPre sc)) (d : ℕ) : ℕ := by
  classical
  have : (movingRayGroup Y.toD7).FiniteIndex :=
    GlobalTheory.T.rayClassGroup_idelic_finiteIndex _ _ 2 (allBad_finite Y.toD7)
  letI := Fintype.ofFinite (Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7)
  exact (Finset.univ.filter fun q => menuClassOrder Y menu q ∣ d).card

/-- For any fixed menu, the primes with observed order lcm `e` have an exact
Dirichlet density determined by the menu's lower-order torsion counts.
No cyclicity assumption on the menu image is needed. -/
theorem hasDirichletDensity_menu_order (Y : Stages) {sc : Consts}
    (menu : Finset (GridRatioColumn Y.B.toPre sc)) {e : ℕ} (he : 0 < e)
    (bad : Finset (HeightOneSpectrum (𝓞 Y.toD7.host.E))) :
    let D := Y.toD7
    @NumberField.Set.HasDirichletDensity D.host.E D.host.instField _
      {p | menu.lcm (fun c => orderOf (c.read p)) = e ∧ p ∉ bad ∧ p ∉ allBad D ∧
        p.asIdeal.inertiaDeg ℤ = 1}
      ((∑ d ∈ e.divisorsAntidiagonal, (μ d.1 : ℝ) * (menuTorsionCount Y menu d.2 : ℝ)) /
        (movingRayGroup Y.toD7).index) := by
  classical
  let Q := Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7
  have : (movingRayGroup Y.toD7).FiniteIndex :=
    GlobalTheory.T.rayClassGroup_idelic_finiteIndex _ _ 2 (allBad_finite Y.toD7)
  let _ := Fintype.ofFinite Q
  let C := (Finset.univ : Finset Q).filter fun q => menuClassOrder Y menu q = e
  have hcount : (C.card : ℤ) =
      ∑ d ∈ e.divisorsAntidiagonal, (μ d.1 : ℤ) * (menuTorsionCount Y menu d.2 : ℤ) :=
    card_order_eq_sum_moebius Finset.univ (menuClassOrder Y menu) he
  have hreal : (C.card : ℝ) =
      ∑ d ∈ e.divisorsAntidiagonal, (μ d.1 : ℝ) * (menuTorsionCount Y menu d.2 : ℝ) := by
    exact_mod_cast hcount
  dsimp only
  rw [← hreal]
  simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and, menuClassOrder_prime]
    using hasDirichletDensity_goodClassPacket Y.toD7 C bad

end GridInterpolation
