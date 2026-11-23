import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Bundle00
universe u v
noncomputable section
section
open scoped BigOperators
open PowerSeries (derivative rescale subst)

namespace Formalism.L2.Th1.C

section Basic

variable {K : Type} [Field K] {σ : Type}

def IntMv (R : Subring K) (f : MvPowerSeries σ K) : Prop :=
  ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n f ∈ R

def IntPS (R : Subring K) (f : PowerSeries K) : Prop :=
  ∀ n : ℕ, PowerSeries.coeff n f ∈ R

def mvExp [CharZero K] (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  subst f $ PowerSeries.exp K

def LG [CharZero K] (R : Subring K) (f : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ IntMv R (mvExp f)

def Cong [CharZero K] (R : Subring K) (f g : MvPowerSeries σ K) : Prop := LG R $ f - g

def IsPt (R : Subring K) (a : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff a = 0 ∧ IntMv R a

def IsOneUnit (R : Subring K) (f : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff f = 1 ∧ IntPS R f

def binom (z : K) (n : ℕ) : K := (∏ i ∈ Finset.range n, (z - (i : K))) / (n.factorial : K)

def IsBinomScalar (R : Subring K) (z : K) : Prop := ∀ n : ℕ, binom z n ∈ R

end Basic

section ZSide

variable {K : Type} [Field K]

def dblInt (e : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => if n < 2 then 0 else PowerSeries.coeff (n - 2) e / ((n : K) * ((n : K) - 1))

def lam (e : PowerSeries K) (s2 : K) : PowerSeries K :=
  dblInt e + PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2

def sgStar [CharZero K] (e : PowerSeries K) (s2 : K) : PowerSeries K :=
  PowerSeries.X * mvExp (-(lam e s2))

def wpShift (e : PowerSeries K) (c : K) : PowerSeries K :=
  1 + PowerSeries.X ^ 2 * (e - PowerSeries.C c)

def HasSecondLogDeriv (f g : PowerSeries K) : Prop :=
  derivative (derivative f) * f - (derivative f) ^ 2
    = g * f ^ 2

def IsEndoZ (e : PowerSeries K) {ι : Type} [Fintype ι] (neg : ι → ι) (c : ι → K)
    (w : ι → PowerSeries K) (al : K) : Prop :=
  (∀ P, neg (neg P) = P) ∧
  (∀ P, HasSecondLogDeriv (wpShift e $ c P) $ 2 * e - w P - w (neg P)) ∧
  PowerSeries.C (al ^ 2) * rescale al e = e + ∑ P, (w P - PowerSeries.C (c P))

def IsogenyFormula [CharZero K] (e : PowerSeries K) (s2 : K) {ι : Type} [Fintype ι] (c : ι → K)
    (al : K) : Prop :=
  (rescale al (sgStar e s2)) ^ 2 * PowerSeries.X ^ (2 * Fintype.card ι) =
    PowerSeries.C (al ^ 2) * (sgStar e s2) ^ (2 * (Fintype.card ι + 1)) * ∏ P, wpShift e (c P)

end ZSide

section USide

variable {K : Type} [Field K] {σ : Type}

def IsLogPair (l linv : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff l = 0 ∧ PowerSeries.coeff 1 l = 1 ∧
  PowerSeries.constantCoeff linv = 0 ∧
  subst l linv = PowerSeries.X ∧ subst linv l = PowerSeries.X

def mulBy (l linv : PowerSeries K) (a : K) : PowerSeries K :=
  subst (PowerSeries.C a * l) linv

def fadd (l linv : PowerSeries K) (a b : MvPowerSeries σ K) : MvPowerSeries σ K :=
  subst (subst a l + subst b l) linv

def fmul (l linv : PowerSeries K) (α : K) (a : MvPowerSeries σ K) : MvPowerSeries σ K :=
  subst (MvPowerSeries.C α * subst a l) linv

def be0 (l linv ph : PowerSeries K) (a b : MvPowerSeries σ K) : MvPowerSeries σ K :=
  subst (fadd l linv a b) ph - subst a ph - subst b ph

def FGInt (R : Subring K) (l linv : PowerSeries K) : Prop :=
  IntMv R $ fadd l linv (MvPowerSeries.X (0 : Fin 2)) $ MvPowerSeries.X (1 : Fin 2)

def IsPh [CharZero K] (e : PowerSeries K) (s2 : K) (l ph : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff ph = 0 ∧
  PowerSeries.X * mvExp (-ph) = subst l (sgStar e s2)

def XIsWp (e l A : PowerSeries K) (c0 : K) : Prop :=
  (A + PowerSeries.C c0 * PowerSeries.X ^ 2) * l ^ 2 =
    PowerSeries.X ^ 2 * subst l (wpShift e 0)

end USide

end Formalism.L2.Th1.C
end
section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def IsogenyReduce : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (c : ι → K) (al : K), al ≠ 0 →
    (IsogenyFormula e s2 c al ↔
      mvExp ((2 * ((Fintype.card ι : K) + 1)) • lam e s2 - (2 : K) • PowerSeries.rescale al (lam e s2))
        = ∏ P, wpShift e (c P))

def IsogenyIff : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (c : ι → K) (w : ι → PowerSeries K) (al : K), al ≠ 0 →
    IsEndoZ e neg c w al →
    (IsogenyFormula e s2 c al ↔ (al ^ 2 - ((Fintype.card ι : K) + 1)) * s2 = ∑ P, c P)

def IsogenyIffBar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP : ι → K) (c0 : K) (w : ι → PowerSeries K) (al albar : K), al ≠ 0 →
    al * albar = (Fintype.card ι : K) + 1 →
    IsEndoZ e neg (fun P => xP P + c0) w al →
    (IsogenyFormula e s2 (fun P => xP P + c0) al ↔
      al * (al - albar) * s2 = ∑ P, (xP P + c0))





end Formalism.L2.Th1.C
end
section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def MvExpLaws : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type),
    mvExp (0 : MvPowerSeries σ K) = 1 ∧
    (∀ f : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (mvExp f) = 1) ∧
    (∀ f g : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → mvExp (f + g) = mvExp f * mvExp g) ∧
    (∀ f g : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → mvExp f = mvExp g → f = g)

def MvExpSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) (f : PowerSeries K) (a : MvPowerSeries σ K),
    PowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (mvExp f : PowerSeries K) = mvExp (PowerSeries.subst a f)

def LGSubgroup : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type),
    LG R (0 : MvPowerSeries σ K) ∧
    (∀ f g : MvPowerSeries σ K, LG R f → LG R g → LG R (f + g)) ∧
    (∀ f : MvPowerSeries σ K, LG R f → LG R (-f))

def LGBinom : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) (z : K), IsBinomScalar R z →
    ∀ f : MvPowerSeries σ K, LG R f → LG R (z • f)

def LGHalf : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type), (2 : K)⁻¹ ∈ R →
    ∀ f : MvPowerSeries σ K, LG R (f + f) → LG R f

def IntBinomScalar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (n : ℤ), IsBinomScalar R (n : K)


def LGSubstMv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) [Finite σ]
    (f : MvPowerSeries σ K), LG R f →
    ∀ (τ : Type) (a : σ → MvPowerSeries τ K), (∀ s, IsPt R $ a s) → LG R (MvPowerSeries.subst a f)



end Formalism.L2.Th1.C
end
section
open scoped BigOperators

namespace Formalism.L2.Th1.C

section Defs4

variable {K : Type} [Field K]


def EndInt (R : Subring K) (l linv : PowerSeries K) (a : K) : Prop := IntPS R $ mulBy l linv a

def Frame (R : Subring K) (l linv ph : PowerSeries K) : Prop :=
  IsLogPair l linv ∧ FGInt R l linv ∧ PowerSeries.constantCoeff ph = 0

variable [CharZero K]

def PhNormAt (R : Subring K) (l linv ph : PowerSeries K) (a b : K) : Prop :=
  Cong R (PowerSeries.subst (mulBy l linv a) ph) $ (a * b) • ph


def F1 (R : Subring K) (l linv ph : PowerSeries K) : Prop :=
  ∀ (σ : Type) (x x' y : MvPowerSeries σ K), IsPt R x → IsPt R x' → IsPt R y →
    Cong R (be0 l linv ph (fadd l linv x x') y) (be0 l linv ph x y + be0 l linv ph x' y)

def ZLinAt (R : Subring K) (l linv ph : PowerSeries K) (z : K) : Prop :=
  ∀ (σ : Type) (x y : MvPowerSeries σ K), IsPt R x → IsPt R y →
    Cong R (be0 l linv ph x $ fmul l linv z y) (z • be0 l linv ph x y)

end Defs4








end Formalism.L2.Th1.C
end
section
open scoped BigOperators

namespace Formalism.L2.Th1.C





def ZLinInt : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → F1 R l linv ph → ∀ n : ℤ, ZLinAt R l linv ph (n : K)


end Formalism.L2.Th1.C
end
section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def veluXs {K : Type} [Field K] {ι : Type} [Fintype ι] (A : PowerSeries K) (xs : ι → PowerSeries K)
    (xP : ι → K) (r : K) : PowerSeries K :=
  A + PowerSeries.X ^ 2 * (∑ P, (xs P - PowerSeries.C (xP P)) - PowerSeries.C r)



def VeluXFromZ : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e l linv A : PowerSeries K) (c0 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP : ι → K) (w xs : ι → PowerSeries K) (al : K),
    IsLogPair l linv → XIsWp e l A c0 → IsEndoZ e neg (fun P => xP P + c0) w al →
    (∀ P, PowerSeries.subst l (w P) = xs P + PowerSeries.C c0) →
    PowerSeries.C (al ^ 2) * PowerSeries.subst (mulBy l linv al) A * PowerSeries.X ^ 2 =
      (mulBy l linv al) ^ 2 * veluXs A xs xP ((al ^ 2 - 1) * c0)

def IsogenyU : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (l linv ph A : PowerSeries K)
    (c0 : K) (ι : Type) [Fintype ι] (xP : ι → K) (al : K),
    IsLogPair l linv → IsPh e s2 l ph → XIsWp e l A c0 →
    IsogenyFormula e s2 (fun P => xP P + c0) al →
    (mulBy l linv al) ^ 2 * mvExp (-((2 : K) • PowerSeries.subst (mulBy l linv al) ph))
        * PowerSeries.X ^ (2 * Fintype.card ι) =
      PowerSeries.C (al ^ 2) * PowerSeries.X ^ (2 * (Fintype.card ι + 1))
        * mvExp (-((2 * ((Fintype.card ι : K) + 1)) • ph))
        * ∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2)

def PhNormUnit : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (e : PowerSeries K) (s2 : K)
    (l linv ph A : PowerSeries K) (c0 : K) (ι : Type) [Fintype ι] (xP : ι → K) (al : K),
    IsLogPair l linv → IsPh e s2 l ph → XIsWp e l A c0 →
    IsogenyFormula e s2 (fun P => xP P + c0) al →
    IsOneUnit R A → (∀ P, xP P ∈ R) → al ∈ R → al⁻¹ ∈ R → al ≠ 0 → (2 : K)⁻¹ ∈ R →
    IntPS R (mulBy l linv al) →
    Cong R (PowerSeries.subst (mulBy l linv al) ph) (((Fintype.card ι : K) + 1) • ph)

end Formalism.L2.Th1.C
end
section
open scoped BigOperators
open Finset (mem_antidiagonal mul_sum range sum_congr sum_range_succ')
open MvPowerSeries (coeff coeff_mul coeff_one coeff_pderiv pderiv)
open Nat (find lt_succ_self)
open Finset

namespace Formalism.L2.Th1.C

variable {K : Type} [Field K] [CharZero K] {σ : Type}

theorem hasSubst_of_cc {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf

private theorem finsupp_degree_add (a b : σ →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  first
  | exact map_add Finsupp.degree a b
  | exact Finsupp.degree_add a b
  | simp [Finsupp.degree_add]

private theorem coeff_mul_eq_zero_of_degree_lt_add' {A B : MvPowerSeries σ K} {a b : ℕ}
    (hA : ∀ m, m.degree < a → coeff m A = 0)
    (hB : ∀ m, m.degree < b → coeff m B = 0)
    (n : σ →₀ ℕ) (hn : n.degree < a + b) : coeff n (A * B) = 0 := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  first
  | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  | simp [mem_antidiagonal] at hp
  | simp at hp
  have hd : p.1.degree + p.2.degree = n.degree := by rw [← finsupp_degree_add, hp]
  by_cases h1 : p.1.degree < a
  rw [hA _ h1, zero_mul]
  rw [hB _ $ by omega, mul_zero]

private theorem coeff_pow_eq_zero_of_degree_lt_mul {A : MvPowerSeries σ K} {a : ℕ}
    (hA : ∀ m, m.degree < a → coeff m A = 0) (k : ℕ) :
    ∀ n, n.degree < k * a → coeff n (A ^ k) = 0 := by
  induction k with
  | zero => intro n hn; simp at hn
  | succ k ih =>
    intro n hn
    rw [pow_succ']
    have e : (k + 1) * a = a + k * a := by ring
    apply coeff_mul_eq_zero_of_degree_lt_add' hA ih n
    rw [e] at hn; exact hn
theorem coeff_pow_eq_zero_of_cc {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    {n : σ →₀ ℕ} {k : ℕ} (h : n.degree < k) : coeff n (f ^ k) = 0 := by
  have h1 : ∀ m, m.degree < 1 → coeff m f = 0 := by
    intro m hm
    have hm0 := (Finsupp.degree_eq_zero_iff m).1 $ by omega
    subst hm0
    simpa using hf
  apply coeff_pow_eq_zero_of_degree_lt_mul h1 k n
  simpa using h
theorem coeff_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    {n : σ →₀ ℕ} {N : ℕ} (hN : n.degree < N) :
    coeff n (mvExp f) =
      ∑ k ∈ range N, ((k.factorial : K))⁻¹ * coeff n (f ^ k) := by
  classical
  unfold mvExp
  rw [PowerSeries.coeff_subst $ hasSubst_of_cc hf,
    finsum_eq_sum_of_support_subset _ (s := range N) ?_]
  refine sum_congr rfl fun k _ => ?_
  simp [PowerSeries.coeff_exp]
  intro k hk
  rw [Function.mem_support] at hk
  simp [Finset.coe_range, Set.mem_Iio]
  by_contra hkN
  apply hk
  simp [coeff_pow_eq_zero_of_cc hf $ show n.degree < k by omega]

theorem mvExp_zero : mvExp (0 : MvPowerSeries σ K) = 1 := by
  classical
  ext n
  rw [coeff_mvExp (map_zero _) $ lt_succ_self n.degree, sum_range_succ']
  simp

theorem constantCoeff_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (mvExp f) = 1 := by
  simpa using (coeff_mvExp hf (n := 0) (N := 1) $ by simp)

private theorem coeff_mvExp_eq_coeff_trunc_sum {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (N : ℕ) (m : σ →₀ ℕ) (hm : m.degree < N) :
    coeff m (mvExp f) =
      coeff m (∑ k ∈ range N, ((k.factorial : K))⁻¹ • f ^ k) := by
  rw [coeff_mvExp hf hm, map_sum]
  simp [map_smul, smul_eq_mul]

private theorem coeff_mul_congr_of_degree_lt {A A' B B' : MvPowerSeries σ K} {N : ℕ}
    (hA : ∀ m, m.degree < N → coeff m A = coeff m A')
    (hB : ∀ m, m.degree < N → coeff m B = coeff m B')
    (n : σ →₀ ℕ) (hn : n.degree < N) :
    coeff n (A * B) = coeff n (A' * B') := by
  classical
  rw [coeff_mul, coeff_mul]
  refine sum_congr rfl fun p hp => ?_
  first
  | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  | simp [mem_antidiagonal] at hp
  | simp at hp
  have hd : p.1.degree + p.2.degree = n.degree := by rw [← finsupp_degree_add, hp]
  rw [hA _ $ by omega, hB _ $ by omega]

theorem pderiv_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (i : σ) :
    pderiv i (mvExp f) = pderiv i f * mvExp f := by
  classical
  ext n
  have hE : pderiv i
      (∑ k ∈ range (n.degree + 1 + 1), ((k.factorial : K))⁻¹ • f ^ k) =
      pderiv i f *
        ∑ k ∈ range (n.degree + 1), ((k.factorial : K))⁻¹ • f ^ k := by
    rw [map_sum, mul_sum, sum_range_succ' _ $ n.degree + 1]
    have h0 : pderiv i (((Nat.factorial 0 : K))⁻¹ • f ^ 0) = 0 := by simp
    rw [h0, add_zero]
    refine sum_congr rfl fun k _ => ?_
    have hc : (((k + 1).factorial : K))⁻¹ * ((k + 1 : ℕ) : K) = ((k.factorial : K))⁻¹ := by
      rw [Nat.factorial_succ]
      push_cast
      have : (k.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      field_simp
    rw [Derivation.map_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, ← Nat.cast_smul_eq_nsmul K,
      smul_smul, hc, mul_smul_comm, mul_comm $ pderiv i f]
  rw [coeff_pderiv, coeff_mvExp_eq_coeff_trunc_sum hf (n.degree + 1 + 1) _ ?_,
    ← coeff_pderiv, hE]
  exact coeff_mul_congr_of_degree_lt (fun _ _ => rfl) (fun m hm => (coeff_mvExp_eq_coeff_trunc_sum hf _ m hm).symm) n
    $ lt_succ_self _
  rw [finsupp_degree_add, Finsupp.degree_single]
  omega

private theorem inv_factorial_mul_choose_eq {k m : ℕ} (h : m ≤ k) :
    ((k.factorial : K))⁻¹ * (k.choose m : K) =
      ((m.factorial : K))⁻¹ * (((k - m).factorial : K))⁻¹ := by
  have h3 : (k.choose m : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos h).ne'
  rw [← Nat.choose_mul_factorial_mul_factorial h]
  push_cast
  first
  | (field_simp; done)
  | (field_simp; ring)

private theorem mvExp_add_binomial_series_coefficients {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f + g) = mvExp f * mvExp g := by
  classical
  have hfg : MvPowerSeries.constantCoeff (f + g) = 0 := by simp [hf, hg]
  ext n
  rw [coeff_mvExp hfg $ lt_succ_self n.degree,
    coeff_mul_congr_of_degree_lt (coeff_mvExp_eq_coeff_trunc_sum hf $ n.degree + 1) (coeff_mvExp_eq_coeff_trunc_sum hg $ n.degree + 1) n
      $ lt_succ_self _,
    Finset.sum_mul_sum, map_sum]
  simp only [map_sum, smul_mul_smul_comm, map_smul, smul_eq_mul]
  have hL : ∀ k ∈ range (n.degree + 1),
      ((k.factorial : K))⁻¹ * coeff n ((f + g) ^ k) =
        ∑ m ∈ range (k + 1), ((m.factorial : K))⁻¹ * (((k - m).factorial : K))⁻¹ *
          coeff n (f ^ m * g ^ (k - m)) := by
    intro k _
    rw [add_pow, map_sum, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := K)) $ k.choose m,
      mul_comm _ $ MvPowerSeries.C _, MvPowerSeries.coeff_C_mul, ← mul_assoc, inv_factorial_mul_choose_eq $ Nat.lt_succ_iff.1 $ Finset.mem_range.1 hm]
  rw [sum_congr rfl hL]
  have hflip := Finset.sum_range_diag_flip (n.degree + 1) fun a b =>
    ((a.factorial : K))⁻¹ * ((b.factorial : K))⁻¹ * coeff n (f ^ a * g ^ b)
  try simp only at hflip
  rw [hflip]
  refine sum_congr rfl fun i hi => ?_
  refine Finset.sum_subset (fun j hj => Finset.mem_range.2
    $ lt_of_lt_of_le (Finset.mem_range.1 hj) $ Nat.sub_le _ _) ?_
  intro j hj hj'
  simp only [Finset.mem_range, not_lt] at hi hj hj'
  rw [coeff_mul_eq_zero_of_degree_lt_add' (fun m hm => coeff_pow_eq_zero_of_cc hf hm)
    (fun m hm => coeff_pow_eq_zero_of_cc hg hm) n $ by omega, mul_zero]

theorem mvExp_neg {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    mvExp (-f) * mvExp f = 1 := by
  have h := mvExp_add_binomial_series_coefficients (f := -f) (g := f) (by simp [hf]) hf
  rw [neg_add_cancel, mvExp_zero] at h
  exact h.symm

theorem mvExp_mul_neg {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    mvExp f * mvExp (-f) = 1 := by
  rw [mul_comm]
  exact mvExp_neg hf

theorem isUnit_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    IsUnit $ mvExp f := isUnit_iff_exists_inv.2 ⟨_, mvExp_mul_neg hf⟩

theorem mvExp_add {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f + g) = mvExp f * mvExp g := mvExp_add_binomial_series_coefficients hf hg

theorem mvExp_sub_mul {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f - g) * mvExp g = mvExp f := by
  rw [← mvExp_add (by simp [hf, hg]) hg, sub_add_cancel]




private theorem eq_zero_of_mvExp_eq_one {h : MvPowerSeries σ K} (hh : MvPowerSeries.constantCoeff h = 0)
    (he : mvExp h = 1) : h = 0 := by
  classical
  by_contra hne
  have hex : ∃ d, ∃ m, m.degree = d ∧ coeff m h ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne $ MvPowerSeries.ext fun m => by simpa using hall _ m rfl
  obtain ⟨m, hmd, hm⟩ := Nat.find_spec hex
  have hmin : ∀ m', m'.degree < find hex → coeff m' h = 0 := by
    intro m' hm'
    by_contra hc
    exact Nat.find_min hex hm' ⟨m', rfl, hc⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hm
    simpa using hh
  have hd1 : 1 ≤ find hex := by
    rw [← hmd]
    by_contra h0
    exact hm0 $ (Finsupp.degree_eq_zero_iff m).1 $ by omega
  have he' := congrArg (coeff m) he
  rw [coeff_mvExp hh $ show m.degree < find hex + 1 by omega, Finset.sum_eq_single 1] at he'
  simp [hm0, coeff_one] at he'
  exact hm he'
  intro k _ hk1
  rcases Nat.lt_or_gt_of_ne hk1 with hk0 | hk2
  have hk : k = 0 := by omega
  subst hk
  simp [hm0, coeff_one]
  rw [coeff_pow_eq_zero_of_degree_lt_mul hmin k m (by rw [hmd]; nlinarith), mul_zero]
  intro h1
  exact absurd (Finset.mem_range.2 $ by omega) h1

theorem mvExp_inj {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) (h : mvExp f = mvExp g) : f = g := by
  have h1 := mvExp_sub_mul hf hg
  rw [h] at h1
  have h2 : mvExp (f - g) = 1 := by
    calc mvExp (f - g) = mvExp (f - g) * mvExp g * mvExp (-g) := by
          rw [mul_assoc, mvExp_mul_neg hg, mul_one]
      _ = 1 := by rw [h1, mvExp_mul_neg hg]
  exact sub_eq_zero.1 $ eq_zero_of_mvExp_eq_one (by simp [hf, hg]) h2

theorem derivative_mvExp {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.derivative (mvExp f : PowerSeries K) =
      PowerSeries.derivative f * (mvExp f : PowerSeries K) := by
  unfold mvExp
  rw [PowerSeries.derivative_subst $ hasSubst_of_cc hf, PowerSeries.derivative_exp, mul_comm]

theorem subst_mvExp {f : PowerSeries K} {a : MvPowerSeries σ K}
    (hf : PowerSeries.constantCoeff f = 0) (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst a (mvExp f : PowerSeries K) = mvExp (PowerSeries.subst a f) := by
  unfold mvExp
  exact PowerSeries.subst_comp_subst_apply (hasSubst_of_cc hf) (hasSubst_of_cc ha) _




theorem formalExpLaws' : MvExpLaws := by
  intro K _ _ σ
  exact ⟨mvExp_zero, fun f hf => constantCoeff_mvExp hf, fun f g hf hg => mvExp_add hf hg,
    fun f g hf hg h => mvExp_inj hf hg h⟩

theorem formalExpSubst' : MvExpSubst := by
  intro K _ _ σ f a hf ha
  exact subst_mvExp hf ha

end Formalism.L2.Th1.C
end
section
open PowerSeries

namespace Formalism.L2.Th1.C

namespace IntegralMvPolynomialLemmas

section Chain

variable {A : Type*} [CommRing A] {σ : Type*}

theorem coeff_subst_congr {g h : PowerSeries A} {a : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (e : σ →₀ ℕ)
    (hgh : ∀ k ≤ e.degree, coeff k g = coeff k h) :
    MvPowerSeries.coeff e (g.subst a) = MvPowerSeries.coeff e (h.subst a) := by
  have hs := HasSubst.of_constantCoeff_zero ha
  rw [coeff_subst hs, coeff_subst hs]
  refine finsum_congr fun k => ?_
  by_cases hk : k ≤ e.degree
  rw [hgh k hk]
  have : MvPowerSeries.coeff e (a ^ k) = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le ?_ $ MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k ha
    exact_mod_cast (not_le.mp hk)
  rw [this, smul_zero, smul_zero]

theorem pderiv_subst_coe (p : Polynomial A) {a : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv i ((p : PowerSeries A).subst a) =
      (derivative (p : PowerSeries A)).subst a * MvPowerSeries.pderiv i a := by
  have hs := HasSubst.of_constantCoeff_zero ha
  rw [subst_coe hs, derivative_coe, subst_coe hs, Derivation.comp_aeval_eq, smul_eq_mul]

theorem degree_le_of_mem_antidiagonal [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) : x.1.degree ≤ d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, map_add]
  omega

theorem pderiv_subst (g : PowerSeries A) {a : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv i (g.subst a) =
      (derivative g).subst a * MvPowerSeries.pderiv i a := by
  classical
  ext d
  have hdeg : (d + Finsupp.single i 1).degree = d.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have h1 : MvPowerSeries.coeff (d + Finsupp.single i 1) (g.subst a) =
      MvPowerSeries.coeff (d + Finsupp.single i 1)
        (((trunc (d.degree + 2) g : Polynomial A) : PowerSeries A).subst a) := by
    apply coeff_subst_congr ha
    intro k hk
    rw [coeff_coe_trunc_of_lt $ by omega]
  rw [MvPowerSeries.coeff_pderiv, h1, ← MvPowerSeries.coeff_pderiv, pderiv_subst_coe _ ha,
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  apply coeff_subst_congr ha
  intro k hk
  have := degree_le_of_mem_antidiagonal hx
  rw [coeff_derivative, coeff_derivative, coeff_coe_trunc_of_lt $ by omega]

theorem degree_snd_lt [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) (h1 : x.1 ≠ 0) : x.2.degree < d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have : x.1.degree ≠ 0 := fun h => h1 $ (Finsupp.degree_eq_zero_iff _).mp h
  rw [← hx, map_add]
  omega

theorem degree_fst_lt [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) (h2 : x.2 ≠ 0) : x.1.degree < d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have : x.2.degree ≠ 0 := fun h => h2 $ (Finsupp.degree_eq_zero_iff _).mp h
  rw [← hx, map_add]
  omega

end Chain

section Integral

variable {K : Type} [Field K] {σ : Type} {R : Subring K}

theorem intMv_one : IntMv R (1 : MvPowerSeries σ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs
  exact R.one_mem
  exact R.zero_mem

theorem intMv_mul {F G : MvPowerSeries σ K} (hF : IntMv R F) (hG : IntMv R G) :
    IntMv R $ F * G := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (hF p.1) $ hG p.2

theorem intMv_pow {F : MvPowerSeries σ K} (hF : IntMv R F) (n : ℕ) : IntMv R $ F ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact intMv_one
  | succ n ih => rw [pow_succ]; exact intMv_mul ih hF

theorem intMv_prod {ι : Type*} (s : Finset ι) {F : ι → MvPowerSeries σ K}
    (hF : ∀ i ∈ s, IntMv R $ F i) : IntMv R (∏ i ∈ s, F i) :=
  Finset.prod_induction F (IntMv R) (fun _ _ => intMv_mul) intMv_one hF


theorem intMv_subst {c : PowerSeries K} (hc : IntPS R c) {a : MvPowerSeries σ K}
    (ha : IsPt R a) : IntMv R $ c.subst a := by
  intro e
  rw [coeff_subst $ HasSubst.of_constantCoeff_zero ha.1]
  refine finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun k => ?_
  rw [smul_eq_mul]
  exact R.mul_mem (hc k) $ intMv_pow ha.2 k e

theorem intMv_substMv {τ : Type} [Finite σ] {F : MvPowerSeries σ K} (hF : IntMv R F)
    {a : σ → MvPowerSeries τ K} (ha : ∀ s, IsPt R $ a s) : IntMv R $ MvPowerSeries.subst a F := by
  intro e
  rw [MvPowerSeries.coeff_subst $ MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (ha s).1]
  refine finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun d => ?_
  rw [smul_eq_mul]
  exact R.mul_mem (hF d) $ intMv_prod _ (fun s _ => intMv_pow (ha s).2 _) e

theorem intMv_of_mul_eq_one {U V : MvPowerSeries σ K} (hU : IntMv R U)
    (hU0 : MvPowerSeries.constantCoeff U = 1) (hUV : U * V = 1) : IntMv R V := by
  classical
  have hV : V = 1 - (U - 1) * V := by rw [sub_mul, hUV]
                                      ring
  have hh : IntMv R $ U - 1 := fun n => by
    rw [map_sub]
    exact R.sub_mem (hU n) $ intMv_one n
  have hh0 : MvPowerSeries.coeff 0 (U - 1) = 0 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, hU0, map_one, sub_self]
  have key : ∀ m n, n.degree = m → MvPowerSeries.coeff n V ∈ R := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hn
      rw [hV, map_sub, MvPowerSeries.coeff_mul]
      refine R.sub_mem (intMv_one n) $ Subring.sum_mem _ fun p hp => ?_
      by_cases h1 : p.1 = 0
      rw [h1, hh0, zero_mul]
      exact R.zero_mem
      exact R.mul_mem (hh _) $ ih _ (hn ▸ degree_snd_lt hp h1) _ rfl
  exact fun n => key _ n rfl

theorem intMv_of_sq {g : MvPowerSeries σ K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hg0 : MvPowerSeries.constantCoeff g = 1) (hgg : IntMv R $ g * g) : IntMv R g := by
  classical
  have hh0 : MvPowerSeries.coeff 0 (g - 1) = 0 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, hg0, map_one, sub_self]
  have hid : ∀ n, MvPowerSeries.coeff n (g - 1) = (2 : K)⁻¹ * (MvPowerSeries.coeff n (g * g)
      - MvPowerSeries.coeff n (1 : MvPowerSeries σ K)
      - MvPowerSeries.coeff n ((g - 1) * (g - 1))) := by
    intro n
    have : g * g - 1 - (g - 1) * (g - 1) = (g - 1) + (g - 1) := by ring
    rw [← map_sub, ← map_sub, this, map_add]
    field_simp
    ring
  have key : ∀ m n, n.degree = m → MvPowerSeries.coeff n (g - 1) ∈ R := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hn
      rw [hid n, MvPowerSeries.coeff_mul n $ g - 1]
      refine R.mul_mem h2 $ R.sub_mem (R.sub_mem (hgg n) $ intMv_one n)
        $ Subring.sum_mem _ fun p hp => ?_
      by_cases h1 : p.1 = 0
      rw [h1, hh0, zero_mul]
      exact R.zero_mem
      by_cases h2' : p.2 = 0
      rw [h2', hh0, mul_zero]
      exact R.zero_mem
      exact R.mul_mem (ih _ (hn ▸ degree_fst_lt hp h2') _ rfl)
        $ ih _ (hn ▸ degree_snd_lt hp h1) _ rfl
  intro n
  have : g = (g - 1) + 1 := by ring
  rw [this, map_add]
  exact R.add_mem (key _ n rfl) $ intMv_one n

end Integral

section Exp

variable {K : Type} [Field K] [CharZero K] {σ : Type}

theorem constantCoeff_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (mvExp f) = 1 := by
  have h := coeff_subst_congr (g := exp K) (h := C (1 : K)) hf 0 fun k hk => by
    have : k = 0 := by simpa using hk
    subst this
    simp
  rw [subst_C] at h
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold mvExp
  rw [h]
  simp


theorem substMv_mvExp {τ : Type} [Finite σ] {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by
  unfold mvExp
  rw [subst_def, subst_def]
  exact MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero hf).const
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) $ exp K

end Exp

end IntegralMvPolynomialLemmas

open IntegralMvPolynomialLemmas

theorem lGSubgroup_of (hE : MvExpLaws) : LGSubgroup := by
  intro K _ _ R σ
  obtain ⟨h0, -, hadd, -⟩ := hE K σ
  refine ⟨⟨map_zero _, ?_⟩, ?_, ?_⟩
  rw [h0]
  exact intMv_one
  intro f g hf hg
  refine ⟨by rw [map_add, hf.1, hg.1, add_zero], ?_⟩
  rw [hadd f g hf.1 hg.1]
  exact intMv_mul hf.2 hg.2
  intro f hf
  have hn : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf.1, neg_zero]
  refine ⟨hn, intMv_of_mul_eq_one hf.2 (constantCoeff_mvExp hf.1) ?_⟩
  rw [← hadd f (-f) hf.1 hn, add_neg_cancel, h0]

theorem lGHalf_of (hE : MvExpLaws) : LGHalf := by
  intro K _ _ R σ h2 f hf
  obtain ⟨-, -, hadd, -⟩ := hE K σ
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    have h := hf.1
    rw [map_add, ← two_mul] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  refine ⟨hf0, intMv_of_sq h2 two_ne_zero (constantCoeff_mvExp hf0) ?_⟩
  rw [← hadd f f hf0 hf0]
  exact hf.2



theorem expIntegralMvSubst' : LGSubstMv := by
  intro K _ _ R σ _ f hf τ a ha
  have ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0 := fun s => (ha s).1
  use MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0) ha0 hf.1
  rw [← substMv_mvExp hf.1 ha0]
  exact intMv_substMv hf.2 ha


end Formalism.L2.Th1.C
end
section
open scoped BigOperators
open MvPowerSeries (constantCoeff pderiv pderiv_one smul_eq_C_mul)
open PowerSeries (coe_substAlgHom coeff_derivative coeff_mk derivative subst)
open Finset

namespace Formalism.L2.Th1.C

variable {K : Type} [Field K] [CharZero K] {σ : Type}

theorem binom_zero (z : K) : binom z 0 = 1 := by simp [binom]

theorem binom_succ (z : K) (n : ℕ) : ((n : K) + 1) * binom z (n + 1) = (z - n) * binom z n := by
  unfold binom
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp

theorem binom_pascal (z : K) (k : ℕ) :
    binom (z + 1) (k + 1) = binom z (k + 1) + binom z k := by
  unfold binom
  rw [Finset.prod_range_succ' fun i => z + 1 - (i : K),
    Finset.prod_range_succ fun i => z - (i : K), Nat.factorial_succ]
  have e : ∏ i ∈ range k, (z + 1 - ((i + 1 : ℕ) : K)) = ∏ i ∈ range k, (z - (i : K)) :=
    Finset.prod_congr rfl fun i _ => by push_cast
                                        ring
  rw [e]
  push_cast
  field_simp
  ring

theorem binom_zero_succ (k : ℕ) : binom (0 : K) (k + 1) = 0 := by
  unfold binom
  rw [Finset.prod_range_succ']
  simp

def binomSeries (z : K) : PowerSeries K := PowerSeries.mk $ binom z

theorem binomSeries_ode (z : K) :
    (1 + PowerSeries.X) * derivative (binomSeries z) = z • binomSeries z := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_derivative, PowerSeries.coeff_smul]
  cases n with
  | zero =>
    have h := binom_succ z 0
    simp [binomSeries, coeff_mk, PowerSeries.coeff_zero_X_mul, smul_eq_mul]
    push_cast at h ⊢
    linear_combination h
  | succ n =>
    have h := binom_succ z $ n + 1
    rw [PowerSeries.coeff_succ_X_mul, coeff_derivative]
    simp [binomSeries, coeff_mk, smul_eq_mul]
    push_cast at h ⊢
    linear_combination h

theorem constantCoeff_subst_binomSeries (z : K) {g : MvPowerSeries σ K}
    (hg : constantCoeff g = 0) :
    constantCoeff (subst g $ binomSeries z) = 1 := by
  have h := IntegralMvPolynomialLemmas.coeff_subst_congr (g := binomSeries z) (h := PowerSeries.C (1 : K)) hg 0
    fun k hk => by
      have : k = 0 := by simpa using hk
      subst this
      simp [binomSeries, binom_zero]
  rw [PowerSeries.subst_C] at h
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  simp

theorem subst_binomSeries_eq_mvExp (z : K) {f : MvPowerSeries σ K}
    (hf : constantCoeff f = 0) :
    subst (mvExp f - 1) (binomSeries z) = mvExp (z • f) := by
  have hg : constantCoeff (mvExp f - 1) = 0 := by
    rw [map_sub, constantCoeff_mvExp hf, map_one, sub_self]
  have hs := hasSubst_of_cc hg
  have hzf : constantCoeff (z • f) = 0 := by
    rw [smul_eq_C_mul, map_mul, hf, mul_zero]
  have hnzf : constantCoeff (-(z • f)) = 0 := by rw [map_neg, hzf, neg_zero]
  set B := subst (mvExp f - 1) (binomSeries z) with hB
  have hode : mvExp f * subst (mvExp f - 1) (derivative $ binomSeries z)
      = z • B := by
    have h := congrArg (subst (mvExp f - 1)) $ binomSeries_ode z
    rw [PowerSeries.subst_mul hs, PowerSeries.subst_add hs, PowerSeries.subst_X hs,
      PowerSeries.subst_smul hs, ← coe_substAlgHom hs, map_one,
      coe_substAlgHom hs] at h
    rw [hB, ← h]
    ring
  have hd : ∀ i, pderiv i B =
      MvPowerSeries.C z * pderiv i f * B := by
    intro i
    apply (isUnit_mvExp hf).mul_left_cancel
    rw [hB, IntegralMvPolynomialLemmas.pderiv_subst _ hg, ← mul_assoc, hode, map_sub, pderiv_one, sub_zero,
      pderiv_mvExp hf, smul_eq_C_mul]
    ring
  have key : B * mvExp (-(z • f)) = 1 := by
    refine MvPowerSeries.pderiv.ext (fun i => ?_) ?_
    rw [Derivation.leibniz, pderiv_mvExp hnzf, hd, map_neg, smul_eq_C_mul,
      Derivation.leibniz, MvPowerSeries.pderiv_C, pderiv_one]
    simp [smul_eq_mul]
    ring
    rw [map_mul, constantCoeff_mvExp hnzf, hB, constantCoeff_subst_binomSeries z hg, map_one,
      mul_one]
  calc B = B * (mvExp (-(z • f)) * mvExp (z • f)) := by rw [mvExp_neg hzf, mul_one]
    _ = mvExp (z • f) := by rw [← mul_assoc, key, one_mul]

theorem expIntegralBinomial' : LGBinom := by
  intro K _ _ R σ z hz f hf
  refine ⟨by rw [smul_eq_C_mul, map_mul, hf.1, mul_zero], ?_⟩
  rw [← subst_binomSeries_eq_mvExp z hf.1]
  refine IntegralMvPolynomialLemmas.intMv_subst (fun n => ?_) ⟨?_, fun n => ?_⟩
  rw [binomSeries, coeff_mk]
  exact hz n
  rw [map_sub, constantCoeff_mvExp hf.1, map_one, sub_self]
  rw [map_sub]
  exact R.sub_mem (hf.2 n) $ IntegralMvPolynomialLemmas.intMv_one n

theorem intBinomialScalar' : IntBinomScalar := by
  intro K _ _ R n k
  induction k generalizing n with
  | zero => rw [binom_zero]; exact R.one_mem
  | succ k ih =>
    induction n using Int.induction_on with
    | zero => rw [Int.cast_zero, binom_zero_succ]; exact R.zero_mem
    | succ m hm =>
      have h := binom_pascal ((m : ℤ) : K) k
      have e : (((m : ℤ) + 1 : ℤ) : K) = ((m : ℤ) : K) + 1 := by push_cast; ring
      rw [e, h]
      exact R.add_mem hm $ ih _
    | pred m hm =>
      have h := binom_pascal (((-(m : ℤ) - 1 : ℤ)) : K) k
      have e : (((-(m : ℤ) - 1 : ℤ)) : K) + 1 = ((-(m : ℤ) : ℤ) : K) := by push_cast; ring
      rw [e] at h
      have h2 : binom (((-(m : ℤ) - 1 : ℤ)) : K) (k + 1) =
          binom ((-(m : ℤ) : ℤ) : K) (k + 1) - binom (((-(m : ℤ) - 1 : ℤ)) : K) k := by
        rw [h]; ring
      rw [h2]
      exact R.sub_mem hm $ ih _

end Formalism.L2.Th1.C
end
section
open scoped BigOperators
open PowerSeries

namespace Formalism.L2.Th1.C

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [CharZero K]

def pExp (f : PowerSeries K) : PowerSeries K := mvExp f

theorem pExp_zero (hE : MvExpLaws) : pExp (0 : PowerSeries K) = 1 := (hE K Unit).1

theorem constantCoeff_pExp (hE : MvExpLaws) (f : PowerSeries K) (hf : constantCoeff f = 0) :
    constantCoeff (pExp f) = 1 := (hE K Unit).2.1 f hf

theorem pExp_add (hE : MvExpLaws) (f g : PowerSeries K) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : pExp (f + g) = pExp f * pExp g := (hE K Unit).2.2.1 f g hf hg

theorem pExp_mul_neg (hE : MvExpLaws) (f : PowerSeries K) (hf : constantCoeff f = 0) :
    pExp f * pExp (-f) = 1 := by
  rw [← pExp_add hE f (-f) hf $ by rw [map_neg, hf, neg_zero], add_neg_cancel, pExp_zero hE]

theorem pExp_nsmul (hE : MvExpLaws) (f : PowerSeries K) (hf : constantCoeff f = 0) (k : ℕ) :
    pExp (k • f) = pExp f ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, pExp_zero hE]
  | succ k ih =>
    have hk : constantCoeff (k • f) = 0 := by rw [map_nsmul, hf, smul_zero]
    rw [succ_nsmul, pExp_add hE _ _ hk hf, ih, pow_succ]

theorem rescale_pExp (a : K) (f : PowerSeries K) (hf : constantCoeff f = 0) :
    rescale a (pExp f) = pExp (rescale a f) := by
  show rescale a (PowerSeries.subst f $ PowerSeries.exp K) =
    PowerSeries.subst (rescale a f) (PowerSeries.exp K)
  rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hf) $ PowerSeries.HasSubst.of_constantCoeff_zero' $ by simp, ← PowerSeries.rescale_eq_subst]

theorem derivative_pExp (f : PowerSeries K) (hf : constantCoeff f = 0) :
    derivative (pExp f) = pExp f * derivative f := by
  show derivative (PowerSeries.subst f $ PowerSeries.exp K) =
    PowerSeries.subst f (PowerSeries.exp K) * derivative f
  rw [PowerSeries.derivative_subst $ PowerSeries.HasSubst.of_constantCoeff_zero' hf, PowerSeries.derivative_exp]

theorem hasSecondLogDeriv_one : HasSecondLogDeriv (1 : PowerSeries K) 0 := by
  simp [HasSecondLogDeriv]

theorem hasSecondLogDeriv_mul {f h g₁ g₂ : PowerSeries K} (h1 : HasSecondLogDeriv f g₁) (h2 : HasSecondLogDeriv h g₂) :
    HasSecondLogDeriv (f * h) $ g₁ + g₂ := by
  unfold HasSecondLogDeriv at *
  have e1 : derivative (f * h) = derivative f * h + f * derivative h := by
    rw [Derivation.leibniz]
    simp [smul_eq_mul]
    ring
  have e2 : derivative (derivative f * h + f * derivative h) =
      derivative (derivative f) * h + 2 * (derivative f * derivative h) +
        f * derivative (derivative h) := by
    rw [map_add, Derivation.leibniz, Derivation.leibniz]
    simp [smul_eq_mul]
    ring
  rw [e1, e2]
  linear_combination h ^ 2 * h1 + f ^ 2 * h2

theorem hasSecondLogDeriv_prod {ι : Type} (s : Finset ι) (f g : ι → PowerSeries K)
    (h : ∀ i ∈ s, HasSecondLogDeriv (f i) $ g i) : HasSecondLogDeriv (∏ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  intro _
  rw [Finset.prod_empty, Finset.sum_empty]
  exact hasSecondLogDeriv_one
  intro a s ha ih hh
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact hasSecondLogDeriv_mul (hh a $ Finset.mem_insert_self a s)
    $ ih fun i hi => hh i $ Finset.mem_insert_of_mem hi

theorem hasSecondLogDeriv_powerSeriesExp (L : PowerSeries K) (hL : constantCoeff L = 0) :
    HasSecondLogDeriv (pExp L) $ derivative $ derivative L := by
  unfold HasSecondLogDeriv
  have h1 := derivative_pExp L hL
  rw [h1, Derivation.leibniz, h1]
  simp [smul_eq_mul]
  ring

theorem hasSecondLogDeriv_right_unique {f g g' : PowerSeries K} (hf : f ≠ 0) (h1 : HasSecondLogDeriv f g)
    (h2 : HasSecondLogDeriv f g') : g = g' := by
  unfold HasSecondLogDeriv at h1 h2
  exact mul_right_cancel₀ (pow_ne_zero 2 hf) $ h1.symm.trans h2

theorem eq_C_mul_of_wronskian {a b : PowerSeries K} (hb : constantCoeff b = 1)
    (h : b * derivative a = a * derivative b) : a = C (constantCoeff a) * b := by
  have hb0 : constantCoeff b ≠ 0 := by rw [hb]
                                       exact one_ne_zero
  have hq : derivative (a * b⁻¹) = derivative (C $ constantCoeff a) := by
    rw [Derivation.leibniz, PowerSeries.derivative_inv', PowerSeries.derivative_C]
    simp only [smul_eq_mul]
    linear_combination (-(b⁻¹ * derivative a)) * PowerSeries.mul_inv_cancel b hb0 + (b⁻¹ ^ 2) * h
  have hq2 :=
    PowerSeries.derivative.ext hq $ by
      rw [map_mul, PowerSeries.constantCoeff_inv, hb, inv_one, mul_one, PowerSeries.constantCoeff_C]
  calc a = a * b⁻¹ * b := by rw [mul_assoc, PowerSeries.inv_mul_cancel b hb0, mul_one]
    _ = C (constantCoeff a) * b := by rw [hq2]

theorem hasSecondLogDeriv_left_unique {f h g : PowerSeries K} (hf : constantCoeff f = 1)
    (hh : constantCoeff h = 1)
    (h1 : constantCoeff (derivative f) = constantCoeff (derivative h))
    (hfg : HasSecondLogDeriv f g) (hhg : HasSecondLogDeriv h g) : f = h := by
  unfold HasSecondLogDeriv at hfg hhg
  have if1 := PowerSeries.mul_inv_cancel f (by rw [hf]; exact one_ne_zero)
  have ih1 := PowerSeries.mul_inv_cancel h (by rw [hh]; exact one_ne_zero)
  have dA : derivative (derivative f * f⁻¹) = g := by
    rw [Derivation.leibniz, PowerSeries.derivative_inv']
    simp only [smul_eq_mul]
    linear_combination f⁻¹ ^ 2 * hfg +
      (g * (f * f⁻¹ + 1) - derivative (derivative f) * f⁻¹) * if1
  have dB : derivative (derivative h * h⁻¹) = g := by
    rw [Derivation.leibniz, PowerSeries.derivative_inv']
    simp only [smul_eq_mul]
    linear_combination h⁻¹ ^ 2 * hhg +
      (g * (h * h⁻¹ + 1) - derivative (derivative h) * h⁻¹) * ih1
  have hA : derivative f * f⁻¹ = derivative h * h⁻¹ := by
    apply PowerSeries.derivative.ext (by rw [dA, dB])
    rw [map_mul, map_mul, PowerSeries.constantCoeff_inv, PowerSeries.constantCoeff_inv, hf, hh, h1]
  have hw : h * derivative f = f * derivative h := by
    linear_combination (f * h) * hA + (-(h * derivative f)) * if1 + (f * derivative h) * ih1
  rw [eq_C_mul_of_wronskian hh hw, hf, map_one, one_mul]

end SlopeTestRemainingChoices

section Calc

variable {K : Type} [Field K] [CharZero K]

theorem derivative_rescale (a : K) (f : PowerSeries K) :
    derivative (rescale a f) = a • rescale a (derivative f) := by
  ext n
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem rescale_C_eq (a b : K) : rescale a (C b : PowerSeries K) = C b := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with hn <;> simp [hn]

theorem constantCoeff_rescale_eq (a : K) (f : PowerSeries K) :
    constantCoeff (rescale a f) = constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_rescale, pow_zero, one_mul]

theorem derivative2_dblInt (e : PowerSeries K) :
    derivative (derivative $ dblInt e) = e := by
  ext n
  simp only [dblInt, PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
  rw [if_neg $ show ¬ (n + 1 + 1 < 2) by omega, show n + 1 + 1 - 2 = n by omega]
  push_cast
  rw [show (n : K) + 1 + 1 - 1 = n + 1 by ring]
  have h2 : (n : K) + 1 + 1 ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
  field_simp <;> ring

theorem derivative2_lam (e : PowerSeries K) (s2 : K) :
    derivative (derivative $ lam e s2) = e + C s2 := by
  unfold lam
  rw [map_add, map_add, derivative2_dblInt]
  congr 1
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_C]
  rcases n with _ | n
  norm_num
  simp

theorem constantCoeff_lam (e : PowerSeries K) (s2 : K) : constantCoeff (lam e s2) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [lam, dblInt]

theorem constantCoeff_derivative_lam (e : PowerSeries K) (s2 : K) :
    constantCoeff (derivative $ lam e s2) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp [lam, dblInt, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

theorem prod_wpShift_form {ι : Type} (s : Finset ι) (e : PowerSeries K) (c : ι → K) :
    ∃ r, ∏ P ∈ s, wpShift e (c P) = 1 + X ^ 2 * r := by
  classical
  refine Finset.induction_on s ⟨0, by simp⟩ ?_
  rintro a s ha ⟨r, hr⟩
  use (e - C (c a)) + r + X ^ 2 * (e - C (c a)) * r
  rw [Finset.prod_insert ha, hr, wpShift]
  ring

end Calc

section Main

theorem isogenyReduce_of (hE : MvExpLaws) : IsogenyReduce := by
  intro K _ _ e s2 ι _ c al hal
  have hL := constantCoeff_lam e s2
  have hR : constantCoeff (rescale al (lam e s2)) = 0 := by rw [constantCoeff_rescale_eq, hL]
  have hresc : rescale al (sgStar e s2) = C al * X * pExp (-(rescale al (lam e s2))) := by
    have h1 := rescale_pExp al (-(lam e s2)) (by rw [map_neg, hL, neg_zero])
    rw [map_neg] at h1
    show rescale al (X * pExp (-(lam e s2))) = _
    rw [map_mul, PowerSeries.rescale_X, h1]
  have e1 : (2 * ((Fintype.card ι : K) + 1)) • lam e s2 = (2 * (Fintype.card ι + 1)) • lam e s2 := by
    rw [← Nat.cast_smul_eq_nsmul K]
    norm_num
  have e2 : -((2 : K) • rescale al (lam e s2)) = 2 • (-(rescale al (lam e s2))) := by
    rw [two_smul, two_smul]
    abel
  have hT : pExp ((2 * ((Fintype.card ι : K) + 1)) • lam e s2 - (2 : K) • rescale al (lam e s2)) =
      pExp (lam e s2) ^ (2 * (Fintype.card ι + 1)) * pExp (-(rescale al (lam e s2))) ^ 2 := by
    rw [sub_eq_add_neg, e1, e2,
      pExp_add hE _ _ (by rw [map_nsmul, hL, smul_zero]) (by rw [map_nsmul, map_neg, hR, neg_zero, smul_zero]),
      pExp_nsmul hE _ hL, pExp_nsmul hE _ (by rw [map_neg, hR, neg_zero])]
  have hsg : sgStar e s2 = X * pExp (-(lam e s2)) := rfl
  have hne : (C (al ^ 2) * X ^ (2 * Fintype.card ι + 2) : PowerSeries K) ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero _ PowerSeries.X_ne_zero)
    intro h0
    apply hal
    simpa using congrArg constantCoeff h0
  unfold IsogenyFormula
  change _ ↔ pExp _ = _
  rw [hT, hresc, hsg]
  have lhs : (C al * X * pExp (-(rescale al (lam e s2)))) ^ 2 * X ^ (2 * Fintype.card ι) =
      (C (al ^ 2) * X ^ (2 * Fintype.card ι + 2)) * pExp (-(rescale al (lam e s2))) ^ 2 := by
    rw [map_pow]
    ring
  have rhs : C (al ^ 2) * (X * pExp (-(lam e s2))) ^ (2 * (Fintype.card ι + 1)) * ∏ P, wpShift e (c P) =
      (C (al ^ 2) * X ^ (2 * Fintype.card ι + 2)) *
        (pExp (-(lam e s2)) ^ (2 * (Fintype.card ι + 1)) * ∏ P, wpShift e (c P)) := by
    ring
  rw [lhs, rhs, mul_right_inj' hne]
  constructor
  intro h
  rw [h, ← mul_assoc, ← mul_pow, pExp_mul_neg hE _ hL, one_pow, one_mul]
  intro h
  rw [← h, ← mul_assoc, ← mul_pow, mul_comm (pExp (-(lam e s2))), pExp_mul_neg hE _ hL, one_pow, one_mul]

theorem isogenyIff_of (hE : MvExpLaws) : IsogenyIff := by
  intro K _ _ e s2 ι _ neg c w al hal hendo
  obtain ⟨hneg, hD, hend⟩ := hendo
  rw [isogenyReduce_of hE K e s2 ι c al hal]
  change pExp _ = _ ↔ _
  set Φ := (2 * ((Fintype.card ι : K) + 1)) • lam e s2 - (2 : K) • rescale al (lam e s2) with hΦdef
  have hΦ : constantCoeff Φ = 0 := by
    rw [hΦdef]
    simp [PowerSeries.smul_eq_C_mul, constantCoeff_rescale_eq, constantCoeff_lam e s2]
  have hΦ1 : constantCoeff (derivative Φ) = 0 := by
    rw [hΦdef]
    simp [PowerSeries.smul_eq_C_mul, derivative_rescale, Derivation.map_smul, constantCoeff_rescale_eq,
      constantCoeff_derivative_lam]
  set W := ∏ P, wpShift e (c P) with hWdef
  set g := ∑ P, (2 * e - w P - w (neg P)) with hgdef
  have hWg : HasSecondLogDeriv W g := hasSecondLogDeriv_prod _ _ _ fun P _ => hD P
  have hEg : HasSecondLogDeriv (pExp Φ) $ derivative $ derivative Φ := hasSecondLogDeriv_powerSeriesExp Φ hΦ
  have hsum_neg : ∑ P, w (neg P) = ∑ P, w P := Equiv.sum_comp (Function.Involutive.toPerm neg hneg) w
  have hg : g = (Fintype.card ι : PowerSeries K) * (2 * e) - 2 * ∑ P, w P := by
    rw [hgdef, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum_neg, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hend' : C al ^ 2 * rescale al e = e + ∑ P, w P - C (∑ P, c P) := by
    rw [← map_pow, hend, Finset.sum_sub_distrib, map_sum]
    ring
  have hd : derivative (derivative Φ) = g + C (2 * (∑ P, c P - (al ^ 2 - ((Fintype.card ι : K) + 1)) * s2)) := by
    rw [hΦdef, map_sub, map_sub, Derivation.map_smul, Derivation.map_smul, Derivation.map_smul, Derivation.map_smul,
      derivative_rescale, Derivation.map_smul, derivative_rescale, derivative2_lam, map_add, rescale_C_eq, hg]
    simp only [PowerSeries.smul_eq_C_mul, map_mul, map_sub, map_add, map_pow, map_natCast, map_one, map_ofNat]
    linear_combination (-2 : PowerSeries K) * hend'
  constructor
  intro h
  have hW0 : W ≠ 0 := by
    intro h0
    have h3 := constantCoeff_pExp hE Φ hΦ
    rw [h, h0, map_zero] at h3
    exact zero_ne_one h3
  have hEg' := hEg
  rw [h] at hEg'
  have h1 := hasSecondLogDeriv_right_unique hW0 hEg' hWg
  rw [hd] at h1
  have h2 : C (2 * (∑ P, c P - (al ^ 2 - ((Fintype.card ι : K) + 1)) * s2)) = 0 := by
    linear_combination h1
  have h3 := congrArg constantCoeff h2
  rw [PowerSeries.constantCoeff_C, map_zero] at h3
  linear_combination -1 * (mul_eq_zero.1 h3).resolve_left two_ne_zero
  intro h
  have hΦg : derivative (derivative Φ) = g := by
    rw [hd, ← h, sub_self, mul_zero, map_zero, add_zero]
  obtain ⟨r, hr⟩ := prod_wpShift_form Finset.univ e c
  have hW2 : constantCoeff (derivative W) = 0 := by
    rw [hWdef, hr, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
  have hWg' : HasSecondLogDeriv W $ derivative $ derivative Φ := by rw [hΦg]
                                                                    exact hWg
  exact hasSecondLogDeriv_left_unique (constantCoeff_pExp hE Φ hΦ) (by
      rw [hWdef, hr]
      simp)
    (by rw [derivative_pExp Φ hΦ, map_mul, hΦ1, mul_zero, hW2]) hEg hWg'

theorem isogenyIffBar_of (hE : MvExpLaws) : IsogenyIffBar := by
  intro K _ _ e s2 ι _ neg xP c0 w al albar hal hbar hendo
  rw [isogenyIff_of hE K e s2 ι neg (xP · + c0) w al hal hendo, ← hbar]
  constructor <;> intro h <;> linear_combination h

end Main

end Formalism.L2.Th1.C
end
section
open scoped BigOperators
open Finsupp (single)
open PowerSeries (subst_C subst_def subst_mul subst_zero_of_constantCoeff_zero)

namespace Formalism.L2.Th1.C

namespace Pts

open IntegralMvPolynomialLemmas

section Toolkit

variable {K : Type} [Field K] {σ : Type} {l linv : PowerSeries K}

theorem hasSubst {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) :
    PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx

theorem subst_subst {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 0)
    {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) (f : PowerSeries K) :
    PowerSeries.subst x (PowerSeries.subst g f) = PowerSeries.subst (PowerSeries.subst x g) f :=
  PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
    (hasSubst hx) f

theorem substMv_subst {τ : Type} [Finite σ] {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : PowerSeries K) :
    MvPowerSeries.subst a (PowerSeries.subst g f) =
      PowerSeries.subst (MvPowerSeries.subst a g) f := by
  rw [subst_def, subst_def]
  exact MvPowerSeries.subst_comp_subst_apply (hasSubst hg).const
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) f

theorem constantCoeff_subst {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst x f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hx f hf

theorem constantCoeff_subst_l (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst x l) = 0 :=
  constantCoeff_subst hx h.1

theorem constantCoeff_subst_linv (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst x linv) = 0 :=
  constantCoeff_subst hx h.2.2.1

theorem subst_l_linv (h : IsLogPair l linv) {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (PowerSeries.subst g linv) l = g := by
  rw [← subst_subst h.2.2.1 hg, h.2.2.2.2, PowerSeries.subst_X $ hasSubst hg]

theorem subst_linv_l (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    PowerSeries.subst (PowerSeries.subst x l) linv = x := by
  rw [← subst_subst h.1 hx, h.2.2.2.1, PowerSeries.subst_X $ hasSubst hx]

theorem constantCoeff_add_l (h : IsLogPair l linv) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst x l + PowerSeries.subst y l) = 0 := by
  rw [map_add, constantCoeff_subst_l h hx, constantCoeff_subst_l h hy, add_zero]


theorem constantCoeff_fadd (h : IsLogPair l linv) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (fadd l linv x y) = 0 :=
  constantCoeff_subst_linv h $ constantCoeff_add_l h hx hy

theorem constantCoeff_fmul (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (fmul l linv a x) = 0 :=
  constantCoeff_subst_linv h $ by rw [map_mul, constantCoeff_subst_l h hx, mul_zero]



theorem l_fmul (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    PowerSeries.subst (fmul l linv a x) l = MvPowerSeries.C a * PowerSeries.subst x l :=
  subst_l_linv h $ by rw [map_mul, constantCoeff_subst_l h hx, mul_zero]


theorem fmul_fmul (h : IsLogPair l linv) (a b : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    fmul l linv a (fmul l linv b x) = fmul l linv (a * b) x := by
  rw [fmul, l_fmul h b hx, fmul, map_mul, mul_assoc]

theorem fmul_one (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) : fmul l linv 1 x = x := by
  rw [fmul, map_one, one_mul, subst_linv_l h hx]

theorem fmul_zero_left (h : IsLogPair l linv) (x : MvPowerSeries σ K) : fmul l linv 0 x = 0 := by
  rw [fmul, map_zero, zero_mul, subst_zero_of_constantCoeff_zero h.2.2.1]

theorem constantCoeff_mulBy (h : IsLogPair l linv) (a : K) :
    PowerSeries.constantCoeff (mulBy l linv a) = 0 := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.C a * l) = 0 := by rw [map_mul, h.1, mul_zero]
  exact constantCoeff_subst h0 h.2.2.1

theorem fmul_eq_subst_mulBy (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    fmul l linv a x = PowerSeries.subst x (mulBy l linv a) := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.C a * l) = 0 := by rw [map_mul, h.1, mul_zero]
  rw [mulBy, subst_subst h0 hx, subst_mul $ hasSubst hx, subst_C, fmul]

theorem mulBy_eq_fmul (a : K) : mulBy l linv a = fmul l linv a (PowerSeries.X : PowerSeries K) := by
  rw [fmul, PowerSeries.X_subst]
  rfl

theorem fadd_comm (x y : MvPowerSeries σ K) : fadd l linv x y = fadd l linv y x := by
  rw [fadd, fadd, add_comm]

theorem fadd_zero (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) : fadd l linv x 0 = x := by
  rw [fadd, subst_zero_of_constantCoeff_zero h.1, add_zero, subst_linv_l h hx]

theorem zero_fadd (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) : fadd l linv 0 x = x := by
  rw [fadd_comm, fadd_zero h hx]


theorem fmul_add (h : IsLogPair l linv) (a b : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    fmul l linv (a + b) x = fadd l linv (fmul l linv a x) (fmul l linv b x) := by
  rw [fadd, l_fmul h a hx, l_fmul h b hx, fmul, map_add, add_mul]

theorem fadd_fmul_neg (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    fadd l linv (fmul l linv a x) (fmul l linv (-a) x) = 0 := by
  rw [← fmul_add h a (-a) hx, add_neg_cancel, fmul_zero_left h]

theorem addDefect_comm (ph : PowerSeries K) (x y : MvPowerSeries σ K) :
    be0 l linv ph x y = be0 l linv ph y x := by
  rw [be0, be0, fadd_comm]
  ring

theorem fadd_eq_substMv (h : IsLogPair l linv) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    fadd l linv x y = MvPowerSeries.subst ![x, y]
      (fadd l linv (MvPowerSeries.X (0 : Fin 2)) $ MvPowerSeries.X (1 : Fin 2)) := by
  have ha : ∀ s, MvPowerSeries.constantCoeff (![x, y] s) = 0 := by
    intro s
    fin_cases s
    exact hx
    exact hy
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  rw [fadd, fadd, substMv_subst (constantCoeff_add_l h (MvPowerSeries.constantCoeff_X 0) h1) ha, MvPowerSeries.subst_add hs,
    substMv_subst (MvPowerSeries.constantCoeff_X 0) ha, substMv_subst h1 ha, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  rfl

theorem coeff_one_linv (h : IsLogPair l linv) : PowerSeries.coeff 1 linv = 1 := by
  have hc := coeff_subst_congr (g := linv)
    (h := PowerSeries.C (PowerSeries.coeff 1 linv) * PowerSeries.X) (a := l) h.1
    (single () 1) fun k hk => by
      rw [Finsupp.degree_single] at hk
      interval_cases k
      simp [h.2.2.1]
      simp
  rw [h.2.2.2.1, subst_mul $ hasSubst h.1, subst_C,
    PowerSeries.subst_X $ hasSubst h.1] at hc
  have h1 : PowerSeries.coeff 1 (PowerSeries.X : PowerSeries K) =
      PowerSeries.coeff 1 (PowerSeries.C (PowerSeries.coeff 1 linv) * l) := hc
  rw [PowerSeries.coeff_one_X, PowerSeries.coeff_C_mul, h.2.1, mul_one] at h1
  exact h1.symm

end Toolkit

section Integral

variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}


theorem intPS_of_intMv {f : PowerSeries K} (hf : IntMv R (f : MvPowerSeries Unit K)) : IntPS R f :=
  fun n => hf $ single () n

theorem intMv_X (s : σ) : IntMv R (MvPowerSeries.X s : MvPowerSeries σ K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  exact R.one_mem
  exact R.zero_mem

theorem isPt_fadd (h : IsLogPair l linv) (hF : FGInt R l linv) {x y : MvPowerSeries σ K}
    (hx : IsPt R x) (hy : IsPt R y) : IsPt R $ fadd l linv x y := by
  use constantCoeff_fadd h hx.1 hy.1
  rw [fadd_eq_substMv h hx.1 hy.1]
  refine intMv_substMv hF fun s => ?_
  fin_cases s
  exact hx
  exact hy

theorem isPt_fmul (h : IsLogPair l linv) {a : K} (ha : EndInt R l linv a) {x : MvPowerSeries σ K}
    (hx : IsPt R x) : IsPt R $ fmul l linv a x := by
  use constantCoeff_fmul h a hx.1
  rw [fmul_eq_subst_mulBy h a hx.1]
  exact intMv_subst ha hx

theorem isPt_X : IsPt R (PowerSeries.X : MvPowerSeries Unit K) :=
  ⟨PowerSeries.constantCoeff_X, intMv_X ()⟩

theorem endInt_zero (h : IsLogPair l linv) : EndInt R l linv 0 := by
  intro n
  rw [mulBy_eq_fmul, fmul_zero_left h, map_zero]
  exact R.zero_mem

theorem endInt_one (h : IsLogPair l linv) : EndInt R l linv 1 := by
  unfold EndInt
  rw [mulBy_eq_fmul, fmul_one h PowerSeries.constantCoeff_X]
  exact intPS_of_intMv isPt_X.2

theorem endInt_add (h : IsLogPair l linv) (hF : FGInt R l linv) {a b : K}
    (ha : EndInt R l linv a) (hb : EndInt R l linv b) : EndInt R l linv $ a + b := by
  unfold EndInt
  rw [mulBy_eq_fmul, fmul_add h a b PowerSeries.constantCoeff_X]
  exact intPS_of_intMv (isPt_fadd h hF (isPt_fmul h ha isPt_X) $ isPt_fmul h hb isPt_X).2

theorem endInt_mul (h : IsLogPair l linv) {a b : K}
    (ha : EndInt R l linv a) (hb : EndInt R l linv b) : EndInt R l linv $ a * b := by
  unfold EndInt
  rw [mulBy_eq_fmul, ← fmul_fmul h a b PowerSeries.constantCoeff_X]
  exact intPS_of_intMv (isPt_fmul h ha $ isPt_fmul h hb isPt_X).2

theorem coeff_substMv_two {τ : Type} (F : MvPowerSeries (Fin 2) K) {a : Fin 2 → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst a F) =
      finsum fun d =>
        MvPowerSeries.coeff d F * MvPowerSeries.coeff e (a 0 ^ d 0 * a 1 ^ d 1) := by
  rw [MvPowerSeries.coeff_subst $ MvPowerSeries.hasSubst_of_constantCoeff_zero ha]
  refine finsum_congr fun d => ?_
  rw [smul_eq_mul, Finsupp.prod_fintype _ _ fun _ => pow_zero _, Fin.prod_univ_two]

theorem coeff_law_of_zero (h : IsLogPair l linv) (d : Fin 2 →₀ ℕ) (hd : d 0 = 0) :
    MvPowerSeries.coeff d
        (fadd l linv (MvPowerSeries.X (0 : Fin 2)) $ MvPowerSeries.X (1 : Fin 2)) =
      MvPowerSeries.coeff d (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) := by
  classical
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have ha : ∀ s, MvPowerSeries.constantCoeff
      ((![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) s) = 0 := by
    intro s
    fin_cases s
    exact map_zero _
    exact hX
  have key := coeff_substMv_two
    (fadd l linv (MvPowerSeries.X (0 : Fin 2)) $ MvPowerSeries.X (1 : Fin 2)) ha
    $ single () $ d 1
  rw [← fadd_eq_substMv h (map_zero _) hX, zero_fadd h hX, finsum_eq_single _ d] at key
  have e1 : MvPowerSeries.coeff (single () $ d 1)
      ((![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 0 ^ d 0 *
        (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 1 ^ d 1) = 1 := by
    rw [hd, pow_zero, one_mul]
    exact PowerSeries.coeff_X_pow_self $ d 1
  rw [e1, mul_one] at key
  rw [← key, MvPowerSeries.coeff_X]
  trans if d 1 = 1 then 1 else 0
  exact PowerSeries.coeff_X $ d 1
  congr 1
  apply propext
  constructor
  intro h1
  ext s
  fin_cases s
  simpa using hd
  simpa using h1
  intro h1
  rw [h1]
  simp
  intro d' hd'
  by_cases h0 : d' 0 = 0
  have h1 : d' 1 ≠ d 1 := by
    intro h1
    apply hd'
    ext s
    fin_cases s
    simpa [hd] using h0
    simpa using h1
  have e1 : MvPowerSeries.coeff (single () $ d 1)
      ((![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 0 ^ d' 0 *
        (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 1 ^ d' 1) = 0 := by
    rw [h0, pow_zero, one_mul]
    have := PowerSeries.coeff_X_pow (R := K) (d 1) $ d' 1
    rwa [if_neg fun hh => h1 hh.symm] at this
  rw [e1, mul_zero]
  have : (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 0 ^ d' 0 = 0 := zero_pow h0
  rw [this, zero_mul, map_zero, mul_zero]

theorem coeff_pow_mem {i : PowerSeries K} {n : ℕ} (hi : ∀ m < n, PowerSeries.coeff m i ∈ R)
    (k : ℕ) : ∀ m < n, PowerSeries.coeff m (i ^ k) ∈ R := by
  induction k with
  | zero =>
    intro m _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    exact R.one_mem
    exact R.zero_mem
  | succ k ih =>
    intro m hm
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Subring.sum_mem _ fun p hp => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact R.mul_mem (ih _ $ by omega) $ hi _ $ by omega

theorem intPS_of_law_eq_zero {F : MvPowerSeries (Fin 2) K} (hF : IntMv R F)
    (hF0 : ∀ d, d 0 = 0 → MvPowerSeries.coeff d F =
      MvPowerSeries.coeff d (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
    {i : PowerSeries K} (hi : PowerSeries.constantCoeff i = 0)
    (hz : MvPowerSeries.subst (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) F = 0) :
    IntPS R i := by
  have ha : ∀ s, MvPowerSeries.constantCoeff
      ((![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) s) = 0 := by
    intro s
    fin_cases s
    exact PowerSeries.constantCoeff_X
    exact hi
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hi' : i = - MvPowerSeries.subst (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K)
      (F - MvPowerSeries.X (1 : Fin 2)) := by
    rw [MvPowerSeries.subst_sub hs, hz, MvPowerSeries.subst_X hs, zero_sub, neg_neg]
    rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc : PowerSeries.coeff n i = - MvPowerSeries.coeff (single () n)
        (MvPowerSeries.subst (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K)
          $ F - MvPowerSeries.X (1 : Fin 2)) := by
      conv_lhs => rw [hi']
      exact map_neg _ _
    rw [hc, coeff_substMv_two _ ha]
    refine R.neg_mem (finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun d => ?_)
    by_cases h0 : d 0 = 0
    rw [map_sub, hF0 d h0, sub_self, zero_mul]
    exact R.zero_mem
    refine R.mul_mem ?_ ?_
    rw [map_sub]
    exact R.sub_mem (hF d) $ intMv_X 1 d
    have e1 : MvPowerSeries.coeff (single () n)
        ((![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) 0 ^ d 0 *
          (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) 1 ^ d 1) =
        if d 0 ≤ n then PowerSeries.coeff (n - d 0) $ i ^ d 1 else 0 :=
      PowerSeries.coeff_X_pow_mul' (i ^ d 1) (d 0) n
    rw [e1]
    split_ifs with hle
    exact coeff_pow_mem ih (d 1) _ $ by omega
    exact R.zero_mem

theorem endInt_neg_one (h : IsLogPair l linv) (hF : FGInt R l linv) : EndInt R l linv $ -1 := by
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  refine intPS_of_law_eq_zero hF (coeff_law_of_zero h) (constantCoeff_mulBy h $ -1) ?_
  rw [← fadd_eq_substMv h hX $ constantCoeff_mulBy h $ -1, mulBy_eq_fmul]
  have := fadd_fmul_neg h 1 hX
  rwa [fmul_one h hX] at this

theorem endInt_neg (h : IsLogPair l linv) (hF : FGInt R l linv) {a : K}
    (ha : EndInt R l linv a) : EndInt R l linv $ -a := by
  rw [← neg_one_mul]
  exact endInt_mul h (endInt_neg_one h hF) ha


end Integral

end Pts

end Formalism.L2.Th1.C
end
section
open scoped BigOperators
open PowerSeries (HasSubst coe_substAlgHom coeff coeff_mul constantCoeff rescale subst subst_C subst_X subst_comp_subst_apply)
open PowerSeries

namespace Formalism.L2.Th1.C

namespace USideA

section Int

variable {K : Type} [Field K] {R : Subring K}

theorem intPS_add {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R $ f + g := fun n => by
  rw [map_add]
  exact R.add_mem (hf n) $ hg n

theorem intPS_sub {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R $ f - g := fun n => by
  rw [map_sub]
  exact R.sub_mem (hf n) $ hg n

theorem intPS_mul {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R $ f * g := fun n => by
  rw [coeff_mul]
  exact R.sum_mem fun p _ => R.mul_mem (hf _) $ hg _

theorem intPS_C {c : K} (hc : c ∈ R) : IntPS R $ PowerSeries.C c := fun n => by
  rw [PowerSeries.coeff_C]
  split_ifs
  exact hc
  exact R.zero_mem

theorem intPS_X_pow (k : ℕ) : IntPS R (PowerSeries.X ^ k : PowerSeries K) := fun n => by
  rw [PowerSeries.coeff_X_pow]
  split_ifs
  exact R.one_mem
  exact R.zero_mem

theorem intPS_X : IntPS R (PowerSeries.X : PowerSeries K) := by
  simpa using (intPS_X_pow 1 : IntPS R (PowerSeries.X ^ 1 : PowerSeries K))

theorem intPS_sum {ι : Type} (s : Finset ι) {F : ι → PowerSeries K} (hF : ∀ i ∈ s, IntPS R (F i)) :
    IntPS R (∑ i ∈ s, F i) := fun n => by
  rw [map_sum]
  exact R.sum_mem fun i hi => hF i hi n

theorem intPS_of_mul_eq_one {U V : PowerSeries K} (hU : IntPS R U)
    (hU0 : constantCoeff U = 1) (hUV : U * V = 1) : IntPS R V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := congrArg (coeff n) hUV
    rw [coeff_mul, PowerSeries.coeff_one] at h
    have hmem0 : ((0, n) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
    rw [← Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal n)
      (fun p => coeff p.1 U * coeff p.2 V)
      hmem0] at h
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0, one_mul] at h
    have h' : coeff n V = (if n = 0 then 1 else 0) -
        ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
          coeff p.1 U * coeff p.2 V := by
      linear_combination h
    rw [h']
    refine R.sub_mem ?_ (by
        refine R.sum_mem fun p hp => R.mul_mem (hU _) $ ih _ ?_
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
        by_contra hle
        apply hne
        obtain ⟨a, b⟩ := p
        simp only [Prod.mk.injEq] at hmem hle ⊢
        refine ⟨?_, ?_⟩ <;> omega)
    split_ifs
    exact R.one_mem
    exact R.zero_mem

end Int

section Log

variable {K : Type} [Field K]

theorem hs_of {a : PowerSeries K} (h : constantCoeff a = 0) : HasSubst a :=
  PowerSeries.HasSubst.of_constantCoeff_zero h

theorem cc_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    constantCoeff (mulBy l linv al) = 0 := by
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr h.2.2.1
  have ha : HasSubst $ PowerSeries.C al * l := hs_of $ by simp [h.1]
  unfold mulBy
  rw [hq, ← coe_substAlgHom ha, map_mul, coe_substAlgHom,
    subst_X ha, map_mul, map_mul, h.1, mul_zero, zero_mul]

theorem subst_mulBy_l {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    subst (mulBy l linv al) l = PowerSeries.C al * l := by
  have ha : HasSubst $ PowerSeries.C al * l := hs_of $ by simp [h.1]
  unfold mulBy
  rw [← subst_comp_subst_apply (hs_of h.2.2.1) ha, h.2.2.2.2, subst_X ha]

theorem subst_rescale {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) (g : PowerSeries K) :
    subst l (rescale al g) =
      subst (mulBy l linv al) (subst l g) := by
  have hl : HasSubst l := hs_of h.1
  have hm : HasSubst $ mulBy l linv al := hs_of $ cc_mulBy h al
  have hC : subst l (PowerSeries.C al) = PowerSeries.C al := subst_C al
  rw [subst_comp_subst_apply hl hm, subst_mulBy_l h, PowerSeries.rescale_eq_subst,
    PowerSeries.smul_eq_C_mul, subst_comp_subst_apply (hs_of $ by simp) hl,
    ← coe_substAlgHom hl, map_mul, coe_substAlgHom, hC,
    subst_X hl]

theorem l_ne_zero {l linv : PowerSeries K} (h : IsLogPair l linv) : l ≠ 0 := by
  intro h0
  have h1 := h.2.1
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem subst_C' (a : PowerSeries K) (c : K) :
    subst a (PowerSeries.C c) = PowerSeries.C c :=
  subst_C c


theorem subst_wpShift_zero {a : PowerSeries K} (ha : HasSubst a) (e : PowerSeries K) :
    subst a (wpShift e 0) = 1 + a ^ 2 * subst a e := by
  unfold wpShift
  rw [← coe_substAlgHom ha]
  simp [map_add, map_one, map_mul, map_pow, map_sub, map_zero, sub_zero,
    coe_substAlgHom, subst_X ha]

end Log

end USideA

open USideA

theorem veluXOfSigma' : VeluXFromZ := by
  intro K _ _ e l linv A c0 ι _ neg xP w xs al h hXW hE hw
  have hl : HasSubst l := hs_of h.1
  have hm : HasSubst $ mulBy l linv al := hs_of $ cc_mulBy h al
  have F0 : (A + PowerSeries.C c0 * PowerSeries.X ^ 2) * l ^ 2 =
      PowerSeries.X ^ 2 * subst l (wpShift e 0) := hXW
  have F1 := F0
  rw [subst_wpShift_zero hl] at F1
  have F2 := congrArg (subst (mulBy l linv al)) F0
  rw [← coe_substAlgHom hm] at F2
  simp only [map_add, map_mul, map_pow, coe_substAlgHom] at F2
  rw [subst_C', subst_X hm, subst_mulBy_l h, subst_comp_subst_apply hl hm,
    subst_mulBy_l h, subst_wpShift_zero $ hs_of $ by simp [h.1]] at F2
  have hZr : subst (PowerSeries.C al * l) e = subst l (rescale al e) := by
    rw [subst_rescale h, subst_comp_subst_apply hl hm, subst_mulBy_l h]
  have F3 := congrArg (subst l) hE.2.2
  rw [← coe_substAlgHom hl] at F3
  simp only [map_add, map_mul, map_sum, map_sub, coe_substAlgHom] at F3
  simp only [subst_C'] at F3
  simp only [hw, ← hZr, map_pow] at F3
  have hsum : ∑ P, (xs P + PowerSeries.C c0 - (PowerSeries.C (xP P) + PowerSeries.C c0)) =
      ∑ P, (xs P - PowerSeries.C (xP P)) := Finset.sum_congr rfl fun P _ => by ring
  rw [hsum] at F3
  unfold veluXs
  simp only [map_pow, map_mul, map_sub, map_one]
  exact sub_eq_zero.mp $ (mul_eq_zero.mp $ by
      linear_combination PowerSeries.X ^ 2 * F2 + mulBy l linv al ^ 2 * PowerSeries.X ^ 2 * l ^ 2 * F3 -
        mulBy l linv al ^ 2 * F1).resolve_left $ pow_ne_zero 2 $ l_ne_zero h

end Formalism.L2.Th1.C
end
section
open scoped BigOperators
open PowerSeries (HasSubst coe_substAlgHom coeff coeff_mul rescale subst subst_C subst_X subst_comp_subst_apply subst_mul)
open PowerSeries

namespace Formalism.L2.Th1.C

namespace USideB

section SlopeTestRemainingChoices

variable {K : Type} [Field K]

theorem hs_of {a : PowerSeries K} (h : PowerSeries.constantCoeff a = 0) : HasSubst a :=
  PowerSeries.HasSubst.of_constantCoeff_zero' h

theorem cc_subst {a f : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.constantCoeff (subst a f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha f hf

theorem cc_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    PowerSeries.constantCoeff (mulBy l linv al) = 0 := by
  exact cc_subst (by simp [h.1]) h.2.2.1

theorem subst_mulBy_l {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    subst (mulBy l linv al) l = PowerSeries.C al * l := by
  have hb : PowerSeries.constantCoeff (PowerSeries.C al * l) = 0 := by simp [h.1]
  rw [mulBy, ← subst_comp_subst_apply (hs_of h.2.2.1) $ hs_of hb, h.2.2.2.2,
    subst_X $ hs_of hb]

theorem subst_rescale {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) (g : PowerSeries K) :
    subst l (rescale al g) =
      subst (mulBy l linv al) (subst l g) := by
  have hl : HasSubst l := hs_of h.1
  rw [subst_comp_subst_apply hl $ hs_of $ cc_mulBy h al, subst_mulBy_l h al,
    PowerSeries.rescale_eq_subst, subst_comp_subst_apply (hs_of $ by simp) hl,
    PowerSeries.subst_smul hl, subst_X hl, PowerSeries.smul_eq_C_mul]

theorem l_ne_zero {l linv : PowerSeries K} (h : IsLogPair l linv) : l ≠ 0 := by
  intro h0
  have h1 := h.2.1
  rw [h0] at h1
  simp at h1

theorem subst_wpShift {e l A : PowerSeries K} {c0 : K} (hl : PowerSeries.constantCoeff l = 0)
    (hX : XIsWp e l A c0) (x : K) :
    PowerSeries.X ^ 2 * subst l (wpShift e $ x + c0) =
      (A - PowerSeries.C x * PowerSeries.X ^ 2) * l ^ 2 := by
  have hs := hs_of hl
  have e1 : wpShift e (x + c0) = wpShift e 0 - PowerSeries.C (x + c0) * PowerSeries.X ^ 2 := by
    simp [wpShift, map_zero, sub_zero]
    ring
  have e2 : subst l (wpShift e $ x + c0) =
      subst l (wpShift e 0) - PowerSeries.C (x + c0) * l ^ 2 := by
    rw [e1, PowerSeries.subst_sub hs, subst_mul hs, subst_C,
      PowerSeries.subst_pow hs, subst_X hs]
    rfl
  rw [e2, mul_sub, ← hX, map_add]
  ring

end SlopeTestRemainingChoices

section FormalExponential

variable {K : Type} [Field K] [CharZero K]

theorem mvExp_pow (hE : MvExpLaws) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0)
    (m : ℕ) : (mvExp f : PowerSeries K) ^ m = mvExp ((m : K) • f) := by
  obtain ⟨L0, -, L2, -⟩ := hE K Unit
  induction m with
  | zero => simp [L0]
  | succ m ih =>
    have hc : PowerSeries.constantCoeff ((m : K) • f) = 0 := by simp [hf]
    rw [pow_succ, ih, ← L2 _ _ hc hf]
    congr 1
    push_cast
    rw [add_smul, one_smul]

end FormalExponential

end USideB

open USideB

section Main

theorem isogenyU_of (hE : MvExpLaws) (hS : MvExpSubst) : IsogenyU := by
  intro K _ _ e s2 l linv ph A c0 ι _ xP al h hph hX hI
  set m := mulBy l linv al with hmdef
  have hl := hs_of h.1
  have hmc := cc_mulBy h al
  have hms := hs_of hmc
  have hneg : ∀ f : PowerSeries K, subst m (-f) = -subst m f := by
    intro f
    rw [← coe_substAlgHom hms, map_neg]

  have k1 : subst l (rescale al (sgStar e s2)) =
      m * mvExp (-(subst m ph)) := by
    rw [subst_rescale h al, ← hph.2, subst_mul hms, subst_X hms,
      hS K Unit (-ph) m (by simp [hph.1]) hmc, hneg]
  have key := congrArg (PowerSeries.substAlgHom hl) hI
  simp only [map_mul, map_pow, map_prod, coe_substAlgHom] at key
  rw [k1, subst_X hl, subst_C, ← hph.2] at key
  have hC : (MvPowerSeries.C al : PowerSeries K) = PowerSeries.C al := rfl
  rw [hC] at key

  have hprod : PowerSeries.X ^ (2 * Fintype.card ι) *
      ∏ P, subst l (wpShift e (xP P + c0)) =
      (∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2)) * l ^ (2 * Fintype.card ι) := by
    calc PowerSeries.X ^ (2 * Fintype.card ι) * ∏ P, subst l (wpShift e (xP P + c0))
        = (∏ _P : ι, (PowerSeries.X : PowerSeries K) ^ 2) *
            ∏ P, subst l (wpShift e (xP P + c0)) := by
          rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
      _ = ∏ P, (PowerSeries.X ^ 2 * subst l (wpShift e (xP P + c0))) :=
          Finset.prod_mul_distrib.symm
      _ = ∏ P, ((A - PowerSeries.C (xP P) * PowerSeries.X ^ 2) * l ^ 2) :=
          Finset.prod_congr rfl fun P _ => subst_wpShift h.1 hX (xP P)
      _ = (∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2)) * ∏ _P : ι, l ^ 2 :=
          Finset.prod_mul_distrib
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have p1 : (mvExp (-(subst m ph)) : PowerSeries K) ^ 2 =
      mvExp (-((2 : K) • subst m ph)) := by
    rw [mvExp_pow hE (by rw [map_neg, cc_subst hmc hph.1, neg_zero]) 2]
    congr 1
    rw [smul_neg]
    norm_num
  have p2 : (mvExp (-ph) : PowerSeries K) ^ (2 * (Fintype.card ι + 1)) =
      mvExp (-((2 * ((Fintype.card ι : K) + 1)) • ph)) := by
    rw [mvExp_pow hE (by rw [map_neg, hph.1, neg_zero]) _]
    congr 1
    rw [smul_neg]
    push_cast
    rfl
  apply mul_right_cancel₀ (pow_ne_zero (2 * Fintype.card ι) (l_ne_zero h))
  rw [← p1, ← p2, map_pow]
  linear_combination PowerSeries.X ^ (2 * Fintype.card ι) * key +
    PowerSeries.C al ^ 2 * PowerSeries.X ^ (2 * (Fintype.card ι + 1)) *
      (mvExp (-ph) : PowerSeries K) ^ (2 * (Fintype.card ι + 1)) * hprod

end Main

namespace USideB

section Integral

variable {K : Type} [Field K]

def intSub (R : Subring K) : Subring $ PowerSeries K where
  carrier := {f | IntPS R f}
  mul_mem' := by
    intro f g hf hg n
    rw [coeff_mul]
    exact R.sum_mem fun p _ => R.mul_mem (hf _) $ hg _
  one_mem' := by
    intro n
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  add_mem' := by
    intro f g hf hg n
    rw [map_add]
    exact R.add_mem (hf _) $ hg _
  zero_mem' := by
    intro n
    rw [map_zero]
    exact R.zero_mem
  neg_mem' := by
    intro f hf n
    rw [map_neg]
    exact R.neg_mem $ hf _

theorem mem_intSub {R : Subring K} {f : PowerSeries K} : f ∈ intSub R ↔ IntPS R f := Iff.rfl

theorem C_mem_intSub {R : Subring K} {a : K} (ha : a ∈ R) : PowerSeries.C a ∈ intSub R := by
  refine mem_intSub.2 fun n => ?_
  rw [PowerSeries.coeff_C]
  split_ifs
  exact ha
  exact R.zero_mem

theorem X_mem_intSub (R : Subring K) : (PowerSeries.X : PowerSeries K) ∈ intSub R := by
  refine mem_intSub.2 fun n => ?_
  rw [PowerSeries.coeff_X]
  split_ifs
  exact R.one_mem
  exact R.zero_mem

theorem int_of_mul {R : Subring K} {U V W : PowerSeries K} (hU : IsOneUnit R U) (hW : IntPS R W)
    (h : V * U = W) : IntPS R V := by
  have h0 : coeff 0 U = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hU.1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (coeff n) h
    simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Nat.sub_self, h0, mul_one] at hc

    have hn : coeff n V = coeff n W -
        ∑ k ∈ Finset.range n, coeff k V * coeff (n - k) U := by
      rw [← hc]
      ring
    rw [hn]
    exact R.sub_mem (hW n)
      $ R.sum_mem fun k hk => R.mul_mem (ih k $ Finset.mem_range.1 hk) $ hU.2 _

theorem intMv_of_intPS {R : Subring K} {f : PowerSeries K} (h : IntPS R f) :
    IntMv R (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun x => by cases x
                                                                   simp
  rw [e]
  exact h $ n ()

end Integral

end USideB

section Main2

theorem phNormUnit_of (hE : MvExpLaws) (_hS : MvExpSubst) (hH : LGHalf) (hU : IsogenyU) :
    PhNormUnit := by
  intro K _ _ R e s2 l linv ph A c0 ι _ xP al h hph hX hI hA hxP hal hali hal0 h2 hm
  obtain ⟨L0, L1, L2, -⟩ := hE K Unit
  have mvc : ∀ f, PowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (f : MvPowerSeries Unit K) = 0 := fun f hf => hf
  have hiso := hU K e s2 l linv ph A c0 ι xP al h hph hX hI
  have hmc := cc_mulBy h al
  have hsc :=
    cc_subst hmc hph.1
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.2 hmc
  set k := Fintype.card ι with hk
  set s := subst (mulBy l linv al) ph with hs
  set D : PowerSeries K := s - ((k : K) + 1) • ph with hD
  set Q := ∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2) with hQ
  set E1 : PowerSeries K := mvExp (-((2 : K) • s)) with hE1
  set E2 : PowerSeries K := mvExp (-((2 * ((k : K) + 1)) • ph)) with hE2
  set F : PowerSeries K := mvExp ((2 * ((k : K) + 1)) • ph) with hF
  rw [hu] at hiso hm

  have h1 : u ^ 2 * E1 = PowerSeries.C (al ^ 2) * E2 * Q := by
    apply mul_left_cancel₀ $ pow_ne_zero (2 * (k + 1)) $ PowerSeries.X_ne_zero (R := K)
    linear_combination hiso
  have cE1 : PowerSeries.constantCoeff E1 = 1 := L1 _ $ mvc _ $ by simp [hsc]
  have cE2 : PowerSeries.constantCoeff E2 = 1 := L1 _ $ mvc _ $ by simp [hph.1]
  have cQ : PowerSeries.constantCoeff Q = 1 := by simp [hQ, map_prod, hA.1]
  have cu : PowerSeries.constantCoeff u ^ 2 = al ^ 2 := by
    simpa [cE1, cE2, cQ] using (congrArg PowerSeries.constantCoeff h1)
  set v := PowerSeries.C al⁻¹ * u with hv
  have cph : PowerSeries.constantCoeff ((2 * ((k : K) + 1)) • ph) = 0 := by simp [hph.1]
  have cs2 : PowerSeries.constantCoeff (-((2 : K) • s)) = 0 := by simp [hsc]
  have hEF : E2 * F = 1 := by
    rw [hE2, hF, ← L2 _ _ (mvc _ $ by simp [hph.1]) $ mvc _ cph, neg_add_cancel, L0]
  have hDD : (mvExp (-(D + D)) : PowerSeries K) = E1 * F := by
    rw [hE1, hF, ← L2 _ _ (mvc _ cs2) $ mvc _ cph]
    congr 1
    rw [hD]
    module

  have hkey : (mvExp (-(D + D)) : PowerSeries K) * v ^ 2 = Q := by
    rw [hDD]
    have hv2 : v ^ 2 = PowerSeries.C al⁻¹ ^ 2 * u ^ 2 := by rw [hv, mul_pow]
    calc E1 * F * v ^ 2 = PowerSeries.C al⁻¹ ^ 2 * F * (u ^ 2 * E1) := by rw [hv2]
                                                                          ring
      _ = PowerSeries.C al⁻¹ ^ 2 * F * (PowerSeries.C (al ^ 2) * E2 * Q) := by rw [h1]
      _ = PowerSeries.C (al⁻¹ ^ 2 * al ^ 2) * (E2 * F) * Q := by simp only [map_mul, map_pow]
                                                                 ring
      _ = Q := by rw [hEF, inv_pow, inv_mul_cancel₀ $ pow_ne_zero 2 hal0, map_one]
                  ring
  have hQi : IntPS R Q := mem_intSub.1 $ prod_mem fun P _ =>
    sub_mem (mem_intSub.2 hA.2) $ mul_mem (C_mem_intSub $ hxP P) $ pow_mem (X_mem_intSub R) 2
  have hI1 := int_of_mul (by
      constructor
      rw [map_pow, hv, map_mul, PowerSeries.constantCoeff_C, mul_pow, cu, inv_pow,
        inv_mul_cancel₀ $ pow_ne_zero 2 hal0]
      exact mem_intSub.1 $ pow_mem (mul_mem (C_mem_intSub hali) $ mem_intSub.2 $ by
        intro n
        have h4 := hm $ n + 1
        rwa [PowerSeries.coeff_succ_X_mul] at h4) 2) hQi hkey
  have cD : PowerSeries.constantCoeff D = 0 := by simp [hD, hsc, hph.1]
  have cDD : PowerSeries.constantCoeff (D + D) = 0 := by simp [cD]
  have cnDD : PowerSeries.constantCoeff (-(D + D)) = 0 := by simp [cD]
  exact hH K R Unit h2 D ⟨mvc _ cDD, intMv_of_intPS $ int_of_mul (⟨L1 _ $ mvc _ cnDD, hI1⟩) (mem_intSub.1 $ one_mem _) $ by rw [← L2 _ _ (mvc _ cDD) $ mvc _ cnDD, add_neg_cancel, L0]⟩

end Main2

end Formalism.L2.Th1.C
end
section
namespace Formalism.L2.Th1.C

theorem mvExpLaws : MvExpLaws := formalExpLaws'
theorem mvExpSubst : MvExpSubst := formalExpSubst'
theorem lGSubgroup : LGSubgroup := lGSubgroup_of mvExpLaws
theorem lGBinom : LGBinom := expIntegralBinomial'
theorem lGHalf : LGHalf := lGHalf_of mvExpLaws
theorem intBinomScalar : IntBinomScalar := intBinomialScalar'
theorem lGSubstMv : LGSubstMv := expIntegralMvSubst'

theorem isogenyIffBar : IsogenyIffBar := isogenyIffBar_of mvExpLaws

theorem veluXFromZ : VeluXFromZ := veluXOfSigma'
theorem isogenyU : IsogenyU := isogenyU_of mvExpLaws mvExpSubst
theorem phNormUnit : PhNormUnit := phNormUnit_of mvExpLaws mvExpSubst lGHalf isogenyU

end Formalism.L2.Th1.C
end
section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.C

namespace Clo

section Cont

variable {K : Type} [Field K] {σ : Type}



variable [TopologicalSpace K] [IsTopologicalRing K] {T : Type} [TopologicalSpace T]



















end Cont

end Clo

open Clo





namespace Clo

section Lin

variable {K : Type} [Field K] {R : Subring K} {l linv : PowerSeries K}

theorem endInt_natCast (h : IsLogPair l linv) (hF : FGInt R l linv) (n : ℕ) :
    EndInt R l linv (n : K) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Pts.endInt_zero h
  | succ n ih => rw [Nat.cast_succ]; exact Pts.endInt_add h hF ih $ Pts.endInt_one h

variable [CharZero K] {ph : PowerSeries K} {σ : Type}

theorem addDefect_zero_right (h : Frame R l linv ph) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) : be0 l linv ph x 0 = 0 := by
  rw [be0, Pts.fadd_zero h.1 hx, PowerSeries.subst_zero_of_constantCoeff_zero h.2.2, sub_self,
    sub_zero]

theorem addDefect_add_right (h1 : F1 R l linv ph) {x y y' : MvPowerSeries σ K} (hx : IsPt R x)
    (hy : IsPt R y) (hy' : IsPt R y') :
    LG R $ be0 l linv ph x (fadd l linv y y') - (be0 l linv ph x y + be0 l linv ph x y') := by
  have := h1 σ y y' x hy hy' hx
  rwa [Pts.addDefect_comm ph _ x, Pts.addDefect_comm ph y x, Pts.addDefect_comm ph y' x] at this

theorem zLin_natCast (h : Frame R l linv ph) (h1 : F1 R l linv ph) {x y : MvPowerSeries σ K}
    (hx : IsPt R x) (hy : IsPt R y) (n : ℕ) :
    LG R $ be0 l linv ph x (fmul l linv (n : K) y) - (n : K) • be0 l linv ph x y := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, Pts.fmul_zero_left h.1, addDefect_zero_right h hx.1, zero_smul, sub_zero]
    exact (lGSubgroup K R σ).1
  | succ n ih =>
    have := (lGSubgroup K R σ).2.1 _ _ (addDefect_add_right h1 hx (Pts.isPt_fmul h.1 (endInt_natCast h.1 h.2.1 n) hy) hy) ih
    rw [Nat.cast_succ, Pts.fmul_add h.1 _ _ hy.1, Pts.fmul_one h.1 hy.1, add_smul, one_smul]
    convert this using 1
    abel

end Lin

end Clo

theorem scalarLinearInt' : ZLinInt := by
  intro K _ _ R l linv ph h h1 n σ x y hx hy
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  rw [Int.cast_natCast]
  exact zLin_natCast h h1 hx hy m
  rw [Int.cast_neg, Int.cast_natCast]
  have hm := endInt_natCast (R := R) h.1 h.2.1 m
  have hp := addDefect_add_right h1 hx (Pts.isPt_fmul h.1 hm hy)
    $ Pts.isPt_fmul h.1 (Pts.endInt_neg h.1 h.2.1 hm) hy
  rw [Pts.fadd_fmul_neg h.1 _ hy.1, addDefect_zero_right h hx.1] at hp
  have := (lGSubgroup K R σ).2.2 _
    $ (lGSubgroup K R σ).2.1 _ _ hp $ zLin_natCast h h1 hx hy m
  unfold Cong
  rw [neg_smul]
  convert this using 1
  abel


end Formalism.L2.Th1.C
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

section Tools

variable {R : Type u} [CommRing R]

abbrev toL : R⟦X⟧ →+* LaurentSeries R := HahnSeries.ofPowerSeries ℤ R

def uPow (n : ℤ) : LaurentSeries R := HahnSeries.single n 1

def dL : LaurentSeries R →ₗ[R] LaurentSeries R := LaurentSeries.hasseDeriv R 1

open Classical in

def compInv (s : R⟦X⟧) : R⟦X⟧ :=
  if h : ∃ t : R⟦X⟧, constantCoeff t = 0 ∧ s.subst t = X then h.choose else 0

end Tools

def integ {K : Type u} [Field K] (f : K⟦X⟧) : K⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else coeff (n - 1) f / (n : K)

section Curve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

def wSer : R⟦X⟧ := (Formalism.ELL.wSeriesUnique R W).choose

def wU : R⟦X⟧ := PowerSeries.mk fun n => coeff (n + 3) $ wSer W

def xS : R⟦X⟧ := invOfUnit (wU W) 1

def yS : R⟦X⟧ := -xS W

def xL : LaurentSeries R := uPow (-2) * toL (xS W)

def yL : LaurentSeries R := uPow (-3) * toL (yS W)

def fw : R⟦X⟧ :=
  1 - C W.a₁ * X - C W.a₂ * X ^ 2 - 2 * C W.a₃ * wSer W - 2 * C W.a₄ * X * wSer W
    - 3 * C W.a₆ * wSer W ^ 2

def fu : R⟦X⟧ :=
  3 * X ^ 2 + C W.a₁ * wSer W + 2 * C W.a₂ * X * wSer W + C W.a₄ * wSer W ^ 2

def om : R⟦X⟧ := invOfUnit (fw W) 1

def D : Derivation R R⟦X⟧ R⟦X⟧ := fw W • derivative

def DL (f : LaurentSeries R) : LaurentSeries R := toL (fw W) * dL f

def iDen : R⟦X⟧ := -1 + C W.a₁ * X + C W.a₃ * wSer W

def iSer : R⟦X⟧ := X * invOfUnit (iDen W) (-1)

end Curve

section Law

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

def lam : MvPowerSeries (Fin 2) R := fun e => coeff (e 0 + e 1 + 1) $ wSer W

def nu : MvPowerSeries (Fin 2) R := (wSer W).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)
  - lam W * MvPowerSeries.X 0

def cThree : MvPowerSeries (Fin 2) R :=
  1 + MvPowerSeries.C W.a₂ * lam W + MvPowerSeries.C W.a₄ * lam W ^ 2
    + MvPowerSeries.C W.a₆ * lam W ^ 3

def cTwo : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.C W.a₁ * lam W + MvPowerSeries.C W.a₂ * nu W + MvPowerSeries.C W.a₃ * lam W ^ 2
    + 2 * MvPowerSeries.C W.a₄ * lam W * nu W + 3 * MvPowerSeries.C W.a₆ * lam W ^ 2 * nu W

def uThird : MvPowerSeries (Fin 2) R :=
  -MvPowerSeries.X 0 - MvPowerSeries.X 1 - cTwo W * MvPowerSeries.invOfUnit (cThree W) 1

def wThird : MvPowerSeries (Fin 2) R := lam W * uThird W + nu W

def fgl : MvPowerSeries (Fin 2) R :=
  uThird W * MvPowerSeries.invOfUnit
    (-1 + MvPowerSeries.C W.a₁ * uThird W + MvPowerSeries.C W.a₃ * wThird W) (-1)

def nSer : ℕ → R⟦X⟧
  | 0 => 0
  | n + 1 => MvPowerSeries.subst (![X, nSer n] : Fin 2 → R⟦X⟧) $ fgl W

def zSer : ℤ → R⟦X⟧
  | Int.ofNat n => nSer W n
  | Int.negSucc n => (iSer W).subst (nSer W $ n + 1)

def halfSer : R⟦X⟧ := compInv $ nSer W 2

end Law

section Log

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

def logSer : K⟦X⟧ := integ $ om W

def expSer : K⟦X⟧ := compInv $ logSer W

def xZ : LaurentSeries K := (toL $ expSer W)⁻¹ ^ 2 * toL ((xS W).subst (expSer W))

def yZ : LaurentSeries K := (toL $ expSer W)⁻¹ ^ 3 * toL ((yS W).subst (expSer W))

def g₂ : K := W.c₄ / 12

def g₃ : K := W.c₆ / 216

def wpL : LaurentSeries K := xZ W + HahnSeries.C (W.b₂ / 12)

def wpReg : K⟦X⟧ := PowerSeries.mk fun n => (wpL W).coeff (n : ℤ)

end Log

section Translate

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)

def tDen : R⟦X⟧ := xS W - C xP * X ^ 2

def tS : R⟦X⟧ := X ^ 2 * invOfUnit (tDen W xP) 1

def nS : R⟦X⟧ :=
  C (W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * X * xS W
    - C (2 * yP + W.a₁ * xP + W.a₃) * yS W
    + C (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3) * X ^ 3

def xPlus : R⟦X⟧ := C xP + X * nS W xP yP * invOfUnit (tDen W xP) 1 ^ 2

def yPlus : R⟦X⟧ :=
  -((yS W - C yP * X ^ 3) * nS W xP yP * invOfUnit (tDen W xP) 1 ^ 3) - C yP
    - C W.a₁ * xPlus W xP yP - C W.a₃

def slopeL : LaurentSeries R := (yL W - HahnSeries.C yP) * toL (tS W xP)

end Translate

end Formalism.L2.Th1.A
end
section
namespace Formalism.L2.Th1.A

variable {A : Type u} [CommRing A]

def IsDer (D : A → A) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = a * D b + b * D a

def ConstCurve (D : A → A) (W : WeierstrassCurve A) : Prop :=
  D W.a₁ = 0 ∧ D W.a₂ = 0 ∧ D W.a₃ = 0 ∧ D W.a₄ = 0 ∧ D W.a₆ = 0

def IsFlow (W : WeierstrassCurve A) (D : A → A) (x y : A) : Prop :=
  W.toAffine.Equation x y ∧ D x = 2 * y + W.a₁ * x + W.a₃ ∧
    D y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y

def WEq (W : WeierstrassCurve A) (u w : A) : Prop :=
  w = u ^ 3 + W.a₁ * u * w + W.a₂ * u ^ 2 * w + W.a₃ * w ^ 2 + W.a₄ * u * w ^ 2 + W.a₆ * w ^ 3

def fwAt (W : WeierstrassCurve A) (u w : A) : A :=
  1 - W.a₁ * u - W.a₂ * u ^ 2 - 2 * W.a₃ * w - 2 * W.a₄ * u * w - 3 * W.a₆ * w ^ 2

def fuAt (W : WeierstrassCurve A) (u w : A) : A :=
  3 * u ^ 2 + W.a₁ * w + 2 * W.a₂ * u * w + W.a₄ * w ^ 2

def IsFlowUW (W : WeierstrassCurve A) (D : A → A) (u w : A) : Prop :=
  WEq W u w ∧ D u = fwAt W u w ∧ D w = fuAt W u w

def FlowOfUW : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (u w v : A),
    IsDer D → IsFlowUW W D u w → v * w = 1 → IsFlow W D (u * v) (-v)


def FlowSq : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y : A),
    IsDer D → ConstCurve D W → IsFlow W D x y →
    D x ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ∧
    D (D x) = 6 * x ^ 2 + W.b₂ * x + W.b₄

def FlowWp : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y c g2 g3 : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → IsUnit (6 : A) →
    12 * c = W.b₂ → 12 * g2 = W.c₄ → 216 * g3 = W.c₆ →
    D (x + c) = 2 * y + W.a₁ * x + W.a₃ ∧
    D (x + c) ^ 2 = 4 * (x + c) ^ 3 - g2 * (x + c) - g3 ∧
    2 * D (D $ x + c) = 12 * (x + c) ^ 2 - g2


def FlowTranslate : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y xP yP t : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → W.toAffine.Equation xP yP → D xP = 0 → D yP = 0 →
    t * (x - xP) = 1 →
    IsFlow W D (W.toAffine.addX x xP $ (y - yP) * t) (W.toAffine.addY x xP y $ (y - yP) * t)

def FlowLogDeriv : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y xP yP t : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → W.toAffine.Equation xP yP → D xP = 0 → D yP = 0 →
    t * (x - xP) = 1 →
    D (t * D x) = 2 * x - W.toAffine.addX x xP ((y - yP) * t)
      - W.toAffine.addX x xP ((y - W.toAffine.negY xP yP) * t)

def ChordRegular : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (x y xP yP t : A),
    W.toAffine.Equation x y → W.toAffine.Equation xP yP → t * (x - xP) = 1 →
    W.toAffine.addX x xP ((y - yP) * t) = xP +
      ((W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * x - (2 * yP + W.a₁ * xP + W.a₃) * y
        + (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3)) * t ^ 2 ∧
    W.toAffine.addY x xP y ((y - yP) * t) =
      -((y - yP) * t * (W.toAffine.addX x xP ((y - yP) * t) - xP)) - yP
        - W.a₁ * W.toAffine.addX x xP ((y - yP) * t) - W.a₃



def FlowThird : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] (W : WeierstrassCurve A) (D : A → A)
    (u1 w1 u2 w2 l n u3 : A),
    IsDer D → ConstCurve D W → IsFlowUW W D u1 w1 → WEq W u2 w2 → D u2 = 0 → D w2 = 0 →
    l * (u1 - u2) = w1 - w2 → n = w1 - l * u1 →
    (1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3) * (u1 + u2 + u3)
      + (W.a₁ * l + W.a₂ * n + W.a₃ * l ^ 2 + 2 * W.a₄ * l * n + 3 * W.a₆ * l ^ 2 * n) = 0 →
    1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3 ≠ 0 → u1 ≠ u2 → u3 ≠ u1 → u3 ≠ u2 →
    WEq W u3 (l * u3 + n) ∧ D u3 = -fwAt W u3 (l * u3 + n) ∧
      D (l * u3 + n) = -fuAt W u3 (l * u3 + n)

def FlowNegUW : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (u w r : A),
    IsDer D → ConstCurve D W → IsFlowUW W D u w → r * (-1 + W.a₁ * u + W.a₃ * w) = 1 →
    IsFlowUW W (fun a => -D a) (u * r) (w * r)

end Formalism.L2.Th1.A
end
section
open PowerSeries (map)
open PowerSeries



namespace Formalism.L2.Th1.A

abbrev curveS {R : Type u} [CommRing R] (W : WeierstrassCurve R) : WeierstrassCurve R⟦X⟧ :=
  W.map (C : R →+* R⟦X⟧)

abbrev curveL {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    WeierstrassCurve $ LaurentSeries R :=
  W.map (HahnSeries.C : R →+* LaurentSeries R)

def WSerSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    Formalism.ELL.WFixed W (wSer W) ∧ ∀ w : R⟦X⟧, Formalism.ELL.WFixed W w → w = wSer W

def WSerFactor : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    wSer W = X ^ 3 * wU W ∧ constantCoeff (wU W) = 1 ∧ wU W * xS W = 1 ∧
    constantCoeff (xS W) = 1 ∧ constantCoeff (yS W) = -1

def UnitSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    constantCoeff (fw W) = 1 ∧ fw W * om W = 1 ∧ constantCoeff (om W) = 1 ∧
    coeff 1 (om W) = W.a₁ ∧ coeff 2 (om W) = W.a₁ ^ 2 + W.a₂ ∧
    constantCoeff (iDen W) = -1 ∧ iDen W * invOfUnit (iDen W) (-1) = 1

def SeriesMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    map φ (wSer W) = wSer (W.map φ) ∧ map φ (wU W) = wU (W.map φ) ∧
    map φ (xS W) = xS (W.map φ) ∧ map φ (yS W) = yS (W.map φ) ∧
    map φ (fw W) = fw (W.map φ) ∧ map φ (fu W) = fu (W.map φ) ∧
    map φ (om W) = om (W.map φ) ∧ map φ (iSer W) = iSer (W.map φ)

def FlowU : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    IsDer (D W) ∧ ConstCurve (D W) (curveS W) ∧ IsFlowUW (curveS W) (D W) X (wSer W) ∧
    fwAt (curveS W) X (wSer W) = fw W ∧ fuAt (curveS W) X (wSer W) = fu W ∧
    ∀ f : R⟦X⟧, om W * D W f = derivative f

def DLSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    IsDer (DL W) ∧ ConstCurve (DL W) (curveL W) ∧ (∀ r : R, DL W (HahnSeries.C r) = 0) ∧
    ∀ f : R⟦X⟧, DL W (toL f) = toL (D W f)

def FlowL : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    IsFlow (curveL W) (DL W) (xL W) (yL W) ∧
    toL X * yL W = -xL W ∧ toL (wSer W) * yL W = -1 ∧ toL (wSer W) * xL W = toL X


def ISerSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    constantCoeff (iSer W) = 0 ∧ coeff 1 (iSer W) = -1 ∧ (iSer W).subst (iSer W) = X ∧
    (wSer W).subst (iSer W) = wSer W * invOfUnit (iDen W) (-1) ∧
    (xS W).subst (iSer W) = invOfUnit (iDen W) (-1) ^ 2 * xS W ∧
    (yS W).subst (iSer W) = invOfUnit (iDen W) (-1) ^ 3 *
      (-yS W - C W.a₁ * X * xS W - C W.a₃ * X ^ 3) ∧
    D W (iSer W) = -(fw W).subst (iSer W) ∧
    (om W).subst (iSer W) * derivative (iSer W) = -om W

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A






def CompInvSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (s : R⟦X⟧), constantCoeff s = 0 → IsUnit (coeff 1 s) →
    constantCoeff (compInv s) = 0 ∧ s.subst (compInv s) = X ∧ (compInv s).subst s = X ∧
    coeff 1 (compInv s) * coeff 1 s = 1 ∧
    (∀ t : R⟦X⟧, constantCoeff t = 0 → s.subst t = X → t = compInv s) ∧
    (∀ t : R⟦X⟧, constantCoeff t = 0 → t.subst s = X → t = compInv s)

def CompInvMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (s : R⟦X⟧),
    constantCoeff s = 0 → IsUnit (coeff 1 s) →
    PowerSeries.map φ (compInv s) = compInv (PowerSeries.map φ s)

def IntegSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (f : K⟦X⟧),
    constantCoeff (integ f) = 0 ∧ derivative (integ f) = f ∧
    ∀ g : K⟦X⟧, constantCoeff g = 0 → derivative g = f → g = integ f

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

def LogSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (logSer W) = 0 ∧ coeff 1 (logSer W) = 1 ∧ derivative (logSer W) = om W ∧
    D W (logSer W) = 1

def ExpSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (expSer W) = 0 ∧ coeff 1 (expSer W) = 1 ∧
    (logSer W).subst (expSer W) = X ∧ (expSer W).subst (logSer W) = X ∧
    derivative (expSer W) = (fw W).subst (expSer W)

def ChainZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (f : K⟦X⟧),
    derivative (f.subst (expSer W)) = (D W f).subst (expSer W)

def LogNeg : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (logSer W).subst (iSer W) = -logSer W ∧
    (expSer W).subst (-X : K⟦X⟧) = (iSer W).subst (expSer W)

def FlowZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    IsFlow (curveL W) dL (xZ W) (yZ W) ∧ toL (expSer W) * yZ W = -xZ W

def WpODE : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    dL (wpL W) = 2 * yZ W + HahnSeries.C W.a₁ * xZ W + HahnSeries.C W.a₃ ∧
    dL (wpL W) ^ 2 = 4 * wpL W ^ 3 - HahnSeries.C (g₂ W) * wpL W - HahnSeries.C (g₃ W) ∧
    dL (dL $ wpL W) = 6 * wpL W ^ 2 - HahnSeries.C (g₂ W / 2)

def WpShape : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    wpL W = uPow (-2) + toL (wpReg W) ∧ coeff 0 (wpReg W) = 0 ∧
    (∀ n : ℕ, Odd n → coeff n (wpReg W) = 0) ∧
    coeff 2 (wpReg W) = g₂ W / 20 ∧ coeff 4 (wpReg W) = g₃ W / 28


def WpRecursion : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (k : ℕ), 3 ≤ k →
    ((k : K) - 2) * (2 * (k : K) + 3) * coeff (2 * k) (wpReg W) =
      3 * ∑ i ∈ Finset.Icc 1 (k - 2), coeff (2 * i) (wpReg W) * coeff (2 * (k - 1 - i)) (wpReg W)

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

abbrev U₁ {R : Type u} [CommRing R] : MvPowerSeries (Fin 2) R := MvPowerSeries.X 0

abbrev U₂ {R : Type u} [CommRing R] : MvPowerSeries (Fin 2) R := MvPowerSeries.X 1

def FglMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    MvPowerSeries.map φ (fgl W) = fgl (W.map φ)

def FglChord : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    lam W * (U₂ - U₁) = (wSer W).subst (U₂ : MvPowerSeries (Fin 2) R) - (wSer W).subst (U₁ : MvPowerSeries (Fin 2) R) ∧
    MvPowerSeries.constantCoeff (uThird W) = 0 ∧
    wThird W = (wSer W).subst (uThird W) ∧
    fgl W = (iSer W).subst (uThird W) ∧
    MvPowerSeries.constantCoeff (fgl W) = 0 ∧
    MvPowerSeries.coeff (Finsupp.single 0 1) (fgl W) = 1 ∧
    MvPowerSeries.coeff (Finsupp.single 1 1) (fgl W) = 1

def FglSum : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K),
    Formalism.ELL.ChordAt W (wSer W) U₁ U₂ $ fgl W



def FglLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (logSer W).subst (fgl W) = (logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K) ∧
    fgl W = (expSer W).subst ((logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K))




def ZSerMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)
    (n : ℤ), PowerSeries.map φ (zSer W n) = zSer (W.map φ) n


def HalfSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R), IsUnit (2 : R) →
    constantCoeff (halfSer W) = 0 ∧ 2 * coeff 1 (halfSer W) = 1 ∧
    (nSer W 2).subst (halfSer W) = X ∧ (halfSer W).subst (nSer W 2) = X ∧
    MvPowerSeries.subst (![halfSer W, halfSer W] : Fin 2 → R⟦X⟧) (fgl W) = X

def HalfLog : Prop :=
  (∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    2 * (logSer W).subst (halfSer W) = logSer W) ∧
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    IsUnit (2 : R) → PowerSeries.map φ (halfSer W) = halfSer (W.map φ)

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

def ZMap : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [CharZero K] [Field L] [CharZero L] (φ : K →+* L)
    (W : WeierstrassCurve K),
    PowerSeries.map φ (logSer W) = logSer (W.map φ) ∧
    PowerSeries.map φ (expSer W) = expSer (W.map φ) ∧
    PowerSeries.map φ (wpReg W) = wpReg (W.map φ) ∧
    φ (g₂ W) = g₂ (W.map φ) ∧ φ (g₃ W) = g₃ (W.map φ)









end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A



def PlusFlow : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    IsFlow (curveS W) (D W) (xPlus W xP yP) (yPlus W xP yP) ∧
    constantCoeff (xPlus W xP yP) = xP ∧ constantCoeff (yPlus W xP yP) = yP



def PlusMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)
    (xP yP : R),
    PowerSeries.map φ (tS W xP) = tS (W.map φ) (φ xP) ∧
    PowerSeries.map φ (xPlus W xP yP) = xPlus (W.map φ) (φ xP) (φ yP) ∧
    PowerSeries.map φ (yPlus W xP yP) = yPlus (W.map φ) (φ xP) (φ yP)



def PlusZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    IsFlow (curveS W) (derivative (R := K)) ((xPlus W xP yP).subst (expSer W))
      ((yPlus W xP yP).subst (expSer W)) ∧
    toL ((tS W xP).subst (expSer W)) * (xZ W - HahnSeries.C xP) = 1 ∧
    dL (toL ((tS W xP).subst (expSer W)) * dL (wpL W))
      = 2 * xZ W - toL ((xPlus W xP yP).subst (expSer W))
        - toL ((xPlus W xP $ W.toAffine.negY xP yP).subst (expSer W))

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

def WpCleared : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (wpReg W) = 0 ∧ (∀ n : ℕ, Odd n → coeff n (wpReg W) = 0) ∧
    (-2 + X ^ 3 * derivative (wpReg W)) ^ 2 =
      4 * (1 + X ^ 2 * wpReg W) ^ 3 - C (g₂ W) * X ^ 4 * (1 + X ^ 2 * wpReg W) - C (g₃ W) * X ^ 6

def WpInU : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    X ^ 2 * (1 + logSer W ^ 2 * (wpReg W).subst (logSer W)) =
      logSer W ^ 2 * (xS W + C (W.b₂ / 12) * X ^ 2)

def TInZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP : K),
    (tS W xP).subst (expSer W) * (1 + X ^ 2 * wpReg W - C (xP + W.b₂ / 12) * X ^ 2) = X ^ 2

def CubeTwoR : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    ∃ c : MvPowerSeries (Fin 2) R, MvPowerSeries.constantCoeff c = -1 ∧
      U₂ ^ 2 * (xS W).subst (U₁ : MvPowerSeries (Fin 2) R)
        - U₁ ^ 2 * (xS W).subst (U₂ : MvPowerSeries (Fin 2) R)
        = c * fgl W * MvPowerSeries.subst
            (![U₁, (iSer W).subst (U₂ : MvPowerSeries (Fin 2) R)] :
              Fin 2 → MvPowerSeries (Fin 2) R) (fgl W)


def CoeffMem : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (S : Subring R),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S →
    (∀ n, coeff n (wSer W) ∈ S) ∧ (∀ n, coeff n (xS W) ∈ S) ∧ (∀ n, coeff n (yS W) ∈ S) ∧
    (∀ n, coeff n (fw W) ∈ S) ∧ (∀ n, coeff n (om W) ∈ S) ∧ (∀ n, coeff n (iSer W) ∈ S) ∧
    (∀ d, MvPowerSeries.coeff d (fgl W) ∈ S) ∧ (∀ (k : ℤ) n, coeff n (zSer W k) ∈ S) ∧
    ((∃ h ∈ S, 2 * h = 1) → ∀ n, coeff n (halfSer W) ∈ S) ∧
    (∀ xP ∈ S, ∀ n, coeff n (tS W xP) ∈ S) ∧
    (∀ xP ∈ S, ∀ yP ∈ S, ∀ n, coeff n (xPlus W xP yP) ∈ S ∧ coeff n (yPlus W xP yP) ∈ S)


end Formalism.L2.Th1.A
end
section
open Formalism.L2.Th1.CM (uSer wpDen wpNum)
open PowerSeries


namespace Formalism.L2.Th1.A

def shortW {K : Type} [Field K] (g2 g3 : K) : WeierstrassCurve K :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -g2 / 4, a₆ := -g3 / 4 }

def ShortInv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    (shortW g2 g3).b₂ = 0 ∧ g₂ (shortW g2 g3) = g2 ∧ g₃ (shortW g2 g3) = g3 ∧
    (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2

def WpNumEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    wpNum (g₂ W) (g₃ W) = 1 + X ^ 2 * wpReg W ∧
    wpDen (g₂ W) (g₃ W) = 1 - C (1 / 2 : K) * X ^ 3 * derivative (wpReg W)


def USerEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    uSer g2 g3 = expSer (shortW g2 g3)

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

def PlusZCleared : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    derivative (derivative $ 1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12)))
        * (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12)))
      - derivative (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))) ^ 2
      = (2 * wpReg W - ((xPlus W xP yP).subst (expSer W) + C (W.b₂ / 12))
          - ((xPlus W xP $ W.toAffine.negY xP yP).subst (expSer W) + C (W.b₂ / 12)))
        * (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))) ^ 2






end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

section Tools

variable {R : Type u} [CommRing R]

theorem eq_substInv_of_right (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s))
    (t : R⟦X⟧) (ht0 : constantCoeff t = 0) (ht : s.subst t = X) :
    t = s.substInvOfIsUnit h1 := by
  have hT := HasSubst.of_constantCoeff_zero' ht0
  have key := subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' h0) hT $ s.substInvOfIsUnit h1
  rwa [subst_substInvOfIsUnit_left s h0 h1, subst_X hT, ht, X_subst] at key

theorem eq_substInv_of_left (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s))
    (t : R⟦X⟧) (ht : t.subst s = X) :
    t = s.substInvOfIsUnit h1 := by
  have hq := HasSubst.substInvOfIsUnit s h1
  have key := subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' h0) hq t
  rw [subst_substInvOfIsUnit_right s h0 h1, ht, subst_X hq, X_subst] at key
  exact key.symm

theorem compInv_eq_substInv (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s)) :
    compInv s = s.substInvOfIsUnit h1 := by
  have hex : ∃ t : R⟦X⟧, constantCoeff t = 0 ∧ s.subst t = X :=
    ⟨s.substInvOfIsUnit h1, constantCoeff_substInvOfIsUnit s h1,
      subst_substInvOfIsUnit_right s h0 h1⟩
  unfold compInv
  rw [dif_pos hex]
  exact eq_substInv_of_right s h0 h1 _ hex.choose_spec.1 hex.choose_spec.2

end Tools

theorem composition_inverse_spec : CompInvSpec.{u} := by
  intro R _ s h0 h1
  rw [compInv_eq_substInv s h0 h1]
  refine ⟨constantCoeff_substInvOfIsUnit s h1, subst_substInvOfIsUnit_right s h0 h1,
    subst_substInvOfIsUnit_left s h0 h1, ?_, fun t ht0 ht => eq_substInv_of_right s h0 h1 t ht0 ht,
    fun t _ ht => eq_substInv_of_left s h0 h1 t ht⟩
  rw [coeff_one_substInvOfIsUnit]
  exact h1.val_inv_mul

theorem composition_inverse_map : CompInvMap.{u, v} := by
  intro R S _ _ φ s h0 h1
  have h0' : constantCoeff (PowerSeries.map φ s) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have h1' : IsUnit $ coeff 1 $ PowerSeries.map φ s := by
    rw [coeff_map]
    exact h1.map φ
  rw [compInv_eq_substInv _ h0' h1', compInv_eq_substInv s h0 h1]
  apply eq_substInv_of_right _ h0' h1'
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_substInvOfIsUnit, map_zero]
  have := PowerSeries.map_subst (HasSubst.substInvOfIsUnit s h1) (h := φ) s
  rw [subst_substInvOfIsUnit_right s h0 h1] at this
  rw [← PowerSeries.map_X φ]
  exact this.symm

theorem integration_spec : IntegSpec.{u} := by
  unfold IntegSpec
  intro K _ _ f
  have hc : ∀ n, coeff (n + 1) (integ f) = coeff n f / ((n : K) + 1) := by
    intro n
    unfold integ
    simp
  refine ⟨?_, (by
      ext n
      rw [coeff_derivative, hc]
      have : ((n : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp), ?_⟩
  unfold integ
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  simp
  intro g hg0 hg
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff_apply, hg0]
    unfold integ
    simp
  | succ k =>
    rw [hc]
    have h1 := congrArg (coeff k) hg
    rw [coeff_derivative] at h1
    have : ((k : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
    rw [← h1]
    field_simp

end Formalism.L2.Th1.A
end
section
open Formalism.ELL (WFixed wSeriesUnique)
open PowerSeries (mul_invOfUnit)
open Units (val_neg val_one)
open PowerSeries



namespace Formalism.L2.Th1.A

namespace CurveSer

section Tools

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem map_invOfUnit (φ : R →+* S) (a : R⟦X⟧) (e : Rˣ) (h : constantCoeff a = e) :
    PowerSeries.map φ (invOfUnit a e) = invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by
  have h1 : PowerSeries.map φ a * PowerSeries.map φ (invOfUnit a e) = 1 := by
    rw [← map_mul, mul_invOfUnit a e h, map_one]
  have h2 : PowerSeries.map φ a * invOfUnit (PowerSeries.map φ a) (Units.map φ e) = 1 := by
    apply mul_invOfUnit
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h]
    simp
  calc PowerSeries.map φ (invOfUnit a e)
      = PowerSeries.map φ (invOfUnit a e) *
          (PowerSeries.map φ a * invOfUnit (PowerSeries.map φ a) (Units.map φ e)) := by
        rw [h2, mul_one]
    _ = (PowerSeries.map φ a * PowerSeries.map φ (invOfUnit a e)) *
          invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by ring
    _ = invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by rw [h1, one_mul]

end Tools

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem wSer_fixed : WFixed W $ wSer W := (wSeriesUnique R W).choose_spec.1

theorem wSer_unique {w : R⟦X⟧} (hw : WFixed W w) : w = wSer W := (wSeriesUnique R W).unique hw $ wSer_fixed W

theorem wSer_cc : constantCoeff (wSer W) = 0 := (wSer_fixed W).1

private theorem exists_wSer_eq_X_cube_mul : ∃ v, wSer W = X ^ 3 * v := by
  have hfix := (wSer_fixed W).2
  obtain ⟨v1, hv1⟩ := (PowerSeries.X_dvd_iff).mpr $ wSer_cc W
  obtain ⟨v2, hv2⟩ : X ^ 2 ∣ wSer W := ⟨X + C W.a₁ * v1 + C W.a₂ * X * v1 + C W.a₃ * v1 ^ 2
      + C W.a₄ * X * v1 ^ 2 + C W.a₆ * X * v1 ^ 3, by rw [hfix, hv1]
                                                      ring⟩
  use 1 + C W.a₁ * v2 + C W.a₂ * X * v2 + C W.a₃ * X * v2 ^ 2 + C W.a₄ * X ^ 2 * v2 ^ 2
    + C W.a₆ * X ^ 3 * v2 ^ 3
  rw [hfix, hv2]
  ring
theorem wSer_eq : wSer W = X ^ 3 * wU W := by
  obtain ⟨v, hv⟩ := exists_wSer_eq_X_cube_mul W
  have hu : wU W = v := by
    ext n
    unfold wU
    rw [coeff_mk, hv]
    simp [coeff_X_pow_mul']
  rwa [hu]

theorem wU_cc : constantCoeff (wU W) = 1 := by
  have hfix := (wSer_fixed W).2
  rw [wSer_eq W] at hfix
  have e : X ^ 3 + C W.a₁ * X * (X ^ 3 * wU W) + C W.a₂ * X ^ 2 * (X ^ 3 * wU W)
      + C W.a₃ * (X ^ 3 * wU W) ^ 2 + C W.a₄ * X * (X ^ 3 * wU W) ^ 2
      + C W.a₆ * (X ^ 3 * wU W) ^ 3
      = X ^ 3 * (1 + X * (C W.a₁ * wU W + C W.a₂ * X * wU W + C W.a₃ * X ^ 2 * wU W ^ 2
        + C W.a₄ * X ^ 3 * wU W ^ 2 + C W.a₆ * X ^ 5 * wU W ^ 3)) := by ring
  simpa [coeff_X_pow_mul'] using (congrArg (coeff 3) $ hfix.trans e)

theorem wU_mul_xS : wU W * xS W = 1 := mul_invOfUnit (wU W) 1 $ by rw [wU_cc W, val_one]

theorem xS_cc : constantCoeff (xS W) = 1 := by
  have h := congrArg constantCoeff $ wU_mul_xS W
  rwa [map_mul, wU_cc W, one_mul, map_one] at h

theorem yS_cc : constantCoeff (yS W) = -1 := by
  unfold yS
  rw [map_neg, xS_cc W]

theorem fw_cc : constantCoeff (fw W) = 1 := by
  unfold fw
  simp [wSer_cc W]

theorem fw_mul_om : fw W * om W = 1 := mul_invOfUnit (fw W) 1 $ by rw [fw_cc W, val_one]

theorem om_cc : constantCoeff (om W) = 1 := by
  have h := congrArg constantCoeff $ fw_mul_om W
  rwa [map_mul, fw_cc W, one_mul, map_one] at h

theorem fw_eq : fw W = 1 - C W.a₁ * X - C W.a₂ * X ^ 2
    - X ^ 3 * (2 * C W.a₃ * wU W + 2 * C W.a₄ * X * wU W + 3 * C W.a₆ * wU W * wSer W) := by
  unfold fw
  linear_combination (-2 * C W.a₃ - 2 * C W.a₄ * X - 3 * C W.a₆ * wSer W) * wSer_eq W

theorem fw_coeff_one : coeff 1 (fw W) = -W.a₁ := by
  rw [fw_eq W]
  simp [coeff_X_pow_mul', coeff_X_pow, coeff_one, coeff_C_mul]

theorem fw_coeff_two : coeff 2 (fw W) = -W.a₂ := by
  rw [fw_eq W]
  simp [coeff_X_pow_mul', coeff_X_pow, coeff_one, coeff_C_mul]

theorem om_coeff_one : coeff 1 (om W) = W.a₁ := by
  have h := congrArg (coeff 1) $ fw_mul_om W
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    fw_cc W, om_cc W, fw_coeff_one W, coeff_one] at h
  first
    | linear_combination h
    | linear_combination -h

theorem om_coeff_two : coeff 2 (om W) = W.a₁ ^ 2 + W.a₂ := by
  have h := congrArg (coeff 2) $ fw_mul_om W
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    fw_cc W, om_cc W, fw_coeff_one W, fw_coeff_two W, om_coeff_one W, coeff_one] at h
  first
    | linear_combination h
    | linear_combination -h

theorem iDen_cc : constantCoeff (iDen W) = -1 := by
  unfold iDen
  simp [wSer_cc W]

theorem iDen_mul_inv : iDen W * invOfUnit (iDen W) (-1) = 1 := mul_invOfUnit (iDen W) (-1) $ by rw [iDen_cc W, val_neg, val_one]

theorem D_apply (f : R⟦X⟧) : D W f = fw W * derivative f := rfl

theorem deriv_wSer_mul_fw : derivative (wSer W) * fw W = fu W := by
  have h := congrArg (derivative (R := R)) (wSer_fixed W).2
  simp [Derivation.leibniz, Derivation.leibniz_pow, derivative_C, derivative_X, smul_eq_mul,
    nsmul_eq_mul] at h
  unfold fw fu
  linear_combination h

theorem om_mul_D (f : R⟦X⟧) : om W * D W f = derivative f := by
  rw [D_apply, ← mul_assoc, mul_comm $ om W, fw_mul_om W, one_mul]

section Map

variable {S : Type v} [CommRing S] (φ : R →+* S)

theorem map_wSer : PowerSeries.map φ (wSer W) = wSer (W.map φ) := by
  refine wSer_unique (W.map φ) ?_
  unfold WFixed
  constructor
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
    wSer_cc W, map_zero]
  conv_lhs => rw [(wSer_fixed W).2]
  simp

theorem map_wU : PowerSeries.map φ (wU W) = wU (W.map φ) := by
  ext n
  simp [wU, coeff_map, coeff_mk, ← map_wSer W φ]

theorem map_xS : PowerSeries.map φ (xS W) = xS (W.map φ) := by
  unfold xS
  rw [map_invOfUnit φ (wU W) 1 $ by rw [wU_cc W, val_one], map_wU W φ, map_one]

theorem map_yS : PowerSeries.map φ (yS W) = yS (W.map φ) := by
  unfold yS
  rw [map_neg, map_xS W φ]

theorem map_fw : PowerSeries.map φ (fw W) = fw (W.map φ) := by
  have h2 : PowerSeries.map φ (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : PowerSeries.map φ (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fw
  simp [map_wSer W φ, h2, h3]

theorem map_fu : PowerSeries.map φ (fu W) = fu (W.map φ) := by
  have h2 : PowerSeries.map φ (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : PowerSeries.map φ (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fu
  simp [map_wSer W φ, h2, h3]

theorem map_om : PowerSeries.map φ (om W) = om (W.map φ) := by
  unfold om
  rw [map_invOfUnit φ (fw W) 1 $ by rw [fw_cc W, val_one], map_fw W φ, map_one]

theorem map_iDen : PowerSeries.map φ (iDen W) = iDen (W.map φ) := by
  unfold iDen
  simp [map_wSer W φ]

theorem map_iSer : PowerSeries.map φ (iSer W) = iSer (W.map φ) := by
  have hu : Units.map (φ : R →* S) (-1) = -1 := Units.ext (by simp)
  unfold iSer
  rw [map_mul, map_X, map_invOfUnit φ (iDen W) (-1) $ by rw [iDen_cc W, val_neg, val_one],
    map_iDen W φ, hu]

end Map

end CurveSer

open CurveSer

theorem w_series_spec : WSerSpec.{u} := by
  unfold WSerSpec
  intro R _ W
  constructor
  exact wSer_fixed W
  exact fun w hw => wSer_unique W hw
theorem w_series_factorization : WSerFactor.{u} := by
  unfold WSerFactor
  intro R _ W
  exact ⟨wSer_eq W, wU_cc W, wU_mul_xS W, xS_cc W, yS_cc W⟩

theorem invariant_differential_units : UnitSpec.{u} := by
  unfold UnitSpec
  intro R _ W
  exact ⟨fw_cc W, fw_mul_om W, om_cc W, om_coeff_one W, om_coeff_two W, iDen_cc W, iDen_mul_inv W⟩

theorem series_map : SeriesMap.{u, v} := by
  unfold SeriesMap
  intro R S _ _ φ W
  exact ⟨map_wSer W φ, map_wU W φ, map_xS W φ, map_yS W φ, map_fw W φ, map_fu W φ, map_om W φ,
    map_iSer W φ⟩

theorem unit_flow : FlowU.{u} := by
  unfold FlowU
  intro R _ W
  have hfw : fwAt (curveS W) X (wSer W) = fw W := by
    unfold fwAt fw
    simp
  have hfu : fuAt (curveS W) X (wSer W) = fu W := by
    unfold fuAt fu
    simp
  refine ⟨?_, ?_, ?_, hfw, hfu, om_mul_D W⟩
  unfold IsDer
  exact ⟨fun a b => map_add (D W) a b, fun a b => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]⟩
  unfold ConstCurve
  simp [D_apply]
  unfold IsFlowUW
  refine ⟨?_, ?_, ?_⟩
  unfold WEq
  simpa using (wSer_fixed W).2
  rw [D_apply, derivative_X, mul_one, hfw]
  rw [D_apply, mul_comm, deriv_wSer_mul_fw W, hfu]

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

namespace ISer

variable {R : Type u} [CommRing R]

def subHom (s : R⟦X⟧) (hs : constantCoeff s = 0) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  substAlgHom $ HasSubst.of_constantCoeff_zero' hs

theorem subHom_apply (s : R⟦X⟧) (hs : constantCoeff s = 0) (f : R⟦X⟧) :
    subHom s hs f = f.subst s := by
  unfold subHom
  rw [PowerSeries.coe_substAlgHom]

theorem subHom_X (s : R⟦X⟧) (hs : constantCoeff s = 0) : subHom s hs X = s := by
  rw [subHom_apply, PowerSeries.subst_X $ HasSubst.of_constantCoeff_zero' hs]

theorem subHom_C (s : R⟦X⟧) (hs : constantCoeff s = 0) (a : R) : subHom s hs (C a) = C a := by
  simpa using ((subHom s hs).commutes a)

theorem eq_wSer_subst (hW : WSerSpec.{u}) (W : WeierstrassCurve R) (s v : R⟦X⟧)
    (hs : constantCoeff s = 0) (hv : constantCoeff v = 0)
    (h : v = s ^ 3 + C W.a₁ * s * v + C W.a₂ * s ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * s * v ^ 2
      + C W.a₆ * v ^ 3) : v = (wSer W).subst s := by
  set w := (wSer W).subst s with hw
  obtain ⟨hfix0, hfix⟩ := (hW R W).1
  have hweq : w = s ^ 3 + C W.a₁ * s * w + C W.a₂ * s ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * s * w ^ 2
      + C W.a₆ * w ^ 3 := by
    have h2 := congrArg (subHom s hs) hfix
    simp [map_add, map_mul, map_pow, subHom_X, subHom_C] at h2
    rw [subHom_apply] at h2
    exact h2
  have hw0 : constantCoeff w = 0 := by
    obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hfix0
    have h3 : w = s * subHom s hs q := by
      rw [hw, ← subHom_apply s hs, hq, map_mul, subHom_X]
    rw [h3, map_mul, hs, zero_mul]
  set E := C W.a₁ * s + C W.a₂ * s ^ 2 + C W.a₃ * (v + w) + C W.a₄ * s * (v + w)
    + C W.a₆ * (v ^ 2 + v * w + w ^ 2) with hE
  have h4 : v - w = (v - w) * E := by
    rw [hE]
    linear_combination h - hweq
  have hu : IsUnit $ 1 - E := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h5 : constantCoeff E = 0 := by
      rw [hE]
      simp [hs, hv, hw0]
    rw [map_sub, map_one, h5, sub_zero]
    exact isUnit_one
  exact sub_eq_zero.mp $ (hu.mul_left_eq_zero).mp $ by linear_combination h4

end ISer

open ISer in
theorem iSerSpec_of (hW : WSerSpec.{u}) (hF : WSerFactor.{u}) (hU : UnitSpec.{u})
    (hD : FlowU.{u}) (hN : FlowNegUW.{u}) : ISerSpec.{u} := by
  intro R _ W
  obtain ⟨hw3, -, hUx, -, -⟩ := hF R W
  obtain ⟨-, hfo, -, -, -, hq0, hqr⟩ := hU R W
  obtain ⟨hDer, hConst, hFlow, -, -, hom⟩ := hD R W
  set r : R⟦X⟧ := invOfUnit (iDen W) (-1) with hr
  have hq : iDen W = -1 + C W.a₁ * X + C W.a₃ * wSer W := rfl
  have hi : iSer W = X * r := rfl
  have hr0 : constantCoeff r = -1 := by
    rw [hr, constantCoeff_invOfUnit]
    simp
  have hi0 : constantCoeff (iSer W) = 0 := by rw [hi]
                                              simp
  have hneg := hN R⟦X⟧ (curveS W) (D W) X (wSer W) r hDer hConst hFlow
    (by
      have : (-1 + (curveS W).a₁ * X + (curveS W).a₃ * wSer W : R⟦X⟧) = iDen W := rfl
      rw [this, mul_comm]
      exact hqr)
  obtain ⟨hE, hDi, -⟩ := hneg
  have hwi : (wSer W).subst (iSer W) = wSer W * r := by
    symm
    apply eq_wSer_subst hW W (iSer W) (wSer W * r) hi0 $ by simp [(hW R W).1.1]
    exact hE
  set φ := subHom (iSer W) hi0 with hφ
  have φa : ∀ f, f.subst (iSer W) = φ f := fun f => (subHom_apply _ _ f).symm
  have φX : φ X = X * r := subHom_X _ _
  have φC : ∀ a, φ (C a) = C a := subHom_C _ _
  have φw : φ (wSer W) = wSer W * r := by rw [← φa, hwi]
  have φq : φ (iDen W) = r := by
    rw [hq]
    simp [map_add, map_mul, map_neg, map_one, φX, φC, φw]
    rw [hq] at hqr
    linear_combination hqr
  have φr : φ r = iDen W := by
    have h1 : φ (iDen W) * φ r = 1 := by rw [← map_mul, hqr, map_one]
    rw [φq] at h1
    linear_combination (iDen W) * h1 - (φ r) * hqr
  have hii : φ (iSer W) = X := by
    rw [hi, map_mul, φX, φr]
    linear_combination X * hqr
  have φU : φ (wU W) = wU W * iDen W ^ 2 := by
    have h1 : φ (wSer W) = φ X ^ 3 * φ (wU W) := by rw [← map_pow, ← map_mul, ← hw3]
    rw [φw, φX] at h1
    have h2 : X ^ 3 * (wU W * r) = X ^ 3 * (r ^ 3 * φ (wU W)) := by
      linear_combination h1 - r * hw3
    linear_combination (-(iDen W) ^ 3) * X_pow_mul_cancel h2
      + (wU W * iDen W ^ 2 - φ (wU W) * ((iDen W * r) ^ 2 + iDen W * r + 1)) * hqr
  have φx : φ (xS W) = r ^ 2 * xS W := by
    have h1 : φ (wU W) * φ (xS W) = 1 := by rw [← map_mul, hUx, map_one]
    rw [φU] at h1
    linear_combination (r ^ 2 * xS W) * h1 - φ (xS W) * (iDen W * r) ^ 2 * hUx
      - φ (xS W) * (iDen W * r + 1) * hqr
  have φfw : φ (fw W) = fwAt (curveS W) (X * r) (wSer W * r) := by
    have : fwAt (curveS W) (X * r) (wSer W * r) = 1 - C W.a₁ * (X * r) - C W.a₂ * (X * r) ^ 2
      - 2 * C W.a₃ * (wSer W * r) - 2 * C W.a₄ * (X * r) * (wSer W * r)
      - 3 * C W.a₆ * (wSer W * r) ^ 2 := rfl
    rw [this, fw]
    simp [map_sub, map_mul, map_pow, map_one, map_ofNat, φX, φC, φw]
  have hDi' : D W (iSer W) = -φ (fw W) := by
    rw [φfw, ← hDi, hi, neg_neg]
  refine ⟨hi0, by
      rw [hi, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
        hr0], ?_, hwi, ?_, ?_, ?_, ?_⟩
  rw [φa, hii]
  rw [φa, φx]
  rw [φa, yS, map_neg, φx]
  rw [hq] at hqr
  linear_combination (r ^ 2 * xS W) * hqr - r ^ 3 * C W.a₃ * xS W * hw3
    - r ^ 3 * C W.a₃ * X ^ 3 * hUx
  rw [φa, hDi']
  rw [φa, ← hom, hDi']
  have h1 : φ (fw W) * φ (om W) = 1 := by rw [← map_mul, hfo, map_one]
  linear_combination (-om W) * h1

end Formalism.L2.Th1.A
end
section
open WeierstrassCurve (b₂ b₄)
namespace Formalism.L2.Th1.A

namespace IsDer

variable {A : Type u} [CommRing A] {D : A → A}

theorem map_add (h : IsDer D) (a b : A) : D (a + b) = D a + D b := h.1 a b

theorem map_mul (h : IsDer D) (a b : A) : D (a * b) = a * D b + b * D a := h.2 a b

theorem map_zero (h : IsDer D) : D 0 = 0 := by
  have h0 := h.1 0 0
  rw [add_zero] at h0
  linear_combination -h0

theorem map_one (h : IsDer D) : D 1 = 0 := by
  have h1 := h.2 1 1
  rw [show (1 : A) * 1 = 1 by ring] at h1
  linear_combination -h1

theorem map_neg (h : IsDer D) (a : A) : D (-a) = -D a := by
  have h1 := h.1 a $ -a
  rw [show a + -a = 0 by ring, h.map_zero] at h1
  linear_combination -h1

theorem map_sub (h : IsDer D) (a b : A) : D (a - b) = D a - D b := by
  rw [sub_eq_add_neg, h.map_add, h.map_neg, ← sub_eq_add_neg]

theorem map_natCast (h : IsDer D) (n : ℕ) : D (n : A) = 0 := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact h.map_zero
  | succ n ih => rw [Nat.cast_succ, h.map_add, ih, h.map_one, add_zero]

theorem map_intCast (h : IsDer D) (n : ℤ) : D (n : A) = 0 := by
  rcases n with n | n
  rw [Int.ofNat_eq_coe, Int.cast_natCast]
  exact h.map_natCast n
  rw [Int.cast_negSucc, h.map_neg, h.map_natCast, neg_zero]

theorem map_ofNat (h : IsDer D) (n : ℕ) [n.AtLeastTwo] : D (OfNat.ofNat n : A) = 0 := by
  have h1 := h.map_natCast $ OfNat.ofNat n
  rwa [Nat.cast_ofNat] at h1

theorem map_sq (h : IsDer D) (a : A) : D (a ^ 2) = 2 * a * D a := by
  rw [pow_two, h.map_mul]
  ring

theorem map_pow_succ (h : IsDer D) (a : A) (n : ℕ) :
    D (a ^ (n + 1)) = (n + 1 : A) * a ^ n * D a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, h.map_mul, ih]
    push_cast
    ring

theorem map_pow (h : IsDer D) (a : A) (n : ℕ) : D (a ^ n) = (n : A) * a ^ (n - 1) * D a := by
  rcases n with _ | n
  rw [pow_zero, h.map_one, Nat.cast_zero, zero_mul, zero_mul]
  rw [h.map_pow_succ, Nat.add_sub_cancel]
  push_cast
  ring

theorem map_of_mul_eq_one (h : IsDer D) {v w : A} (hvw : v * w = 1) : D v = -v ^ 2 * D w := by
  have h2 := h.2 v w
  rw [hvw, h.map_one] at h2
  linear_combination (-D v) * hvw - v * h2

theorem neg (h : IsDer D) : IsDer fun a => -D a :=
  ⟨fun a b => by
    show -D (a + b) = -D a + -D b
    rw [h.map_add]
    ring,
   fun a b => by
    show -D (a * b) = a * -D b + b * -D a
    rw [h.map_mul]
    ring⟩



end IsDer

theorem chartFlowToFlow : FlowOfUW.{u} := by
  intro A _ W D u w v h hF hvw
  obtain ⟨hW, hDu, hDw⟩ := hF
  unfold WEq at hW
  have hDv : D v = -v ^ 2 * fuAt W u w := by rw [h.map_of_mul_eq_one hvw, hDw]
  refine ⟨?_, ?_, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  linear_combination ((-1) * v^2 + 1 * W.a₁ * u * v^2 + 1 * W.a₃ * v + 1 * W.a₃ * w * v^2 + 1 * W.a₂ * u^2 * v^2 + 1 * W.a₄ * u * v + 1 * W.a₄ * u * w * v^2 + 1 * W.a₆ + 1 * W.a₆ * w * v + 1 * W.a₆ * w^2 * v^2) * hvw + (1 * v^3) * hW
  rw [h.map_mul, hDv, hDu]
  simp [fwAt, fuAt]
  linear_combination ((-3) * v + 2 * W.a₁ * u * v + 1 * W.a₂ * u^2 * v + 3 * W.a₃ * w * v + 2 * W.a₄ * u * w * v + 3 * W.a₆ * w^2 * v + 1 * W.a₃) * hvw + (3 * v^2) * hW
  rw [h.map_neg, hDv]
  simp [fuAt]
  linear_combination (2 * W.a₂ * u * v + 1 * W.a₄ + 1 * W.a₄ * w * v + 1 * W.a₁ * v) * hvw

theorem flowDifferentialEquation : FlowSq.{u} := by
  intro A _ W D x y h hC hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  obtain ⟨hE, hDx, hDy⟩ := hF
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  constructor
  rw [hDx, b₂, b₄, WeierstrassCurve.b₆]
  linear_combination 4 * hE
  rw [hDx]
  simp [h.map_add, h.map_mul, h.map_ofNat, c1, c3, hDx, hDy]
  rw [b₂, b₄]
  ring

theorem flowWeierstrassForm : FlowWp.{u} := by
  intro A _ W D x y c g2 g3 h hC hF hu6 h12c h12g2 h216g3
  obtain ⟨hsq1, hsq2⟩ := flowDifferentialEquation A W D x y h hC hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  obtain ⟨hE, hDx, hDy⟩ := hF
  obtain ⟨s, hs⟩ := hu6.exists_right_inv
  have hb := congrArg D h12c
  simp [b₂, h.map_add, h.map_mul, h.map_sq, h.map_ofNat, c1, c2] at hb
  have h12 : 12 * D c = 0 := by linear_combination hb
  have hDc : D c = 0 := by linear_combination (-(6 * s + 1) * D c) * hs + 3 * s ^ 2 * h12
  have hDxc : D (x + c) = D x := by rw [h.map_add, hDc, add_zero]
  rw [WeierstrassCurve.c₄] at h12g2
  rw [WeierstrassCurve.c₆] at h216g3
  have hb4 : 2 * W.b₄ = 12 * c ^ 2 - g2 := by
    linear_combination (-(6 * s + 1) * (2 * W.b₄ - (12 * c ^ 2 - g2))) * hs + 3 * s ^ 2 * h12g2
      - 3 * s ^ 2 * (12 * c + W.b₂) * h12c
  have hb6 : W.b₆ = -g3 + 4 * c ^ 3 - c * g2 := by
    linear_combination (-(36 * s ^ 2 + 6 * s + 1) * (W.b₆ - (-g3 + 4 * c ^ 3 - c * g2))) * hs
      + s ^ 3 * (h216g3 + (144 * c ^ 2 + 12 * c * W.b₂ + W.b₂ ^ 2 - 36 * W.b₄) * h12c
        + 216 * c * hb4)
  refine ⟨?_, ?_, ?_⟩
  rw [hDxc, hDx]
  rw [hDxc]
  linear_combination hsq1 - x ^ 2 * h12c + x * hb4 + hb6
  rw [hDxc]
  linear_combination 2 * hsq2 - 2 * x * h12c + hb4

theorem chartFlowNegation : FlowNegUW.{u} := by
  intro A _ W D u w r h hC hF hr
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  obtain ⟨hW, hDu, hDw⟩ := hF
  unfold WEq at hW
  have hDq : D (-1 + W.a₁ * u + W.a₃ * w) = W.a₁ * fwAt W u w + W.a₃ * fuAt W u w := by
    simp only [h.map_add, h.map_neg, h.map_one, h.map_mul, c1, c3, hDu, hDw]
    ring
  have hDr : D r = -r ^ 2 * (W.a₁ * fwAt W u w + W.a₃ * fuAt W u w) := by
    rw [h.map_of_mul_eq_one hr, hDq]
  refine ⟨?_, ?_, ?_⟩
  unfold WEq
  linear_combination ((-1) * w * r + 1 * w * r^2) * hr + (1 * r^3) * hW
  show -D (u * r) = fwAt W (u * r) (w * r)
  rw [h.map_mul, hDr, hDu]
  simp only [fwAt, fuAt]
  linear_combination ((-1) * W.a₁ * u * r + (-1) * W.a₂ * u^2 * r + (-3) * W.a₃ * w * r + (-2) * W.a₄ * u * w * r + (-3) * W.a₆ * w^2 * r + 1 * 1) * hr + ((-3) * W.a₃ * r^2) * hW
  show -D (w * r) = fuAt W (u * r) (w * r)
  rw [h.map_mul, hDr, hDw]
  simp only [fwAt, fuAt]
  linear_combination (3 * u^2 * r + 2 * W.a₁ * w * r + 2 * W.a₂ * u * w * r + 1 * W.a₄ * w^2 * r) * hr + (3 * W.a₁ * r^2) * hW

theorem chordFormula : ChordRegular.{u} := by
  intro A _ W x y xP yP t h1 h2 ht
  rw [WeierstrassCurve.Affine.equation_iff] at h1 h2
  refine ⟨by
      simp [WeierstrassCurve.Affine.addX]
      linear_combination t ^ 2 * h1 + t ^ 2 * h2
        - (W.a₁ * (y - yP) * t - (W.a₂ + x + 2 * xP) * (1 + t * (x - xP))) * ht, ?_⟩
  simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY]
  linear_combination (y - yP) * ht

end Formalism.L2.Th1.A
end
section
namespace Formalism.L2.Th1.A
namespace CubicFlow

variable {A : Type u} [CommRing A]

def gE (W : WeierstrassCurve A) (z v : A) : A :=
  z ^ 3 + W.a₁ * z * v + W.a₂ * z ^ 2 * v + W.a₃ * v ^ 2 + W.a₄ * z * v ^ 2 + W.a₆ * v ^ 3 - v

def k3 (W : WeierstrassCurve A) (l : A) : A := 1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3
def k2 (W : WeierstrassCurve A) (l n : A) : A :=
  W.a₁ * l + W.a₂ * n + W.a₃ * l ^ 2 + 2 * W.a₄ * l * n + 3 * W.a₆ * l ^ 2 * n
def k1 (W : WeierstrassCurve A) (l n : A) : A :=
  W.a₁ * n + 2 * W.a₃ * l * n + W.a₄ * n ^ 2 + 3 * W.a₆ * l * n ^ 2 - l
def k0 (W : WeierstrassCurve A) (n : A) : A := W.a₃ * n ^ 2 + W.a₆ * n ^ 3 - n

lemma gE_line (W : WeierstrassCurve A) (l n z : A) :
    gE W z (l * z + n) = k3 W l * z ^ 3 + k2 W l n * z ^ 2 + k1 W l n * z + k0 W n := by
  unfold gE k3 k2 k1 k0
  ring

lemma gE_line_der (W : WeierstrassCurve A) (l n z : A) :
    fuAt W z (l * z + n) - l * fwAt W z (l * z + n)
      = 3 * k3 W l * z ^ 2 + 2 * k2 W l n * z + k1 W l n := by
  unfold fuAt fwAt k3 k2 k1
  ring

lemma wEq_iff (W : WeierstrassCurve A) (z v : A) : WEq W z v ↔ gE W z v = 0 := by
  unfold WEq gE
  constructor <;> intro h <;> linear_combination -h

lemma der_gE {D : A → A} (hD : IsDer D) {W : WeierstrassCurve A} (hC : ConstCurve D W) (z v : A) :
    D (gE W z v) = fuAt W z v * D z - fwAt W z v * D v := by
  obtain ⟨hadd, hmul⟩ := hD
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  have hsub : ∀ a b, D (a - b) = D a - D b := by
    intro a b
    have h := hadd (a - b) b
    rw [sub_add_cancel] at h
    rw [h]
    ring
  have hp2 : ∀ a, D (a ^ 2) = 2 * a * D a := fun a => by rw [sq, hmul]; ring
  have hp3 : ∀ a, D (a ^ 3) = 3 * a ^ 2 * D a := fun a => by
    rw [show a ^ 3 = a * a ^ 2 by ring, hmul, hp2]; ring
  unfold gE fuAt fwAt
  simp [hsub, hadd, hmul, hp2, hp3, c1, c2, c3, c4, c6]
  ring

lemma cubic_roots [IsDomain A] {C3 C2 C1 C0 z1 z2 z3 : A} (hz : z1 ≠ z2)
    (h1 : C3 * z1 ^ 3 + C2 * z1 ^ 2 + C1 * z1 + C0 = 0)
    (h2 : C3 * z2 ^ 3 + C2 * z2 ^ 2 + C1 * z2 + C0 = 0)
    (he1 : C3 * (z1 + z2 + z3) + C2 = 0) :
    C3 * z3 ^ 3 + C2 * z3 ^ 2 + C1 * z3 + C0 = 0 ∧
      C3 * (z1 * z2 + z1 * z3 + z2 * z3) - C1 = 0 ∧ C3 * (z1 * z2 * z3) + C0 = 0 := by
  have hq : (z1 - z2) * (C3 * (z1 ^ 2 + z1 * z2 + z2 ^ 2) + C2 * (z1 + z2) + C1) = 0 := by
    linear_combination h1 - h2
  have e2 : C3 * (z1 * z2 + z1 * z3 + z2 * z3) - C1 = 0 := by
    linear_combination -(mul_eq_zero.mp hq).resolve_left (sub_ne_zero.mpr hz) + (z1 + z2) * he1
  have e3 : C3 * (z1 * z2 * z3) + C0 = 0 := by
    linear_combination h1 - z1 ^ 2 * he1 + z1 * e2
  refine ⟨?_, e2, e3⟩
  linear_combination z3 ^ 2 * he1 - z3 * e2 + e3

end CubicFlow

open CubicFlow

theorem flowThirdPoint : FlowThird.{u} := by
  intro A _ _ W D u1 w1 u2 w2 l n u3 hD hC hF hW2 hDu2 hDw2 hl hn hsum hk3 h12 h31 h32
  obtain ⟨hW1, hDu1, hDw1⟩ := hF
  have hD' := hD
  obtain ⟨hadd, hmul⟩ := hD'
  have hw1 : w1 = l * u1 + n := by linear_combination -hn
  have hw2 : w2 = l * u2 + n := by linear_combination hl - hn
  have r2 : k3 W l * u2 ^ 3 + k2 W l n * u2 ^ 2 + k1 W l n * u2 + k0 W n = 0 := by
    rw [← gE_line, ← hw2]
    exact (wEq_iff W u2 w2).1 hW2
  have hs : k3 W l * (u1 + u2 + u3) + k2 W l n = 0 := hsum
  obtain ⟨r3, e2, -⟩ := cubic_roots h12 (by rw [← gE_line, ← hw1]; exact (wEq_iff W u1 w1).1 hW1) r2 hs
  have hD0 : D 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have hDline : ∀ z, D (l * z + n) = l * D z + z * D l + D n := by
    intro z
    rw [hadd, hmul]

  have T1 : u1 * D l + D n = 3 * k3 W l * u1 ^ 2 + 2 * k2 W l n * u1 + k1 W l n := by
    have h := hDline u1
    rw [← hw1, hDw1, hDu1] at h
    have hd := gE_line_der W l n u1
    rw [← hw1] at hd
    linear_combination hd - h
  have T2 : u2 * D l + D n = 0 := by
    have h := hDline u2
    rw [← hw2, hDw2, hDu2] at h
    linear_combination -h
  have hq : (u1 - u2) * (D l - k3 W l * (u1 - u3)) = 0 := by
    linear_combination T1 - T2 + 2 * u1 * hs - e2
  have hDl := sub_eq_zero.mp $ (mul_eq_zero.mp hq).resolve_left $ sub_ne_zero.mpr h12
  have hg3 : gE W u3 (l * u3 + n) = 0 := by rw [gE_line]
                                            exact r3
  have hd3 := der_gE hD hC u3 $ l * u3 + n
  rw [hg3, hD0, hDline] at hd3
  have hd3' := gE_line_der W l n u3
  have hK : k3 W l * (u3 - u1) * (u3 - u2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hk3 $ sub_ne_zero.mpr h31) $ sub_ne_zero.mpr h32
  have hkey : (k3 W l * (u3 - u1) * (u3 - u2)) * (D u3 + fwAt W u3 (l * u3 + n)) = 0 := by
    linear_combination -hd3 - D u3 * hd3' - D u3 * (2 * u3 * hs - e2)
      + fwAt W u3 (l * u3 + n) * (u3 - u2) * hDl + fwAt W u3 (l * u3 + n) * T2
  have hX : D u3 = -fwAt W u3 (l * u3 + n) := by
    have := (mul_eq_zero.mp hkey).resolve_left hK
    linear_combination this
  use (wEq_iff W u3 _).2 hg3, hX
  rw [hDline]
  linear_combination l * hX + hd3' + 2 * u3 * hs - e2 + (u3 - u2) * hDl + T2

end Formalism.L2.Th1.A
end
section
namespace Formalism.L2.Th1.A

variable {A : Type u} [CommRing A]

theorem IsDer.exists_derivation {D : A → A} (h : IsDer D) :
    ∃ d : Derivation ℤ A A, ∀ a, D a = d a := by
  refine ⟨Derivation.mk' (AddMonoidHom.mk' D h.1).toIntLinearMap fun a b => ?_, fun a => rfl⟩
  simp [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul]
  exact h.2 a b

theorem der_mul (d : Derivation ℤ A A) (a b : A) : d (a * b) = a * d b + b * d a := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem der_sq (d : Derivation ℤ A A) (a : A) : d (a ^ 2) = 2 * a * d a := by
  rw [pow_two, der_mul]
  ring



theorem der_inv (d : Derivation ℤ A A) {t s : A} (ht : t * s = 1) : d t = -t ^ 2 * d s := by
  have h0 : t * d s + s * d t = 0 := by rw [← der_mul, ht, Derivation.map_one_eq_zero]
  trans t * s * d t
  rw [ht, one_mul]
  linear_combination t * h0

theorem chord_rel {a₁ a₂ a₃ a₄ a₆ x y xP yP t L : A}
    (hE : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hEP : yP ^ 2 + a₁ * xP * yP + a₃ * yP = xP ^ 3 + a₂ * xP ^ 2 + a₄ * xP + a₆)
    (ht : t * (x - xP) = 1) (hL : L * (x - xP) = y - yP) :
    (a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
        - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)) = 0 ∧
      (a₆ - (y - L * x) ^ 2 - a₃ * (y - L * x))
        + x * xP * (L ^ 2 + a₁ * L - a₂ - x - xP) = 0 := by
  have hα : (a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
      - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)) = 0 := by
    linear_combination (-((a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
      - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)))) * ht - t * hE + t * hEP
      - t * (L * xP + (y - L * x) + yP + a₁ * xP + a₃) * hL
  use hα
  linear_combination (-1 : A) * hE - x * hα

theorem der_slope (W : WeierstrassCurve A) (d : Derivation ℤ A A) {x y xP yP t : A}
    (hE : W.toAffine.Equation x y) (hx : d x = 2 * y + W.a₁ * x + W.a₃)
    (hy : d y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hEP : W.toAffine.Equation xP yP) (hxP : d xP = 0) (hyP : d yP = 0)
    (ht : t * (x - xP) = 1) :
    d ((y - yP) * t) = x - W.toAffine.addX x xP ((y - yP) * t) := by
  have hL : ((y - yP) * t) * (x - xP) = y - yP := by linear_combination (y - yP) * ht
  obtain ⟨hα, -⟩ := chord_rel ((WeierstrassCurve.Affine.equation_iff x y).1 hE) ((WeierstrassCurve.Affine.equation_iff xP yP).1 hEP) ht hL
  have hdxs : d (x - xP) = d x := by rw [map_sub, hxP, sub_zero]
  rw [der_mul, map_sub, hyP, sub_zero, der_inv d ht, hdxs, hx, hy]
  simp [WeierstrassCurve.Affine.addX]
  linear_combination (x - (((y - yP) * t) ^ 2 + W.a₁ * ((y - yP) * t) - W.a₂ - x - xP)) * ht + t * hα

theorem flowTranslation : FlowTranslate.{u} := by
  intro A _ W D x y xP yP t hD hC hF hEP hxP hyP ht
  obtain ⟨d, hd⟩ := hD.exists_derivation
  obtain ⟨hE, hx, hy⟩ := hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  rw [hd] at hx hy hxP hyP c1 c2 c3 c4 c6
  have hDL := der_slope W d hE hx hy hEP hxP hyP ht
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).1 hE
  have hEP' := (WeierstrassCurve.Affine.equation_iff xP yP).1 hEP
  have hL : ((y - yP) * t) * (x - xP) = y - yP := by linear_combination (y - yP) * ht
  obtain ⟨hα, hβ⟩ := chord_rel hE' hEP' ht hL
  set L := (y - yP) * t with hLdef
  have hDL' := hDL
  refine ⟨?_, ?_, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX]
  linear_combination (-1 : A) * hβ - (L ^ 2 + W.a₁ * L - W.a₂ - x - xP) * hα
  rw [hd]
  simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX, map_sub, map_add, der_sq, der_mul, c1, c2, hx, hxP, hDL']
  ring
  rw [hd]
  simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX, map_neg, map_sub, map_add, der_sq, der_mul, c1, c2, c3, hx, hy, hxP, hDL']
  linear_combination (-2 : A) * hα

theorem flowLogDerivative : FlowLogDeriv.{u} := by
  intro A _ W D x y xP yP t hD hC hF hEP hxP hyP ht
  obtain ⟨d, hd⟩ := hD.exists_derivation
  obtain ⟨hE, hx, hy⟩ := hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  rw [hd] at hx hy hxP hyP c1 c2 c3 c4 c6
  have hQ := der_slope W d hE hx hy ((WeierstrassCurve.Affine.equation_neg xP yP).2 hEP) hxP (by
      simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, der_mul, hyP, hxP, c1, c3]
      ring) ht

  have hsplit : t * (2 * y + W.a₁ * x + W.a₃) =
      (y - yP) * t + (y - W.toAffine.negY xP yP) * t + W.a₁ * (t * (x - xP)) := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  simp only [hd]
  rw [hx, hsplit, map_add, map_add, der_slope W d hE hx hy hEP hxP hyP ht, hQ, ht, mul_one, c1]
  ring

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

namespace Univ

abbrev Z : Type := MvPolynomial (Fin 5) ℤ

def W₀ : WeierstrassCurve Z :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

def φ_of {R : Type u} [CommRing R] (W : WeierstrassCurve R) : Z →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

theorem map_eq {R : Type u} [CommRing R] (W : WeierstrassCurve R) : W₀.map (φ_of W) = W := by
  cases W
  simp [Univ.W₀, Univ.φ_of, WeierstrassCurve.map]

abbrev K₀ : Type := FractionRing Z

def ι : Z →+* K₀ := algebraMap Z K₀

theorem ι_injective : Function.Injective ι := IsFractionRing.injective Univ.Z Univ.K₀

instance charZero_K₀ : CharZero K₀ := charZero_of_injective_algebraMap $ IsFractionRing.injective Z K₀

def WK : WeierstrassCurve K₀ := W₀.map ι

theorem mv_map_injective {σ : Type*} {A : Type*} {B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) :
    Function.Injective (MvPowerSeries.map f : MvPowerSeries σ A →+* MvPowerSeries σ B) := by
  intro a b h
  ext e
  apply hf
  simpa using (congrArg (MvPowerSeries.coeff e) h)

theorem ps_map_injective {A : Type*} {B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective $ PowerSeries.map f := by
  intro a b h
  ext e
  apply hf
  simpa using (congrArg (PowerSeries.coeff e) h)


theorem ps_transfer {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {A B : Z⟦X⟧} (h : PowerSeries.map ι A = PowerSeries.map ι B) :
    PowerSeries.map (φ_of W) A = PowerSeries.map (φ_of W) B := by
  rw [ps_map_injective ι ι_injective h]

end Univ

namespace Fgl1

local notation "L" i => MvPowerSeries.coeff $ Finsupp.single i 1
local notation "cc" => MvPowerSeries.constantCoeff

section Tools

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem mv_map_invOfUnit {σ : Type*} (φ : R →+* S) (a : MvPowerSeries σ R) (e : Rˣ) (e' : Sˣ)
    (h : cc a = e) (h' : φ e = e') :
    MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e)
      = MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' := by
  have h3 : MvPowerSeries.map φ a * MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e) = 1 := by
    rw [← map_mul, MvPowerSeries.mul_invOfUnit a e h, map_one]
  calc MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e)
      = MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e) *
          (MvPowerSeries.map φ a * MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e') := by
        rw [MvPowerSeries.mul_invOfUnit _ _ $ by rw [MvPowerSeries.constantCoeff_map, h, h'], mul_one]
    _ = (MvPowerSeries.map φ a * MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e)) *
          MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' := by ring
    _ = MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' := by rw [h3, one_mul]

theorem L_mul (φ ψ : MvPowerSeries (Fin 2) R) (i : Fin 2) :
    (L i) (φ * ψ) = cc φ * (L i) ψ + (L i) φ * cc ψ := by
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ]
  try ring

theorem L_C (a : R) (i : Fin 2) : (L i) (MvPowerSeries.C a : MvPowerSeries (Fin 2) R) = 0 := by
  simp [MvPowerSeries.coeff_C]

theorem L_X (i j : Fin 2) :
    (L i) (MvPowerSeries.X j : MvPowerSeries (Fin 2) R) = if i = j then 1 else 0 := by
  simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero]

theorem sub_cancel {f : MvPowerSeries (Fin 2) R}
    (h : f * (MvPowerSeries.X 0 - MvPowerSeries.X 1) = 0) : f = 0 := by
  have key : ∀ e,
      (if Finsupp.single 0 1 ≤ e then MvPowerSeries.coeff (e - Finsupp.single 0 1) f else 0) =
      (if Finsupp.single 1 1 ≤ e then MvPowerSeries.coeff (e - Finsupp.single 1 1) f else 0) := by
    intro e
    have h1 := congrArg (MvPowerSeries.coeff e) h
    rw [mul_sub, map_sub, map_zero, sub_eq_zero,
      show (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 0 1) 1 from rfl,
      show (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 1 1) 1 from rfl,
      MvPowerSeries.coeff_mul_monomial, MvPowerSeries.coeff_mul_monomial] at h1
    simpa using h1
  let mk : ℕ → ℕ → (Fin 2 →₀ ℕ) := fun a b => Finsupp.single 0 a + Finsupp.single 1 b
  have hall : ∀ b a, MvPowerSeries.coeff (mk a b) f = 0 := by
    intro b
    induction b with
    | zero =>
      intro a
      have h := key $ mk (a + 1) 0
      have hp : Finsupp.single 0 1 ≤ mk (a + 1) 0 := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      have hn : ¬ Finsupp.single 1 1 ≤ mk (a + 1) 0 := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      rw [if_pos hp, if_neg hn] at h
      have e1 : mk (a + 1) 0 - Finsupp.single 0 1 = mk a 0 := by
        ext i
        fin_cases i <;> simp [mk]
      rwa [e1] at h
    | succ b ih =>
      intro a
      have h := key $ mk (a + 1) $ b + 1
      have hp : Finsupp.single 0 1 ≤ mk (a + 1) (b + 1) := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      have hq : Finsupp.single 1 1 ≤ mk (a + 1) (b + 1) := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      rw [if_pos hp, if_pos hq] at h
      have e1 : mk (a + 1) (b + 1) - Finsupp.single 0 1 = mk a (b + 1) := by
        ext i
        fin_cases i <;> simp [mk]
      have e2 : mk (a + 1) (b + 1) - Finsupp.single 1 1 = mk (a + 1) b := by
        ext i
        fin_cases i <;> simp [mk]
      rwa [e1, e2, ih $ a + 1] at h
  ext e
  have he : e = mk (e 0) (e 1) := by
    ext i
    fin_cases i <;> simp [mk]
  rw [he, hall]
  simp

open Formalism.ELL.WeierstrassChordSeries in

theorem vieta' {A : Type*} [CommRing A] {a1 a2 a3 a4 a6 l n z1 z2 z3 : A}
    (hz : ∀ f, f * (z1 - z2) = 0 → f = 0)
    (h1 : G a1 a2 a3 a4 a6 z1 (l * z1 + n) = 0) (h2 : G a1 a2 a3 a4 a6 z2 (l * z2 + n) = 0)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0) :
    G a1 a2 a3 a4 a6 z3 (l * z3 + n) = 0 := by
  have hQ : (c3 a2 a4 a6 l * (z1 ^ 2 + z1 * z2 + z2 ^ 2) + c2 a1 a2 a3 a4 a6 l n * (z1 + z2) +
      (a1 * n + 2 * a3 * l * n + a4 * n ^ 2 + 3 * a6 * l * n ^ 2 - l)) * (z1 - z2) = 0 := by
    unfold G at h1 h2
    unfold c3 c2
    linear_combination h1 - h2
  have hQ0 := hz _ hQ
  unfold G at h1 ⊢
  unfold c3 c2 at hQ0 he1
  linear_combination h1 + (z3 - z1) * hQ0 + (z3 - z1) * (z3 - z2) * he1

open Formalism.ELL.WeierstrassChordSeries in
theorem weq_iff (W : WeierstrassCurve R) (s v : MvPowerSeries (Fin 2) R) :
    Formalism.ELL.WEqAt W s v ↔ G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) s v = 0 := by
  unfold Formalism.ELL.WEqAt G
  simp [MvPowerSeries.smul_eq_C_mul]
  constructor
  intro h
  linear_combination (-1 : MvPowerSeries (Fin 2) R) * h
  intro h
  linear_combination (-1 : MvPowerSeries (Fin 2) R) * h

end Tools

section W

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

theorem wSer_fixed : Formalism.ELL.WFixed W $ wSer W := (Formalism.ELL.wSeriesUnique R W).choose_spec.1

theorem wSer_unique {w : R⟦X⟧} (hw : Formalism.ELL.WFixed W w) : w = wSer W := (Formalism.ELL.wSeriesUnique R W).choose_spec.2 w hw

theorem wSer_low : coeff 0 (wSer W) = 0 ∧ coeff 1 (wSer W) = 0 ∧ coeff 2 (wSer W) = 0 ∧
    coeff 3 (wSer W) = 1 := by
  obtain ⟨h0, hfix⟩ := wSer_fixed W
  have c0 : coeff 0 (wSer W) = 0 := by rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have c1 : coeff 1 (wSer W) = 0 := by
    have h := congrArg (coeff 1) hfix
    simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, c0, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X, mul_assoc] at h
    exact h
  have c2 : coeff 2 (wSer W) = 0 := by
    have h := congrArg (coeff 2) hfix
    simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, c0, c1, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X, mul_assoc] at h
    exact h
  exact ⟨c0, c1, c2, (by
      have h := congrArg (coeff 3) hfix
      simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, c0, c1, c2, PowerSeries.coeff_X_pow,
        PowerSeries.coeff_X, mul_assoc] at h
      exact h)⟩

theorem wSer_map (φ : R →+* S) : PowerSeries.map φ (wSer W) = wSer (W.map φ) := by
  refine wSer_unique (W.map φ) ⟨?_, ?_⟩
  have h0 := (wSer_fixed W).1
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  have h := congrArg (PowerSeries.map φ) (wSer_fixed W).2
  simpa [map_add, map_mul, map_pow] using h

end W

section Map

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)

theorem coeff_lam (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (lam W) = coeff (e 0 + e 1 + 1) (wSer W) := rfl

theorem lam_map : MvPowerSeries.map φ (lam W) = lam (W.map φ) := by
  ext e
  rw [MvPowerSeries.coeff_map, coeff_lam, coeff_lam, ← wSer_map, PowerSeries.coeff_map]

theorem nu_map : MvPowerSeries.map φ (nu W) = nu (W.map φ) := by
  simp [nu, map_sub, map_mul, MvPowerSeries.map_X, lam_map]
  rw [PowerSeries.map_subst $ PowerSeries.HasSubst.X 0, MvPowerSeries.map_X, wSer_map]

theorem cThree_map : MvPowerSeries.map φ (cThree W) = cThree (W.map φ) := by
  simp [cThree, map_add, map_mul, map_pow, lam_map]

theorem cTwo_map : MvPowerSeries.map φ (cTwo W) = cTwo (W.map φ) := by
  simp [cTwo, map_add, map_mul, map_pow, lam_map, nu_map, map_ofNat]

end Map

section Coeffs

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

abbrev Wi (i : Fin 2) : MvPowerSeries (Fin 2) R :=
  (wSer W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)

theorem coeff_Wi (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (Wi W i)
      = if e = Finsupp.single i (e i) then coeff (e i) $ wSer W else 0 := by
  classical
  rw [PowerSeries.coeff_subst $ PowerSeries.HasSubst.X i, finsum_eq_single _ $ e i]
  simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul]
  split_ifs <;> simp
  intro d hd
  simp only [MvPowerSeries.coeff_X_pow]
  rw [if_neg]
  simp
  intro h
  apply hd
  rw [h]
  simp

open Formalism.ELL.WeierstrassChordSeries (eq_single_iff) in
theorem lam_mul : (MvPowerSeries.X 1 - MvPowerSeries.X 0) * lam W = Wi W 1 - Wi W 0 := by
  ext e
  have he := eq_single_iff e
  rw [sub_mul, map_sub, map_sub,
    show (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 1 1) 1 from rfl,
    show (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 0 1) 1 from rfl,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, coeff_Wi, coeff_Wi, coeff_lam, coeff_lam]
  simp [he.1, he.2, Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_apply, one_mul]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0 <;> simp [h0, h1]
  rw [if_pos $ by omega, Nat.sub_add_cancel $ by omega]
  rw [if_pos $ by omega, Nat.sub_add_cancel $ by omega]
  rw [if_pos $ by omega, if_pos $ by omega, show e 0 + (e 1 - 1) + 1 = e 0 - 1 + e 1 + 1 by omega, sub_self]

theorem Wi_cc (i : Fin 2) : cc (Wi W i) = 0 := by
  have h0 : coeff 0 (wSer W) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (wSer_fixed W).1
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Wi]
  simp [h0]

theorem Wi_L (i j : Fin 2) : (L j) (Wi W i) = 0 := by
  rw [coeff_Wi]
  split_ifs
  simp [Finsupp.single_apply]
  split_ifs <;> simp [(wSer_low W).1, (wSer_low W).2.1]
  rfl

theorem lam_cc : cc (lam W) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lam]
  simpa using (wSer_low W).2.1

theorem lam_L (i : Fin 2) : (L i) (lam W) = 0 := by
  rw [coeff_lam]
  fin_cases i <;> simp [(wSer_low W).2.2.1]

theorem nu_cc : cc (nu W) = 0 := by
  have h := Wi_cc W 0
  simp [Wi] at h
  simp [nu, h, lam_cc]

theorem nu_L (i : Fin 2) : (L i) (nu W) = 0 := by
  have h := Wi_L W 0 i
  simp [Wi] at h
  rw [nu, map_sub, L_mul, lam_cc, lam_L, h]
  simp

theorem cThree_cc : cc (cThree W) = 1 := by
  simp [cThree, lam_cc]

theorem cTwo_cc : cc (cTwo W) = 0 := by
  simp [cTwo, lam_cc, nu_cc]

theorem cTwo_L (i : Fin 2) : (L i) (cTwo W) = 0 := by
  simp [cTwo, sq, L_mul, lam_cc, lam_L, nu_cc, nu_L]

theorem uThird_cc : cc (uThird W) = 0 := by
  simp [uThird, cTwo_cc]

theorem uThird_L (i : Fin 2) : (L i) (uThird W) = -1 := by
  simp [uThird, L_mul, L_X, cTwo_cc, cTwo_L]
  fin_cases i <;> simp

theorem wThird_cc : cc (wThird W) = 0 := by
  simp [wThird, lam_cc, nu_cc, uThird_cc]

abbrev dd : MvPowerSeries (Fin 2) R :=
  -1 + MvPowerSeries.C W.a₁ * uThird W + MvPowerSeries.C W.a₃ * wThird W

theorem dd_cc : cc (dd W) = -1 := by
  simp [dd, uThird_cc, wThird_cc]

theorem fgl_cc : cc (fgl W) = 0 := by
  simp [fgl, uThird_cc]

theorem fgl_L (i : Fin 2) : (L i) (fgl W) = 1 := by
  rw [fgl, L_mul, uThird_cc, uThird_L, MvPowerSeries.constantCoeff_invOfUnit]
  simp

end Coeffs

section Map2

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)

theorem uThird_map : MvPowerSeries.map φ (uThird W) = uThird (W.map φ) := by
  simp [uThird, map_sub, map_neg, map_mul, MvPowerSeries.map_X, cTwo_map]
  rw [mv_map_invOfUnit φ (cThree W) 1 1 (by simp [cThree_cc]) $ by simp, cThree_map]

theorem wThird_map : MvPowerSeries.map φ (wThird W) = wThird (W.map φ) := by
  simp [wThird, map_add, map_mul, lam_map, uThird_map, nu_map]

theorem fgl_map : MvPowerSeries.map φ (fgl W) = fgl (W.map φ) := by
  simp only [fgl]
  rw [map_mul, mv_map_invOfUnit φ _ (-1) (-1) (by simpa using dd_cc W) $ by simp]
  simp [map_add, map_mul, uThird_map, wThird_map]


theorem fgl_univ : fgl W = MvPowerSeries.map (Univ.φ_of W) (fgl Univ.W₀) := by
  rw [fgl_map, Univ.map_eq]


end Map2

section Third

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open Formalism.ELL.WeierstrassChordSeries (G c3 c2) in
theorem wThird_eq : wThird W = (wSer W).subst (uThird W) := by
  have hUs := fun s hs =>
    Formalism.ELL.wSubstUnique R W (wSer W) (wSer_fixed W) (Fin 2) s hs
  have h0 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 0) $ by simp).1
  have h1 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 1) $ by simp).1
  have hW0 : Wi W 0 = lam W * MvPowerSeries.X 0 + nu W := by unfold nu
                                                             ring
  have hW1 : Wi W 1 = lam W * MvPowerSeries.X 1 + nu W := by
    have := lam_mul W
    unfold nu; linear_combination -this
  change G _ _ _ _ _ _ (Wi W 0) = 0 at h0
  change G _ _ _ _ _ _ (Wi W 1) = 0 at h1
  have hinv : cThree W * MvPowerSeries.invOfUnit (cThree W) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by rw [cThree_cc]; rfl)
  have he1 : c3 (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) (lam W) *
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + uThird W) +
      c2 (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
        (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) (lam W) (nu W) = 0 := by
    change cThree W * _ + cTwo W = 0
    rw [uThird]
    linear_combination (-cTwo W) * hinv
  rw [hW0] at h0
  rw [hW1] at h1
  exact (hUs (uThird W) $ uThird_cc W).2 (wThird W) (wThird_cc W) $ (weq_iff W _ _).mpr $ vieta' (fun f hf => sub_cancel hf) h0 h1 he1

theorem fgl_eq : fgl W = (iSer W).subst (uThird W) := by
  have ha := HasSubst.of_constantCoeff_zero $ uThird_cc W
  have e := congrArg (PowerSeries.subst (uThird W)) $ PowerSeries.mul_invOfUnit (iDen W) (-1) $ by simp [iDen, (wSer_fixed W).1]
  have hs : (iDen W).subst (uThird W) = dd W := by
    unfold iDen
    rw [← PowerSeries.coe_substAlgHom ha]
    simp [map_add, map_neg, map_one, map_mul]
    rw [PowerSeries.coe_substAlgHom ha, PowerSeries.subst_C, PowerSeries.subst_C,
      PowerSeries.subst_X ha, ← wThird_eq]
  have h1 : (1 : PowerSeries R).subst (uThird W) = 1 := by
    rw [← PowerSeries.coe_substAlgHom ha, map_one]
  rw [PowerSeries.subst_mul ha, hs, h1] at e
  have e2 : dd W * MvPowerSeries.invOfUnit (dd W) (-1) = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by rw [dd_cc]; simp)
  have hinv :=
    left_inv_eq_right_inv (by rw [mul_comm]; exact e) e2
  rw [iSer, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, hinv, fgl]

end Third

section Field

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

open Formalism.ELL.WeierstrassChordSeries (z3 w3 F2) in
theorem formal_group_eq_w_series : fgl W = F2 W (wSer W) := by
  have h3 : uThird W = z3 W (wSer W) := by
    unfold uThird z3
    rw [MvPowerSeries.invOfUnit_eq' _ _ (by rw [cThree_cc]; rfl)]
    rfl
  have h4 : wThird W = w3 W (wSer W) := by
    unfold wThird w3
    rw [h3]
    rfl
  unfold fgl F2
  rw [MvPowerSeries.invOfUnit_eq' _ _ (by rw [dd_cc]; simp), h3, h4]
  rfl

end Field

end Fgl1

theorem formal_group_map : FglMap.{u, v} := fun _ _ _ _ φ W => Fgl1.fgl_map W φ

theorem formal_group_chord : FglChord.{u} := by
  intro R _ W
  refine ⟨?_, Fgl1.uThird_cc W, Fgl1.wThird_eq W, Fgl1.fgl_eq W, Fgl1.fgl_cc W, Fgl1.fgl_L W 0, Fgl1.fgl_L W 1⟩
  rw [mul_comm]
  exact Fgl1.lam_mul W

theorem formal_group_sum : FglSum.{u} := by
  intro K _ W
  rw [Fgl1.formal_group_eq_w_series]
  exact Formalism.ELL.WeierstrassChordSeries.chord Formalism.ELL.wSubstUnique $ Fgl1.wSer_fixed W

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

variable {R : Type u} [CommRing R]

theorem dL_coeff (f : LaurentSeries R) (n : ℤ) :
    (dL f).coeff n = ((n + 1 : ℤ) : R) * f.coeff (n + 1) := by
  show (LaurentSeries.hasseDeriv R 1 f).coeff n = _
  rw [LaurentSeries.hasseDeriv_coeff]
  simp [zsmul_eq_mul]

theorem uPow_mul_coeff (m n : ℤ) (f : LaurentSeries R) :
    (uPow m * f).coeff n = f.coeff (n - m) := by
  first
    | (have h := HahnSeries.coeff_single_mul_add (r := (1 : R)) (x := f) (a := n - m) (b := m)
       rw [sub_add_cancel, one_mul] at h
       exact h)
    | (have h := HahnSeries.single_mul_coeff_add (r := (1 : R)) (x := f) (a := n - m) (b := m)
       rw [sub_add_cancel, one_mul] at h
       exact h)

theorem C_mul_coeff (r : R) (f : LaurentSeries R) (n : ℤ) :
    (HahnSeries.C r * f).coeff n = r * f.coeff n := by
  rw [HahnSeries.C_mul_eq_smul]
  first | rw [HahnSeries.coeff_smul, smul_eq_mul] | rw [HahnSeries.smul_coeff, smul_eq_mul] | simp

theorem toL_coeff_nat (f : R⟦X⟧) (n : ℕ) : (toL f).coeff (n : ℤ) = coeff n f := by
  exact HahnSeries.ofPowerSeries_apply_coeff f n

theorem toL_coeff_neg (f : R⟦X⟧) {n : ℤ} (hn : n < 0) : (toL f).coeff n = 0 := by
  first
    | (rw [PowerSeries.coeff_coe, if_pos hn])
    | (simp [toL, HahnSeries.ofPowerSeries_apply]
       rw [HahnSeries.embDomain_notin_range]
       rintro ⟨k, hk⟩
       simp at hk
       omega)

theorem uPow_zero : (uPow 0 : LaurentSeries R) = 1 := rfl

theorem uPow_one : (uPow 1 : LaurentSeries R) = toL X := by
  show HahnSeries.single (1 : ℤ) (1 : R) = _
  rw [HahnSeries.ofPowerSeries_X]

theorem uPow_add (m n : ℤ) : (uPow (m + n) : LaurentSeries R) = uPow m * uPow n := by
  show HahnSeries.single (m + n) (1 : R) = HahnSeries.single m 1 * HahnSeries.single n 1
  rw [HahnSeries.single_mul_single, mul_one]

theorem uPow_neg_mul (n : ℤ) : (uPow (-n) : LaurentSeries R) * uPow n = 1 := by
  rw [← uPow_add]
  first | rw [neg_add_cancel] | rw [neg_add_self] | rw [add_left_neg]
  exact uPow_zero



theorem uPow_natCast (n : ℕ) : (uPow (n : ℤ) : LaurentSeries R) = toL (X ^ n) := by
  induction n with
  | zero => simp [uPow_zero]
  | succ k ih => rw [Nat.cast_succ, uPow_add, ih, uPow_one, ← map_mul, pow_succ]

theorem toL_C (r : R) : toL (C r) = (HahnSeries.C r : LaurentSeries R) := by
  first
    | exact HahnSeries.ofPowerSeries_C r
    | simp [toL]

theorem toL_injective : Function.Injective (toL : R⟦X⟧ → LaurentSeries R) := by
  exact HahnSeries.ofPowerSeries_injective

theorem exists_uPow_mul_toL (f : LaurentSeries R) :
    ∃ m F, f = uPow m * toL F := by
  use f.order, f.powerSeriesPart
  first
    | exact (LaurentSeries.single_order_mul_powerSeriesPart f).symm
    | (show f = uPow f.order * HahnSeries.ofPowerSeries ℤ R f.powerSeriesPart
       rw [LaurentSeries.ofPowerSeries_powerSeriesPart]
       change f = uPow f.order * (uPow (-f.order) * f)
       rw [← mul_assoc, uPow_mul_neg, one_mul])

theorem dL_uPow_mul (m : ℤ) (f : LaurentSeries R) :
    dL (uPow m * f) = uPow m * dL f + HahnSeries.C ((m : ℤ) : R) * uPow (m - 1) * f := by
  rw [show HahnSeries.C ((m : ℤ) : R) * uPow (m - 1) * f
      = HahnSeries.C ((m : ℤ) : R) * (uPow (m - 1) * f) from mul_assoc _ _ _]
  ext n
  first | rw [HahnSeries.add_coeff] | rw [HahnSeries.coeff_add] | rw [HahnSeries.add_coeff']
  rw [dL_coeff, uPow_mul_coeff, uPow_mul_coeff, dL_coeff, C_mul_coeff, uPow_mul_coeff]
  have h1 : n + 1 - m = n - m + 1 := by ring
  have h2 : n - (m - 1) = n - m + 1 := by ring
  rw [h1, h2]
  push_cast
  ring

theorem dL_toL (f : R⟦X⟧) : dL (toL f) = toL (derivative f) := by
  ext n
  rw [dL_coeff]
  rcases lt_or_ge n 0 with hn | hn
  rw [toL_coeff_neg _ hn]
  rcases lt_or_eq_of_le (show n + 1 ≤ 0 by omega) with h | h
  rw [toL_coeff_neg _ h, mul_zero]
  rw [h]
  simp
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hk : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast
                                                    ring
  rw [hk, toL_coeff_nat, toL_coeff_nat, PowerSeries.coeff_derivative]
  push_cast
  ring

theorem dL_mul (f g : LaurentSeries R) : dL (f * g) = f * dL g + g * dL f := by
  obtain ⟨m, F, rfl⟩ := exists_uPow_mul_toL f
  obtain ⟨k, G, rfl⟩ := exists_uPow_mul_toL g
  have e : uPow m * toL F * (uPow k * toL G) = uPow (m + k) * toL (F * G) := by
    rw [uPow_add, map_mul]
    ring
  have h0 : (uPow (m + k) : LaurentSeries R) = uPow m * uPow k := uPow_add m k
  have h1 : (uPow (m + k - 1) : LaurentSeries R) = uPow (m - 1) * uPow k := by
    rw [← uPow_add]
    congr 1; ring
  have h2 : (uPow (m + k - 1) : LaurentSeries R) = uPow m * uPow (k - 1) := by
    rw [← uPow_add]
    congr 1; ring
  have h3 : (HahnSeries.C (((m + k : ℤ)) : R) : LaurentSeries R)
      = HahnSeries.C ((m : ℤ) : R) + HahnSeries.C ((k : ℤ) : R) := by
    rw [Int.cast_add, map_add]
  rw [e, dL_uPow_mul, dL_toL, Derivation.leibniz]
  simp only [dL_uPow_mul, dL_toL, smul_eq_mul, map_add, map_mul]
  linear_combination (toL F * toL (derivative G) + toL G * toL (derivative F)) * h0
    + (toL F * toL G * uPow (m + k - 1)) * h3
    + (HahnSeries.C ((m : ℤ) : R) * toL F * toL G) * h1
    + (HahnSeries.C ((k : ℤ) : R) * toL F * toL G) * h2

theorem dL_uPow (n : ℤ) :
    dL (uPow n : LaurentSeries R) = HahnSeries.C ((n : ℤ) : R) * uPow (n - 1) := by
  have h1 : dL (1 : LaurentSeries R) = 0 := by
    have h := dL_toL (R := R) 1
    rwa [map_one, Derivation.map_one_eq_zero, map_zero] at h
  have h := dL_uPow_mul n (1 : LaurentSeries R)
  rwa [mul_one, mul_one, h1, mul_zero, zero_add] at h

theorem dL_C (r : R) : dL (HahnSeries.C r : LaurentSeries R) = 0 := by
  rw [← toL_C, dL_toL]
  first | rw [PowerSeries.derivative_C, map_zero] | simp













theorem isDer_dL : (∀ a b : LaurentSeries R, dL (a + b) = dL a + dL b) ∧
    (∀ a b : LaurentSeries R, dL (a * b) = a * dL b + b * dL a) := by
  constructor
  exact fun a b => map_add dL a b
  exact dL_mul
end Formalism.L2.Th1.A
end
section
open PowerSeries (coe_substAlgHom derivative_X subst_X)
open WeierstrassCurve (map_a₁ map_a₂ map_a₃ map_a₄ map_a₆)
open PowerSeries



namespace Formalism.L2.Th1.A

namespace Wp

variable {K : Type u} [Field K]

def sig {e : K⟦X⟧} (he : HasSubst e) : K⟦X⟧ →+* LaurentSeries K :=
  toL.comp (substAlgHom he : K⟦X⟧ →ₐ[K] K⟦X⟧).toRingHom

theorem sig_apply {e : K⟦X⟧} (he : HasSubst e) (f : K⟦X⟧) : sig he f = toL (f.subst e) := by
  simp [sig, coe_substAlgHom]

theorem sig_X {e : K⟦X⟧} (he : HasSubst e) : sig he X = toL e := by
  rw [sig_apply, subst_X he]

theorem sig_C {e : K⟦X⟧} (he : HasSubst e) (r : K) : sig he (C r) = HahnSeries.C r := by
  have h : (C r : K⟦X⟧).subst e = C r := by
    rw [← coe_substAlgHom he]
    exact (PowerSeries.substAlgHom he).commutes r
  rw [sig_apply, h, HahnSeries.ofPowerSeries_C]

theorem isDer_dL' : IsDer (dL : LaurentSeries K → LaurentSeries K) := isDer_dL

theorem constCurve_dL (W : WeierstrassCurve K) : ConstCurve dL $ curveL W := by
  have h : ∀ c, dL (HahnSeries.C c : LaurentSeries K) = 0 := by
    intro c
    ext n
    simp [dL, HahnSeries.C_apply]
  exact ⟨h _, h _, h _, h _, h _⟩

variable (W : WeierstrassCurve K) {e : K⟦X⟧} (he : HasSubst e)

theorem fwAt_sig : fwAt (curveL W) (sig he X) (sig he $ wSer W) = sig he (fw W) := by
  simp [fwAt, fw, map_sub, map_mul, map_pow, map_one, map_ofNat, sig_C,
    map_a₁, map_a₂, map_a₃,
    map_a₄, map_a₆]

theorem fuAt_sig : fuAt (curveL W) (sig he X) (sig he $ wSer W) = sig he (fu W) := by
  simp [fuAt, fu, map_add, map_mul, map_pow, map_ofNat, sig_C,
    map_a₁, map_a₂, map_a₄]

theorem wEq_sig : WEq (curveL W) (sig he X) $ sig he $ wSer W := by
  have h := congrArg (sig he) $ (Formalism.ELL.wSeriesUnique K W).choose_spec.1.2
  simp [map_add, map_mul, map_pow, sig_C] at h
  simp [WEq, map_a₁, map_a₂, map_a₃,
    map_a₄, map_a₆]
  exact h

theorem isFlowUW_sig (hc : ∀ f, derivative (f.subst e) = (D W f).subst e) :
    IsFlowUW (curveL W) dL (sig he X) $ sig he $ wSer W := by
  have hw : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
      + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 :=
    (Formalism.ELL.wSeriesUnique K W).choose_spec.1.2
  have hd := congrArg (derivative (R := K)) hw
  simp [map_add, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_C,
    derivative_X, smul_eq_mul, nsmul_eq_mul] at hd
  have hDw : D W (wSer W) = fu W := by
    rw [D, Derivation.smul_apply, smul_eq_mul, fw, fu]
    linear_combination hd
  have hDX : D W X = fw W := by
    rw [D, Derivation.smul_apply, smul_eq_mul, derivative_X, mul_one]
  refine ⟨wEq_sig W he, ?_, ?_⟩
  have h2 : dL (sig he X) = sig he (fw W) := by
    have h1 := hc X
    rw [subst_X he, hDX] at h1
    rw [sig_X, sig_apply, dL_toL, h1]
  rw [h2, fwAt_sig]
  have h2 : dL (sig he $ wSer W) = sig he (fu W) := by
    rw [sig_apply, sig_apply, dL_toL, hc $ wSer W, hDw]
  rw [h2, fuAt_sig]

theorem inv_mul_sig (hne : toL e ≠ 0) :
    (toL e)⁻¹ ^ 3 * sig he (xS W) * sig he (wSer W) = 1 := by
  have h1 : sig he (wU W) * sig he (xS W) = 1 := by rw [← map_mul, CurveSer.wU_mul_xS, map_one]
  rw [CurveSer.wSer_eq, map_mul, map_pow, sig_X]
  calc (toL e)⁻¹ ^ 3 * sig he (xS W) * (toL e ^ 3 * sig he (wU W))
      = ((toL e)⁻¹ * toL e) ^ 3 * (sig he (wU W) * sig he (xS W)) := by ring
    _ = 1 := by rw [h1, inv_mul_cancel₀ hne, one_pow, one_mul]

include he in
theorem isFlow_sig (hc : ∀ f, derivative (f.subst e) = (D W f).subst e)
    (hne : toL e ≠ 0) :
    IsFlow (curveL W) dL ((toL e)⁻¹ ^ 2 * toL ((xS W).subst e))
      $ (toL e)⁻¹ ^ 3 * toL ((yS W).subst e) := by
  have h := chartFlowToFlow _ (curveL W) dL (sig he X) (sig he $ wSer W)
    ((toL e)⁻¹ ^ 3 * sig he (xS W)) isDer_dL' (isFlowUW_sig W he hc) $ inv_mul_sig W he hne
  have h2 := inv_mul_cancel₀ hne
  have hx : sig he X * ((toL e)⁻¹ ^ 3 * sig he (xS W)) = (toL e)⁻¹ ^ 2 * toL ((xS W).subst e) := by
    rw [sig_X, sig_apply]
    linear_combination (toL e)⁻¹ ^ 2 * toL ((xS W).subst e) * h2
  have hy : -((toL e)⁻¹ ^ 3 * sig he (xS W)) = (toL e)⁻¹ ^ 3 * toL ((yS W).subst e) := by
    rw [← sig_apply he $ yS W, yS, map_neg, mul_neg]
  rwa [hx, hy] at h

include he in
theorem mul_yZ_sig (hne : toL e ≠ 0) :
    toL e * ((toL e)⁻¹ ^ 3 * toL ((yS W).subst e)) = -((toL e)⁻¹ ^ 2 * toL ((xS W).subst e)) := by
  have hy : (yS W).subst e = -((xS W).subst e) := by
    rw [yS, ← coe_substAlgHom he, map_neg]
  rw [hy, map_neg]
  have ht := mul_inv_cancel₀ hne
  calc toL e * ((toL e)⁻¹ ^ 3 * -toL ((xS W).subst e))
      = -((toL e * (toL e)⁻¹) * ((toL e)⁻¹ ^ 2 * toL ((xS W).subst e))) := by ring
    _ = -((toL e)⁻¹ ^ 2 * toL ((xS W).subst e)) := by rw [ht, one_mul]

end Wp

open Wp

theorem flowZ_of (hE : ExpSpec.{u}) (hC : ChainZ.{u}) : FlowZ.{u} := by
  intro K _ _ W
  obtain ⟨h0, h1, -, -, -⟩ := hE K W
  have he := HasSubst.of_constantCoeff_zero' h0
  have hne : toL (expSer W) ≠ 0 := by
    intro h
    have h' : expSer W = 0 := HahnSeries.ofPowerSeries_injective $ by rw [h, map_zero]
    rw [h', map_zero] at h1
    exact zero_ne_one h1
  constructor
  exact Wp.isFlow_sig W he (hC K W) hne
  exact Wp.mul_yZ_sig W he hne
theorem wpODE_of (hE : ExpSpec.{u}) (hC : ChainZ.{u}) : WpODE.{u} := by
  intro K _ _ W
  have hg3 : 216 * (HahnSeries.C (g₃ W) : LaurentSeries K) = (curveL W).c₆ := by
    rw [WeierstrassCurve.map_c₆, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 216, ← map_mul]
    congr 1
    rw [g₃]
    field_simp
  obtain ⟨h1, h2, h3⟩ := flowWeierstrassForm _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C $ W.b₂ / 12)
    (HahnSeries.C $ g₂ W) (HahnSeries.C $ g₃ W) isDer_dL' (constCurve_dL W) ((flowZ_of hE hC K W).1) (by
        have h := (IsUnit.mk0 (6 : K) $ by norm_num).map (HahnSeries.C : K →+* LaurentSeries K)
        rwa [map_ofNat] at h) (by
        rw [WeierstrassCurve.map_b₂, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
        congr 1
        field_simp) (by
            rw [WeierstrassCurve.map_c₄, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
            congr 1
            rw [g₂]
            field_simp) hg3
  refine ⟨?_, h2, ?_⟩
  simpa only [wpL, map_a₁, map_a₃] using h1
  have hh : (HahnSeries.C (1 / 2 : K) : LaurentSeries K) * 2 = 1 := by
    rw [← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 2, ← map_mul, ← map_one HahnSeries.C]
    congr 1
    norm_num
  have hg : (HahnSeries.C (g₂ W / 2) : LaurentSeries K)
      = HahnSeries.C (1 / 2 : K) * HahnSeries.C (g₂ W) := by
    rw [← map_mul]
    congr 1
    ring
  rw [hg]
  change 2 * dL (dL $ wpL W) = 12 * wpL W ^ 2 - HahnSeries.C (g₂ W) at h3
  linear_combination HahnSeries.C (1 / 2 : K) * h3 - (dL (dL $ wpL W) - 6 * wpL W ^ 2) * hh

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

namespace CurveL

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem DL_apply (f : LaurentSeries R) : DL W f = toL (fw W) * dL f := rfl

theorem isDer_DL : IsDer $ DL W := by
  unfold IsDer
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  simp [DL, map_add, mul_add]
  simp [DL, dL_mul]
  ring

theorem DL_C (r : R) : DL W (HahnSeries.C r) = 0 := by
  simp only [DL, dL_C, mul_zero]

theorem constCurve_DL : ConstCurve (DL W) $ curveL W := ⟨DL_C W _, DL_C W _, DL_C W _, DL_C W _, DL_C W _⟩

theorem DL_toL (f : R⟦X⟧) : DL W (toL f) = toL (D W f) := by
  rw [DL_apply, dL_toL, CurveSer.D_apply, map_mul]

theorem fwAt_toL : fwAt (curveL W) (toL X) (toL $ wSer W) = toL (fw W) := by
  have h2 : toL (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : toL (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fwAt fw
  simp [h2, h3]

theorem fuAt_toL : fuAt (curveL W) (toL X) (toL $ wSer W) = toL (fu W) := by
  have h2 : toL (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : toL (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fuAt fu
  simp [h2, h3]

theorem isFlowUW_toL : IsFlowUW (curveL W) (DL W) (toL X) $ toL $ wSer W := by
  unfold IsFlowUW
  refine ⟨?_, ?_, ?_⟩
  unfold WEq
  conv_lhs => rw [(CurveSer.wSer_fixed W).2]
  simp
  rw [DL_toL, CurveSer.D_apply, derivative_X, mul_one, fwAt_toL]
  rw [DL_toL, CurveSer.D_apply, mul_comm $ fw W, CurveSer.deriv_wSer_mul_fw, fuAt_toL]

theorem inv_mul_wSer : uPow (-3) * toL (xS W) * toL (wSer W) = 1 := by
  have e0 : toL (X ^ 3 : R⟦X⟧) = uPow 3 := by
    unfold uPow
    rw [HahnSeries.ofPowerSeries_X_pow]
    norm_num
  have e1 : uPow (-3) * toL (X ^ 3 : R⟦X⟧) = 1 := by
    rw [e0, ← uPow_add, show (-3 + 3 : ℤ) = 0 by norm_num]
    first
      | rfl
      | simp
  have e2 : toL (wU W) * toL (xS W) = 1 := by
    rw [← map_mul, CurveSer.wU_mul_xS, map_one]
  rw [CurveSer.wSer_eq W, map_mul]
  linear_combination (toL (wU W) * toL (xS W)) * e1 + e2

theorem toL_X_mul_inv : toL X * (uPow (-3) * toL (xS W)) = xL W := by
  have e : toL (X : R⟦X⟧) * uPow (-3) = uPow (-2) := by
    have e0 : toL (X : R⟦X⟧) = uPow 1 := by
      unfold uPow
      exact HahnSeries.ofPowerSeries_X
    rw [e0, ← uPow_add]
    norm_num
  unfold xL
  rw [← mul_assoc, e]

theorem neg_inv : -(uPow (-3) * toL (xS W)) = yL W := by
  unfold yL yS
  rw [map_neg, mul_neg]

theorem isFlow_xL_yL : IsFlow (curveL W) (DL W) (xL W) $ yL W := by
  obtain ⟨hW, hDu, hDw⟩ := isFlowUW_toL W
  have hvw := inv_mul_wSer W
  have hD := isDer_DL W
  have h1 : DL W 1 = 0 := by simpa using DL_C W 1
  have hv := hD.2 (uPow (-3) * toL (xS W)) $ toL $ wSer W
  rw [hvw, h1, hDw] at hv
  unfold fuAt at hv
  have hneg : ∀ f, DL W (-f) = -DL W f := fun f => by simp [DL, map_neg, mul_neg]
  unfold IsFlow
  rw [← toL_X_mul_inv W, ← neg_inv W, hD.2, hDu, hneg]
  unfold fwAt
  unfold WEq at hW
  rw [WeierstrassCurve.Affine.equation_iff]
  set w := toL (wSer W) with hw
  set v := uPow (-3) * toL (xS W) with hv'
  set u := toL (X : R⟦X⟧) with hu
  set Dv := DL W v with hDv
  refine ⟨?_, ?_, ?_⟩
  linear_combination v ^ 3 * hW + (-v ^ 2 + (curveL W).a₁ * u * v ^ 2
    + (curveL W).a₂ * u ^ 2 * v ^ 2 + (curveL W).a₃ * v * (w * v + 1)
    + (curveL W).a₄ * u * v * (w * v + 1) + (curveL W).a₆ * (w ^ 2 * v ^ 2 + w * v + 1)) * hvw
  linear_combination 3 * v ^ 2 * hW + (-3 * v + 2 * (curveL W).a₁ * u * v
    + (curveL W).a₂ * u ^ 2 * v + (curveL W).a₃ * (3 * v * w + 1)
    + 2 * (curveL W).a₄ * u * v * w + 3 * (curveL W).a₆ * w * v * w - u * Dv) * hvw
    - u * v * hv
  linear_combination ((curveL W).a₁ * v + 2 * (curveL W).a₂ * u * v
    + (curveL W).a₄ * (v * w + 1) + Dv) * hvw + v * hv

theorem toL_X_mul_yL : toL X * yL W = -xL W := by
  rw [← neg_inv W, ← toL_X_mul_inv W]
  ring

theorem toL_wSer_mul_yL : toL (wSer W) * yL W = -1 := by
  rw [← neg_inv W]
  linear_combination -(inv_mul_wSer W)

theorem toL_wSer_mul_xL : toL (wSer W) * xL W = toL X := by
  rw [← toL_X_mul_inv W]
  linear_combination toL (X : R⟦X⟧) * inv_mul_wSer W

end CurveL

open CurveL

theorem invariant_derivation_spec : DLSpec.{u} := by
  unfold DLSpec
  intro R _ W
  exact ⟨isDer_DL W, constCurve_DL W, DL_C W, DL_toL W⟩

theorem invariant_flow : FlowL.{u} := by
  unfold FlowL
  intro R _ W
  exact ⟨isFlow_xL_yL W, toL_X_mul_yL W, toL_wSer_mul_yL W, toL_wSer_mul_xL W⟩


end Formalism.L2.Th1.A
end
section
open PowerSeries (coe_substAlgHom subst subst_X subst_comp_subst_apply)
open PowerSeries



namespace Formalism.L2.Th1.A

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R]

theorem subst_neg' {a : R⟦X⟧} (ha : HasSubst a) (f : R⟦X⟧) : (-f).subst a = -f.subst a := by
  first
    | (rw [← coe_substAlgHom ha]; exact map_neg _ f)
    | simp [PowerSeries.subst_neg ha]

theorem subst_one' {a : R⟦X⟧} (ha : HasSubst a) : (1 : R⟦X⟧).subst a = 1 := by
  first
    | (rw [← coe_substAlgHom ha]; exact map_one _)
    | simp

private theorem hasSubst_lemma {a : R⟦X⟧} (h : constantCoeff a = 0) : HasSubst a := by
  first
  | exact HasSubst.of_constantCoeff_zero' h
  | exact HasSubst.of_constantCoeff_zero h
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' h

private theorem powerSeries_subst_mul_of_hasSubst {a : R⟦X⟧} (ha : HasSubst a) (f g : R⟦X⟧) :
    (f * g).subst a = f.subst a * g.subst a := by
  first
  | exact PowerSeries.subst_mul ha f g
  | (rw [← coe_substAlgHom ha]; exact map_mul _ f g)

private theorem constantCoeff_powerSeries_subst_eq_zero {a f : R⟦X⟧} (ha0 : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    constantCoeff (f.subst a) = 0 := by
  obtain ⟨h, rfl⟩ := (PowerSeries.X_dvd_iff).mpr hf
  rw [powerSeries_subst_mul_of_hasSubst $ hasSubst_lemma ha0, subst_X $ hasSubst_lemma ha0, map_mul, ha0, zero_mul]

private theorem powerSeries_subst_subst_eq_subst_subst {a b f : R⟦X⟧} (ha : HasSubst a) (hb : HasSubst b) :
    subst b (subst a f : R⟦X⟧)
      = subst (subst b a : R⟦X⟧) f := by
  first
  | exact subst_comp_subst_apply ha hb f
  | exact (subst_comp_subst_apply ha hb f).symm
  | rw [subst_comp_subst_apply ha hb]

theorem subst_injective_of_leftInverse {l e a b : R⟦X⟧} (hl : HasSubst l) (ha : HasSubst a)
    (hb : HasSubst b) (hel : e.subst l = X) (h : l.subst a = l.subst b) : a = b := by
  calc a = e.subst (l.subst a) := by
        rw [← powerSeries_subst_subst_eq_subst_subst hl ha, hel, subst_X ha]
    _ = e.subst (l.subst b) := by rw [h]
    _ = b := by rw [← powerSeries_subst_subst_eq_subst_subst hl hb, hel, subst_X hb]

end SlopeTestRemainingChoices

theorem logSpec_of (hI : IntegSpec.{u}) (hU : UnitSpec.{u}) : LogSpec.{u} := by
  intro K _ _ W
  obtain ⟨hc, hd, -⟩ := hI K $ om W
  obtain ⟨-, hfo, ho0, -⟩ := hU K W
  refine ⟨hc, ?_, hd, ?_⟩
  simp [logSer, integ, coeff_mk]
  simp [ho0]
  simp [D, logSer, Derivation.smul_apply, smul_eq_mul, hd, hfo]

theorem expSpec_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u}) :
    ExpSpec.{u} := by
  intro K _ _ W
  obtain ⟨hL0, hL1, hLd, -⟩ := logSpec_of hI hU K W
  obtain ⟨-, hfo, -⟩ := hU K W
  obtain ⟨hE0, hLE, hEL, hcoef, -⟩ := hC K (logSer W) hL0 (by rw [hL1]; exact isUnit_one)
  have hLE' : (logSer W).subst (expSer W) = X := hLE
  have hs : HasSubst $ expSer W := hasSubst_lemma hE0
  refine ⟨hE0, ?_, hLE, hEL, ?_⟩
  have h : coeff 1 (expSer W) * coeff 1 (logSer W) = 1 := hcoef
  rwa [hL1, mul_one] at h
  have h1 := congrArg (derivative (R := K)) hLE'
  rw [derivative_subst hs, hLd, derivative_X] at h1
  have h2 : (fw W).subst (expSer W) * (om W).subst (expSer W) = 1 := by
    rw [← powerSeries_subst_mul_of_hasSubst hs, hfo, subst_one' hs]
  calc derivative (expSer W)
      = ((fw W).subst (expSer W) * (om W).subst (expSer W)) * derivative (expSer W) := by
        rw [h2, one_mul]
    _ = (fw W).subst (expSer W) := by rw [mul_assoc, h1, mul_one]

theorem chainZ_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u}) :
    ChainZ.{u} := by
  intro K _ _ W f
  obtain ⟨hE0, -, -, -, hEd⟩ := expSpec_of hI hC hU K W
  have hs := hasSubst_lemma hE0
  rw [derivative_subst hs, hEd]
  simp [D, Derivation.smul_apply, smul_eq_mul]
  rw [powerSeries_subst_mul_of_hasSubst hs, mul_comm]

theorem logNeg_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u})
    (hS : ISerSpec.{u}) : LogNeg.{u} := by
  intro K _ _ W
  obtain ⟨hL0, -, hLd, -⟩ := logSpec_of hI hU K W
  obtain ⟨hE0, -, hLE, hEL, -⟩ := expSpec_of hI hC hU K W
  obtain ⟨hi0, -, -, -, -, -, -, hiom⟩ := hS K W
  have hsi := hasSubst_lemma hi0
  have hsE := hasSubst_lemma hE0
  have hL' : (logSer W).subst (iSer W) = -logSer W := by
    obtain ⟨-, -, huniq⟩ := hI K $ -om W
    have e1 := huniq ((logSer W).subst (iSer W)) (constantCoeff_powerSeries_subst_eq_zero hi0 hL0)
      $ by rw [derivative_subst hsi, hLd, hiom]
    rw [e1, huniq (-logSer W) (by rw [map_neg, hL0, neg_zero]) $ by rw [map_neg, hLd]]
  use hL'
  have hnX0 : constantCoeff (-X : K⟦X⟧) = 0 := by simp
  have hsn := hasSubst_lemma hnX0
  apply subst_injective_of_leftInverse (l := logSer W) (e := expSer W) (hasSubst_lemma hL0)
    (hasSubst_lemma $ constantCoeff_powerSeries_subst_eq_zero hnX0 hE0) (hasSubst_lemma $ constantCoeff_powerSeries_subst_eq_zero hE0 hi0) hEL
  rw [← powerSeries_subst_subst_eq_subst_subst hsE hsn, hLE, subst_X hsn, ← powerSeries_subst_subst_eq_subst_subst hsi hsE, hL',
    subst_neg' hsE, hLE]

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

namespace Fgl2
local notation "L" i => MvPowerSeries.coeff $ Finsupp.single i 1
local notation "cc" => MvPowerSeries.constantCoeff

section Subst

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

abbrev curveM : WeierstrassCurve $ MvPowerSeries (Fin 2) R :=
  W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)

theorem fw_subst {s : MvPowerSeries (Fin 2) R} (hs : cc s = 0) :
    (fw W).subst s = fwAt (curveM W) s ((wSer W).subst s) := by
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have hC : ∀ a, (PowerSeries.C a).subst s = MvPowerSeries.C a := fun a => by
    rw [← PowerSeries.coe_substAlgHom hs']
    exact (PowerSeries.substAlgHom hs').commutes a
  rw [← PowerSeries.coe_substAlgHom hs']
  simp [fw, fwAt, map_sub, map_mul, map_pow, map_ofNat, map_one]
  rw [PowerSeries.coe_substAlgHom hs']
  simp [hC, PowerSeries.subst_X hs', WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  try ring

theorem fu_subst {s : MvPowerSeries (Fin 2) R} (hs : cc s = 0) :
    (fu W).subst s = fuAt (curveM W) s ((wSer W).subst s) := by
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have hC : ∀ a, (PowerSeries.C a).subst s = MvPowerSeries.C a := fun a => by
    rw [← PowerSeries.coe_substAlgHom hs']
    exact (PowerSeries.substAlgHom hs').commutes a
  rw [← PowerSeries.coe_substAlgHom hs']
  simp [fu, fuAt, map_mul, map_add, map_pow, map_ofNat]
  rw [PowerSeries.coe_substAlgHom hs']
  simp [hC, PowerSeries.subst_X hs', WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄]
  try ring

theorem weq_subst {s : MvPowerSeries (Fin 2) R} (hs : cc s = 0) :
    WEq (curveM W) s $ (wSer W).subst s := by
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have hC : ∀ a, (PowerSeries.C a).subst s = MvPowerSeries.C a := fun a => by
    rw [← PowerSeries.coe_substAlgHom hs']
    exact (PowerSeries.substAlgHom hs').commutes a
  have h := (unit_flow R W).2.2.1.1
  unfold WEq at h ⊢
  have h2 := congrArg (PowerSeries.substAlgHom (R := R) hs') h
  simp [map_mul, map_add, map_pow] at h2
  rw [PowerSeries.coe_substAlgHom hs'] at h2
  simp [hC, PowerSeries.subst_X hs', WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h2 ⊢
  exact h2

def Dm (i : Fin 2) (a : MvPowerSeries (Fin 2) R) : MvPowerSeries (Fin 2) R :=
  (fw W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) * MvPowerSeries.pderiv i a

theorem isDer_Dm (i : Fin 2) : IsDer $ Dm W i := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  unfold Dm
  rw [map_add, mul_add]
  unfold Dm
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

theorem const_Dm (i : Fin 2) : ConstCurve (Dm W i) $ curveM W := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold Dm
    simp [MvPowerSeries.pderiv_C]

theorem Dm_subst (i : Fin 2) {s : MvPowerSeries (Fin 2) R} (hs : cc s = 0) (f : R⟦X⟧) :
    Dm W i (f.subst s) = (derivative f).subst s * Dm W i s := by
  unfold Dm
  rw [Formalism.G.LogCR.pderiv_psubst hs]
  ring

theorem flow_Dm (i : Fin 2) : IsFlowUW (curveM W) (Dm W i) (MvPowerSeries.X i) $ Fgl1.Wi W i := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) = 0 :=
    MvPowerSeries.constantCoeff_X i
  have hF := unit_flow R W
  have hDX : Dm W i (MvPowerSeries.X i) = (fw W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) := by
    unfold Dm
    rw [MvPowerSeries.pderiv_X_self, mul_one]
  refine ⟨weq_subst W hX, ?_, ?_⟩
  rw [hDX, fw_subst W hX]
  rw [Dm_subst W i hX, ← fu_subst W hX, hDX]
  have h3 : fw W * derivative (wSer W) = fu W := by
    have h4 := hF.2.2.1.2.2
    rw [hF.2.2.2.2.1] at h4
    simpa [D, Derivation.smul_apply, smul_eq_mul] using h4
  rw [← h3, ← PowerSeries.coe_substAlgHom (R := R) $ PowerSeries.HasSubst.of_constantCoeff_zero hX, map_mul, mul_comm]

theorem Dm_X_of_ne {i j : Fin 2} (h : j ≠ i) : Dm W i (MvPowerSeries.X j) = 0 := by
  unfold Dm
  rw [MvPowerSeries.pderiv_X_of_ne h, mul_zero]

theorem lam_mul' (i j : Fin 2) :
    lam W * (MvPowerSeries.X i - MvPowerSeries.X j) = Fgl1.Wi W i - Fgl1.Wi W j := by
  have h :=
    (formal_group_chord R W).1
  fin_cases i <;> fin_cases j
  simp
  show lam W * (MvPowerSeries.X 0 - MvPowerSeries.X 1) = Fgl1.Wi W 0 - Fgl1.Wi W 1
  rwa [← neg_sub, mul_neg, h, neg_sub]
  simp

theorem nu_eq (i : Fin 2) : nu W = Fgl1.Wi W i - lam W * MvPowerSeries.X i := by
  fin_cases i
  rfl
  show nu W = Fgl1.Wi W 1 - lam W * MvPowerSeries.X 1
  unfold nu
  linear_combination ((formal_group_chord R W).1)

theorem third_rel (i j : Fin 2) (hij : i ≠ j) :
    cThree W * (MvPowerSeries.X i + MvPowerSeries.X j + uThird W) + cTwo W = 0 := by
  have hinv : cThree W * MvPowerSeries.invOfUnit (cThree W) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ $ by simp [Fgl1.cThree_cc]
  have hsum : (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) + MvPowerSeries.X j =
      MvPowerSeries.X 0 + MvPowerSeries.X 1 := by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | rfl | exact add_comm _ _
  rw [hsum, uThird]
  linear_combination (-(cTwo W)) * hinv

theorem Dm_uThird [IsDomain R] (i : Fin 2) : Dm W i (uThird W) = -(fw W).subst (uThird W) := by
  obtain ⟨j, hji⟩ : ∃ j, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
  have hD2 : Dm W i (Fgl1.Wi W j) = 0 := by
    rw [Dm_subst W i (MvPowerSeries.constantCoeff_X j), Dm_X_of_ne W hji, mul_zero]
  have hne12 : (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ≠ MvPowerSeries.X j := fun h =>
    hji (MvPowerSeries.X_inj.mp h).symm
  have hcoef : ∀ k l, MvPowerSeries.coeff (Finsupp.single k 1)
      (MvPowerSeries.X l : MvPowerSeries (Fin 2) R) = if k = l then 1 else 0 := by
    intro k l
    rw [MvPowerSeries.coeff_X]
    by_cases h : k = l
    simp [h]
    simp [h, Finsupp.single_left_inj one_ne_zero]
  have hne31 : uThird W ≠ MvPowerSeries.X i := fun h => by
    have h1 := Fgl1.uThird_L (W := W) j
    rw [h, hcoef, if_neg hji] at h1
    exact one_ne_zero (neg_eq_zero.mp h1.symm)
  have hne32 : uThird W ≠ MvPowerSeries.X j := fun h => by
    have h1 := Fgl1.uThird_L (W := W) i
    rw [h, hcoef, if_neg (Ne.symm hji)] at h1
    exact one_ne_zero (neg_eq_zero.mp h1.symm)
  have hC3 : (1 + (curveM W).a₂ * lam W + (curveM W).a₄ * lam W ^ 2 + (curveM W).a₆ * lam W ^ 3) ≠ 0 := by
    intro h
    have h1 := congrArg MvPowerSeries.constantCoeff (show cThree W = 0 from h)
    rw [Fgl1.cThree_cc, map_zero] at h1
    exact one_ne_zero h1
  haveI : IsDomain (MvPowerSeries (Fin 2) R) := NoZeroDivisors.to_isDomain _
  have hT := flowThirdPoint (MvPowerSeries (Fin 2) R) (curveM W) (Dm W i) (MvPowerSeries.X i) (Fgl1.Wi W i)
    (MvPowerSeries.X j) (Fgl1.Wi W j) (lam W) (nu W) (uThird W) (isDer_Dm W i) (const_Dm W i) (flow_Dm W i)
    (weq_subst W (MvPowerSeries.constantCoeff_X j)) (Dm_X_of_ne W hji) hD2 (lam_mul' W i j) (nu_eq W i) (third_rel W i j (Ne.symm hji)) hC3 hne12 hne31 hne32
  rw [hT.2.1, fw_subst W (Fgl1.uThird_cc (W := W)), ← Fgl1.wThird_eq (W := W)]
  rfl

theorem formal_inverse_spec : ISerSpec.{u} := iSerSpec_of w_series_spec w_series_factorization invariant_differential_units unit_flow chartFlowNegation

theorem Dm_fgl [IsDomain R] (i : Fin 2) : Dm W i (fgl W) = (fw W).subst (fgl W) := by
  have hu := (formal_group_chord R W).2.1
  have hu' := PowerSeries.HasSubst.of_constantCoeff_zero hu
  have hS := formal_inverse_spec R W
  have hD : derivative (iSer W) * fw W = -(fw W).subst (iSer W) := by
    have h := hS.2.2.2.2.2.2.1
    simp [D, Derivation.smul_apply, smul_eq_mul] at h
    rwa [mul_comm]
  have hmul : ∀ f g : R⟦X⟧, (f * g).subst (uThird W) = f.subst (uThird W) * g.subst (uThird W) :=
    fun f g => by rw [← PowerSeries.coe_substAlgHom (R := R) hu', map_mul]
  have hneg : ∀ f : R⟦X⟧, (-f).subst (uThird W) = -(f.subst (uThird W)) :=
    fun f => by rw [← PowerSeries.coe_substAlgHom (R := R) hu', map_neg]
  rw [Fgl1.fgl_eq, Dm_subst W i hu, Dm_uThird W i, ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hS.1) hu', mul_neg,
    ← hmul, hD, hneg, neg_neg]

end Subst

section Transfer

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem map_pderiv (φ : R →+* S) (i : Fin 2) (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv i f)
      = MvPowerSeries.pderiv i (MvPowerSeries.map φ f) := by
  ext n
  simp [MvPowerSeries.coeff_pderiv]

theorem map_Dm (φ : R →+* S) (W : WeierstrassCurve R) (i : Fin 2) (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.map φ (Dm W i f) = Dm (W.map φ) i (MvPowerSeries.map φ f) := by
  unfold Dm
  rw [map_mul, map_pderiv,
    PowerSeries.map_subst $ PowerSeries.HasSubst.of_constantCoeff_zero $ MvPowerSeries.constantCoeff_X i,
    (series_map R S φ W).2.2.2.2.1, MvPowerSeries.map_X]

theorem Dm_fgl' (W : WeierstrassCurve R) (i : Fin 2) : Dm W i (fgl W) = (fw W).subst (fgl W) := by
  have h1 := congrArg (MvPowerSeries.map $ Univ.φ_of W) $ Dm_fgl Univ.W₀ i
  rw [map_Dm, Univ.map_eq, ← Fgl1.fgl_univ, PowerSeries.map_subst $ PowerSeries.HasSubst.of_constantCoeff_zero $ Fgl1.fgl_cc Univ.W₀,
    (series_map _ _ (Univ.φ_of W) Univ.W₀).2.2.2.2.1, Univ.map_eq, ← Fgl1.fgl_univ] at h1
  exact h1

theorem fw_mul_om_subst (W : WeierstrassCurve R) {s : MvPowerSeries (Fin 2) R} (hs : cc s = 0) :
    (fw W).subst s * (om W).subst s = 1 := by
  have h1 : fw W * om W = 1 := by
    have h := (unit_flow R W).2.2.2.2.2 X
    simp [D, Derivation.smul_apply, PowerSeries.derivative_X, smul_eq_mul, mul_one] at h
    rwa [mul_comm]
  rw [← PowerSeries.coe_substAlgHom (R := R) $ PowerSeries.HasSubst.of_constantCoeff_zero hs, ← map_mul, h1, map_one]

theorem om_fgl (W : WeierstrassCurve R) (i : Fin 2) :
    (om W).subst (fgl W) * MvPowerSeries.pderiv i (fgl W)
      = (om W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) := by
  have h := Dm_fgl' W i
  unfold Dm at h
  have h1 := fw_mul_om_subst W $ Fgl1.fgl_cc W
  have h2 := fw_mul_om_subst W $ MvPowerSeries.constantCoeff_X i
  linear_combination ((om W).subst (fgl W) * (om W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)) * h +
    (om W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) * h1 -
    ((om W).subst (fgl W) * MvPowerSeries.pderiv i (fgl W)) * h2


end Transfer

section Log

variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem formal_logarithm_spec : LogSpec.{u} := logSpec_of integration_spec invariant_differential_units

theorem formal_exponential_spec : ExpSpec.{u} := expSpec_of integration_spec composition_inverse_spec invariant_differential_units


private theorem eq_zero_of_pderiv_zero_of_pderiv_one_eq_zero {h : MvPowerSeries (Fin 2) K}
    (h0 : MvPowerSeries.pderiv 0 h = 0) (h1 : MvPowerSeries.pderiv 1 h = 0)
    (hc : MvPowerSeries.constantCoeff h = 0) : h = 0 := by
  ext n
  rw [map_zero]
  by_cases hn : n = 0
  subst hn
  simpa using hc
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hn $ Finsupp.ext hne
  have hD : MvPowerSeries.pderiv i h = 0 := by
    fin_cases i
    exact h0
    exact h1
  have h2 := congrArg (MvPowerSeries.coeff $ n - Finsupp.single i 1) hD
  rw [MvPowerSeries.coeff_pderiv, map_zero] at h2
  have hsum : n - Finsupp.single i 1 + Finsupp.single i 1 = n := by
    ext j
    by_cases hj : j = i
    subst hj
    simp
    omega
    simp [Ne.symm hj]
  rw [hsum] at h2
  exact (mul_eq_zero.mp h2).resolve_right $ Nat.cast_add_one_ne_zero _

theorem log_fgl : (logSer W).subst (fgl W) = (logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
    + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K) := by
  have hL := formal_logarithm_spec K W
  have hF := Fgl1.fgl_cc W
  rw [← sub_eq_zero]
  apply eq_zero_of_pderiv_zero_of_pderiv_one_eq_zero
  rw [map_sub, map_add, Formalism.G.LogCR.pderiv_psubst hF, Formalism.G.LogCR.pderiv_psubst $ MvPowerSeries.constantCoeff_X 0,
    Formalism.G.LogCR.pderiv_psubst $ MvPowerSeries.constantCoeff_X 1, hL.2.2.1, om_fgl W 0,
    MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne $ by decide, mul_zero, mul_one, add_zero, sub_self]
  rw [map_sub, map_add, Formalism.G.LogCR.pderiv_psubst hF, Formalism.G.LogCR.pderiv_psubst $ MvPowerSeries.constantCoeff_X 0,
    Formalism.G.LogCR.pderiv_psubst $ MvPowerSeries.constantCoeff_X 1, hL.2.2.1, om_fgl W 1,
    MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne $ by decide, mul_zero, mul_one, zero_add, sub_self]
  have hc : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff ((logSer W).subst a) = 0 := fun a ha => by
    rw [PowerSeries.subst, Formalism.G.LogP.constantCoeff_subst_of_zero _ fun _ => ha]
    exact hL.1
  rw [map_sub, map_add, hc _ hF, hc _ $ MvPowerSeries.constantCoeff_X 0, hc _ $ MvPowerSeries.constantCoeff_X 1]
  simp

end Log

section Group




variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


end Group

section Inv




end Inv

end Fgl2


theorem formal_group_logarithm : FglLog.{u} := by
  intro K _ _ W
  use Fgl2.log_fgl W
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero $ Fgl1.fgl_cc W
  rw [← Fgl2.log_fgl W, ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero (Fgl2.formal_logarithm_spec K W).1) hF, (Fgl2.formal_exponential_spec K W).2.2.2.1, PowerSeries.subst_X hF]




end Formalism.L2.Th1.A
end
section
open PowerSeries (coeff_map map_X map_algebraMap_eq_subst_X)
open PowerSeries



namespace Formalism.L2.Th1.A

namespace ZSer

local notation "FF[" W "](" a ", " b ")" =>
  MvPowerSeries.subst (![a, b] : Fin 2 → PowerSeries _) $ fgl W

section Tools

variable {R : Type u} [CommRing R]

theorem hasSubst_pair {a b : R⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    MvPowerSeries.HasSubst (![a, b] : Fin 2 → R⟦X⟧) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s
  exacts [ha, hb]

theorem subst_pair_subst {a b : R⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    {g : MvPowerSeries (Fin 2) R} (hg : MvPowerSeries.constantCoeff g = 0) (f : R⟦X⟧) :
    MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) (f.subst g)
      = f.subst (MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) g) := by
  simp [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const $ PowerSeries.HasSubst.of_constantCoeff_zero hg) $ hasSubst_pair ha hb]

theorem subst_subst_pair {a b c : R⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (hc : constantCoeff c = 0) (g : MvPowerSeries (Fin 2) R) :
    PowerSeries.subst c (MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) g : R⟦X⟧)
      = MvPowerSeries.subst (![a.subst c, b.subst c] : Fin 2 → R⟦X⟧) g := by
  simp [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pair ha hb) $ PowerSeries.HasSubst.const $ PowerSeries.HasSubst.of_constantCoeff_zero hc]
  congr 1
  funext s
  fin_cases s <;> rfl

theorem map_subst_pair {S : Type v} [CommRing S] (φ : R →+* S) {a b : R⟦X⟧}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (g : MvPowerSeries (Fin 2) R) :
    PowerSeries.map φ (MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) g)
      = MvPowerSeries.subst (![PowerSeries.map φ a, PowerSeries.map φ b] : Fin 2 → S⟦X⟧)
          (MvPowerSeries.map φ g) := by
  refine (MvPowerSeries.map_subst (hasSubst_pair ha hb) (h := φ) g).trans ?_
  congr 1
  funext s
  fin_cases s <;> rfl


theorem subst_C_mul {s : R⟦X⟧} (hs : HasSubst s) (r : R) (f : R⟦X⟧) :
    (C r * f).subst s = C r * f.subst s := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, PowerSeries.subst_smul hs]

theorem cc_subst {g s : R⟦X⟧} (hs : constantCoeff s = 0) :
    constantCoeff (g.subst s) = constantCoeff g := by
  erw [PowerSeries.constantCoeff_subst $ HasSubst.of_constantCoeff_zero hs, finsum_eq_single _ 0]
  simp
  intro d hd
  simp
  rw [show MvPowerSeries.constantCoeff s = 0 from hs, zero_pow hd, mul_zero]

theorem coeff_one_subst {f s : R⟦X⟧} (hs : constantCoeff s = 0) :
    coeff 1 (f.subst s) = coeff 1 f * coeff 1 s := by
  obtain ⟨t, rfl⟩ : X ∣ s := X_dvd_iff.mpr hs
  erw [PowerSeries.coeff_subst $ HasSubst.of_constantCoeff_zero hs, finsum_eq_single _ 1]
  simp
  intro d hd
  rcases d with _ | _ | d
  simp
  exact absurd rfl hd
  rw [mul_pow]
  show coeff (d + 1 + 1) f • coeff 1 (X ^ (d + 1 + 1) * t ^ (d + 1 + 1)) = 0
  rw [coeff_X_pow_mul', if_neg $ show ¬ (d + 1 + 1 ≤ 1) by omega, smul_zero]

end Tools

section Ring

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem FF_cc {a b : R⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    constantCoeff (FF[W](a, b)) = 0 := by
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair ha hb)
    (fun i => by fin_cases i; exacts [ha, hb]) $ Fgl1.fgl_cc W

theorem FF_map {S : Type v} [CommRing S] (φ : R →+* S) {a b : R⟦X⟧}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    PowerSeries.map φ (FF[W](a, b)) = FF[W.map φ](PowerSeries.map φ a, PowerSeries.map φ b) := by
  rw [map_subst_pair φ ha hb, Fgl1.fgl_map W φ]

theorem iSer_cc : constantCoeff (iSer W) = 0 := by
  rw [iSer, map_mul, constantCoeff_X, zero_mul]

theorem nSer_zero : nSer W 0 = 0 := rfl

theorem nSer_succ (n : ℕ) : nSer W (n + 1) = FF[W](X, nSer W n) := rfl

theorem nSer_cc (n : ℕ) : constantCoeff (nSer W n) = 0 := by
  induction n with
  | zero => rw [nSer_zero, map_zero]
  | succ n ih => rw [nSer_succ]; exact FF_cc W constantCoeff_X ih

theorem zSer_ofNat (n : ℕ) : zSer W (n : ℤ) = nSer W n := rfl

theorem zSer_negSucc (n : ℕ) : zSer W (Int.negSucc n) = (iSer W).subst (nSer W $ n + 1) := rfl

theorem zSer_cc (n : ℤ) : constantCoeff (zSer W n) = 0 := by
  rcases n with n | n
  exact nSer_cc W n
  rw [zSer_negSucc, cc_subst $ nSer_cc W $ n + 1, iSer_cc]

theorem nSer_map {S : Type v} [CommRing S] (φ : R →+* S) (n : ℕ) :
    PowerSeries.map φ (nSer W n) = nSer (W.map φ) n := by
  induction n with
  | zero => rw [nSer_zero, nSer_zero, map_zero]
  | succ n ih =>
    rw [nSer_succ, nSer_succ, FF_map W φ constantCoeff_X $ nSer_cc W n, ih, map_X]

theorem zSer_map {S : Type v} [CommRing S] (φ : R →+* S) (n : ℤ) :
    PowerSeries.map φ (zSer W n) = zSer (W.map φ) n := by
  rcases n with n | n
  exact nSer_map W φ n
  rw [zSer_negSucc, zSer_negSucc]
  refine (PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' $ nSer_cc W $ n + 1) (h := φ)
    $ iSer W).trans ?_
  rw [CurveSer.map_iSer]
  exact congrArg (PowerSeries.subst · $ iSer $ W.map φ) $ nSer_map W φ $ n + 1


end Ring

section Field

variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem iSerSpec' : ISerSpec.{u} :=
  iSerSpec_of w_series_spec w_series_factorization invariant_differential_units unit_flow chartFlowNegation

theorem log_cc : constantCoeff (logSer W) = 0 := by
  rw [logSer, integ, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, if_pos rfl]

theorem log_one : coeff 1 (logSer W) = 1 := by
  rw [logSer, integ, coeff_mk, if_neg one_ne_zero]
  simp [Nat.sub_self, coeff_zero_eq_constantCoeff_apply, CurveSer.om_cc, Nat.cast_one, div_one]

theorem log_inj {a b : K⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (h : (logSer W).subst a = (logSer W).subst b) : a = b := by
  exact subst_injective_of_leftInverse (HasSubst.of_constantCoeff_zero' $ log_cc W)
    (HasSubst.of_constantCoeff_zero' ha) (HasSubst.of_constantCoeff_zero' hb) (((expSpec_of integration_spec composition_inverse_spec invariant_differential_units) K W).2.2.2.1) h

theorem log_FF (hL : FglLog.{u}) {a b : K⟦X⟧} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) :
    (logSer W).subst (FF[W](a, b)) = (logSer W).subst a + (logSer W).subst b := by
  have hab := hasSubst_pair ha hb
  have e := congrArg (MvPowerSeries.subst (![a, b] : Fin 2 → K⟦X⟧)) (hL K W).1
  rw [subst_pair_subst ha hb $ Fgl1.fgl_cc W, MvPowerSeries.subst_add hab,
    subst_pair_subst ha hb $ MvPowerSeries.constantCoeff_X 0,
    subst_pair_subst ha hb $ MvPowerSeries.constantCoeff_X 1,
    MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab] at e
  exact e

theorem log_nSer (hL : FglLog.{u}) (n : ℕ) :
    (logSer W).subst (nSer W n) = C (n : K) * logSer W := by
  have hX : (logSer W).subst (X : K⟦X⟧) = logSer W := by
    rw [← map_algebraMap_eq_subst_X]
    rfl
  induction n with
  | zero =>
    rw [nSer_zero, Nat.cast_zero, map_zero, zero_mul]
    exact PowerSeries.subst_zero_of_constantCoeff_zero $ log_cc W
  | succ n ih =>
    rw [nSer_succ, log_FF W hL constantCoeff_X $ nSer_cc W n, ih, hX, Nat.cast_succ, map_add, map_one,
      add_mul, one_mul, add_comm]

theorem log_zSer (hL : FglLog.{u}) (n : ℤ) :
    (logSer W).subst (zSer W n) = C (n : K) * logSer W := by
  rcases n with n | n
  show (logSer W).subst (nSer W n) = C (((n : ℕ) : ℤ) : K) * logSer W
  exact_mod_cast log_nSer W hL n
  have hs := nSer_cc W $ n + 1
  rw [zSer_negSucc, ← PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' $ iSer_cc W)
    $ HasSubst.of_constantCoeff_zero' hs, ((logNeg_of integration_spec composition_inverse_spec invariant_differential_units iSerSpec') K W).1, subst_neg' $ HasSubst.of_constantCoeff_zero' hs,
    log_nSer W hL $ n + 1, Int.cast_negSucc, map_neg, neg_mul]



theorem field_one (hL : FglLog.{u}) : zSer W 1 = X := by
  apply log_inj W (zSer_cc W 1) constantCoeff_X
  rw [log_zSer W hL 1, Int.cast_one, map_one, one_mul]
  have hx : (fun _ => (X : K⟦X⟧)) = MvPowerSeries.X := by
    funext u
    rfl
  simp [PowerSeries.subst]
  rw [hx, MvPowerSeries.subst_self]
  rfl

theorem field_coeff (hL : FglLog.{u}) (n : ℤ) : coeff 1 (zSer W n) = (n : K) := by
  have h := congrArg (coeff 1) $ log_zSer W hL n
  rwa [coeff_one_subst $ zSer_cc W n, log_one, one_mul, coeff_C_mul, log_one, mul_one] at h

end Field

section Transfer

open Univ

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem zSer_univ (n : ℤ) : PowerSeries.map (φ_of W) (zSer W₀ n) = zSer W n := by
  rw [zSer_map]
  congr 1
  ext <;> simp [W₀, φ_of]



theorem ring_one (hL : FglLog.{0}) : zSer W 1 = X := by
  have h : PowerSeries.map Univ.ι (zSer W₀ 1) = PowerSeries.map Univ.ι X := by
    rw [zSer_map, map_X]
    exact field_one Univ.WK hL
  have h2 := Univ.ps_transfer W h
  rwa [zSer_univ, map_X] at h2

theorem ring_coeff (hL : FglLog.{0}) (n : ℤ) : coeff 1 (zSer W n) = (n : R) := by
  have h1 : Univ.ι (coeff 1 $ zSer W₀ n) = Univ.ι (n : Univ.Z) := by
    rw [← coeff_map, zSer_map, map_intCast]
    exact field_coeff Univ.WK hL n
  rw [← zSer_univ W n, coeff_map, Univ.ι_injective h1, map_intCast]

theorem nSer_two_coeff (hL : FglLog.{0}) : coeff 1 (nSer W 2) = 2 := by
  have h : coeff 1 (zSer W ((2 : ℕ) : ℤ)) = (((2 : ℕ) : ℤ) : R) := ring_coeff W hL _
  rw [zSer_ofNat] at h
  rw [h]
  norm_num

theorem nSer_one (hL : FglLog.{0}) : nSer W 1 = X := by
  have h := ring_one W hL
  rwa [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, zSer_ofNat] at h

theorem nSer_two (hL : FglLog.{0}) : nSer W 2 = FF[W](X, X) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, nSer_succ, nSer_one W hL]

end Transfer

end ZSer

theorem z_series_map : ZSerMap.{u, v} := by
  intro R S _ _ φ W n
  exact ZSer.zSer_map W φ n



theorem halfSpec_of (hL : FglLog.{0}) : HalfSpec.{u} := by
  intro R _ W h2
  obtain ⟨hh0, hsh, hhs, hm, -, -⟩ := composition_inverse_spec R (nSer W 2) (ZSer.nSer_cc W 2) $ by
      rwa [ZSer.nSer_two_coeff W hL]
  have hh0' := hh0
  have hh : HasSubst $ halfSer W := HasSubst.of_constantCoeff_zero' hh0'
  refine ⟨hh0', ?_, hsh, hhs, ?_⟩
  rwa [mul_comm, ← (ZSer.nSer_two_coeff W hL)]
  have key : PowerSeries.subst (halfSer W) (MvPowerSeries.subst (![X, X] : Fin 2 → R⟦X⟧) (fgl W) : R⟦X⟧)
      = MvPowerSeries.subst (![(X : R⟦X⟧).subst (halfSer W), (X : R⟦X⟧).subst (halfSer W)] : Fin 2 → R⟦X⟧)
          (fgl W) :=
    ZSer.subst_subst_pair constantCoeff_X constantCoeff_X hh0' $ fgl W
  rw [PowerSeries.subst_X hh] at key
  rwa [← key, ← ZSer.nSer_two W hL]

theorem halfLog_of (hL : FglLog.{u}) (hL0 : FglLog.{0}) : HalfLog.{u, v} := by
  refine ⟨fun K _ _ W => ?_, fun R S _ _ φ W h2 => ?_⟩
  obtain ⟨hh0, -, hsh, -, -⟩ := halfSpec_of hL0 K W $ isUnit_iff_ne_zero.mpr two_ne_zero
  have hh := HasSubst.of_constantCoeff_zero' hh0
  have hX : (logSer W).subst (X : K⟦X⟧) = logSer W := by
    rw [← map_algebraMap_eq_subst_X]
    rfl
  have e2 : PowerSeries.subst (halfSer W) ((logSer W).subst (nSer W 2)) = logSer W := by
    rw [PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' $ ZSer.nSer_cc W 2) hh, hsh, hX]
  rwa [ZSer.log_nSer W hL 2, ZSer.subst_C_mul hh, Nat.cast_ofNat, map_ofNat] at e2
  have hc : coeff 1 (nSer W 2) = 2 := ZSer.nSer_two_coeff W hL0
  have hu : IsUnit $ coeff 1 $ nSer W 2 := by
    rwa [hc]
  show PowerSeries.map φ (compInv $ nSer W 2) = compInv (nSer (W.map φ) 2)
  rw [composition_inverse_map R S φ (nSer W 2) (ZSer.nSer_cc W 2) hu, ZSer.nSer_map]

end Formalism.L2.Th1.A
end
section
open HahnSeries (ofPowerSeries_C single_mul_single)
open PowerSeries (constantCoeff_invOfUnit map map_C map_X)
open WeierstrassCurve (map_a₁ map_a₂ map_a₃ map_a₄ map_a₆)
open PowerSeries



namespace Formalism.L2.Th1.A

namespace Plus

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)

theorem tDen_cc : constantCoeff (tDen W xP) = 1 := by
  simp [tDen, xS, constantCoeff_invOfUnit]

theorem tDen_mul_inv : tDen W xP * invOfUnit (tDen W xP) 1 = 1 := PowerSeries.mul_invOfUnit _ _ $ by simpa using tDen_cc W xP


theorem toL_tDen_mul_inv : toL (tDen W xP) * toL (invOfUnit (tDen W xP) 1) = 1 := by
  rw [← map_mul, tDen_mul_inv, map_one]

theorem toL_X_mul : (toL X : LaurentSeries R) * uPow (-1) = 1 := by
  simp [uPow, HahnSeries.ofPowerSeries_X, single_mul_single, HahnSeries.single_zero_one]

theorem uPow_neg_two : (uPow (-2) : LaurentSeries R) = uPow (-1) ^ 2 := by
  simp only [uPow]
  rw [sq, single_mul_single]
  norm_num

theorem uPow_neg_three : (uPow (-3) : LaurentSeries R) = uPow (-1) ^ 3 := by
  simp only [uPow]
  rw [pow_three, single_mul_single, single_mul_single]
  norm_num

theorem xL_eq : xL W = uPow (-1) ^ 2 * toL (xS W) := by
  rw [xL, uPow_neg_two]

theorem yL_eq : yL W = uPow (-1) ^ 3 * toL (yS W) := by
  rw [yL, uPow_neg_three]

theorem toL_tDen : toL (tDen W xP) = toL (xS W) - HahnSeries.C xP * toL X ^ 2 := by
  simp [tDen, map_sub, map_mul, map_pow, ofPowerSeries_C]

theorem toL_tS : toL (tS W xP) = toL X ^ 2 * toL (invOfUnit (tDen W xP) 1) := by
  simp [tS, map_mul, map_pow]

theorem xL_sub : xL W - HahnSeries.C xP = uPow (-1) ^ 2 * toL (tDen W xP) := by
  rw [toL_tDen, xL_eq, mul_sub]
  have h : (uPow (-1) : LaurentSeries R) ^ 2 * (HahnSeries.C xP * toL X ^ 2) = HahnSeries.C xP := by
    rw [mul_left_comm, ← mul_pow, mul_comm (uPow (-1) : LaurentSeries R) $ toL X, toL_X_mul,
      one_pow, mul_one]
  rw [h]

theorem yL_sub : yL W - HahnSeries.C yP = uPow (-1) ^ 3 * toL (yS W - C yP * X ^ 3) := by
  rw [yL_eq, map_sub, map_mul, map_pow, ofPowerSeries_C, mul_sub]
  have h : (uPow (-1) : LaurentSeries R) ^ 3 * (HahnSeries.C yP * toL X ^ 3) = HahnSeries.C yP := by
    rw [mul_left_comm, ← mul_pow, mul_comm (uPow (-1) : LaurentSeries R) $ toL X, toL_X_mul,
      one_pow, mul_one]
  rw [h]

theorem toL_tS_mul : toL (tS W xP) * (xL W - HahnSeries.C xP) = 1 := by
  rw [xL_sub, toL_tS]
  calc (toL X : LaurentSeries R) ^ 2 * toL (invOfUnit (tDen W xP) 1) * (uPow (-1) ^ 2 * toL (tDen W xP))
      = ((toL X : LaurentSeries R) * uPow (-1)) ^ 2
          * (toL (tDen W xP) * toL (invOfUnit (tDen W xP) 1)) := by ring
    _ = 1 := by rw [toL_X_mul, toL_tDen_mul_inv, one_pow, one_mul]


theorem toL_nS : toL (nS W xP yP) =
    HahnSeries.C (W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * toL X * toL (xS W)
      - HahnSeries.C (2 * yP + W.a₁ * xP + W.a₃) * toL (yS W)
      + HahnSeries.C (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3) * toL X ^ 3 := by
  simp [nS, map_add, map_sub, map_mul, map_pow, ofPowerSeries_C]

theorem toL_xPlus : toL (xPlus W xP yP) = HahnSeries.C xP
    + toL X * toL (nS W xP yP) * toL (invOfUnit (tDen W xP) 1) ^ 2 := by
  simp [xPlus, map_add, map_mul, map_pow, ofPowerSeries_C]

theorem toL_yPlus : toL (yPlus W xP yP) =
    -(toL (yS W - C yP * X ^ 3) * toL (nS W xP yP) * toL (invOfUnit (tDen W xP) 1) ^ 3)
      - HahnSeries.C yP - HahnSeries.C W.a₁ * toL (xPlus W xP yP) - HahnSeries.C W.a₃ := by
  simp [yPlus, map_sub, map_neg, map_mul, map_pow, ofPowerSeries_C]









theorem equation_C {xP yP : R} (hP : W.toAffine.Equation xP yP) :
    (curveL W).toAffine.Equation (HahnSeries.C xP) $ HahnSeries.C yP := by
  rw [WeierstrassCurve.Affine.equation_iff] at hP ⊢
  simpa using (congrArg (HahnSeries.C : R →+* LaurentSeries R) hP)

theorem chord (hFL : FlowL.{u}) {xP yP : R} (hP : W.toAffine.Equation xP yP) :
    toL (xPlus W xP yP) = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) ∧
    toL (yPlus W xP yP)
      = (curveL W).toAffine.addY (xL W) (HahnSeries.C xP) (yL W) (slopeL W xP yP) := by
  obtain ⟨hX, hY⟩ := chordFormula _ (curveL W) (xL W) (yL W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL $ tS W xP) (hFL R W).1.1 (equation_C W hP) $ toL_tS_mul W xP
  have h : (toL X : LaurentSeries R) * uPow (-1) = 1 := toL_X_mul
  have hx : toL (xPlus W xP yP)
      = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) := by
    rw [slopeL, hX, toL_xPlus, toL_nS, toL_tS, xL_eq, yL_eq]
    simp only [map_a₁, map_a₂, map_a₃,
      map_a₄, map_a₆, map_add, map_sub, map_mul, map_pow,
      map_ofNat]
    generalize toL (invOfUnit (tDen W xP) 1) = v
    generalize toL (xS W) = xs
    generalize toL (yS W) = ys
    linear_combination (-(HahnSeries.C W.a₄ - HahnSeries.C W.a₁ * HahnSeries.C yP
        + 2 * HahnSeries.C W.a₂ * HahnSeries.C xP + 3 * HahnSeries.C xP ^ 2) * xs * v ^ 2
          * toL X ^ 2 * (toL X * uPow (-1) + 1)
      + (2 * HahnSeries.C yP + HahnSeries.C W.a₁ * HahnSeries.C xP + HahnSeries.C W.a₃) * ys
          * v ^ 2 * toL X * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * h
  use hx
  rw [slopeL] at hx ⊢
  rw [hY, ← hx, toL_yPlus, yL_sub, toL_tS]
  simp only [map_a₁, map_a₃]
  rw [toL_xPlus]
  linear_combination (toL (yS W - C yP * X ^ 3) * toL (nS W xP yP)
    * toL (invOfUnit (tDen W xP) 1) ^ 3 * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * h

theorem isFlow_of_toL (hDL : DLSpec.{u}) {a b : R⟦X⟧}
    (h : IsFlow (curveL W) (DL W) (toL a) $ toL b) : IsFlow (curveS W) (D W) a b := by
  obtain ⟨hE, h1, h2⟩ := h
  obtain ⟨-, -, -, hD⟩ := hDL R W
  have inj : Function.Injective (toL : R⟦X⟧ →+* LaurentSeries R) := HahnSeries.ofPowerSeries_injective
  refine ⟨?_, ?_, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff] at hE ⊢
  apply inj
  simpa using hE
  apply inj
  rw [← hD]
  simpa [map_ofNat toL 2] using h1
  apply inj
  rw [← hD]
  simpa [map_ofNat toL 2, map_ofNat toL 3] using h2

theorem nS_cc : constantCoeff (nS W xP yP) = 2 * yP + W.a₁ * xP + W.a₃ := by
  simp [nS, yS, xS, constantCoeff_invOfUnit]

theorem xPlus_cc : constantCoeff (xPlus W xP yP) = xP := by
  simp [xPlus]

theorem yPlus_cc : constantCoeff (yPlus W xP yP) = yP := by
  simp [yPlus, yS, xS, xPlus_cc, nS_cc, constantCoeff_invOfUnit] <;> ring

section Map

variable {S : Type v} [CommRing S] (φ : R →+* S)

theorem map_tDen : map φ (tDen W xP) = tDen (W.map φ) (φ xP) := by
  simp [tDen, map_sub, map_mul, map_pow, map_C, map_X, CurveSer.map_xS]

theorem map_inv : map φ (invOfUnit (tDen W xP) 1)
    = invOfUnit (tDen (W.map φ) $ φ xP) 1 := by
  have h1 : tDen (W.map φ) (φ xP) * map φ (invOfUnit (tDen W xP) 1) = 1 := by
    rw [← Plus.map_tDen W xP φ, ← map_mul, tDen_mul_inv, map_one]
  calc map φ (invOfUnit (tDen W xP) 1)
      = (invOfUnit (tDen (W.map φ) $ φ xP) 1 * tDen (W.map φ) (φ xP))
          * map φ (invOfUnit (tDen W xP) 1) := by
        rw [mul_comm (invOfUnit (tDen (W.map φ) $ φ xP) 1) $ tDen (W.map φ) $ φ xP, tDen_mul_inv (W.map φ) $ φ xP, one_mul]
    _ = invOfUnit (tDen (W.map φ) $ φ xP) 1 := by rw [mul_assoc, h1, mul_one]

theorem map_tS : map φ (tS W xP) = tS (W.map φ) (φ xP) := by
  simp [tS, map_mul, map_pow, map_X, Plus.map_inv W xP φ]

theorem map_nS : map φ (nS W xP yP) = nS (W.map φ) (φ xP) (φ yP) := by
  simp [nS, yS, map_add, map_sub, map_mul, map_neg, map_pow, map_C, map_X,
    CurveSer.map_xS, map_a₁, map_a₂, map_a₃,
    map_a₄, map_a₆, map_ofNat]

theorem map_xPlus : map φ (xPlus W xP yP) = xPlus (W.map φ) (φ xP) (φ yP) := by
  simp [xPlus, map_add, map_mul, map_pow, map_C, map_X,
    Plus.map_nS W xP yP φ, Plus.map_inv W xP φ]

theorem map_yPlus : map φ (yPlus W xP yP) = yPlus (W.map φ) (φ xP) (φ yP) := by
  simp [yPlus, yS, map_add, map_sub, map_neg, map_mul, map_pow, map_C,
    map_X, CurveSer.map_xS, Plus.map_nS W xP yP φ, Plus.map_inv W xP φ,
    Plus.map_xPlus W xP yP φ, map_a₁, map_a₃]

end Map

end Plus

open Plus



theorem plusFlow_of (hDL : DLSpec.{u}) (hFL : FlowL.{u}) : PlusFlow.{u} := by
  intro R _ W xP yP hP
  obtain ⟨hDer, hConst, hC, -⟩ := hDL R W
  obtain ⟨hx, hy⟩ := chord W hFL hP
  have h := flowTranslation _ (curveL W) (DL W) (xL W) (yL W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL (tS W xP)) hDer hConst (hFL R W).1 (equation_C W hP) (hC xP) (hC yP)
    $ toL_tS_mul W xP
  rw [slopeL] at hx hy
  rw [← hx, ← hy] at h
  exact ⟨isFlow_of_toL W hDL h, xPlus_cc W xP yP, yPlus_cc W xP yP⟩



theorem addition_map : PlusMap.{u, v} := by
  intro R S _ _ φ W xP yP
  exact ⟨Plus.map_tS W xP φ, Plus.map_xPlus W xP yP φ, Plus.map_yPlus W xP yP φ⟩

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

namespace WpSh

theorem alg_first {S : Type*} [CommRing S] (z zi A B c2 c3 : S) (hz : z * zi = 1)
    (h : (zi ^ 2 * B + (-2) * zi ^ 3 * A) ^ 2 = 4 * (zi ^ 2 * A) ^ 3 - c2 * (zi ^ 2 * A) - c3) :
    (z * B - 2 * A) ^ 2 = 4 * A ^ 3 - c2 * z ^ 4 * A - c3 * z ^ 6 := by
  have e1 : z ^ 6 * (zi ^ 2 * B + (-2) * zi ^ 3 * A) ^ 2 = (z * B * (z * zi) ^ 2 - 2 * A * (z * zi) ^ 3) ^ 2 := by ring
  have e2 : z ^ 6 * (4 * (zi ^ 2 * A) ^ 3 - c2 * (zi ^ 2 * A) - c3)
      = 4 * A ^ 3 * (z * zi) ^ 6 - c2 * z ^ 4 * A * (z * zi) ^ 2 - c3 * z ^ 6 := by ring
  rw [hz] at e1 e2
  simp only [one_pow, mul_one] at e1 e2
  rw [← e1, h, e2]

theorem alg_second {S : Type*} [CommRing S] (z zi A B c : S) (hz : z * zi = 1)
    (h : (-2) * ((-3) * zi ^ 4) + B = 6 * (zi ^ 2 + A) ^ 2 - c) :
    z ^ 2 * B = 12 * A + z ^ 2 * (6 * (A * A)) - z ^ 2 * c := by
  have e : z ^ 2 * ((-2) * ((-3) * zi ^ 4) + B) = z ^ 2 * (6 * (zi ^ 2 + A) ^ 2 - c) := by rw [h]
  have e' : z ^ 2 * B = 12 * A * (z * zi) ^ 2 + z ^ 2 * (6 * (A * A)) - z ^ 2 * c := by
    linear_combination e
  rwa [hz, one_pow, mul_one] at e'

variable {K : Type u} [Field K]

theorem z_mul_zi : (toL X : LaurentSeries K) * uPow (-1) = 1 := by
  simp only [uPow, HahnSeries.ofPowerSeries_X, HahnSeries.single_mul_single, mul_one]
  rw [show (1 : ℤ) + -1 = 0 by norm_num, ← HahnSeries.C_apply, map_one]

theorem uPow_neg_two : (uPow (-2) : LaurentSeries K) = uPow (-1) ^ 2 := by
  rw [sq, ← uPow_add]
  norm_num

theorem uPow_neg_three : (uPow (-2 - 1) : LaurentSeries K) = uPow (-1) ^ 3 := by
  rw [pow_succ, sq, ← uPow_add, ← uPow_add]
  norm_num

theorem uPow_neg_four : (uPow (-2 - 1 - 1) : LaurentSeries K) = uPow (-1) ^ 4 := by
  rw [pow_succ, pow_succ, sq, ← uPow_add, ← uPow_add, ← uPow_add]
  norm_num

theorem C_neg_two : (HahnSeries.C (((-2 : ℤ)) : K) : LaurentSeries K) = -2 := by
  rw [Int.cast_neg, Int.cast_ofNat, map_neg, map_ofNat]

theorem C_neg_three : (HahnSeries.C (((-2 - 1 : ℤ)) : K) : LaurentSeries K) = -3 := by
  rw [Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_one, map_sub, map_neg, map_ofNat,
    map_one]
  norm_num

theorem add_eq_mul (r : K⟦X⟧) :
    (uPow (-2) : LaurentSeries K) + toL r = uPow (-2) * toL (1 + X ^ 2 * r) := by
  rw [map_add, map_one, map_mul, map_pow, mul_add, mul_one, uPow_neg_two]
  congr 1
  linear_combination (-(toL X * uPow (-1) + 1) * toL r) * z_mul_zi (K := K)

theorem coeff_ofNat_mul (a : ℕ) [a.AtLeastTwo] (f : K⟦X⟧) (n : ℕ) :
    coeff n ((OfNat.ofNat a : K⟦X⟧) * f) = (OfNat.ofNat a : K) * coeff n f := by
  rw [(map_ofNat C a).symm, coeff_C_mul]

theorem coeff_X_mul_derivative (f : K⟦X⟧) (n : ℕ) :
    coeff n (X * derivative f) = (n : K) * coeff n f := by
  rcases n with _ | m
  simp
  rw [coeff_succ_X_mul, coeff_derivative]
  push_cast
  ring

theorem coeff_shift_zero {f : K⟦X⟧} (A : K⟦X⟧) {n m : ℕ} (hf : ∀ k < n, coeff k f = 0)
    (hm : 0 < m) : coeff n (X ^ m * (f * A)) = 0 := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [hf p.1 $ by omega, zero_mul]
  rfl

theorem derivative_X_sq_mul (t : K⟦X⟧) :
    derivative (X ^ 2 * t) = 2 * X * t + X ^ 2 * derivative t := by
  rw [pow_two, mul_assoc, Derivation.leibniz, Derivation.leibniz, derivative_X]
  simp [smul_eq_mul]
  ring

theorem derivative_X_mul (t : K⟦X⟧) :
    derivative (X * t) = t + X * derivative t := by
  rw [Derivation.leibniz, derivative_X]
  simp [smul_eq_mul]
  ring

theorem rescale_C' (a c : K) : rescale a (C c) = C c := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

theorem derivative_rescale_neg_one (r : K⟦X⟧) :
    derivative (rescale (-1 : K) r) = -rescale (-1 : K) (derivative r) := by
  ext n
  simp [coeff_derivative, coeff_rescale, map_neg]
  ring

def ClearedM (g2 g3 : K) (M : K⟦X⟧) : Prop :=
  (X * derivative M - 2 * M) ^ 2 = 4 * M ^ 3 - C g2 * X ^ 4 * M - C g3 * X ^ 6

def Cleared (g2 g3 : K) (r : K⟦X⟧) : Prop :=
  (-2 + X ^ 3 * derivative r) ^ 2 =
    4 * (1 + X ^ 2 * r) ^ 3 - C g2 * X ^ 4 * (1 + X ^ 2 * r) - C g3 * X ^ 6

theorem clearedM_of_ode {g2 g3 : K} {M : K⟦X⟧}
    (h : dL (uPow (-2) * toL M) ^ 2 = 4 * (uPow (-2) * toL M) ^ 3
      - HahnSeries.C g2 * (uPow (-2) * toL M) - HahnSeries.C g3) : ClearedM g2 g3 M := by
  have hd : dL (uPow (-2) * toL M : LaurentSeries K)
      = uPow (-1) ^ 2 * toL (derivative M) + (-2) * uPow (-1) ^ 3 * toL M := by
    rw [dL_mul, dL_toL, dL_uPow, C_neg_two, uPow_neg_two, uPow_neg_three]
    ring
  rw [hd, uPow_neg_two] at h
  have e := alg_first (toL X) (uPow $ -1) (toL M) (toL $ derivative M) (HahnSeries.C g2)
    (HahnSeries.C g3) z_mul_zi h
  unfold ClearedM
  apply toL_injective
  simp only [map_sub, map_mul, map_pow, map_ofNat, HahnSeries.ofPowerSeries_C]
  linear_combination e

theorem cleared_of_clearedM {g2 g3 : K} {r : K⟦X⟧} (h : ClearedM g2 g3 (1 + X ^ 2 * r)) :
    Cleared g2 g3 r := by
  unfold ClearedM at h
  unfold Cleared
  rw [map_add, Derivation.map_one_eq_zero, derivative_X_sq_mul] at h
  have e : X * (0 + (2 * X * r + X ^ 2 * derivative r)) - 2 * (1 + X ^ 2 * r)
      = -2 + X ^ 3 * derivative r := by ring
  rwa [e] at h

theorem cleared_of_ode {g2 g3 : K} {r : K⟦X⟧}
    (h : dL (uPow (-2) + toL r) ^ 2 = 4 * (uPow (-2) + toL r) ^ 3
      - HahnSeries.C g2 * (uPow (-2) + toL r) - HahnSeries.C g3) : Cleared g2 g3 r := by
  rw [add_eq_mul] at h
  exact cleared_of_clearedM $ clearedM_of_ode h

theorem cleared_main {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) :
    4 * (X * derivative r) + 12 * r =
      X ^ 2 * (C g2 + C g3 * X ^ 2 + C g2 * X ^ 2 * r - 12 * r ^ 2 - 4 * X ^ 2 * r ^ 3
        + X ^ 2 * derivative r ^ 2) := by
  unfold Cleared at h
  have hX : (X : K⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
  apply mul_left_cancel₀ hX
  linear_combination (-1 : K⟦X⟧) * h

theorem cleared_unique [CharZero K] {g2 g3 : K} {r s : K⟦X⟧} (hr : Cleared g2 g3 r)
    (hs : Cleared g2 g3 s) : r = s := by
  have key : ∀ n, coeff n (4 * (X * derivative (r - s)) + 12 * (r - s)) =
      coeff n (X ^ 4 * ((r - s) * C g2) + X ^ 2 * ((r - s) * (-12 * (r + s)))
        + X ^ 4 * ((r - s) * (-4 * (r ^ 2 + r * s + s ^ 2)))
        + X ^ 3 * ((X * derivative (r - s)) * (derivative r + derivative s))) := by
    intro n
    congr 1
    rw [map_sub]
    linear_combination (cleared_main hr) - cleared_main hs
  have main : ∀ n, (∀ k < n, coeff k (r - s) = 0) → coeff n (r - s) = 0 := by
    intro n hn
    have hn' : ∀ k < n, coeff k (X * derivative (r - s)) = 0 := by
      intro k hk
      rw [coeff_X_mul_derivative, hn k hk, mul_zero]
    have t4 := coeff_shift_zero (m := 3) (derivative r + derivative s) hn' $ by norm_num
    have e := key n
    simp only [map_add] at e
    rw [coeff_shift_zero (m := 4) (C g2) hn $ by norm_num, coeff_shift_zero (m := 2) (-12 * (r + s)) hn $ by norm_num, coeff_shift_zero (m := 4) (-4 * (r ^ 2 + r * s + s ^ 2)) hn $ by norm_num, t4, coeff_ofNat_mul, coeff_ofNat_mul, coeff_X_mul_derivative] at e
    have e2 : ((4 : K) * n + 12) * coeff n (r - s) = 0 := by linear_combination e
    have h4 : ((4 : K) * n + 12) ≠ 0 := by
      exact_mod_cast (show (4 * n + 12 : ℕ) ≠ 0 by omega)
    exact (mul_eq_zero.mp e2).resolve_left h4
  have all : ∀ n, coeff n (r - s) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih => exact main n ih
  rw [← sub_eq_zero]
  ext n
  rw [all n, map_zero]

theorem cleared_low [CharZero K] {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) :
    coeff 0 r = 0 ∧ coeff 1 r = 0 ∧ coeff 2 r = g2 / 20 ∧ coeff 4 r = g3 / 28 := by
  have E := cleared_main h
  have lhs : ∀ n, coeff n (4 * (X * derivative r) + 12 * r) = (4 * (n : K) + 12) * coeff n r := by
    intro n
    rw [map_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_X_mul_derivative]
    ring
  have r0 : coeff 0 r = 0 := by
    have e := congrArg (coeff 0) E
    rw [lhs, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 0))] at e
    have h12 : (4 * ((0 : ℕ) : K) + 12) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp e).resolve_left h12
  have r1 : coeff 1 r = 0 := by
    have e := congrArg (coeff 1) E
    rw [lhs, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 1))] at e
    have h16 : (4 * ((1 : ℕ) : K) + 12) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp e).resolve_left h16
  obtain ⟨t, rfl⟩ : X ^ 2 ∣ r := by
    rw [X_pow_dvd_iff]
    intro m hm
    interval_cases m <;> assumption
  have E2 : 4 * (X * derivative t) + 20 * t = C g2 + X ^ 2 * (C g3 + X ^ 2 * (C g2 * t - 12 * t ^ 2
      - 4 * X ^ 4 * t ^ 3 + (2 * t + X * derivative t) ^ 2)) := by
    have hX : (X : K⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [derivative_X_sq_mul] at E
    linear_combination E
  have lt : ∀ n, coeff n (4 * (X * derivative t) + 20 * t) = (4 * (n : K) + 20) * coeff n t := by
    intro n
    rw [map_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_X_mul_derivative]
    ring
  have f0 := congrArg (coeff 0) E2
  rw [lt, map_add, coeff_C, if_pos rfl, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 0))] at f0
  have f2 := congrArg (coeff 2) E2
  rw [lt, map_add, coeff_C, if_neg (by norm_num : (2 : ℕ) ≠ 0), coeff_X_pow_mul', if_pos (le_refl 2),
    Nat.sub_self, map_add, coeff_C, if_pos rfl, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 0))] at f2
  push_cast at f0 f2
  refine ⟨r0, r1, ?_, ?_⟩
  rw [coeff_X_pow_mul', if_pos (le_refl 2), Nat.sub_self, eq_div_iff (by norm_num)]
  linear_combination f0
  rw [coeff_X_pow_mul', if_pos (by norm_num : 2 ≤ 4), show 4 - 2 = 2 from rfl, eq_div_iff (by norm_num)]
  linear_combination f2

theorem cleared_neg {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) :
    Cleared g2 g3 $ rescale (-1 : K) r := by
  unfold Cleared at h ⊢
  have e := congrArg (rescale (-1 : K)) h
  simp [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, rescale_X,
    rescale_C'] at e
  rw [derivative_rescale_neg_one]
  linear_combination e

theorem cleared_odd [CharZero K] {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) (n : ℕ)
    (hn : Odd n) : coeff n r = 0 := by
  have e1 := congrArg (coeff n) $ cleared_unique (cleared_neg h) h
  rw [coeff_rescale, hn.neg_one_pow] at e1
  exact (mul_eq_zero.mp $ by linear_combination (-1 : K) * e1).resolve_left two_ne_zero

theorem second_cleared {c : K} {r : K⟦X⟧}
    (h : dL (dL $ uPow (-2) + toL r) = 6 * (uPow (-2) + toL r) ^ 2 - HahnSeries.C c) :
    X ^ 2 * derivative (derivative r) = 12 * r + X ^ 2 * (6 * (r * r)) - X ^ 2 * C c := by
  rw [map_add, dL_uPow, dL_toL] at h
  rw [map_add, dL_mul, dL_C, dL_uPow, dL_toL] at h
  rw [C_neg_two, C_neg_three, uPow_neg_four, mul_zero, add_zero, uPow_neg_two] at h
  have e := alg_second (toL X) (uPow $ -1) (toL r) (toL $ derivative $ derivative r)
    (HahnSeries.C c) z_mul_zi h
  apply toL_injective
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, HahnSeries.ofPowerSeries_C]
  linear_combination e

theorem sum_even (a : ℕ → K) (h0 : a 0 = 0) (hodd : ∀ n, Odd n → a n = 0) (q : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * q), a p.1 * a p.2 =
      ∑ i ∈ Finset.Icc 1 (q - 1), a (2 * i) * a (2 * (q - i)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  dsimp only
  have himg : ∑ i ∈ Finset.Icc 1 (q - 1), a (2 * i) * a (2 * (q - i))
      = ∑ k ∈ (Finset.Icc 1 $ q - 1).image fun i => 2 * i, a k * a (2 * q - k) := by
    rw [Finset.sum_image fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    omega
  rw [himg]
  symm
  apply Finset.sum_subset
  intro k hk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
  rw [Finset.mem_Icc] at hi
  rw [Finset.mem_range]
  omega
  intro k hk hk'
  rw [Finset.mem_range] at hk
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | hko
  by_cases hj0 : j = 0
  rw [show k = 0 by omega, h0, zero_mul]
  by_cases hjq : j = q
  rw [show 2 * q - k = 0 by omega, h0, mul_zero]
  exfalso
  apply hk'
  exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  rw [hodd k hko, zero_mul]

theorem recursion_of [CharZero K] {c : K} {r : K⟦X⟧}
    (h : X ^ 2 * derivative (derivative r) = 12 * r + X ^ 2 * (6 * (r * r)) - X ^ 2 * C c)
    (h0 : coeff 0 r = 0) (hodd : ∀ n, Odd n → coeff n r = 0) (q : ℕ) (hq : 1 ≤ q) :
    ((q : K) - 1) * (2 * (q : K) + 5) * coeff (2 * q + 2) r =
      3 * ∑ i ∈ Finset.Icc 1 (q - 1), coeff (2 * i) r * coeff (2 * (q - i)) r := by
  have h2 : 2 ≤ 2 * q + 2 := by omega
  have h3 : 2 * q + 2 - 2 = 2 * q := by omega
  have h4 : 2 * q ≠ 0 := by omega
  have e := congrArg (coeff $ 2 * q + 2) h
  simp only [map_sub, map_add, coeff_X_pow_mul', if_pos h2, h3, coeff_ofNat_mul, coeff_derivative,
    coeff_C, if_neg h4, sub_zero] at e
  rw [show 2 * q + 1 + 1 = 2 * q + 2 by omega] at e
  rw [coeff_ofNat_mul, coeff_ofNat_mul, coeff_mul, sum_even (coeff · r) h0 hodd q] at e
  push_cast at e
  linear_combination (1 / 2 : K) * e

theorem wpL_eq (hE : ExpSpec.{u}) [CharZero K] (W : WeierstrassCurve K) :
    ∃ M, constantCoeff M = 1 ∧ wpL W = uPow (-2) * toL M := by
  obtain ⟨e0, e1, -⟩ := hE K W
  have hs := HasSubst.of_constantCoeff_zero' e0
  obtain ⟨E, hE'⟩ := X_dvd_iff.mpr e0
  have hE0 : constantCoeff E = 1 := by
    rw [hE'] at e1
    have := coeff_succ_X_mul 0 E
    rw [zero_add, e1] at this
    rw [← coeff_zero_eq_constantCoeff_apply, ← this]
  have hEi := PowerSeries.mul_inv_cancel E (by rw [hE0]; exact one_ne_zero)
  have hEi0 : constantCoeff E⁻¹ = 1 := by
    have := congrArg constantCoeff hEi
    rwa [map_mul, hE0, one_mul, map_one] at this
  have hinv : (toL $ expSer W)⁻¹ = uPow (-1) * toL E⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [hE', map_mul]
    have := congrArg toL hEi
    rw [map_mul, map_one] at this
    linear_combination toL E * toL E⁻¹ * z_mul_zi (K := K) + this
  obtain ⟨T, hT⟩ : X ∣ xS W - 1 :=
    X_dvd_iff.mpr $ by rw [map_sub, CurveSer.xS_cc, map_one, sub_self]
  have hT' : xS W = 1 + X * T := by linear_combination hT
  have hx0 : constantCoeff ((xS W).subst (expSer W)) = 1 := by
    rw [hT', ← coe_substAlgHom hs, map_add, map_one, map_mul, coe_substAlgHom, subst_X hs,
      map_add, map_one, map_mul, e0, zero_mul, add_zero]
  refine ⟨E⁻¹ ^ 2 * (xS W).subst (expSer W) + C (W.b₂ / 12) * X ^ 2, ?_, ?_⟩
  rw [map_add, map_mul, map_pow, hEi0, hx0, map_mul, map_pow, constantCoeff_X]
  simp
  rw [wpL, xZ, hinv, map_add, map_mul, map_mul, map_pow, map_pow, toL_C, uPow_neg_two]
  linear_combination
    (-HahnSeries.C (W.b₂ / 12) * (toL X * uPow (-1) + 1)) * z_mul_zi (K := K)

theorem wpL_shape (hE : ExpSpec.{u}) (hO : WpODE.{u}) [CharZero K] (W : WeierstrassCurve K) :
    wpL W = uPow (-2) + toL (wpReg W) ∧ Cleared (g₂ W) (g₃ W) (wpReg W) := by
  obtain ⟨M, hM1, hM⟩ := wpL_eq hE W
  have hode := (hO K W).2.1
  rw [hM] at hode
  have hC := clearedM_of_ode hode
  obtain ⟨M1, hM1'⟩ : X ∣ M - 1 := by
    rw [X_dvd_iff, map_sub, hM1, map_one, sub_self]
  have hMe : M = 1 + X * M1 := by
    rw [← hM1']
    ring
  rw [hMe] at hC
  unfold ClearedM at hC
  rw [map_add, Derivation.map_one_eq_zero, derivative_X_mul] at hC
  have key : X * (8 * M1 - X * (-4 * derivative M1 - 11 * M1 ^ 2 - 2 * X * M1 * derivative M1
      + X ^ 2 * derivative M1 ^ 2 - 4 * X * M1 ^ 3 + C (g₂ W) * X ^ 2 * (1 + X * M1)
      + C (g₃ W) * X ^ 4)) = 0 := by
    linear_combination (-1 : K⟦X⟧) * hC
  have hc : constantCoeff M1 = 0 := by
    have e := congrArg constantCoeff $ (mul_eq_zero.mp key).resolve_left X_ne_zero
    rw [map_sub, map_mul, map_mul, constantCoeff_X, zero_mul, sub_zero, map_ofNat, map_zero] at e
    apply (mul_eq_zero.mp e).resolve_left
    norm_num
  obtain ⟨M2, hM2⟩ : X ∣ M1 := X_dvd_iff.mpr hc
  have hL : wpL W = uPow (-2) + toL M2 := by
    rw [hM, hMe, hM2, show (1 : K⟦X⟧) + X * (X * M2) = 1 + X ^ 2 * M2 by ring, add_eq_mul]
  have hR : wpReg W = M2 := by
    ext n
    rw [wpReg, coeff_mk, hL]
    first
    | simp [uPow, show (n : ℤ) ≠ -2 by omega]
    | simp [uPow, HahnSeries.single_coeff_of_ne, show (n : ℤ) ≠ -2 by omega]
    | simp [uPow, show (n : ℤ) ≠ -2 by omega]
  constructor
  rwa [hR]
  rw [hR]
  apply cleared_of_ode
  rw [← hL]
  exact (hO K W).2.1

end WpSh

open WpSh


theorem wpShape_of (hE : ExpSpec.{u}) (hO : WpODE.{u}) : WpShape.{u} := by
  intro K _ _ W
  obtain ⟨h1, h2⟩ := wpL_shape hE hO W
  obtain ⟨a, _, c, d⟩ := cleared_low h2
  exact ⟨h1, a, fun n hn => cleared_odd h2 n hn, c, d⟩

theorem wpCleared_of (hE : ExpSpec.{u}) (hO : WpODE.{u}) : WpCleared.{u} := by
  intro K _ _ W
  obtain ⟨_, h2⟩ := wpL_shape hE hO W
  refine ⟨?_, fun n hn => cleared_odd h2 n hn, h2⟩
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact (cleared_low h2).1

theorem wpRecursion_of (hE : ExpSpec.{u}) (hO : WpODE.{u}) : WpRecursion.{u} := by
  intro K _ _ W k hk
  obtain ⟨h1, h2⟩ := wpL_shape hE hO W
  have hs := (hO K W).2.2
  rw [h1] at hs
  have e := recursion_of (second_cleared hs) (cleared_low h2).1 (cleared_odd h2) (k - 1)
    $ by omega
  have k1 : k - 1 - 1 = k - 2 := by omega
  have k2 : 2 * (k - 1) + 2 = 2 * k := by omega
  have k3 : ((k - 1 : ℕ) : K) = (k : K) - 1 := by
    rw [Nat.cast_sub $ by omega, Nat.cast_one]
  rw [k1, k2, k3] at e
  linear_combination e

end Formalism.L2.Th1.A
end
section
namespace Formalism.L2.Th1.A

theorem compInvSpec : CompInvSpec.{u} := composition_inverse_spec
theorem compInvMap : CompInvMap.{u, v} := composition_inverse_map
theorem integSpec : IntegSpec.{u} := integration_spec

theorem flowNegUW : FlowNegUW.{u} := chartFlowNegation
theorem chordRegular : ChordRegular.{u} := chordFormula
theorem flowLogDeriv : FlowLogDeriv.{u} := flowLogDerivative

theorem wSerSpec : WSerSpec.{u} := w_series_spec
theorem wSerFactor : WSerFactor.{u} := w_series_factorization
theorem unitSpec : UnitSpec.{u} := invariant_differential_units
theorem seriesMap : SeriesMap.{u, v} := series_map
theorem flowU : FlowU.{u} := unit_flow
theorem dLSpec : DLSpec.{u} := invariant_derivation_spec
theorem flowL : FlowL.{u} := invariant_flow
theorem iSerSpec : ISerSpec.{u} := iSerSpec_of wSerSpec wSerFactor unitSpec flowU flowNegUW

theorem logSpec : LogSpec.{u} := logSpec_of integSpec unitSpec
theorem expSpec : ExpSpec.{u} := expSpec_of integSpec compInvSpec unitSpec
theorem chainZ : ChainZ.{u} := chainZ_of integSpec compInvSpec unitSpec
theorem logNeg : LogNeg.{u} := logNeg_of integSpec compInvSpec unitSpec iSerSpec
theorem flowZ : FlowZ.{u} := flowZ_of expSpec chainZ
theorem wpODE : WpODE.{u} := wpODE_of expSpec chainZ

theorem fglMap : FglMap.{u, v} := formal_group_map
theorem fglChord : FglChord.{u} := formal_group_chord
theorem fglSum : FglSum.{u} := formal_group_sum

theorem plusFlow : PlusFlow.{u} := plusFlow_of dLSpec flowL
theorem plusMap : PlusMap.{u, v} := addition_map

end Formalism.L2.Th1.A
end
section
namespace Formalism.L2.Th1.A

theorem wpShape : WpShape.{u} := wpShape_of expSpec wpODE
theorem wpCleared : WpCleared.{u} := wpCleared_of expSpec wpODE
theorem wpRecursion : WpRecursion.{u} := wpRecursion_of expSpec wpODE

theorem fglLog : FglLog.{u} := formal_group_logarithm

theorem zSerMap : ZSerMap.{u, v} := z_series_map
theorem halfSpec : HalfSpec.{u} := halfSpec_of fglLog
theorem halfLog : HalfLog.{u, v} := halfLog_of fglLog fglLog

end Formalism.L2.Th1.A
end
section
open PowerSeries


namespace Formalism.L2.Th1.A

theorem short_weierstrass_inverse : ShortInv := by
  unfold ShortInv
  intro K _ _ g2 g3
  refine ⟨?_, ?_, ?_, ?_⟩
  simp only [shortW, WeierstrassCurve.b₂]
  ring
  unfold g₂
  simp only [shortW, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring
  unfold g₃
  simp only [shortW, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring
  simp only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

namespace BridgeK

open Formalism.L2.Th1.CM

theorem cW_eq {K : Type} [Field K] (g2 g3 : K) (k : ℕ) :
    cW g2 g3 k = if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
      if 4 ≤ k then
        3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
          ∑ m : Fin $ k - 3, cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
      else 0 := by
  conv_lhs => unfold cW
  rw [Nat.strongRecOn_eq]
  simp [dite_eq_ite]
  rfl


theorem cW_succ (hS : WpShape.{0}) (hR : WpRecursion.{0}) {K : Type} [Field K] [CharZero K]
    (W : WeierstrassCurve K) (k : ℕ) :
    cW (g₂ W) (g₃ W) (k + 1) = coeff (2 * k) (wpReg W) := by
  obtain ⟨_, h0, _, h2, h4⟩ := hS K W
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    interval_cases k
    rw [cW_eq]
    simp [h0]
    rw [cW_eq]
    simp [h2]
    rw [cW_eq]
    simp [h4]
    have hrec := hR K W k hk
    rw [cW_eq, if_neg $ show k + 1 ≠ 2 by omega, if_neg $ show k + 1 ≠ 3 by omega,
      if_pos $ show 4 ≤ k + 1 by omega]
    have hsum : (∑ m : Fin $ k + 1 - 3, cW (g₂ W) (g₃ W) (m.val + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m.val + 2)))
        = ∑ i ∈ Finset.Icc 1 (k - 2), coeff (2 * i) (wpReg W) * coeff (2 * (k - 1 - i)) (wpReg W) := by
      rw [Fin.sum_univ_eq_sum_range (fun m => cW (g₂ W) (g₃ W) (m + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m + 2)))
        $ k + 1 - 3]
      refine Finset.sum_nbij' (fun m => m + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
      intro a ha
      rw [Finset.mem_range] at ha
      rw [Finset.mem_Icc]
      omega
      intro a ha
      rw [Finset.mem_Icc] at ha
      rw [Finset.mem_range]
      omega
      intro a _
      omega
      intro a ha
      rw [Finset.mem_Icc] at ha
      omega
      intro m hm
      rw [Finset.mem_range] at hm
      rw [show m + 2 = m + 1 + 1 by omega, show k + 1 - (m + 1 + 1) = k - 2 - m + 1 by omega,
        ih (m + 1) $ by omega, ih (k - 2 - m) $ by omega, show k - 1 - (m + 1) = k - 2 - m by omega]
    rw [hsum]
    have hne1 : (2 * ((k : K) + 1) + 1) ≠ 0 := by
      have e : ((2 * k + 3 : ℕ) : K) = 2 * ((k : K) + 1) + 1 := by
        push_cast
        ring
      rw [← e]
      exact_mod_cast (show 2 * k + 3 ≠ 0 by omega)
    have hne2 : ((k : K) + 1 - 3) ≠ 0 := by
      have e : ((k - 2 : ℕ) : K) = (k : K) + 1 - 3 := by
        push_cast [Nat.cast_sub $ show 2 ≤ k by omega]
        ring
      rw [← e]
      exact_mod_cast (show k - 2 ≠ 0 by omega)
    push_cast
    rw [div_mul_eq_mul_div, div_eq_iff $ mul_ne_zero hne1 hne2]
    linear_combination -hrec


end BridgeK

open BridgeK Formalism.L2.Th1.CM in
theorem wpNumEq_of (hS : WpShape.{0}) (hR : WpRecursion.{0}) : WpNumEq := by
  unfold WpNumEq
  intro K _ _ W
  obtain ⟨_, h0, hodd, _, _⟩ := hS K W
  constructor
  ext n
  unfold wpNum
  rw [coeff_mk, map_add, coeff_one, coeff_X_pow_mul']
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  rcases Nat.lt_or_ge j 1 with hj | hj
  interval_cases j
  simp
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [if_neg (show 2 * (i + 1) ≠ 0 by omega), if_pos (even_two_mul (i + 1)),
    if_neg (show 2 * (i + 1) ≠ 0 by omega), if_pos (show 2 ≤ 2 * (i + 1) by omega),
    Nat.mul_div_cancel_left (i + 1) (by norm_num : 0 < 2),
    show 2 * (i + 1) - 2 = 2 * i by omega, cW_succ hS hR W i, zero_add]
  rw [if_neg (show 2 * j + 1 ≠ 0 by omega),
    if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)),
    if_neg (show 2 * j + 1 ≠ 0 by omega), zero_add]
  split_ifs with h
  rw [show 2 * j + 1 - 2 = 2 * (j - 1) + 1 by omega, hodd _ (odd_two_mul_add_one (j - 1))]
  rfl
  ext n
  unfold wpDen
  rw [coeff_mk, map_sub, coeff_one, mul_assoc (C (1 / 2 : K)) (X ^ 3) (derivative (wpReg W)),
    coeff_C_mul, coeff_X_pow_mul']
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  rcases Nat.lt_or_ge j 2 with hj | hj
  interval_cases j <;> simp
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 + 1 := ⟨j - 2, by omega⟩
  rw [if_neg (show 2 * (i + 1 + 1) ≠ 0 by omega), if_pos (even_two_mul (i + 1 + 1)),
    if_neg (show 2 * (i + 1 + 1) ≠ 0 by omega), if_pos (show 3 ≤ 2 * (i + 1 + 1) by omega),
    Nat.mul_div_cancel_left (i + 1 + 1) (by norm_num : 0 < 2),
    show 2 * (i + 1 + 1) - 3 = 2 * i + 1 by omega, coeff_derivative,
    show 2 * i + 1 + 1 = 2 * (i + 1) by ring, cW_succ hS hR W (i + 1)]
  push_cast
  ring
  rw [if_neg (show 2 * j + 1 ≠ 0 by omega),
    if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)),
    if_neg (show 2 * j + 1 ≠ 0 by omega)]
  split_ifs with h
  rw [show 2 * j + 1 - 3 = 2 * (j - 1) by omega, coeff_derivative,
    hodd _ (odd_two_mul_add_one (j - 1))]
  ring
  ring


theorem uSerEq_of (hS : WpShape.{0}) (hR : WpRecursion.{0}) : USerEq := by
  intro K _ _ g2 g3
  obtain ⟨hb, hg2, hg3, -⟩ := short_weierstrass_inverse K g2 g3
  set W := shortW g2 g3 with hW
  obtain ⟨hnum, hden⟩ := wpNumEq_of hS hR K W
  rw [hg2, hg3] at hnum hden
  obtain ⟨hshape, -⟩ := hS K W
  obtain ⟨hd, -⟩ := wpODE.{0} K W
  obtain ⟨-, hfl⟩ := flowZ.{0} K W
  have hx : wpL W = xZ W := by
    rw [wpL, hb]
    simp
  have ha1 : W.a₁ = 0 := rfl
  have ha3 : W.a₃ = 0 := rfl
  rw [ha1, ha3, map_zero, zero_mul, add_zero, add_zero] at hd

  have hrel : toL (expSer W) * dL (wpL W) = -2 * wpL W := by
    rw [hd, hx]
    linear_combination 2 * hfl
  rw [hshape, map_add, dL_uPow, dL_toL] at hrel
  have h3 : (uPow (-2 - 1) : LaurentSeries K) * toL (X ^ 3) = 1 := by
    rw [← uPow_natCast]
    exact uPow_neg_mul 3
  have h2 : (uPow (-2) : LaurentSeries K) * toL (X ^ 3) = toL X := by
    rw [← uPow_natCast, ← uPow_add, ← uPow_one]
    norm_num
  have hC : (HahnSeries.C (((-2 : ℤ)) : K) : LaurentSeries K) = toL (C (-2 : K)) := by
    rw [toL_C]
    norm_num
  have hps : expSer W * (C (-2 : K) + X ^ 3 * derivative (wpReg W)) =
      C (-2 : K) * (X + X ^ 3 * wpReg W) := by
    apply toL_injective
    have hm2 : (toL (C (-2 : K)) : LaurentSeries K) = -2 := by
      rw [map_neg C, map_neg toL]
      congr 1
      rw [map_ofNat C, map_ofNat toL]
    simp only [map_mul, map_add]
    rw [hC] at hrel
    linear_combination toL (X ^ 3) * hrel - toL (expSer W) * toL (C (-2 : K)) * h3 - 2 * h2
      - (toL X + toL (X ^ 3) * toL (wpReg W)) * hm2
  have hab : (C (1 / 2 : K) : K⟦X⟧) * C (-2 : K) = -1 := by
    rw [← map_mul]
    norm_num
  have hcc : constantCoeff (CM.wpDen g2 g3) ≠ 0 := by
    rw [hden]
    simp
  symm
  rw [CM.uSer, eq_mul_inv_iff_mul_eq hcc, hnum, hden]
  linear_combination -(C (1 / 2 : K) : K⟦X⟧) * hps + (expSer W - X - X ^ 3 * wpReg W) * hab

end Formalism.L2.Th1.A
end
section
open PowerSeries (coeff_map map)
open PowerSeries



namespace Formalism.L2.Th1.A

namespace More

section Tools

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem map_derivative (φ : R →+* S) (f : R⟦X⟧) :
    map φ (derivative f) = derivative (map φ f) := by
  ext n
  simp [PowerSeries.coeff_derivative, coeff_map]


variable (W : WeierstrassCurve R)

end Tools

end More

open More

namespace More

end More

namespace More

end More

namespace More


end More




namespace More

variable {K : Type u} [Field K] (W : WeierstrassCurve K) (S : Subring K)




end More



namespace More

variable {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L)

theorem map_integ (f : K⟦X⟧) : map φ (integ f) = integ (map φ f) := by
  ext n
  simp [integ, coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp [map_div₀]

theorem map_logSer (W : WeierstrassCurve K) :
    map φ (logSer W) = logSer (W.map φ) := by
  rw [logSer, map_integ, CurveSer.map_om, logSer]

theorem map_g₂ (W : WeierstrassCurve K) : φ (g₂ W) = g₂ (W.map φ) := by
  simp [g₂, map_div₀, WeierstrassCurve.map_c₄, map_ofNat]

theorem map_g₃ (W : WeierstrassCurve K) : φ (g₃ W) = g₃ (W.map φ) := by
  simp [g₃, map_div₀, WeierstrassCurve.map_c₆, map_ofNat]

theorem map_cleared {g2 g3 : K} {r : K⟦X⟧} (h : WpSh.Cleared g2 g3 r) :
    WpSh.Cleared (φ g2) (φ g3) $ map φ r := by
  unfold WpSh.Cleared at h ⊢
  simpa [map_derivative, PowerSeries.map_X, PowerSeries.map_C, map_ofNat] using (congrArg (map φ) h)

end More

theorem z_series_map_spec : ZMap.{u, v} := by
  intro K L _ _ _ _ φ W
  obtain ⟨l0, l1, -⟩ := logSpec K W
  refine ⟨map_logSer φ W, ?_, ?_, map_g₂ φ W, map_g₃ φ W⟩
  rw [expSer, compInvMap K L φ (logSer W) l0 (by rw [l1]; exact isUnit_one), map_logSer, expSer]
  have h1 := map_cleared φ (WpSh.wpL_shape expSpec wpODE W).2
  rw [map_g₂, map_g₃] at h1
  exact WpSh.cleared_unique h1 (WpSh.wpL_shape expSpec wpODE $ W.map φ).2

end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

namespace CubeR

open Univ CurveSer
local notation "cc" => MvPowerSeries.constantCoeff

section Tools

variable {σ : Type*} {A : Type u} {B : Type v} [CommRing A] [CommRing B]

theorem pair_vector_map (φ : A →+* B) (a b : MvPowerSeries σ A) :
    (fun i => MvPowerSeries.map φ $ (![a, b] : Fin 2 → MvPowerSeries σ A) i)
      = ![MvPowerSeries.map φ a, MvPowerSeries.map φ b] := by
  funext i
  fin_cases i <;> rfl

theorem hasSubst2 {a b : MvPowerSeries σ A} (ha : cc a = 0) (hb : cc b = 0) :
    MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ A) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero $ Fin.forall_fin_two.2 ⟨ha, hb⟩

theorem map_formal_group_subst (φ : A →+* B) (W : WeierstrassCurve A) {a b : MvPowerSeries σ A}
    (ha : cc a = 0) (hb : cc b = 0) :
    MvPowerSeries.map φ (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ A) $ fgl W)
      = MvPowerSeries.subst
          (![MvPowerSeries.map φ a, MvPowerSeries.map φ b] : Fin 2 → MvPowerSeries σ B)
          (fgl $ W.map φ) := by
  rw [MvPowerSeries.map_subst $ hasSubst2 ha hb, pair_vector_map, Fgl1.fgl_map]


theorem iSer_cc (W : WeierstrassCurve A) : constantCoeff (iSer W) = 0 := by
  simp [iSer]

theorem iSer_subst_cc (W : WeierstrassCurve A) {a : MvPowerSeries σ A} (ha : cc a = 0) :
    cc ((iSer W).subst a) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha _ $ iSer_cc W

theorem inv_wU_subst {K : Type u} [Field K] (W : WeierstrassCurve K) {a : MvPowerSeries σ K}
    (ha : cc a = 0) : ((Formalism.ELL.wU $ wSer W).subst a)⁻¹ = (xS W).subst a := by
  have hs := HasSubst.of_constantCoeff_zero ha
  have h1 : (xS W).subst a * (wU W).subst a = 1 := by
    rw [← subst_mul hs, mul_comm, wU_mul_xS, ← coe_substAlgHom hs, map_one]
  have h0 : cc ((wU W).subst a) ≠ 0 := by
    intro h
    have := congrArg cc h1
    rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  exact (MvPowerSeries.inv_eq_iff_mul_eq_one h0).2 h1


theorem invSer_eq {K : Type u} [Field K] (W : WeierstrassCurve K) :
    Formalism.ELL.invSer W (wSer W) = iSer W := by
  unfold Formalism.ELL.invSer iSer
  rw [PowerSeries.invOfUnit_eq' (iDen W) (-1) $ by rw [iDen_cc, Units.val_neg, Units.val_one]]
  rfl

theorem mem_range {x : K₀} (hx : x ∈ Formalism.ELL.coeffRing WK) : ∃ z : Z, ι z = x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [⟨W₀.a₁, rfl⟩, ⟨W₀.a₂, rfl⟩, ⟨W₀.a₃, rfl⟩, ⟨W₀.a₄, rfl⟩, ⟨W₀.a₆, rfl⟩]
  | algebraMap r => exact ⟨(r : Z), by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩

theorem lift (c : MvPowerSeries σ K₀) (h : ∀ d, MvPowerSeries.coeff d c ∈ Formalism.ELL.coeffRing WK) :
    ∃ c₀ : MvPowerSeries σ Z, MvPowerSeries.map ι c₀ = c := by
  choose f hf using fun d => mem_range $ h d
  use f
  ext d
  exact (MvPowerSeries.coeff_map ι d (f : MvPowerSeries σ Z)).trans $ hf d

theorem lift_cc {c₀ : MvPowerSeries σ Z} (h : cc (MvPowerSeries.map ι c₀) = -1) : cc c₀ = -1 := by
  apply ι_injective
  rw [MvPowerSeries.constantCoeff_map] at h
  rw [h, map_neg, map_one]

end Tools

section Two

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] (W : WeierstrassCurve A)

def lhs2 : MvPowerSeries (Fin 2) A :=
  U₂ ^ 2 * (xS W).subst (U₁ : MvPowerSeries (Fin 2) A)
    - U₁ ^ 2 * (xS W).subst (U₂ : MvPowerSeries (Fin 2) A)

def diff2 : MvPowerSeries (Fin 2) A :=
  MvPowerSeries.subst
    (![U₁, (iSer W).subst (U₂ : MvPowerSeries (Fin 2) A)] : Fin 2 → MvPowerSeries (Fin 2) A) $ fgl W

theorem map_quadratic_lhs (φ : A →+* B) : MvPowerSeries.map φ (lhs2 W) = lhs2 (W.map φ) := by
  unfold lhs2
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, PowerSeries.map_subst $ HasSubst.X 0,
    PowerSeries.map_subst $ HasSubst.X 1, map_xS, MvPowerSeries.map_X, MvPowerSeries.map_X]

theorem map_diff2 (φ : A →+* B) : MvPowerSeries.map φ (diff2 W) = diff2 (W.map φ) := by
  unfold diff2
  rw [map_formal_group_subst φ W (MvPowerSeries.constantCoeff_X 0)
    $ iSer_subst_cc W $ MvPowerSeries.constantCoeff_X 1, PowerSeries.map_subst $ HasSubst.X 1,
    map_iSer, MvPowerSeries.map_X, MvPowerSeries.map_X]

theorem two_univ : ∃ c, cc c = -1 ∧ lhs2 W₀ = c * fgl W₀ * diff2 W₀ := by
  obtain ⟨c, hc, hc0, h⟩ := Formalism.ELL.cubeTwo K₀ WK (wSer WK) (fgl WK) (wSer_fixed WK)
    (Fgl1.fgl_cc WK) $ fglSum K₀ WK
  obtain ⟨c₀, rfl⟩ := lift c hc
  refine ⟨c₀, lift_cc hc0, mv_map_injective ι ι_injective ?_⟩
  rw [inv_wU_subst WK $ MvPowerSeries.constantCoeff_X 0,
    inv_wU_subst WK $ MvPowerSeries.constantCoeff_X 1, invSer_eq] at h
  rwa [map_mul, map_mul, map_quadratic_lhs, map_diff2, Fgl1.fgl_map]

end Two

section Three

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] (W : WeierstrassCurve A)






end Three

end CubeR

open CubeR Univ

theorem cube_two_relation : CubeTwoR.{u} := by
  intro R _ W
  obtain ⟨c, hc, h⟩ := two_univ
  refine ⟨MvPowerSeries.map (φ_of W) c, ?_, ?_⟩
  rw [MvPowerSeries.constantCoeff_map, hc, map_neg, map_one]
  have := congrArg (MvPowerSeries.map $ φ_of W) h
  rwa [map_mul, map_mul, map_quadratic_lhs, map_diff2, Fgl1.fgl_map, map_eq] at this


theorem coeffMem_of (hZ : ZSerMap.{u, u}) (hH : HalfLog.{u, u}) : CoeffMem.{u} := by
  intro R _ W S h1 h2 h3 h4 h6
  let WS : WeierstrassCurve S := ⟨⟨W.a₁, h1⟩, ⟨W.a₂, h2⟩, ⟨W.a₃, h3⟩, ⟨W.a₄, h4⟩, ⟨W.a₆, h6⟩⟩
  have hW : WS.map S.subtype = W := by ext <;> rfl
  have key : ∀ f g, PowerSeries.map S.subtype f = g → ∀ n, coeff n g ∈ S := by
    rintro f g rfl n
    rw [coeff_map]
    exact (coeff n f).2
  obtain ⟨m1, -, m3, m4, m5, -, m7, m8⟩ := seriesMap S R S.subtype WS
  rw [hW] at m1 m3 m4 m5 m7 m8
  refine ⟨key _ _ m1, key _ _ m3, key _ _ m4, key _ _ m5, key _ _ m7, key _ _ m8, ?_, ?_, ?_, ?_, ?_⟩
  intro d
  have := fglMap S R S.subtype WS
  rw [hW] at this
  rw [← this, MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff d $ fgl WS).2
  intro k
  have := hZ S R S.subtype WS k
  rw [hW] at this
  exact key _ _ this
  rintro ⟨h, hh, h2h⟩
  have := hH.2 S R S.subtype WS $ by
      refine IsUnit.of_mul_eq_one (⟨h, hh⟩ : S) ?_
      apply Subtype.ext
      exact h2h
  rw [hW] at this
  exact key _ _ this
  intro xP hx
  have := (plusMap S R S.subtype WS ⟨xP, hx⟩ 0).1
  rw [hW] at this
  exact key _ _ this
  intro xP hx yP hy n
  obtain ⟨-, p2, p3⟩ := plusMap S R S.subtype WS ⟨xP, hx⟩ ⟨yP, hy⟩
  rw [hW] at p2 p3
  constructor
  exact key _ _ p2 n
  exact key _ _ p3 n
end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A


namespace Two

variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem e0 : constantCoeff (expSer W) = 0 := by
  unfold expSer compInv
  split_ifs with h
  exact h.choose_spec.1
  simp

theorem he : HasSubst $ expSer W := PowerSeries.HasSubst.of_constantCoeff_zero' $ e0 W

theorem toL_exp_ne : toL (expSer W) ≠ 0 := by
  intro h
  have h1 := (expSpec K W).2.1
  rw [(map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h, map_zero] at h1
  exact zero_ne_one h1

theorem exp_mul_inv : toL (expSer W) * (toL $ expSer W)⁻¹ = 1 := mul_inv_cancel₀ $ toL_exp_ne W

theorem uPow_mul_sq : (uPow (-2) : LaurentSeries K) * toL X ^ 2 = 1 := by
  simp only [uPow]
  rw [← map_pow, HahnSeries.ofPowerSeries_X_pow, HahnSeries.single_mul_single]
  norm_num [HahnSeries.single_zero_one]

theorem tS_mul (xP : K) :
    toL ((tS W xP).subst (expSer W)) * (xZ W - HahnSeries.C xP) = 1 := by
  have hc : constantCoeff (tDen W xP) = 1 := by
    simp [tDen, xS, PowerSeries.constantCoeff_invOfUnit]
  have hC : (C xP : K⟦X⟧).subst (expSer W) = C xP := by
    rw [← PowerSeries.coe_substAlgHom $ he W]
    exact (PowerSeries.substAlgHom $ he W).commutes xP
  have ht : (xS W).subst (expSer W) = (tDen W xP).subst (expSer W) + C xP * expSer W ^ 2 := by
    rw [tDen, ← PowerSeries.coe_substAlgHom $ he W, map_sub, map_mul, map_pow,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_X $ he W, hC]
    ring
  have h1 : toL ((tDen W xP).subst (expSer W)) * toL ((invOfUnit (tDen W xP) 1).subst (expSer W)) = 1 := by
    rw [← map_mul, ← PowerSeries.coe_substAlgHom $ he W, ← map_mul, PowerSeries.mul_invOfUnit _ _ $ by simpa using hc, map_one, map_one]
  have hE := mul_inv_cancel₀ $ toL_exp_ne W
  have hs : (tS W xP).subst (expSer W) = expSer W ^ 2 * (invOfUnit (tDen W xP) 1).subst (expSer W) := by
    rw [tS, ← PowerSeries.coe_substAlgHom $ he W, map_mul, map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X $ he W]
  rw [hs, xZ, ht]
  simp only [map_add, map_mul, map_pow, HahnSeries.ofPowerSeries_C]
  linear_combination (toL (expSer W) * (toL $ expSer W)⁻¹ + 1) * (toL ((invOfUnit (tDen W xP) 1).subst (expSer W)) * toL ((tDen W xP).subst (expSer W)) + HahnSeries.C xP * toL ((invOfUnit (tDen W xP) 1).subst (expSer W)) * toL (expSer W) ^ 2) * hE + h1

theorem chordZ {xP yP : K} (hP : W.toAffine.Equation xP yP) :
    toL ((xPlus W xP yP).subst (expSer W)) = (curveL W).toAffine.addX (xZ W) (HahnSeries.C xP)
      ((yZ W - HahnSeries.C yP) * toL ((tS W xP).subst (expSer W))) := by
  obtain ⟨hX, -⟩ := chordRegular _ (curveL W) (xZ W) (yZ W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL ((tS W xP).subst (expSer W))) (flowZ K W).1.1 (Plus.equation_C W hP)
    $ tS_mul W xP
  have h := exp_mul_inv W
  rw [hX, xZ, yZ]
  simp only [← Wp.sig_apply (he W)]
  simp only [xPlus, nS, tS, map_add, map_sub, map_mul, map_pow, map_ofNat, Wp.sig_C, Wp.sig_X,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  generalize Wp.sig (he W) (invOfUnit (tDen W xP) 1) = v
  generalize Wp.sig (he W) (xS W) = xs
  generalize Wp.sig (he W) (yS W) = ys
  generalize (toL (expSer W))⁻¹ = q at h ⊢
  generalize toL (expSer W) = E at h ⊢
  linear_combination (-(HahnSeries.C W.a₄ - HahnSeries.C W.a₁ * HahnSeries.C yP
        + 2 * HahnSeries.C W.a₂ * HahnSeries.C xP + 3 * HahnSeries.C xP ^ 2) * xs * v ^ 2
          * E ^ 2 * (E * q + 1)
      + (2 * HahnSeries.C yP + HahnSeries.C W.a₁ * HahnSeries.C xP + HahnSeries.C W.a₃) * ys
          * v ^ 2 * E * ((E * q) ^ 2 + E * q + 1)) * h

theorem isFlow_subst {a b : K⟦X⟧} (h : IsFlow (curveS W) (D W) a b) :
    IsFlow (curveS W) (derivative (R := K)) (a.subst (expSer W)) $ b.subst (expSer W) := by
  obtain ⟨hE, hDa, hDb⟩ := h
  have hφ : ∀ f : K⟦X⟧, f.subst (expSer W) = PowerSeries.substAlgHom (he W) f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hC : ∀ c : K, PowerSeries.substAlgHom (he W) (C c) = C c := fun c =>
    (PowerSeries.substAlgHom $ he W).commutes c
  refine ⟨?_, ?_, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff] at hE ⊢
  have h2 := congrArg (PowerSeries.substAlgHom $ he W) hE
  simp [map_add, map_mul, map_pow, curveS, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, hC] at h2 ⊢
  rwa [hφ, hφ]
  rw [chainZ K W, hDa]
  simp [hφ, map_add, map_mul, map_ofNat, curveS, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, hC]
  rw [chainZ K W, hDb]
  simp [hφ, map_add, map_sub, map_mul, map_pow, map_ofNat, curveS, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, hC]







end Two

open Two

theorem addition_integral : PlusZ.{u} := by
  intro K _ _ W xP yP hP
  use isFlow_subst W (plusFlow K W xP yP hP).1, tS_mul W xP
  have h := flowLogDeriv _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C xP) (HahnSeries.C yP)
    (toL $ (tS W xP).subst (expSer W)) Wp.isDer_dL' (Wp.constCurve_dL W) (flowZ K W).1
    (Plus.equation_C W hP) (dL_C _) (dL_C _) $ tS_mul W xP
  rw [WeierstrassCurve.Affine.map_negY] at h
  have hw : dL (wpL W) = dL (xZ W) := by rw [wpL, map_add, dL_C, add_zero]
  rw [hw, chordZ W hP, chordZ W $ (WeierstrassCurve.Affine.equation_neg xP yP).2 hP, h]


namespace Two

variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem wpInZ (hS : WpShape.{u}) : expSer W ^ 2 * (1 + X ^ 2 * wpReg W)
    = X ^ 2 * ((xS W).subst (expSer W) + C (W.b₂ / 12) * expSer W ^ 2) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
  have hw := (hS K W).1
  unfold wpL xZ at hw
  have hP : (uPow (-2) : LaurentSeries K) * toL X ^ 2 = 1 := uPow_mul_sq
  have hE1 : toL (expSer W) * (toL $ expSer W)⁻¹ = 1 := mul_inv_cancel₀ $ toL_exp_ne W
  simp only [map_mul, map_pow, map_add, map_one, HahnSeries.ofPowerSeries_C]
  linear_combination (-(toL X ^ 2 * toL (expSer W) ^ 2)) * hw + (-(toL (expSer W) ^ 2)) * hP
    + (toL X ^ 2 * toL ((xS W).subst (expSer W)) * (toL (expSer W) * (toL $ expSer W)⁻¹ + 1)) * hE1

end Two

theorem wpInU_of (hS : WpShape.{u}) : WpInU.{u} := by
  intro K _ _ W
  have hl := PowerSeries.HasSubst.of_constantCoeff_zero' (logSpec K W).1
  have hel := (expSpec K W).2.2.2.1
  have hself : ∀ f : K⟦X⟧, f.subst (X : K⟦X⟧) = f := fun f => by
    show MvPowerSeries.subst (fun _ => (PowerSeries.X : K⟦X⟧)) f = f
    have e : (fun _ : Unit => (PowerSeries.X : K⟦X⟧)) = MvPowerSeries.X := funext fun _ => rfl
    rw [e, MvPowerSeries.subst_self]
    rfl
  have h2 := congrArg (PowerSeries.substAlgHom hl) $ Two.wpInZ W hS
  simp [map_mul, map_pow, map_add, map_one, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hl] at h2
  have e1 : PowerSeries.substAlgHom hl (expSer W) = X := by rw [PowerSeries.coe_substAlgHom]
                                                            exact hel
  have e2 : PowerSeries.substAlgHom hl (wpReg W) = (wpReg W).subst (logSer W) := by
    rw [PowerSeries.coe_substAlgHom]
  have e3 : PowerSeries.substAlgHom hl ((xS W).subst (expSer W)) = xS W := by
    rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_comp_subst_apply (Two.he W) hl, hel, hself]
  have e3' : PowerSeries.subst (logSer W : K⟦X⟧) (PowerSeries.subst (expSer W : K⟦X⟧) $ xS W) = xS W := by
    rw [PowerSeries.subst_comp_subst_apply (Two.he W) hl, hel, hself]
  have e4' : PowerSeries.subst (logSer W : K⟦X⟧) (C (W.b₂ / 12) : K⟦X⟧) = C (W.b₂ / 12) := by
    rw [← PowerSeries.coe_substAlgHom hl]
    exact (PowerSeries.substAlgHom hl).commutes _
  simp [hel, e3', e4'] at h2
  exact h2

theorem tInZ_of (hS : WpShape.{u}) : TInZ.{u} := by
  intro K _ _ W xP
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
  have h1 := Two.tS_mul W xP
  have hw := (hS K W).1
  unfold wpL at hw
  have hP : (uPow (-2) : LaurentSeries K) * toL X ^ 2 = 1 := Two.uPow_mul_sq
  simp only [map_mul, map_sub, map_add, map_one, map_pow, HahnSeries.ofPowerSeries_C]
  linear_combination (-(toL ((tS W xP).subst (expSer W)) * toL X ^ 2)) * hw + toL X ^ 2 * h1
    + (-(toL $ (tS W xP).subst (expSer W))) * hP


end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

namespace Nn

section Unique

variable {R : Type u} [CommRing R]

theorem X_pow_succ_dvd_of_derivative
    (hR : ∀ (n : ℕ) (r : R), n ≠ 0 → (n : R) * r = 0 → r = 0) {f : R⟦X⟧} {n : ℕ}
    (h0 : constantCoeff f = 0) (h : X ^ n ∣ derivative f) : X ^ (n + 1) ∣ f := by
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro m hm
  rcases m with _ | k
  simpa using h0
  have hk := h k $ by omega
  rw [PowerSeries.coeff_derivative] at hk
  apply hR (k + 1) _ $ Nat.succ_ne_zero k
  rw [mul_comm]
  exact_mod_cast hk

theorem eq_zero_of_forall_X_pow_dvd {f : R⟦X⟧} (h : ∀ n : ℕ, X ^ n ∣ f) : f = 0 := by
  ext n
  simpa using ((PowerSeries.X_pow_dvd_iff).mp (h $ n + 1) n $ Nat.lt_succ_self n)

end Unique

end Nn

open Nn






theorem plusZCleared_of (hZ : PlusZ.{u}) (hT : TInZ.{u}) : PlusZCleared.{u} := by
  intro K _ _ W xP yP hP
  obtain ⟨-, -, hlog⟩ := hZ K W xP yP hP
  have hsh := (wpShape K W).1
  set P := wpReg W with hPdef
  set c : K := xP + W.b₂ / 12 with hc
  set T := (tS W xP).subst (expSer W) with hTdef
  set xp := (xPlus W xP yP).subst (expSer W) with hxp
  set xm := (xPlus W xP $ W.toAffine.negY xP yP).subst (expSer W) with hxm
  set f : K⟦X⟧ := 1 + X ^ 2 * (P - C c) with hf
  have hf0 : constantCoeff f = 1 := by simp [hf]
  set g : K⟦X⟧ := invOfUnit f 1 with hg
  have hfg : f * g = 1 := mul_invOfUnit _ _ $ by rw [hf0, Units.val_one]
  have hTf : T * f = X ^ 2 := by rw [← hT K W xP, hf]
                                 ring
  have hTg : T = X ^ 2 * g := by linear_combination g * hTf - T * hfg
  have hdf : X * derivative f = 2 * (f - 1) + X ^ 3 * derivative P := by
    rw [hf]
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
      derivative_C, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hdg : derivative g = -g ^ 2 * derivative f := by
    have h := congrArg (derivative (R := K)) hfg
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h
    linear_combination g * h - derivative g * hfg
  have hz : (toL X : LaurentSeries K) * uPow (-1) = 1 := Plus.toL_X_mul
  have hxZ : xZ W = uPow (-2) + toL P - HahnSeries.C (W.b₂ / 12) := by
    rw [← hsh, wpL]
    ring

  have hdwp : dL (wpL W) = uPow (-1) ^ 3 * (toL X * toL (derivative f) - 2 * toL f) := by
    have h1 : toL X * toL (derivative f) = 2 * (toL f - 1) + toL X ^ 3 * toL (derivative P) := by
      rw [← map_mul, hdf]
      simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
    rw [hsh, map_add, dL_uPow, dL_toL, h1]
    have e3 : (uPow (-2 - 1) : LaurentSeries K) = uPow (-1) ^ 3 := by
      rw [← Plus.uPow_neg_three]
      norm_num
    rw [e3]
    have e2 : (HahnSeries.C (((-2 : ℤ) : K)) : LaurentSeries K) = -2 := by
      push_cast
      rw [map_neg, map_ofNat]
    rw [e2]
    linear_combination (-toL (derivative P)
      * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * hz
  have hprod : toL T * dL (wpL W) = toL (g * derivative f) - 2 * uPow (-1) := by
    have hfg' : toL f * toL g = 1 := by rw [← map_mul, hfg, map_one]
    rw [hdwp, hTg, map_mul, map_mul, map_pow]
    linear_combination (toL g * toL (derivative f) * ((toL X * uPow (-1)) ^ 2
        + toL X * uPow (-1) + 1) - 2 * toL g * toL f * uPow (-1) * (toL X * uPow (-1) + 1)) * hz
      - 2 * uPow (-1) * hfg'
  rw [hprod, map_sub, dL_toL, dL_mul, dL_uPow, hxZ] at hlog
  have e2' : (uPow (-1 - 1) : LaurentSeries K) = uPow (-2) := by norm_num
  have e1 : (HahnSeries.C (((-1 : ℤ) : K)) : LaurentSeries K) = -1 := by
    push_cast
    rw [map_neg, map_one]
  have d2 : dL (2 : LaurentSeries K) = 0 := by
    rw [← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 2, dL_C]
  rw [e2', e1, d2] at hlog
  have hmain : derivative (g * derivative f) = 2 * P - (xp + C (W.b₂ / 12))
      - (xm + C (W.b₂ / 12)) := by
    apply toL_injective
    simp only [map_add, map_sub, map_mul, map_ofNat, toL_C]
    linear_combination hlog
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hdg] at hmain
  rw [← hmain]
  linear_combination (-(derivative $ derivative f) * f
    + derivative f ^ 2 * (f * g + 1)) * hfg

end Formalism.L2.Th1.A
end
section
namespace Formalism.L2.Th1.A

theorem cubeTwoR : CubeTwoR.{u} := cube_two_relation
theorem coeffMem : CoeffMem.{u} := coeffMem_of zSerMap halfLog

theorem shortInv : ShortInv := short_weierstrass_inverse
theorem uSerEq : USerEq := uSerEq_of wpShape wpRecursion

end Formalism.L2.Th1.A
end
section
open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)






def at1 {K ι : Type} [Field K] (x : ι) (f : PowerSeries K) : MvPowerSeries ι K :=
  PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K) f














def hh1 {K E : Type} [Field K] [Fintype E] (p : ℕ) (c c' : K) : MvPowerSeries (Bool × E) K :=
  ∑ e : E, (MvPowerSeries.C c * MvPowerSeries.X (false, e) * MvPowerSeries.X (true, e) ^ p -
    MvPowerSeries.C c' * MvPowerSeries.X (false, e) ^ p * MvPowerSeries.X (true, e))



end Formalism.InvariantFactorPaths.G7
end
section
open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)


def Simeq {K ι : Type} [NormedField K] [CharZero K] (f g : MvPowerSeries ι K) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ Integral (mvExp $ f - g)

def SimeqRules : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K],
    (∀ f : MvPowerSeries ι K, Simeq f f) ∧
    (∀ f g : MvPowerSeries ι K, Simeq f g → Simeq g f) ∧
    (∀ f g h : MvPowerSeries ι K, Simeq f g → Simeq g h → Simeq f h) ∧
    (∀ f g f' g' : MvPowerSeries ι K, Simeq f g → Simeq f' g' → Simeq (f + f') (g + g')) ∧
    (∀ (κ : Type) [Finite ι] (f g : MvPowerSeries ι K) (φ : ι → MvPowerSeries κ K),
      (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral $ φ i) → Simeq f g →
      Simeq (MvPowerSeries.subst φ f) (MvPowerSeries.subst φ g))






section Coord

variable {K : Type} [Field K] {ν r0 r1 : ℕ}







end Coord






end Formalism.InvariantFactorPaths.G7
end
section
open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)


section Defs

variable {K : Type} [Field K]

def cob (F : MvPowerSeries (Fin 2) K) (f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst F f - at1 0 f - at1 1 f

def swap2 (H : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] H

def in3 (f : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] f

def d1 (F H : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![in3 F, MvPowerSeries.X 2] H -
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] H -
    MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] H

def DivAB (H : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, n 0 = 0 ∨ n 1 = 0 → MvPowerSeries.coeff n H = 0

end Defs











end Formalism.InvariantFactorPaths.G7
end
section
open PowerSeries (coeff mk)
namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7

section Alg

variable {K : Type} [Field K] [CharZero K]

def fExp {ι : Type} (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  PowerSeries.subst f $ PowerSeries.exp K

def fLog {ι : Type} (g : MvPowerSeries ι K) : MvPowerSeries ι K :=
  PowerSeries.subst (g - 1) $ PowerSeries.log K

def prim (f : PowerSeries K) : PowerSeries K :=
  mk fun n => if n = 0 then 0 else coeff (n - 1) f / (n : K)

abbrev dz (f : PowerSeries K) : PowerSeries K := PowerSeries.derivative f

def IsWp (g2 g3 : K) (P : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff P = 0 ∧ (∀ n, Odd n → coeff n P = 0) ∧
    (-2 + PowerSeries.X ^ 3 * dz P) ^ 2 =
      4 * (1 + PowerSeries.X ^ 2 * P) ^ 3 -
        PowerSeries.C g2 * PowerSeries.X ^ 4 * (1 + PowerSeries.X ^ 2 * P) -
        PowerSeries.C g3 * PowerSeries.X ^ 6

def sigS (P : PowerSeries K) : PowerSeries K := -prim (prim P)

def sigma (P : PowerSeries K) : PowerSeries K := PowerSeries.X * fExp (sigS P)

def sgStar (s2 : K) (P : PowerSeries K) : PowerSeries K :=
  sigma P * fExp (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2))





def atS (f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) f

def atD (f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) f

def par0 (f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  atS f + atD f - 2 * at1 0 f - 2 * at1 1 f

def wpDiff (P : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2 +
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (at1 1 P - at1 0 P)

def dq (P : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  fun n => if Even (n 0) ∧ Even (n 1) then coeff (n 0 + n 1 + 2) P else 0

def ev0 (h : MvPowerSeries (Fin 2) K) : PowerSeries K :=
  MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0] h

abbrev pd {ι : Type} (i : ι) (h : MvPowerSeries ι K) : MvPowerSeries ι K :=
  MvPowerSeries.pderiv i h

def lU (l : PowerSeries K) : PowerSeries K := mk fun n => coeff (n + 1) l

def phO (s2 : K) (P l : PowerSeries K) : PowerSeries K :=
  -PowerSeries.subst l (sigS P) + PowerSeries.C (s2 / 2) * l ^ 2 - fLog (lU l)


def FI (F : MvPowerSeries (Fin 2) K) (i : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 1 i] F

def par (F : MvPowerSeries (Fin 2) K) (i f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst F f + PowerSeries.subst (FI F i) f - 2 * at1 0 f - 2 * at1 1 f


end Alg

section Norm

open Formalism.DworkPowerSeriesWeights (Integral)

variable {K : Type} [NormedField K]

def LawLog (F : MvPowerSeries (Fin 2) K) (l : PowerSeries K) : Prop :=
  MvPowerSeries.constantCoeff F = 0 ∧ Integral F ∧ PowerSeries.constantCoeff l = 0 ∧
    coeff 1 l = 1 ∧ cob F l = 0

def IsInv (l i : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff i = 0 ∧ Integral (ι := Unit) i ∧ PowerSeries.subst i l = -l

def IsHalf (l h : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff h = 0 ∧ Integral (ι := Unit) h ∧
    PowerSeries.subst h l = PowerSeries.C (2 : K)⁻¹ * l

def CurveHyp (F : MvPowerSeries (Fin 2) K) (i l P ep : PowerSeries K) (c0 : K) : Prop :=
  Integral (ι := Unit) ep ∧ PowerSeries.constantCoeff ep = 1 ∧
    PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2) ∧
    ∃ c : MvPowerSeries (Fin 2) K, Integral c ∧ MvPowerSeries.constantCoeff c = -1 ∧
      MvPowerSeries.X 1 ^ 2 * at1 0 ep - MvPowerSeries.X 0 ^ 2 * at1 1 ep = c * F * FI F i

end Norm

end Formalism.L2.Th1.B
end
section
open PowerSeries (coeff)
namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (at1)

def ExpLogRules : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type),
    (∀ f g : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → fExp (f + g) = fExp f * fExp g) ∧
    (∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (fExp f) = 1 ∧ fLog (fExp f) = f) ∧
    (∀ g : MvPowerSeries ι K, MvPowerSeries.constantCoeff g = 1 →
      MvPowerSeries.constantCoeff (fLog g) = 0 ∧ fExp (fLog g) = g)

def ExpLogDeriv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Finite ι] (i : ι),
    (∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      pd i (fExp f) = fExp f * pd i f) ∧
    (∀ g : MvPowerSeries ι K, MvPowerSeries.constantCoeff g = 1 → g * pd i (fLog g) = pd i g)

def ExpLogSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι κ : Type) [Finite ι] (φ : ι → MvPowerSeries κ K),
    (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
    (∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.subst φ (fExp f) = fExp (MvPowerSeries.subst φ f)) ∧
    (∀ g : MvPowerSeries ι K, MvPowerSeries.constantCoeff g = 1 →
      MvPowerSeries.subst φ (fLog g) = fLog (MvPowerSeries.subst φ g))

def PrimRules : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : PowerSeries K),
    dz (prim f) = f ∧ PowerSeries.constantCoeff (prim f) = 0

def WaveUnique : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (h : MvPowerSeries (Fin 2) K),
    pd 0 (pd 0 h) = pd 1 (pd 1 h) → ev0 h = 0 → ev0 (pd 1 h) = 0 → h = 0

def WaveKills : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : PowerSeries K),
    pd 0 (pd 0 $ par0 f) - pd 1 (pd 1 $ par0 f) = -2 * at1 0 (dz $ dz f) + 2 * at1 1 (dz $ dz f)

def ParCauchy : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : PowerSeries K),
    PowerSeries.constantCoeff f = 0 → coeff 1 f = 0 →
    ev0 (par0 f) = 0 ∧ ev0 (pd 1 $ par0 f) = 0

def WpReduced : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    PowerSeries.X ^ 4 * dz P ^ 2 - 4 * PowerSeries.X * dz P =
        12 * P + 12 * PowerSeries.X ^ 2 * P ^ 2 + 4 * PowerSeries.X ^ 4 * P ^ 3 -
          PowerSeries.C g2 * PowerSeries.X ^ 2 * (1 + PowerSeries.X ^ 2 * P) -
          PowerSeries.C g3 * PowerSeries.X ^ 4 ∧
      PowerSeries.X ^ 2 * dz (dz P) =
        12 * P + 6 * PowerSeries.X ^ 2 * P ^ 2 - PowerSeries.C (g2 / 2) * PowerSeries.X ^ 2






def DqRule : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (P : PowerSeries K),
    (∀ n, Odd n → coeff n P = 0) →
    at1 0 P - at1 1 P = (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * dq P

def AddSigmaLog : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    par0 (sigS P) = fLog (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P)

def AddSigma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (atS (sigma P) * atD (sigma P)) =
      at1 0 (sigma P) ^ 2 * at1 1 (sigma P) ^ 2 * wpDiff P

def AddSgStar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 s2 : K) (P : PowerSeries K), IsWp g2 g3 P →
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (atS (sgStar s2 P) * atD (sgStar s2 P)) =
      at1 0 (sgStar s2 P) ^ 2 * at1 1 (sgStar s2 P) ^ 2 * wpDiff P


def SigmaOdd : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (P : PowerSeries K),
    (∀ n, Odd n → coeff n P = 0) →
    coeff 1 (sigma P) = 1 ∧ ∀ n, Even n → coeff n (sigma P) = 0


end Formalism.L2.Th1.B
end
section
namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7


def HalfExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l : PowerSeries K), LawLog F l → ‖(2 : K)‖ = 1 → ∃ h, IsHalf l h

def SimeqInt : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (f g f' g' : MvPowerSeries ι K),
    Simeq f g → Simeq f' g' →
    Simeq (f - f') (g - g') ∧ Simeq (-f) (-g) ∧ ∀ n : ℤ, Simeq ((n : MvPowerSeries ι K) * f) $ n * g



def SimeqLog : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g : MvPowerSeries ι K),
    MvPowerSeries.constantCoeff g = 1 → Integral g → Simeq (fLog g) 0 ∧ Simeq (-fLog g) 0

def PhODef : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (s2 : K) (P l : PowerSeries K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    PowerSeries.constantCoeff (phO s2 P l) = 0 ∧
      PowerSeries.subst l (sgStar s2 P) = PowerSeries.X * fExp (-phO s2 P l)




def ParO : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 →
    Simeq (par F i $ phO s2 P l) 0



def CobRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l f : PowerSeries K), LawLog F l → PowerSeries.constantCoeff f = 0 →
    DivAB (cob F f) ∧ swap2 (cob F f) = cob F f

def Cube : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i f : PowerSeries K), LawLog F l → IsInv l i → ‖(2 : K)‖ = 1 →
    Simeq (par F i f) 0 → Simeq (d1 F $ cob F f) 0

def LogSigmaPullbackCocycle : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → ‖(2 : K)‖ = 1 →
    DivAB (cob F $ phO s2 P l) ∧ swap2 (cob F $ phO s2 P l) = cob F (phO s2 P l) ∧
      Simeq (d1 F $ cob F $ phO s2 P l) 0 ∧ Simeq (d1 F $ swap2 $ cob F $ phO s2 P l) 0







end Formalism.L2.Th1.B
end
section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.A (g₂ g₃ wpReg)
open Formalism.L2.Th1.B (IsWp fExp sigma)
open Formalism.L2.Th1.C (IsEndoZ IsogenyFormula)

namespace Formalism.L2.Th1.F

def taylor0 (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)

def pSeries (L : PeriodPair) : PowerSeries ℂ := taylor0 $ L.weierstrassPExcept 0

def TaylorRing : Prop :=
  (∀ f g : ℂ → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
    taylor0 (fun z => f z + g z) = taylor0 f + taylor0 g ∧
    taylor0 (fun z => f z * g z) = taylor0 f * taylor0 g) ∧
  (∀ c : ℂ, taylor0 (fun _ => c) = PowerSeries.C c) ∧ taylor0 (fun z => z) = PowerSeries.X ∧
  (∀ f g : ℂ → ℂ, f =ᶠ[nhds 0] g → taylor0 f = taylor0 g)

def TaylorDeriv : Prop :=
  (∀ f : ℂ → ℂ, AnalyticAt ℂ f 0 → taylor0 (deriv f) = PowerSeries.derivative (taylor0 f)) ∧
  (∀ (f : ℂ → ℂ) (a : ℂ), AnalyticAt ℂ f 0 →
    taylor0 (fun z => f $ a * z) = PowerSeries.rescale a (taylor0 f)) ∧
  (∀ f g : ℂ → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → taylor0 f = taylor0 g → f =ᶠ[nhds 0] g)

def TaylorExp : Prop :=
  ∀ f : ℂ → ℂ, AnalyticAt ℂ f 0 → f 0 = 0 →
    taylor0 (fun z => Complex.exp $ f z) = fExp (taylor0 f)

def PSeriesCoeff : Prop :=
  ∀ (L : PeriodPair) (n : ℕ),
    PowerSeries.coeff n (pSeries L) = if n = 0 then 0 else ((n : ℂ) + 1) * L.G (n + 2)

def TaylorIsWp : Prop := ∀ L : PeriodPair, IsWp L.g₂ L.g₃ $ pSeries L

def TaylorSigma : Prop := ∀ L : PeriodPair, taylor0 (wSigma L) = sigma (pSeries L)

def TaylorSgStar : Prop :=
  ∀ L : PeriodPair, taylor0 (sgStar L) = Formalism.L2.Th1.B.sgStar (s2 L) (pSeries L)

def TaylorSgStar' : Prop :=
  ∀ L : PeriodPair, taylor0 (sgStar L) = Formalism.L2.Th1.C.sgStar (pSeries L) (s2 L)



def IsWpUnique : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P P' : PowerSeries K),
    IsWp g2 g3 P → IsWp g2 g3 P' → P = P'

def CurveBridge : Prop :=
  ∀ (W : WeierstrassCurve ℂ) (L : PeriodPair), g₂ W = L.g₂ → g₃ W = L.g₃ →
    wpReg W = pSeries L

def EndoZInstance : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∃ neg : S → S, (∀ P : S, (neg P : ℂ) + (P : ℂ) ∈ L.lattice) ∧
      IsEndoZ (pSeries L) neg (fun P : S => L.weierstrassP (P : ℂ))
        (fun P : S => taylor0 fun z => L.weierstrassP $ z + (P : ℂ)) α

def IsogenyFormulaInstance : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    IsogenyFormula (pSeries L) (s2 L) (fun P : S => L.weierstrassP (P : ℂ)) α

end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM

namespace Formalism.L2.Th1.F


def shortW {K : Type} [Field K] (g2 g3 : K) : WeierstrassCurve K := ⟨0, 0, 0, -g2 / 4, -g3 / 4⟩







def HasCMByStable : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), HasCMBy d L → ∀ m n : ℤ,
    MulStable L ((m : ℂ) + (n : ℂ) * omegaK d) ∧
    Complex.normSq ((m : ℂ) + (n : ℂ) * omegaK d)
      = (m : ℝ) ^ 2 + (m : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 * ((1 + (d : ℝ)) / 4)

def HasCMByScale : Prop :=
  ∀ (d : ℕ) (L : PeriodPair) (c : ℂ) (hc : c ≠ 0), HasCMBy d L → HasCMBy d (scalePair L c hc)










end Formalism.L2.Th1.F
end
section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)

namespace Formalism.L2.Th1.F

namespace CmBy

private lemma re_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).re = (m : ℝ) + (n : ℝ) / 2 := by
  simp [omegaK]
  ring

private lemma im_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).im = (n : ℝ) * Real.sqrt d / 2 := by
  simp [omegaK]
  ring

lemma normSq_omega (d : ℕ) (m n : ℤ) :
    Complex.normSq ((m : ℂ) + (n : ℂ) * omegaK d)
      = (m : ℝ) ^ 2 + (m : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 * ((1 + (d : ℝ)) / 4) := by
  rw [Complex.normSq_apply, re_add_mul_omegaK, im_add_mul_omegaK]
  linear_combination ((n : ℝ) ^ 2 / 4) * Real.mul_self_sqrt (Nat.cast_nonneg d)

lemma ne_zero (d : ℕ) (hd : 0 < d) (m n : ℤ) (h : (m, n) ≠ (0, 0)) :
    (m : ℂ) + (n : ℂ) * omegaK d ≠ 0 := by
  intro h0
  have hre := re_add_mul_omegaK d m n
  have him := im_add_mul_omegaK d m n
  rw [h0, Complex.zero_re] at hre
  rw [h0, Complex.zero_im] at him
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr $ by exact_mod_cast hd
  have hn : (n : ℝ) = 0 := by
    have h2 : (n : ℝ) * Real.sqrt d = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    exact h1
    linarith
  have hm : (m : ℝ) = 0 := by rw [hn] at hre
                              linarith
  have hn' : n = 0 := by exact_mod_cast hn
  have hm' : m = 0 := by exact_mod_cast hm
  apply h
  rw [hm', hn']
end CmBy

theorem has_cm_stable : HasCMByStable := by
  intro d L hL m n
  refine ⟨?_, CmBy.normSq_omega d m n⟩
  intro w hw
  have he : ((m : ℂ) + (n : ℂ) * omegaK d) * w = m • w + n • (omegaK d * w) := by
    simp [zsmul_eq_mul]
    ring
  rw [he]
  exact L.lattice.add_mem (L.lattice.smul_mem m hw) $ L.lattice.smul_mem n $ hL w hw

theorem hasCMByScale_of (h : Homogeneity) : HasCMByScale := by
  intro d L c hc hL w hw
  rw [(h L c hc).1] at hw ⊢
  rw [show c⁻¹ * (omegaK d * w) = omegaK d * (c⁻¹ * w) by ring]
  exact hL _ hw




theorem has_cm_scale : HasCMByScale := hasCMByScale_of homogeneity




end Formalism.L2.Th1.F
end
end
