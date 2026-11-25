module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalIntertwining

@[expose] public section

theorem UpperTheory.Reformulated.B.Qe22.aeval_inter
    {M N : Type} [inst : AddCommGroup M] [inst_1 : Module ℂ M]
    [inst_2 : AddCommGroup N] [inst_3 : Module ℂ N]
    (f : M →ₗ[ℂ] N) (T : Module.End ℂ M) (T' : Module.End ℂ N)
    (h : ∀ x, f (T x) = T' (f x)) (p : Polynomial ℂ) (x : M) :
    f (Polynomial.aeval T p x) = Polynomial.aeval T' p (f x) :=
  UpperTheory.Reformulated.B.AevalIntertwining.map_aeval f T T' h p x
