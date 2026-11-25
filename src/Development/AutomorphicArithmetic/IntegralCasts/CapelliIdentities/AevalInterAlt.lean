module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalIntertwining

@[expose] public section

theorem UpperTheory.Reformulated.B.Qi58.aeval_inter
    {L M N : Type} [inst : Field L] [inst_1 : AddCommGroup M] [inst_2 : Module L M]
    [inst_3 : AddCommGroup N] [inst_4 : Module L N]
    (c : M →ₗ[L] N) (f : Module.End L M) (g : Module.End L N)
    (h : ∀ x, c (f x) = g (c x)) (Q : Polynomial L) (x : M) :
    c (Polynomial.aeval f Q x) = Polynomial.aeval g Q (c x) :=
  UpperTheory.Reformulated.B.AevalIntertwining.map_aeval c f g h Q x
