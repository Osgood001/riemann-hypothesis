module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalIntertwining

@[expose] public section

theorem UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine.{u_1, u_2}
    {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : Module ℂ Y]
    [inst_2 : AddCommGroup Z] [inst_3 : Module ℂ Z]
    (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z)
    (h : ∀ y, ψ (A y) = B (ψ y)) (p : Polynomial ℂ) (y : Y) :
    ψ (Polynomial.aeval A p y) = Polynomial.aeval B p (ψ y) :=
  UpperTheory.Reformulated.B.AevalIntertwining.map_aeval ψ A B h p y
