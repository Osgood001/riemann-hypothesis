module

public import Mathlib

@[expose] public section

namespace UpperTheory.Reformulated.B.AevalIntertwining

/-- A linear map intertwining two operators also intertwines their polynomial evaluations. -/
theorem map_aeval {K M N : Type*} [CommSemiring K] [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] (φ : M →ₗ[K] N) (f : Module.End K M) (g : Module.End K N)
    (h : ∀ x, φ (f x) = g (φ x)) (p : Polynomial K) (x : M) :
    φ (Polynomial.aeval f p x) = Polynomial.aeval g p (φ x) := by
  let ψ := (Module.AEval'.of g).toLinearMap.comp φ
  have hψ (m : M) : ψ (f m) = (Polynomial.X : Polynomial K) • ψ m :=
    (congrArg (Module.AEval'.of g) (h m)).trans (Module.AEval'.X_smul_of g _).symm
  exact (LinearMap.ofAEval f ψ hψ).map_smul p (Module.AEval'.of f x)

end UpperTheory.Reformulated.B.AevalIntertwining

theorem UpperTheory.Reformulated.B.AevalIntertwining.aeval_intertwine
    {K : Type} [inst : Field K] {M N : Type} [inst_1 : AddCommGroup M] [inst_2 : Module K M]
    [inst_3 : AddCommGroup N] [inst_4 : Module K N]
    (φ : M →ₗ[K] N) (f : Module.End K M) (f' : Module.End K N)
    (h : ∀ x, φ (f x) = f' (φ x)) (p : Polynomial K) (x : M) :
    φ (Polynomial.aeval f p x) = Polynomial.aeval f' p (φ x) :=
  UpperTheory.Reformulated.B.AevalIntertwining.map_aeval φ f f' h p x
