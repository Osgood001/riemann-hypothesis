module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridKeyCount
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions
open Formalism.L2.Host GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

namespace GlobalTheory.Mem.LiteralAutomorphy.KeyFiniteness

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem mem_CS_actual {X : Stages} {T : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {sc : Consts}
    (G : GridData L sc) (a : Fin X.toD7.R.m) :
    G.ch.chiH (a.1 + 1) ∈ CS X.toD7 sc.cGap G.pl.v0 a := by
  obtain ⟨v, _, h⟩ := Set.mem_iUnion₂.mp (mem_KS G)
  have hv : G.pl.v0 = v := h.1
  subst v
  exact h.2.2 a (Set.mem_univ _)

private theorem actual_unr_iff {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : Consts}
    (G : GridData L sc) (i : ℕ) (hi : 1 ≤ i) (him : i ≤ D.R.m)
    (p : HeightOneSpectrum (𝓞 D.host.E)) :
    (G.ch.chiH i).UnrAt p ↔ p.under (𝓞 D.host.F) ∉ G.pl.S0 := by
  refine ⟨fun h hp => ?_, G.ch.unr i hi him p⟩
  rcases G.pl.mem_S0_of_sum_eq.1 hp with e | e
  · exact (G.ch.lev0 i hi him p e).2 h
  · exact (G.ch.lev1 i hi him p e).2 fun z hz _ => h z hz

/-- After adjoining the ray-index roots of unity, the unramified values of a single
reference grid suffice for any original grid at the same base place. -/
theorem valuesIn_of_basePlace_eq {X Y : Stages} {T U : Type}
    {L : Formalism.IndefR.Links.LevCh X.toD7 T} {L' : Formalism.IndefR.Links.LevCh Y.toD7 U}
    {sc : Consts} (G : GridData L sc) (G₀ : GridData L' sc) (hP : X.B.toPre = Y.B.toPre)
    (hv : HEq G.pl.v0 G₀.pl.v0) {K : Type} [Field K] (e : K →+* ℂ)
    (hμ : ∃ ζ : K, IsPrimitiveRoot ζ (rayIndexAt X.toD7 G.pl.v0))
    (hval : ∀ i, 1 ≤ i → i ≤ Y.toD7.R.m → (G₀.ch.chiH i).ValuesIn 0 e) :
    ∀ i, 1 ≤ i → i ≤ X.toD7.R.m → (G.ch.chiH i).ValuesIn 0 e := by
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := X
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := Y
  change P = Q at hP
  subst Q
  classical
  have hv0 := eq_of_heq hv
  have hS : G.pl.S0 = G₀.pl.S0 := congrArg (fun v ↦ insert v _) hv0
  intro i hi him v hχv
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
  have ha : a < P.R.m := him
  let χ := G.ch.chiH (a + 1)
  let ψ := G₀.ch.chiH (a + 1)
  have hψv : ψ.UnrAt v := by
    apply (actual_unr_iff G₀ _ hi him v).2
    rw [← hS]
    exact (actual_unr_iff G _ hi him v).1 hχv
  obtain ⟨y, hy⟩ := hval (a + 1) hi him v hψv
  have hψ := mem_CS_actual G₀ ⟨a, ha⟩
  rw [← hv0] at hψ
  have h' := val_ratio_pow_rayIndexAt (mem_CS_actual G ⟨a, ha⟩) hψ v
  have : NeZero (rayIndexAt _ G.pl.v0) := ⟨(rayIndexAt_pos _ _).ne'⟩
  obtain ⟨ζ, hζ⟩ := hμ
  have hζ' := hζ.map_of_injective (f := e) e.injective
  obtain ⟨n, -, hn⟩ := hζ'.eq_pow_of_pow_eq_one h'
  have hye : e y = (ψ.val v : ℂ) := by simpa [HChar.valTw, ψ] using hy
  refine ⟨y * ζ ^ n, ?_⟩
  change e (y * ζ ^ n) = χ.valTw 0 v
  change (e ζ) ^ n = (χ.val v : ℂ) / (ψ.val v : ℂ) at hn
  rw [map_mul, map_pow, hye, hn]
  simpa [HChar.valTw] using mul_div_cancel₀ (χ.val v : ℂ) (ψ.val v).ne_zero

/-- Every realization of a reference grid that contains the prescribed ray roots
realizes every original grid over the same base place, even at another stage. -/
theorem fieldHas_of_basePlace_eq {X Y : Stages} {T U : Type}
    {L : Formalism.IndefR.Links.LevCh X.toD7 T} {L' : Formalism.IndefR.Links.LevCh Y.toD7 U}
    {sc : Consts} (G : GridData L sc) (G₀ : GridData L' sc) (hP : X.B.toPre = Y.B.toPre)
    (hv : HEq G.pl.v0 G₀.pl.v0) {K : Type} [Field K] (e : K →+* ℂ)
    (hμ : ∃ ζ : K, IsPrimitiveRoot ζ (rayIndexAt X.toD7 G.pl.v0))
    (hF : FieldHas G₀ e) : FieldHas G e := by
  refine ⟨valuesIn_of_basePlace_eq G G₀ hP hv e hμ hF.values, ?_⟩
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := X
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := Y
  change P = Q at hP
  subst Q
  classical
  have hv0 := eq_of_heq hv
  intro v hs
  have hd : G.pl.depth sc v = G₀.pl.depth sc v := by
    unfold Places.depth
    split_ifs with h h' h'
    · rfl
    · exact absurd (h.trans hv0) h'
    · exact absurd (h'.trans hv0.symm) h
    · rfl
  rw [hd]
  apply hF.roots
  have hS : G.pl.S0 = G₀.pl.S0 := congrArg (fun v ↦ insert v _) hv0
  rwa [← hS]

end GlobalTheory.Mem.LiteralAutomorphy.KeyFiniteness
