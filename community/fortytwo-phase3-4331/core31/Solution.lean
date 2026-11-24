import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.E CrystallineSemistableComparison.CH GlobalTheory.EtC

namespace AlpogeRHCore31

theorem etaleComparisonAndFirstChernUnique :
    (∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
      EtMap l K) ∧
    (∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (X : Scheme.{0})
      (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l)
      (D : LineData X),
      Etale D.f →
      ∀ (y y' : ∀ n, MH (PX q κ) n 2),
        IsFirstChernClassOfLineBundle q κ D y →
        IsFirstChernClassOfLineBundle q κ D y' → y = y') :=
  ⟨CrystallineSemistableComparison.E.etMap, CrystallineSemistableComparison.E.firstChern_unique⟩

end AlpogeRHCore31
