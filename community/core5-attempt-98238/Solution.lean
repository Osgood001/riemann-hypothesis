import ComparatorChallenges.RHCore5Defs
import Bundle13
namespace AlpogeRHCore5

theorem functorialResolutionCharZero : FunctorialResolution.FunctorialResolutionCharZero.{0} := by
  obtain ⟨R, h1, h2, h3⟩ := FunctorialResolution.EmbeddedResolution.strongResolutionOfSingularitiesCharZero
  exact ⟨fun k _ _ X f _ _ _ =>
    ⟨(R k X f).length, (R k X f).tower, (R k X f).isoZero, (R k X f).center, (R k X f).isBlowup⟩, h1, h2, h3⟩

end AlpogeRHCore5
