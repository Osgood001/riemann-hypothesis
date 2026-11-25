import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainOfTransference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace AlpogeRHCore28

theorem fundamentalDomainPointBound
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (hD5 : CoveringRadiusStatement) :
    FundamentalDomainPointBound (E := E) :=
  ReciprocityTheory.ChartRestriction.G.FD.fundamentalDomain_of_transference hD5

end AlpogeRHCore28
