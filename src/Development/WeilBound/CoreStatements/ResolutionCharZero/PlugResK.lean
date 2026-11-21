import Mathlib
import Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromRes

section
namespace PositivityTheory.ResPlug.FromRes

theorem resW : PositivityTheory.ResPlug.ResW :=
  resW_of_functorialResolution FunctorialResolution.functorialResolutionCharZero.{0}

end PositivityTheory.ResPlug.FromRes
end

section
namespace PositivityTheory.ResPlug.FromRes

theorem princW : PositivityTheory.ResPlug.PrincW :=
  princW_of_functorialPrincipalization FunctorialResolution.functorialPrincipalizationCharZero.{0}

end PositivityTheory.ResPlug.FromRes
end

section
namespace PositivityTheory.ResPlug.FromRes

theorem resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement :=
  PositivityTheory.ResPlug.resK_of_weak resW princW

end PositivityTheory.ResPlug.FromRes
end
