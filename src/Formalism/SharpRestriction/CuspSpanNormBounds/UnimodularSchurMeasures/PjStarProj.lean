import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionConvolutionIdentity

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.PlaceDegreeData (phA IsOpIntA)

section One

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  {Hp : Type} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]



end One

section Two

variable {G1 G2 : Type} [Group G1] [Group G2] [MeasurableSpace G1] [MeasurableSpace G2]
  (μ1 : Measure G1) (μ2 : Measure G2) [SFinite μ1] [SFinite μ2]
  {Hp : Type} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]



end Two

section Three

variable {G1 : Type} {Hs L : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]


end Three

end Formalism.MainNotions.LeviCoordinates

end
