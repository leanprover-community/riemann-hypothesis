import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.WeightedL1OfL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.PhiIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurG

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]


def wr (y : Mt k r) : ℝ := gN (Matrix.of y : Mat k r) ^ (-(2 * AB k r))

end ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit
