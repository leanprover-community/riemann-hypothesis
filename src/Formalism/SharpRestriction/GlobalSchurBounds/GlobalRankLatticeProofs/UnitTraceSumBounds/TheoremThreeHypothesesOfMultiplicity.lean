import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IntegralityOfCommutation
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.WeylForK

namespace Formalism.MainNotions.StandardLattice

theorem weylForK_holds : Formalism.MainNotions.DiscreteSeriesWeylDimension.WeylForK := weylForK_closed


theorem theorem_three_hypotheses_of_multiplicity (D : Formalism.BasicNotions.D7) (hF : Formalism.MainNotions.PlaceDegreeData.DiscreteSeriesLowestKTypeFormula D) (hM : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne) : Adm3 D :=
  integrality_of_commutation D hF weylForK_holds hM

end Formalism.MainNotions.StandardLattice
