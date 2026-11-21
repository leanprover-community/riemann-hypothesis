import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.ArithmeticLatticeHypothesis

namespace Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements


lemma JJ : J * J = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J]





end Formalism.SLP.GlobalBoundRefinements.P
