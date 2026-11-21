import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.SqPairGlueMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.FiniteAdeleIdempotentOfFMulSelf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.HyperbolicPlane
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairDichotomy
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairSelection
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.CmpSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.StepGlue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOf

section
theorem square_pair_glue : PI.SqPair.PLocalAll → Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen :=
  PI.SqPairW.sqPairGlue_main
end

section
theorem local_cartan_pair : PI.SqPair.LocCartanPair :=
  PI.SqPair.LCP.locCartanPair_of PI.SqPair.LCP.pair_dichotomy PI.SqPair.LCP.base_lagrangian
    (PI.SqPair.LCP.step_of PI.SqPair.LCP.pair_selection PI.SqPair.LCP.hyperbolic_plane
      PI.SqPair.LCP.pair_split')
end

section
theorem square_pair_local : PI.SqPair.PLocalAll := PI.SqPairLocal.sqPairLocal_of local_cartan_pair
end

section
theorem split_pair_generation : Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen := square_pair_glue square_pair_local
end
