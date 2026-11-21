import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.EvaluationSums.SuccAboveSuccEqCons

noncomputable section

namespace PositivityTheory.KB.ChainCochainPairing

variable {G : Type} [Group G]

def evh {m : ℕ} (Φ : (Fin (m + 1) → G) → ℝ) : Chn G m →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ fun g => Φ (Fin.partialProd g)







end PositivityTheory.KB.ChainCochainPairing
