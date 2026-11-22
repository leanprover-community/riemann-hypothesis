module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ClosedEqNablaC
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL

noncomputable section

namespace PI.WHw

theorem bC_exists_killed {r n : ℕ}
    (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0 :=
  GlobalTheory.Branching.exists_killed_of_rowDivClosed M hM hne

end PI.WHw
