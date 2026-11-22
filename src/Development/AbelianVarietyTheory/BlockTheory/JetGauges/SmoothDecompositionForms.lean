module

public import Mathlib
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.IsLowUnitH
public import Formalism.PeriodIntegrals.BesselMapUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply

@[expose] public section

open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms

abbrev Ix (k r : ℕ) := Fin (2 * r + k + 1)

abbrev Mx (k r : ℕ) := Matrix (Ix k r) (Ix k r) ℂ

attribute [instance] HRep.instNorm HRep.instInner HRep.instComplete

variable {k r : ℕ}

section Tensor

variable {ι : Type} [Fintype ι]

variable [DecidableEq ι]

end Tensor

section Checks

variable {ι : Type} [Fintype ι]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms

end
