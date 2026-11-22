module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

end GroundTheory.Heights₂.Heights
