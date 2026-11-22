module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.BlockSphereMeanLinForm

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

end GlobalTheory.ChowHt
