module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurveFilt

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section SupSpan

variable [DecidableEq K]

end SupSpan

end ReciprocityTheory.ChartRestriction.G.AI.I1
