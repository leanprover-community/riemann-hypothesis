module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
open scoped ComplexOrder

noncomputable section

abbrev ProjField (K : Type) [Field K] (i : ℕ) : Type := FractionRing (MvPolynomial (Fin i) K)

def LineOfLargeDegreeFromZ.Statement : Prop :=
  SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement → LineOfLargeDegree.Statement

end

end GroundTheory.Heights₂.Heights
