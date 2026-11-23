module

public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.InducedSectionsSpanStatement
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.RationalBitableauLatticeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

section B1
end B1

section B2
end B2

section B9
theorem global_sections_schur (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.GlobalSectionsSchur D := fun n _ mu R _ _ hR =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_one n mu R hR
end B9

section lowerOffDiagonalCoeff
theorem bracket_polynomial_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.BracketPolynomialSpan D := fun n _ mu hmu =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_two n mu hmu
end lowerOffDiagonalCoeff

section Mod

end Mod

section B6
end B6

end Formalism.MainNotions.G.ColumnFamilies
