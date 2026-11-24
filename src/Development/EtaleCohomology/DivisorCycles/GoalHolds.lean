module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.DivWCoreLacUseType
public import Development.EtaleCohomology.DivisorCycles.FinBigCorner
public import Development.EtaleCohomology.DivisorCycles.FinDegAll
public import Development.EtaleCohomology.DivisorCycles.FinDenseAlg
public import Development.EtaleCohomology.DivisorCycles.FinFinDense
public import Development.EtaleCohomology.DivisorCycles.FinFinEmbed
public import Development.EtaleCohomology.DivisorCycles.FinFinPoly
public import Development.EtaleCohomology.DivisorCycles.FinFinSub
public import Development.EtaleCohomology.DivisorCycles.FinKey
public import Development.EtaleCohomology.DivisorCycles.FinMatUnits
public import Development.EtaleCohomology.DivisorCycles.FinRep
public import Development.EtaleCohomology.DivisorCycles.FinSemis
public import Development.EtaleCohomology.DivisorCycles.FinSpecLie
public import Development.EtaleCohomology.DivisorCycles.FinStruct
public import Development.EtaleCohomology.DivisorCycles.Imports
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

theorem goal_holds : DivWCoreLac :=
  goal_of LateralTheory.Fin.SpecLie.intersectionNumber_baseChange LateralTheory.Fin.DegAll.intersectionNumber_baseChange LateralTheory.Fin.Struct.intersectionNumber_baseChange LateralTheory.Fin.Key.intersectionNumber_baseChange LateralTheory.Fin.BigCorner.intersectionNumber_baseChange LateralTheory.Fin.Semis.intersectionNumber_baseChange LateralTheory.Fin.MatrixUnits₂.intersectionNumber_baseChange LateralTheory.Fin.Rep.intersectionNumber_baseChange LateralTheory.Fin.DenseAlg.intersectionNumber_baseChange LateralTheory.Fin.FinSub.intersectionNumber_baseChange LateralTheory.Fin.FinDense.intersectionNumber_baseChange LateralTheory.Fin.FinPoly.intersectionNumber_baseChange LateralTheory.Fin.FinEmbed.intersectionNumber_baseChange

end LateralTheory.DivDb
