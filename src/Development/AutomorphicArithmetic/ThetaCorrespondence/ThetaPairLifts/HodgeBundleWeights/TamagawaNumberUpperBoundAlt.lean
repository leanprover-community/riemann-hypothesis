module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ArchimedeanTamagawaUpperBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberUpperBound
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.LevelStabilisers.MemStabOfLev
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ProductMapEquality.PiCdEqMap
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.UpperFactors.FactorUpper
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section
namespace MainStatements.Tam.Plug
theorem tamagawa_number_upper_bound : _root_.MainStatements.Tam.ArchimedeanTamagawaUpperBound := _root_.MainStatements.Tam.tamagawa_number_upper_bound MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.num
end MainStatements.Tam.Plug
end
