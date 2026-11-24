module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.DivideAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.IsWeightedHomogeneousPairingLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.PairingPowMemSymbolRange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.PolarizationBihomogeneous
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

namespace PI.OpWords

theorem opBound_of_vanish (hV : Vanish) : Formalism.MainNotions.TestSideCounting.OpBound :=
  opWords_of symbolMapInjective symbolMapMulLeft symbolMapMulRight symbolMapBihomogeneous weightOfEigenvector
    polarizationBihomogeneous rttRelation pairingWeightCancel pairingDivisibility hV pairingPowMemSymbolRange

end PI.OpWords
