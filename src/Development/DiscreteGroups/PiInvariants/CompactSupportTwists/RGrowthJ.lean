module

public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CutTailC
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.DomOneMeasure
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.KerSplitLIntSub
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

@[expose] public section

noncomputable section

open PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

theorem rGrowthPiJ_of (hU : PiVecEx → PiInv → UncutHalf) (hT : PiVecEx → PiInv → CutTail2) : RGrowthPiJ :=
  fun hE hS hV hI => growth_of_ellipticFormula hE hS domOne kerSplit (hU hV hI) (hT hV hI)

end DiscreteGroups.T1.G

end
