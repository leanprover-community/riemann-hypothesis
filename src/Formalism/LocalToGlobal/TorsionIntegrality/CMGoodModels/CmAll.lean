module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgStatus
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorStatus

@[expose] public section

namespace Formalism.L2.Th1.CM

theorem cm1 : JInvariantIntegrality := ReciprocityTheory.ChartRestriction.L1.cm1
theorem cm4 : CM4 := ReciprocityTheory.ChartRestriction.L1.cm4
theorem cm3 : CM3 := ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree
theorem cm2 [h : Fact CM2] : CM2 := h.out

end Formalism.L2.Th1.CM
