module

public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
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
public import ReciprocityTheory.SemistableReduction.DetSubtypeCompAssociatedProd
public import ReciprocityTheory.SemistableReduction.GaussExtensionAndResidueTrdegEq
public import ReciprocityTheory.SemistableReduction.GenericImageFinite
public import ReciprocityTheory.SemistableReduction.IntegralClosureRankAndResidueTrdegLe
public import ReciprocityTheory.SemistableReduction.NormValuationEqFactorization

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem fieldOfS : FieldOfSStatement := genericImageFinite

theorem dedekindRank : DedekindRankStatement := integralClosureRank_and_residueTrdegLe.1

theorem residueTrdeg : ResidueTrdegStatement := residueTrdeg_holds residueTrdegLe

theorem normLength : NormLengthStatement := gaugeSplitting_holds

theorem normOrd : NormOrdStatement := normValuation_eq_factorization normLength

end ReciprocityTheory.MultiplicativeHeights.Closed
