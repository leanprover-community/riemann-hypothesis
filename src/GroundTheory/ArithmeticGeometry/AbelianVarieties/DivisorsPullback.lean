module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsOrd
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FunctionFieldPoint
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

universe u

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]



variable [IsAlgClosed F]


omit [DecidableEq F] [W.IsElliptic] [IsAlgClosed F] in
theorem aeval_genX (p : F[X]) :
    aeval (genX W) p = algebraMap F[X] W.toAffine.FunctionField p := by
  simp only [genX_eq, aeval_algebraMap_apply, aeval_X_left, AlgHom.id_apply]

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem valuationInfty_algebraMap_const_eq_one {c : F} (hc : c ≠ 0) :
    valuationInfty W (algebraMap F W.toAffine.FunctionField c) = 1 := by
  rw [valuationInfty_eq_exp W ((map_ne_zero_iff _ (algebraMap F _).injective).mpr hc),
    ordInfty_algebraMap_const W hc, neg_zero, exp_zero]


end GroundTheory.Arith.Abelian
