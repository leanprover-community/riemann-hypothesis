module

import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsSubgroupHolds
public import Formalism.EllipticTorsion.FormalGroupPointsTorsionFree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u

noncomputable section

namespace Formalism.ELL.TorsionIntegralEllipticTorsion

open WeierstrassCurve Formalism.ELL

lemma y_int {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) :
    ‖y‖ ≤ 1 := by
  apply Formalism.ELL.FormalGroupPointsSubgroup.y_int <;> assumption

end Formalism.ELL.TorsionIntegralEllipticTorsion

namespace Formalism.ELL

open WeierstrassCurve

theorem torsionIntegral_of (h : Formalism.ELL.FormalGroupPointsTorsionFree.{u}) : Formalism.ELL.TorsionIntegral.{u} := by
  intro K _ _ W hW hΔ n hn x y hxy hnP
  have hx : ‖x‖ ≤ 1 := by
    by_contra hx
    push Not at hx
    exact Affine.Point.some_ne_zero hxy (h K W hW hΔ n hn _ hx hnP)
  exact ⟨hx, TorsionIntegralEllipticTorsion.y_int W hW hxy.1 hx⟩

end Formalism.ELL
