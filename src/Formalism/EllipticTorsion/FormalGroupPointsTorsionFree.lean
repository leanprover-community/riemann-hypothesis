module

public import Formalism.EllipticTorsion.Statement
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
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

universe u

noncomputable section

local instance (α : Sort u) : DecidableEq α := Classical.decEq α

namespace Formalism.ELL

open WeierstrassCurve

def InFormalGroupPoints {K : Type u} [NormedField K] {W : WeierstrassCurve K} : W.toAffine.Point → Prop
  | .zero => True
  | .some x _ _ => 1 < ‖x‖


open Classical in
def FormalGroupPointsSubgroup' : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ P Q : W.toAffine.Point, InFormalGroupPoints P → InFormalGroupPoints Q → InFormalGroupPoints (P + Q) ∧ InFormalGroupPoints (-P)


def FormalGroupPointsTorsionFree : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ (n : ℕ), ‖(n : K)‖ = 1 → ∀ P : W.toAffine.Point, InFormalGroupPoints P → n • P = 0 → P = 0


def TorsionIntegral : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ (n : ℕ), ‖(n : K)‖ = 1 → ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      n • (Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1

end Formalism.ELL
