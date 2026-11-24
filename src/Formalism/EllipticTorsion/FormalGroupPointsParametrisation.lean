module

public import Formalism.EllipticTorsion.FormalGroupPointsTorsionFree
public import Formalism.EllipticTorsion.WChordSeries
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

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

def evalPS {K : Type u} [NormedField K] (f : PowerSeries K) (t : K) : K :=
  ∑' n : ℕ, coeff n f * t ^ n

def evalMv2 {K : Type u} [NormedField K] (F : MvPowerSeries (Fin 2) K) (a b : K) : K :=
  ∑' d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F * a ^ (d 0) * b ^ (d 1)

def uOf {K : Type u} [Field K] {W : WeierstrassCurve K} : W.toAffine.Point → K
  | .zero => 0
  | .some x y _ => -x / y

def FormalGroupPointsParametrisation : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (W : WeierstrassCurve K) (w : PowerSeries K), IntegralModel W → WFixed W w →
    (∀ t : K, 0 < ‖t‖ → ‖t‖ < 1 →
      evalPS w t ≠ 0 ∧ W.toAffine.Nonsingular (t / evalPS w t) (-1 / evalPS w t) ∧
        1 < ‖t / evalPS w t‖ ∧ -(t / evalPS w t) / (-1 / evalPS w t) = t) ∧
    (∀ (x y : K), W.toAffine.Nonsingular x y → 1 < ‖x‖ →
      0 < ‖-x / y‖ ∧ ‖-x / y‖ < 1 ∧
        x = (-x / y) / evalPS w (-x / y) ∧ y = -1 / evalPS w (-x / y))


open scoped Classical in
open Classical in
def FormalGroupPointsHomomorphism : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (W : WeierstrassCurve K) (w : PowerSeries K) (F₂ : MvPowerSeries (Fin 2) K),
    IntegralModel W → WFixed W w → IntegralMv F₂ → MvPowerSeries.constantCoeff F₂ = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F₂ →
    ∀ P Q : W.toAffine.Point, InFormalGroupPoints P → InFormalGroupPoints Q → uOf (P + Q) = evalMv2 F₂ (uOf P) (uOf Q)

end Formalism.ELL
