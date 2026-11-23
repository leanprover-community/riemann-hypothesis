module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementJ
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.L2.Th1.A (fgl iSer logSer wpReg g₂ g₃ IntModel)

section Defs

variable {K : Type} [Field K] [CharZero K]

def sgW (W : WeierstrassCurve K) (s2 : K) : PowerSeries K := sgStar s2 (wpReg W)

def phW (W : WeierstrassCurve K) (s2 : K) : PowerSeries K := phO s2 (wpReg W) (logSer W)

def beW (W : WeierstrassCurve K) (s2 : K) : MvPowerSeries (Fin 2) K := cob (fgl W) (phW W s2)

def e1W (W : WeierstrassCurve K) (xT : K) : K := xT + W.b₂ / 12

def kapW (W : WeierstrassCurve K) (xT : K) : K := 3 * e1W W xT ^ 2 - g₂ W / 4

def evenSigmaLogAtTwoTorsion (W : WeierstrassCurve K) (s2 xT : K) : PowerSeries K :=
  phE s2 (e1W W xT) (kapW W xT) (wOf (e1W W xT) (wpReg W)) (logSer W)

end Defs

def CurveSigma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    PowerSeries.constantCoeff (phW W s2) = 0 ∧
    PowerSeries.subst (logSer W) (sgW W s2) = PowerSeries.X * fExp (-phW W s2) ∧
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (atS (sgW W s2) * atD (sgW W s2)) =
      at1 0 (sgW W s2) ^ 2 * at1 1 (sgW W s2) ^ 2 * wpDiff (wpReg W)

def CurvePar : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W →
    Simeq (par (fgl W) (iSer W) (phW W s2)) 0 ∧
    Simeq (ι := Unit) (PowerSeries.subst (iSer W) (phW W s2)) (phW W s2) ∧
    Simeq (ι := Unit)
      (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), PowerSeries.X] (beW W s2))
      (2 * phW W s2) ∧
    ∀ (n : ℤ) (N : PowerSeries K), PowerSeries.constantCoeff N = 0 →
      PowerSeries.subst N (logSer W) = PowerSeries.C (n : K) * logSer W →
      Simeq (ι := Unit) (PowerSeries.subst N (phW W s2)) (((n ^ 2 : ℤ) : PowerSeries K) * phW W s2)

def WeierstrassBiadditiveModEquiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W → ‖(2 : K)‖ = 1 →
    DivAB (beW W s2) ∧ swap2 (beW W s2) = beW W s2 ∧
      Simeq (d1 (fgl W) (beW W s2)) 0 ∧ Simeq (d1 (fgl W) (swap2 (beW W s2))) 0

end Formalism.L2.Th1.B
