module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
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

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (at1 cob d1 in3 swap2 DivAB)

section Alg

variable {K : Type} [Field K] [CharZero K]

def divByXSq (w : PowerSeries K) : PowerSeries K := PowerSeries.mk fun n => PowerSeries.coeff (n + 2) w

def sW (w : PowerSeries K) : PowerSeries K :=
  PowerSeries.X * fExp (PowerSeries.C (1 / 2 : K) * fLog (divByXSq w))

def gT (ep : PowerSeries K) (xT : K) : PowerSeries K := ep - PowerSeries.C xT * PowerSeries.X ^ 2

def thT (ep : PowerSeries K) (xT yT : K) : PowerSeries K :=
  (ep + PowerSeries.C yT * PowerSeries.X ^ 3) * (gT ep xT)⁻¹

def LT (ep : PowerSeries K) (xT yT a1 : K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.X 1 * at1 0 (thT ep xT yT) + MvPowerSeries.X 0 * at1 1 (thT ep xT yT) -
    MvPowerSeries.C a1 * MvPowerSeries.X 0 * MvPowerSeries.X 1

def thZ (s2 e1 kap : K) (w : PowerSeries K) : PowerSeries K :=
  sigma1 e1 kap w * fExp (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2))

end Alg

section Norm

open Formalism.DworkPowerSeriesWeights (Integral)

variable {K : Type} [NormedField K] [CharZero K]

def TwoHyp (g2 g3 c0 a1 a3 xT yT : K) : Prop :=
  2 * yT + a1 * xT + a3 = 0 ∧ 4 * (xT + c0) ^ 3 - g2 * (xT + c0) - g3 = 0 ∧
    ‖xT‖ ≤ 1 ∧ ‖yT‖ ≤ 1 ∧ ‖a1‖ ≤ 1 ∧ ‖3 * (xT + c0) ^ 2 - g2 / 4‖ ≤ 1

end Norm

end Formalism.L2.Th1.B
