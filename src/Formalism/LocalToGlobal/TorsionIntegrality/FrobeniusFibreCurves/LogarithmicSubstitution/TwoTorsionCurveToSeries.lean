module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.DivByXSq
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementJ
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormHalfB2SubTwoTorsionLeOne
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
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
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Crv2

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr IsLogPair mulBy EndInt PhNormAt IsBinomScalar)
open Formalism.L2.Th1.A (fgl iSer logSer expSer wpReg g₂ g₃ IntModel xS tS xPlus bridgeWp bridgeLaw
  bridgeCurve bridgeCurve3)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem logPair (W : WeierstrassCurve K) : IsLogPair (logSer W) (expSer W) :=
  (Formalism.L2.Th1.C.curveFrame K ⊤ W ⟨trivial, trivial, trivial, trivial, trivial⟩).1

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem twoHyp (W : WeierstrassCurve K) (xT yT : K) (hW : IntModel W)
    (hE : W.toAffine.Equation xT yT) (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) (hx : ‖xT‖ ≤ 1)
    (hy : ‖yT‖ ≤ 1) : TwoHyp (g₂ W) (g₃ W) (W.b₂ / 12) W.a₁ W.a₃ xT yT :=
  ⟨h2, Crv.two_torsion_x_root_of_cubic W xT yT hE h2, hx, hy, hW.1, Crv.norm_kap W xT yT hW h2 hx hy⟩

end Norm

end Formalism.L2.Th1.B.Crv2
