module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

def wp3 (P : PowerSeries K) (j k : Fin 3) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.X j ^ 2 - MvPowerSeries.X k ^ 2 +
    MvPowerSeries.X j ^ 2 * MvPowerSeries.X k ^ 2 * (at1 k P - at1 j P)

def det3 (P : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  Matrix.det (Matrix.of fun j : Fin 3 =>
    ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K) ^ 3,
      MvPowerSeries.X j * (1 + MvPowerSeries.X j ^ 2 * at1 j P),
      -2 + MvPowerSeries.X j ^ 3 * at1 j (dz P)])

def vand3 (K : Type) [Field K] : MvPowerSeries (Fin 3) K :=
  (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
    (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) *
    (MvPowerSeries.X 1 - MvPowerSeries.X 2)

def evalSumThree (f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  PowerSeries.subst
    (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f

def evalDiffThree (j k : Fin 3) (f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  PowerSeries.subst (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K) f

def fsE (f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  evalSumThree f + evalDiffThree 0 1 f + evalDiffThree 0 2 f + evalDiffThree 1 2 f - 3 * at1 0 f - 3 * at1 1 f - 3 * at1 2 f

def ev3 (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1, 0] h

def F3 (F : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] F

def lawDifferenceThree (F : MvPowerSeries (Fin 2) K) (i : PowerSeries K) (j k : Fin 3) :
    MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), at1 k i] F

def par3 (F : MvPowerSeries (Fin 2) K) (i f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  PowerSeries.subst (F3 F) f + PowerSeries.subst (lawDifferenceThree F i 0 1) f +
    PowerSeries.subst (lawDifferenceThree F i 0 2) f + PowerSeries.subst (lawDifferenceThree F i 1 2) f -
    3 * at1 0 f - 3 * at1 1 f - 3 * at1 2 f

end Alg

section Norm

open Formalism.DworkPowerSeriesWeights (Integral)

variable {K : Type} [NormedField K]

def CurveHyp3 (F : MvPowerSeries (Fin 2) K) (l P ep : PowerSeries K) (a1 a3 : K) : Prop :=
  PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative (R := K) P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3) ∧
    ∃ e : MvPowerSeries (Fin 3) K, Integral e ∧ MvPowerSeries.constantCoeff e = -1 ∧
      Matrix.det (Matrix.of fun j : Fin 3 =>
        ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K) ^ 3, MvPowerSeries.X j * at1 j ep,
          -at1 j ep]) =
        e * F3 F * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
          (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2)

end Norm

end Formalism.L2.Th1.B
