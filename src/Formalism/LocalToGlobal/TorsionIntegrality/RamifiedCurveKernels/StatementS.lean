module

public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementR
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
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

section DefsS

variable {K : Type} [Field K]

def toZ {n : Type} (linv : PowerSeries K) (G : MvPowerSeries n K) : MvPowerSeries n K :=
  MvPowerSeries.subst
    (fun i => (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K)) G

def phSum {n : Type} [Fintype n] (c : n → K) (ph : PowerSeries K) : MvPowerSeries n K :=
  ∑ i, c i • (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) ph : MvPowerSeries n K)

def sqSum {n : Type} [Fintype n] (c : n → K) : MvPowerSeries n K :=
  ∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i ^ 2

def linSub {n m : Type} [Fintype m] (A : n → m → K) (f : MvPowerSeries n K) : MvPowerSeries m K :=
  MvPowerSeries.subst
    (fun i => (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x : MvPowerSeries m K)) f

end DefsS

def ShapeOrth : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K) (d : ℕ),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative (R := K) l) →
    PowerSeries.constantCoeff ph = 0 → ShapeAt l linv ph d →
    ∀ (n : Type) [Fintype n] (c : n → K), (∀ i, ‖c i‖ ≤ 1) →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    ∃ J : MvPowerSeries n K, JetsIntegral J ∧
      toZ linv (mvExp (-(phSum c ph)) * G) =
        mvExp (-(MvPowerSeries.C (jet l ph 2 / 2) * sqSum c)) * J

def EigenSplit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι T X : Type) [DecidableEq T] (ty : ι → T) (pr : T → T)
    (BB : ι → ι → K) (th : K) (chi chi' : X → T → K),
    th ≠ 0 → (∀ i j, ‖BB i j‖ ≤ 1) →
    (∀ x i j, ‖(chi x (ty i) - chi' x (ty j)) * BB i j‖ ≤ ‖th‖) →
    (∀ τ ρ, ρ ≠ pr τ → ∃ x, ‖chi x τ - chi' x ρ‖ = 1) →
    ∃ q : ι → ι → K, (∀ i j, ‖q i j‖ ≤ 1) ∧
      ∀ i j, BB i j = (if ty j = pr (ty i) then BB i j else 0) + th * q i j

def ShapeCong : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (n m : Type) [Fintype n] [Fintype m]
    (S0 th : K) (c : n → K) (A : n → m → K) (be Q2 : MvPowerSeries m K),
    ‖(2 : K)‖ = 1 → ‖S0 * th‖ ≤ 1 → (∀ i x, ‖A i x‖ ≤ 1) →
    MvPowerSeries.constantCoeff be = 0 → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum c) = MvPowerSeries.C 2 * be + MvPowerSeries.C th * Q2 →
    ∀ J : MvPowerSeries n K, JetsIntegral J →
    ∃ sg : MvPowerSeries m K, JetsIntegral sg ∧
      linSub A (mvExp (-(MvPowerSeries.C (S0 / 2) * sqSum c)) * J) = mvExp ((-S0) • be) * sg

end Formalism.L2.Th1.G
