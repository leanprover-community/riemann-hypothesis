module

public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementS
public import Formalism.GaussJetBounds.StatementI
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
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

section DefsT

variable {K : Type} [Field K]

def th0 [CharZero K] (W : WeierstrassCurve K) (x0 y0 s2 : K) : PowerSeries K :=
  mvExp (-(lam (wTr W x0 y0) s2))

end DefsT

def KernelTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative (R := K) l) →
    PowerSeries.constantCoeff ph = 0 → (∀ i : ℕ, 1 ≤ i → ‖jet l ph i‖ ≤ 1) →
    ∀ (n : Type) [Fintype n] (c : n → K), (∀ i, ‖c i‖ ≤ 1) →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    JetsIntegral (toZ linv (mvExp (-(phSum c ph)) * G)) ∧
    ∀ P : MvPolynomial n K, (∀ m, ‖AddMonoidAlgebra.coeff P m‖ ≤ 1) →
      ‖jetPair P (toZ linv (mvExp (-(phSum c ph)) * G))‖ ≤ 1

def SplitVanishTwo : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ (l linv ph : PowerSeries K) (a b : K),
    Frame R l linv ph → F1 R l linv ph → EndInt R l linv a →
    a ∈ closure (Set.range (fun n : ℤ => (n : K))) → PhNormAt R l linv ph a b →
    a ≠ 0 → a ≠ b → b ≠ 1 →
    IsBinomScalar R (a * (a - b))⁻¹ → IsBinomScalar R (a * (1 - b))⁻¹ →
    LG R ph

end Formalism.L2.Th1.G
