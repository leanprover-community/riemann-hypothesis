module

public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementS
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementP
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

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.G (linSub)
open Formalism.DworkPowerSeriesWeights (JetsIntegral mfact)

def scl {K : Type} [Field K] (n : Type) [DecidableEq n] (c : K) : n → n → K := fun i j => if i = j then c else 0

def LogDerJets : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F a : PowerSeries K) (ρ : ℝ), 1 ≤ ρ →
    PowerSeries.derivative (R := K) F = a * F → ‖PowerSeries.constantCoeff F‖ ≤ 1 →
    (∀ i : ℕ, ‖((i.factorial : ℕ) : K) * PowerSeries.coeff i a‖ ≤ ρ) →
    ∀ i : ℕ, ‖((i.factorial : ℕ) : K) * PowerSeries.coeff i F‖ ≤ ρ ^ i

def PowLogDer : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (G V : PowerSeries K) (c : K) (M : ℕ), 0 < M → c ≠ 0 →
    G ^ M = PowerSeries.C (c ^ M) * V →
    PowerSeries.C (M : K) * (PowerSeries.derivative (R := K) G * V) = G * PowerSeries.derivative (R := K) V

def ProdScaleJets : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (κ n : Type) [Fintype κ] [Fintype n] [DecidableEq n] (c : K)
    (r : κ → K) (H : κ → n → PowerSeries K), (∀ k, ‖r k‖ ≤ 1) →
    (∀ k i (j : ℕ), ‖((j.factorial : ℕ) : K) * PowerSeries.coeff j (H k i)‖ * ‖c‖ ^ j ≤ 1) →
    JetsIntegral (linSub (scl n c) (Formalism.L2.Th1.E.thetaProd r H))

def LinScale : Prop :=
  ∀ (K : Type) [Field K] (n m : Type) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (c : K) (A : n → m → K)
    (f : MvPowerSeries n K),
    linSub (scl m c) (linSub A f) = linSub (fun i x => c * A i x) f ∧
    linSub A (linSub (scl n c) f) = linSub (fun i x => c * A i x) f

end Formalism.L2.AlgTh
