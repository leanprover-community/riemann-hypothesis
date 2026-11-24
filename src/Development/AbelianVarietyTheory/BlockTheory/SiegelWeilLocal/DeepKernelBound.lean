module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound

open Formalism.MainNotions.S GlobalTheory.Count

def dimN (B : RowsAut) : ℕ := B.I.n ^ 2 * B.I.f

def stepBe (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt n * b ^ 2 + 3 / 2 * ((n : ℝ) * Real.sqrt n) + 3 * (P : ℝ)

def radRh (B : RowsAut) (q : ℕ) (τ : ℝ) : ℝ :=
  (B.I.n : ℝ) ^ 2 * Real.sqrt B.I.f * B.g * B.I.rd * (2 * τ) ^ ((1 : ℝ) / q) / 4

def DeepKernelBound : Prop :=
  ∀ (Cg : ℝ) (n₀ : ℕ) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ)
    (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA),
    0 ≤ Cg → 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b →
    (∀ v, IsGauge (B.I.ε v) (c v)) →
    least B.I x < tauStar B q b →
    (kern B.I (phe B d) x x).re ≤
      (2 * radRh B q (least B.I x) * Real.sqrt B.I.f *
            stepBe B.I.n b (8 * q * dimN B + dimN B)) ^ (16 * q * dimN B) *
        (6 * stepBe B.I.n b (8 * q * dimN B + dimN B)) ^ dimN B *
        Real.exp B.I.f *
        (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * dimN B) *
        (B.D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal

end GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound
