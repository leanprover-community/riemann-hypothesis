module

public import Formalism.GradedWeylDivisibility.StatementB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

noncomputable section

namespace PI

def stdGram {N : ℕ} (ν : Fin N → ℕ) {r : ℕ} (e : Module.Basis (Fin r) ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)) :
    Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j =>
    Formalism.GradedWeylDivisibility.fockQ (MvPolynomial.map (Int.castRingHom ℚ) (e i : MvPolynomial (Fin N × Fin N) ℤ))
              (MvPolynomial.map (Int.castRingHom ℚ) (e j : MvPolynomial (Fin N × Fin N) ℤ)) /
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν)

def MuStd {N : ℕ} (ν : Fin N → ℕ) (μ : ℝ) : Prop :=
  ∃ (r : ℕ) (e : Module.Basis (Fin r) ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)), 0 < r ∧
    μ = -Real.log ((stdGram ν e).det : ℝ) / r

def cNu {N : ℕ} (ν : Fin N → ℕ) : ℝ :=
  (Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) : ℝ) / ∏ l, ((ν l).factorial : ℝ)

def HookBound : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ), Antitone ν →
    1 ≤ cNu ν ∧ cNu ν ≤ ((ν ⟨0, hN⟩ : ℝ) + N) ^ (N * (N - 1) / 2)

def StdSlopeLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (μ : ℝ), Antitone ν → MuStd ν μ →
    -((∑ l, (ν l : ℝ)) * Real.log N + Real.log (cNu ν)) ≤ μ

end PI
