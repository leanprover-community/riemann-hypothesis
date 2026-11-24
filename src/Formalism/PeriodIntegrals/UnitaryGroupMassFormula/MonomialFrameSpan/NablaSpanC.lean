module

public import Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl
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

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

abbrev nablaSpanC (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 : ℕ)
    (nu : Lt → YoungDiagram) : Submodule ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) :=
  Submodule.span ℂ_[l] (Set.range fun J : ColChoice N0 nu =>
    MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J))

def StepBack : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ),
    ExpansionCoeffValuationGe N0 N1 l nu Th B → KvalGe N0 N1 l nu Th B

def StepSpan : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (I : ColChoice N1 nu),
    applyAt0 N0 N1 l Th (Gxz N0 N1 nu I) ∈ nablaSpanC Lt l N0 nu

def StepSat : Prop :=
  MinorProdSpanHasCompl → ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 : ℕ)
    (nu : Lt → YoungDiagram) (P : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) (B : ℝ),
    P ∈ nablaSpanC Lt l N0 nu →
    (∀ m, ‖AddMonoidAlgebra.coeff P m‖ ≤ (l : ℝ) ^ (-B)) →
    ∃ c : ColChoice N0 nu →₀ ℂ_[l], (∀ J, ‖c J‖ ≤ (l : ℝ) ^ (-B)) ∧
      P = c.sum fun J a => a • MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)

end GenFrameSpan
