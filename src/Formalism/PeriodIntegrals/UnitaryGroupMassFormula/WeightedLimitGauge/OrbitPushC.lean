module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI
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

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def hq (k : ℕ) (T' : ℝ) (y : Fin k → ℂ) (θ : ℝ) : (Fin k → ℂ) × ℂ :=
  (y, (Real.sqrt (∑ i, Complex.normSq (y i) + T') : ℂ) * Complex.exp (θ * Complex.I))

def hqI (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) : ℝ≥0∞ :=
  ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ∫⁻ y, E.indicator 1 (hq k T' y θ)

def HypTh : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ E, MeasurableSet E → hypM k T' E = c * hqI k T' E

def ConeVol : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ E, MeasurableSet E → volume (coneSh k T' E) = c * hqI k T' E

theorem coneForm_of (hH : HypTh) (hV : ConeVol) : ConeForm := by
  intro k T' hT'
  obtain ⟨c1, h10, h1t, h1⟩ := hH k T' hT'
  obtain ⟨c2, h20, h2t, h2⟩ := hV k T' hT'
  refine ⟨c1 / c2, ENNReal.div_pos h10 h2t |>.ne', ENNReal.div_ne_top h1t h20, fun E hE => ?_⟩
  rw [h1 E hE, h2 E hE, ← mul_assoc, ENNReal.div_mul_cancel h20 h2t]

end PI.RhsWLim.W
