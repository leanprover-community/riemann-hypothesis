module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair
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
import Mathlib.Tactic.Linter.Style
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

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def UnitInv : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ q ∈ UWb k r, qᴴ * q = 1 → ν.map (rmulM q) = ν

def HermInv : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ B₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, B₀ᴴ * Hb k * B₀ = Hb k → B₀ᴴ = B₀ →
      ν.map (rmulM (embWb k r B₀)) = ν

def PolarDecW : Prop :=
  ∀ (k r : ℕ) (p : Mat k r), p ∈ UWb k r → ∃ B₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
    B₀ᴴ * Hb k * B₀ = Hb k ∧ B₀ᴴ = B₀ ∧ ∃ q ∈ UWb k r, qᴴ * q = 1 ∧ p = embWb k r B₀ * q

theorem rmulM_comp {k r : ℕ} (a b : Mat k r) : rmulM b ∘ rmulM a = rmulM (a * b) := by
  funext x
  show Matrix.of x * a * b = Matrix.of x * (a * b)
  rw [Matrix.mul_assoc]

theorem rmulM_meas {k r : ℕ} (p : Mat k r) : Measurable (rmulM p : Mt k r → Mt k r) :=
  (rmulM_cont p).measurable

theorem unimodW_of (hU : UnitInv) (hH : HermInv) (hP : PolarDecW) : UnimodW := by
  intro k r ν hk hG p hp
  obtain ⟨B₀, hB, hBh, q, hq, hqu, rfl⟩ := hP k r p hp
  rw [← rmulM_comp, ← Measure.map_map (rmulM_meas q) (rmulM_meas _), hH k r ν hk hG B₀ hB hBh,
    hU k r ν hk hG q hq hqu]

end PI.RhsWLim.W
