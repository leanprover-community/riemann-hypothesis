module

public import Formalism.IncomingBounds.IncomingBound
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlowProgrammeBoundsAndLowLevelOptimum
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

theorem _root_.GlobalTheory.T.flow_programme_bounds_and_low_level_optimum : ∀ (l d : ℕ) [NeZero d] (D : ZMod d → ℝ), 2 ≤ l → (∀ a, 0 ≤ D a) →
  rho l * ∑ a, D a ≤ Fnum l d D ∧ (∀ t : ℝ, 0 ≤ t → Fnum l d (fun a => t * D a) = t * Fnum l d D) ∧ Formalism.BasicNotions.lpF l d D = Fnum l d D ∧
  ∀ i₀ : ℕ, ∃ x : ZMod d → ℕ → ℝ, IsFlow l d D x ∧ (∀ a i, i₀ ≤ i → x a i = 0) ∧ gam l * ∑ a, D a - flowVal d x ≤ Fnum l d D + ((l : ℝ) ^ i₀)⁻¹ * ∑ a, D a := by
  first | exact @GlobalTheory.FlowProgrammeFacts.main | exact GlobalTheory.FlowProgrammeFacts.main | (intros; apply GlobalTheory.FlowProgrammeFacts.main <;> assumption)
