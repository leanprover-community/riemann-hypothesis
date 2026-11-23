module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoordinatesInverseFirstColumnInfiniteGL
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

theorem _root_.GlobalTheory.T.exists_coordinates_inverseFirstColumn_infiniteGL : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ), 1 ≤ k → ∃ (hh : MatInf E (k + 1) → MatInf E k) (TT : MatInf E (k + 1) → VecInf E k), Measurable hh ∧ Measurable TT ∧ (∀ g, 0 < detNorm E (k + 1) g → detNorm E k (hh g) = detNorm E (k + 1) g) ∧ (∀ g γ : MatInf E (k + 1), 0 < detNorm E (k + 1) g → 0 < detNorm E (k + 1) γ → (∀ w a, γ w a 0 = if a = 0 then 1 else 0) → ∀ β : MatInf E k, (∀ w a b, β w a b = γ w a.succ b.succ) → hh (γ * g) = β * hh g ∧ ∀ w, TT (γ * g) w ᵥ* Matrix.of (β w) = TT g w + fun b => γ w 0 b.succ) ∧ ∀ (F : MatInf E k → ENNReal) (Q : VecInf E k → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable F → Measurable Q → Measurable Φ → ∫⁻ g, F (hh g) * Q (TT g) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0) ∂(haarGL E (k + 1)) = (∫⁻ x, Φ x) * (∫⁻ T, Q T) * ∫⁻ h, F h * ENNReal.ofReal (detNorm E k h) ∂(haarGL E k) := by
  first | exact @GlobalTheory.FirstColumnCoord.coordinates | exact GlobalTheory.FirstColumnCoord.coordinates | (intros; apply GlobalTheory.FirstColumnCoord.coordinates <;> assumption)
