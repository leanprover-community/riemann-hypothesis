module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideUnfolding
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitude_one_side_unfolding : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (c : ℝ), OneSide z π ψ μG μW μN νS Φ c → ∀ (f : Mt k r → ℝ≥0∞) (Q : Set (Mt k r)) (Vol : ℝ≥0∞), Measurable f → MeasurableSet Q → (∀ s ∈ Sset k r z, ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q)) → (∀ g ∈ GG k r, ∫⁻ n, f (rmulM g n) ∂μN ≤ Vol) → ∀ w : Wp, ‖w‖ = 1 → ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS := by
  first | exact @GlobalTheory.Amp.OnePiece.one_piece | exact GlobalTheory.Amp.OnePiece.one_piece | (intros; apply GlobalTheory.Amp.OnePiece.one_piece <;> assumption)
