module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWIrreducibleAndSchurAverage
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.hcTypeW_irreducible_and_schur_average : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → (∀ u, IsHCTypeW k r z u π → Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π) ∧ ∀ μW : Measure (Mt k r), IsURepOn (UWset k r z) π → IsIrredOn (UWset k r z) π → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → ∀ w ξ : Wp, ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW = ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) := by
  first | exact @GlobalTheory.Amp.Schur.type_irred_and_avg | exact GlobalTheory.Amp.Schur.type_irred_and_avg | (intros; apply GlobalTheory.Amp.Schur.type_irred_and_avg <;> assumption)
