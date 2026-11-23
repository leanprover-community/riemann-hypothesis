module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
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

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.majorant_flag_lengths_invariance_torus_positivity : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), (∀ a, lA k r z (s * x * κ) a = lA k r z x a) ∧ Sg k r z (s * x * κ) = Sg k r z x) ∧ (∀ (a : Fin r → ℝ), (∀ b, 0 < a b) → ∀ m ∈ UH (Hb k), ∀ b : Fin r, lA k r z (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) b.castSucc = (a b)⁻¹) ∧ (∀ x, 1 ≤ Sg k r z x ∧ (∀ a, 0 ≤ lA k r z x a ∧ lA k r z x a ≤ Sg k r z x) ∧ (Sg k r z x = 1 ∨ ∃ a, Sg k r z x = lA k r z x a)) := by
  first | exact @GlobalTheory.Amp.LInv.lengths_basic | exact GlobalTheory.Amp.LInv.lengths_basic | (intros; apply GlobalTheory.Amp.LInv.lengths_basic <;> assumption)
