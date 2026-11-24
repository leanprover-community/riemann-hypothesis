module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
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

theorem _root_.GlobalTheory.T.normalFormFlagZero_middle_inverse_minor_orthogonal : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → Tz k r z' = Tz k r z ∧ (∃ m ∈ UH (Hb k), ∀ w, inWb k r w → g₀ *ᵥ w = mEmb k r m *ᵥ w) ∧ IsNormal0 k r hj β c⁻¹ z' z g₀⁻¹ ∧ 0 < Dj k r hj z z' g₀ ∧ Dj k r hj z' z g₀⁻¹ = Dj k r hj z z' g₀ ∧ (∀ l : Fin (r + 2), ‖Dmin k r z' z g₀⁻¹ l‖ = ‖Dmin k r z z' g₀ l‖) ∧ ∀ w, w ∈ Hcom k r z z' g₀ ⊔ Xsp k r ↔ ∀ a : Fin (r + 1), herm (Hpk k r) w (fvec k r z' a) = 0 := by
  first | exact @GlobalTheory.Amp.NfMid.normal0_middle | exact GlobalTheory.Amp.NfMid.normal0_middle | (intros; apply GlobalTheory.Amp.NfMid.normal0_middle <;> assumption)
