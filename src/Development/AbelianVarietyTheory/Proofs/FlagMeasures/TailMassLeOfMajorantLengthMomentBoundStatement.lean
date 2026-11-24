module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TailMassLeOfMajorantLengthMomentBound
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

theorem _root_.GlobalTheory.T.tail_mass_le_of_majorantLengthMomentBound : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ), 1 ≤ H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → ∀ i : ℕ, ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z (Matrix.of x))}, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal ((r + 1) * 4 ^ q * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
  first | exact @GlobalTheory.Amp.Cheb.tail_mass_le | exact GlobalTheory.Amp.Cheb.tail_mass_le | (intros; apply GlobalTheory.Amp.Cheb.tail_mass_le <;> assumption)
