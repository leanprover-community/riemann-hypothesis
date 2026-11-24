module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreGramNumberNullAndCutoffIntegralBound
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

theorem _root_.GlobalTheory.T.fibre_gramNumber_null_and_cutoff_integral_bound : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yv k r z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR k r β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  first | exact @GlobalTheory.Amp.FibNf.fibre_bound | exact GlobalTheory.Amp.FibNf.fibre_bound | (intros; apply GlobalTheory.Amp.FibNf.fibre_bound <;> assumption)
