module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralContinuousMultilinearMapPiMeasure
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.integral_continuousMultilinearMap_pi_measure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (E : ι → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i), (∀ i, Integrable (g i) (μ i)) → Integrable (fun x : ∀ i, X i => Φ fun i => g i (x i)) (Measure.pi μ) ∧ ∫ x, Φ (fun i => g i (x i)) ∂Measure.pi μ = Φ fun i => ∫ y, g i y ∂μ i := by
  first | exact @GlobalTheory.MultilinFubini.integral_multilinear_pi | exact GlobalTheory.MultilinFubini.integral_multilinear_pi | (intros; apply GlobalTheory.MultilinFubini.integral_multilinear_pi <;> assumption)
