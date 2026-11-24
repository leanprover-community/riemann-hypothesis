module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharacters
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.exists_rapid_superposition_characters' : ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (Φ : Z → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (κ : X → ℂ) (τ : X → Z →L[ℝ] ℝ), Measurable κ ∧ (∀ z, Measurable fun x => τ x z) ∧ (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) ∧ ∀ z, Φ z = ∫ x, κ x * (𝐞 (τ x z) : ℂ) ∂ν := by
  first | exact @GlobalTheory.JSW.exists_rapid_superposition_characters | exact GlobalTheory.JSW.exists_rapid_superposition_characters | (intros; apply GlobalTheory.JSW.exists_rapid_superposition_characters <;> assumption)
