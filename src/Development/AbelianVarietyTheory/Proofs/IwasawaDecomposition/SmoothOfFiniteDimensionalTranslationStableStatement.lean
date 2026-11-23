module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfFiniteDimensionalTranslationStable
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

open MeasureTheory Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.deriv_mem_and_contDiff_of_translation_stable : ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by
  first | exact @GlobalTheory.smooth_of_finiteDimensional_translation_stable | exact GlobalTheory.smooth_of_finiteDimensional_translation_stable | (intros; apply GlobalTheory.smooth_of_finiteDimensional_translation_stable <;> assumption)
