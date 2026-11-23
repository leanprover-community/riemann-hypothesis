module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupport
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas

@[expose] public section

open GlobalTheory.Orb
open scoped Topology ContDiff Manifold

theorem _root_.GlobalTheory.T.exists_contDiff_comp_of_locally_smooth_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c → HasCompactSupport f → (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧ ∀ g, c g ∈ V → f g = Φ (c g)) → ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  first | exact @GlobalTheory.glue_smooth_of_compactSupport | exact GlobalTheory.glue_smooth_of_compactSupport | (intros; apply GlobalTheory.glue_smooth_of_compactSupport <;> assumption)
