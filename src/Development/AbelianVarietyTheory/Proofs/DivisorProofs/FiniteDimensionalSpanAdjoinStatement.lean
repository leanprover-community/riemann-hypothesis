module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAdjoin
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

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.finiteDimensional_span_adjoin_apply_of_annihilating : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V) (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) → ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) → FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := by
  first | exact @GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin | exact GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin | (intros; apply GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin <;> assumption)
