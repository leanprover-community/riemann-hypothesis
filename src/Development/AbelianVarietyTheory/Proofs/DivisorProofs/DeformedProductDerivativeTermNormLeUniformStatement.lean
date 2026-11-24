module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedProductDerivativeTermNormLeUniform
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

theorem _root_.GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (m : I → ℕ) (r : ℝ), r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 → ‖dTerm φ (2 * s) m z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) := by
  first | exact @GlobalTheory.DeformedSum.Bound.dTerm_bound | exact GlobalTheory.DeformedSum.Bound.dTerm_bound | (intros; apply GlobalTheory.DeformedSum.Bound.dTerm_bound <;> assumption)
