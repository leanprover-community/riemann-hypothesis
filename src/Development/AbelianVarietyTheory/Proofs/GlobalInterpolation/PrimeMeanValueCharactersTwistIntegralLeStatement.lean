module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeMeanValueCharactersTwistIntegralLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.primeMeanValue_characters_twist_integral_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T N y : ℝ) (a : ℕ → ℂ), 1 ≤ T → (2 * q * T) ^ 2 ≤ N → ∑ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T, ‖∑ p ∈ primesIoc N y, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤ C * ∑ p ∈ primesIoc N y, (p : ℝ) * ‖a p‖ ^ 2 / Real.log p := by
  first | exact @GlobalTheory.PrimeMeanValue.prime_mean_value | exact GlobalTheory.PrimeMeanValue.prime_mean_value | (intros; apply GlobalTheory.PrimeMeanValue.prime_mean_value <;> assumption)
