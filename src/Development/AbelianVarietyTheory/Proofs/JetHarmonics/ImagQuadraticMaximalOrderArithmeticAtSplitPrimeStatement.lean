module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
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

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → (InOK d 1 ∧ InOK d (wK d) ∧ ∀ α β, InOK d α → InOK d β → InOK d (α + β) ∧ InOK d (α * β) ∧ InOK d (-α) ∧ InOK d (conj α)) ∧ (∀ α, InOK d α → (∃ a : ℤ_[q], ι α = zc a) ∧ (∃ N : ℕ, (N : ℂ) = α * conj α) ∧ α ∈ algebraicClosure ℚ ℂ) ∧ (∀ (α : ℂ) (n : ℕ), InOK d α → ‖ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ‖ι (conj α)‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α / (q : ℂ) ^ n)) ∧ (∀ m s : ℕ, Nat.Coprime s q → ∃ e, InOK d e ∧ ‖ι ((s : ℂ) * e) - 1‖ ≤ (q : ℝ) ^ (-(m : ℤ)) ∧ ‖ι (conj e)‖ ≤ (q : ℝ) ^ (-(m : ℤ))) ∧ (∀ n : ℕ, ∃ α, InOK d α ∧ ‖ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) ∧ ¬ InOK d (α / 2)) ∧ (∀ x y, InOK d x → InOK d y → ∃ k : ℤ, (h1 d x y).im = k) ∧ ¬ q ∣ d := by
  first | exact @GlobalTheory.MomOne.okArith | exact GlobalTheory.MomOne.okArith | (intros; apply GlobalTheory.MomOne.okArith <;> assumption)
