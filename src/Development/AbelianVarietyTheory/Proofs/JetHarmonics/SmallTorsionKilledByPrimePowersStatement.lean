module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowers
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

theorem _root_.GlobalTheory.T.smallTorsion_killed_by_prime_powers : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → (∀ p p', M.Small p → M.Small p' → M.Small (p + p') ∧ M.Small (-p)) ∧ (∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]), ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧ ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p)) ∧ (∀ p, PrimeTo d q p → M.Small p → InOK d p) ∧ ∀ (p α s : ℂ), InOK d α → α ≠ 0 → PrimeTo d q s → InOK d (α * p + s - 1 / 2) → M.Small p → q ≠ 2 ∧ InOK d (s - 1 / 2) := by
  first | exact @GlobalTheory.MomOne.smallTors | exact GlobalTheory.MomOne.smallTors | (intros; apply GlobalTheory.MomOne.smallTors <;> assumption)
