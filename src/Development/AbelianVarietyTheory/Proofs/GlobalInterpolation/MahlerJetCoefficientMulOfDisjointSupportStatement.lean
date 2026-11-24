module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulOfDisjointSupport
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.MomN

theorem _root_.GlobalTheory.T.mahlerJetCoefficient_mul_of_disjoint_support : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι'] (u : ι' → V) (F H : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ H → ∀ (S T : Finset ι'), Disjoint S T → (∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u F k = 0) → (∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u H k = 0) → (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = 0) ∧ (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) * GlobalTheory.MomN.mahler u H (fun p => if p ∈ T then N p else 0)) := by
  first | exact @GlobalTheory.mahler_mul_of_disjoint_support | exact GlobalTheory.mahler_mul_of_disjoint_support | (intros; apply GlobalTheory.mahler_mul_of_disjoint_support <;> assumption)
