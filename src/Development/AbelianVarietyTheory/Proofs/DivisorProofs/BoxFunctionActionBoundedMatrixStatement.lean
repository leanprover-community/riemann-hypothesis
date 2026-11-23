module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionActionBoundedMatrix
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

open ValuativeRel Matrix


theorem _root_.GlobalTheory.T.box_function_action_bounded_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (t : Fin r → k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → (∀ l, valuation k (t l) ≤ valuation k ((ϖ ^ c : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ (C i₀ + t ᵥ* (H * C))) (fun _ => m) - GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan | exact GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan | (intros; apply GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan <;> assumption)
