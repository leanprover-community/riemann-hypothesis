module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankFiltrationStep
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


theorem _root_.GlobalTheory.T.low_rank_filtration_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ), r < Fintype.card A → ∀ Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix A D k → ℂ)), Φ ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank | exact GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank | (intros; apply GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank <;> assumption)
