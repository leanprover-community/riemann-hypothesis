module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductRenormalization
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

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.infinite_product_renormalization : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (c : Finset ι → ℝ≥0) (S₁ : Finset ι), (∀ v, 0 ≤ a v) → Summable (fun v => |a v - 1|) → (∀ S, S₁ ⊆ S → ∀ v, v ∉ S → (c S : ℝ) = c (insert v S) * a v) → ∃ (c₀ : ℝ≥0) (S₀ : Finset ι), S₁ ⊆ S₀ ∧ ∀ S, S₀ ⊆ S → (0 < ∏' v : {v // v ∉ S}, a v.1) ∧ (c S : ℝ) = c₀ * ∏' v : {v // v ∉ S}, a v.1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail | exact GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail | (intros; apply GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail <;> assumption)
