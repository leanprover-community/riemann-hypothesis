module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramDetIndexSublattice
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.gram_det_eq_sq_mul_gram_det_of_mem_span : ∀ (U V ι κ : Type) [AddCommGroup U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (φ : U →ₗ[ℤ] V) (u : ι → U) (v : κ → U), Fintype.card ι = Fintype.card κ → (∀ k, v k ∈ Submodule.span ℤ (Set.range u)) → ∃ m : ℕ, (Matrix.gram ℝ fun k => φ (v k)).det = (m : ℝ) ^ 2 * (Matrix.gram ℝ fun i => φ (u i)).det ∧ ∀ i, (m : ℤ) • u i ∈ Submodule.span ℤ (Set.range v) := by
  exact @GlobalTheory.gram_det_index_sublattice
