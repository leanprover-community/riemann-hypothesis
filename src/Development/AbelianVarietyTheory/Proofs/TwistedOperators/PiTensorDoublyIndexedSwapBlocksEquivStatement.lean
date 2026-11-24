module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorDoublyIndexedSwapBlocksEquiv
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

open scoped TensorProduct

theorem _root_.GlobalTheory.T.piTensor_doubly_indexed_swap_blocks_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)] [∀ i j, Module ℂ (Y i j)] (σ : ∀ i j, Representation ℂ (GL (c i j) k) (Y i j)), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.piTensor fun j => σ i j).comp (GlobalTheory.SmGL.swapBlocks k c)) (GlobalTheory.SmGL.piTensor fun j => GlobalTheory.SmGL.piTensor fun i => σ i j)) := by
  first | exact @GlobalTheory.SmGL.piTensor_swapBlocks_equiv | exact GlobalTheory.SmGL.piTensor_swapBlocks_equiv | (intros; apply GlobalTheory.SmGL.piTensor_swapBlocks_equiv <;> assumption)
