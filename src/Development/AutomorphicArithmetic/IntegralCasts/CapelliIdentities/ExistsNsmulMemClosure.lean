module

public import Mathlib.Algebra.Ring.Rat
public import Mathlib.LinearAlgebra.Span.Defs
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

theorem UpperTheory.Reformulated.B.ExistsNsmulMemClosure.exists_nsmul_mem_closure.{u_1} :
    ∀ {V : Type u_1} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℚ V] (s : Set V),
    ∀ w ∈ Submodule.span ℚ s, ∃ (k : ℕ), (0 : ℕ) < k ∧ k • w ∈ AddSubgroup.closure s := by
  intro V _ _ s w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using AddSubgroup.subset_closure hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact add_mem (nsmul_mem hx b) (nsmul_mem hy a)
  | smul q x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    refine ⟨q.den * a, Nat.mul_pos q.den_pos ha, ?_⟩
    have h : (q.den * a) • (q • x) = q.num • (a • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ a x,
        ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
      congr 1
      rw [← Rat.mul_den_eq_num q]
      push_cast
      ring
    rw [h]
    exact zsmul_mem hx _
