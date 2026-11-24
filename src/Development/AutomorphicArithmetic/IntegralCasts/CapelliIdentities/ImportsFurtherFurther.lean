module

public import Mathlib.NumberTheory.NumberField.Basic
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

theorem UpperTheory.Reformulated.B.Qo3.exists_smul_mem_of_mem_span :
    ∀ {L V : Type} [inst : Field L] [NumberField L] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module L V] [inst_4 : _root_.Module (NumberField.RingOfIntegers L) V]
    [IsScalarTower (NumberField.RingOfIntegers L) L V] (Y : Submodule (NumberField.RingOfIntegers L) V) {S : Set V},
    (∀ x ∈ S, x ∈ Y) →
      ∀ {p : V},
        p ∈ Submodule.span L S →
          ∃ (b : NumberField.RingOfIntegers L), b ≠ (0 : NumberField.RingOfIntegers L) ∧ b • p ∈ Y := by
  intro L V _ _ _ _ _ _ Y S hS p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hS x hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Y.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Y.smul_mem b hax
    · rw [mul_smul]; exact Y.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers L)) c
    refine ⟨a * d, mul_ne_zero ha (nonZeroDivisors.coe_ne_zero d), ?_⟩
    have h : (d : NumberField.RingOfIntegers L) • (c • x) = n • x := by
      rw [← algebraMap_smul L (d : NumberField.RingOfIntegers L), smul_smul, mul_comm, hnd,
        algebraMap_smul]
    rw [mul_smul, h, smul_comm]
    exact Y.smul_mem n hax
