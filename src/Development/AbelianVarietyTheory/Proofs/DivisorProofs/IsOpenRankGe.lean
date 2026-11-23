module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalFormStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Matrix

theorem GlobalTheory.isOpen_setOf_le_rank_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (s : ℕ), IsOpen {X : Matrix A D k | s ≤ X.rank} := by
  intro k _ _ _ _ A D _ _ _ _ s
  rw [isOpen_iff_mem_nhds]
  intro X hX
  obtain ⟨H, Q, hHQ⟩ := GlobalTheory.T.matrix_rank_normal_form k A D X
  have hc : Continuous fun Y : Matrix A D k => (H * Y * Q).det :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
  have hopen : IsOpen {Y : Matrix A D k | (H * Y * Q).det ≠ 0} :=
    isOpen_ne_fun hc continuous_const
  filter_upwards [hopen.mem_nhds (by simp [hHQ])] with Y hY
  replace hY : (H * Y * Q).det ≠ 0 := hY
  show s ≤ Y.rank
  refine le_trans hX ?_
  have hu : IsUnit (H * Y * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hY)
  have hr : (H * Y * Q).rank = X.rank := by
    rw [Matrix.rank_of_isUnit _ hu]; simp
  calc X.rank = (H * Y * Q).rank := hr.symm
    _ ≤ (H * Y).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Y.rank := Matrix.rank_mul_le_right _ _
