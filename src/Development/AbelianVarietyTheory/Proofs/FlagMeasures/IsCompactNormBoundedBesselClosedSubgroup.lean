module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf


open scoped Matrix.Norms.L2Operator in
theorem isCompact_closed_inter_opn_le {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ)) (hS : IsClosed S)
    (R : ℝ) : IsCompact {g | g ∈ S ∧ opn g ≤ R} := by

  let e := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
  have hK : IsCompact (e ⁻¹' Metric.closedBall 0 R) :=
    e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hset : {g | g ∈ S ∧ opn g ≤ R} = S ∩ e ⁻¹' Metric.closedBall 0 R := by
    ext g
    simp [opn, e, mem_closedBall_zero_iff]
  rw [hset]
  exact hK.inter_left hS

theorem isCompact_normBounded : ∀ (k r : ℕ) (S : Set (Mat k r)), IsClosedSub k r S →
    ∀ R : ℝ, IsCompact {g | g ∈ S ∧ opn g ≤ R} := by
  intro k r S hS R
  exact isCompact_closed_inter_opn_le S hS.2.1 R

end GlobalTheory.SgInf
