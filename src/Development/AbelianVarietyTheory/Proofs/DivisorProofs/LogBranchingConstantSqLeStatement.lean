module

public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLe
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

open Formalism.BasicNotions


theorem _root_.GlobalTheory.T.log_branching_constant_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B → (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) → Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  first | exact @GlobalTheory.BranchBound.log_brBd_sq_le | exact GlobalTheory.BranchBound.log_brBd_sq_le | (intros; apply GlobalTheory.BranchBound.log_brBd_sq_le <;> assumption)
