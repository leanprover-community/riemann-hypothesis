module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le : ∀ (D : D7) (N : ℕ), Finite (Cls D N (intG D N)) ∧ (Nat.card (Cls D N (intG D N)) : ℝ) ≤ (12 * (fF D : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * fF D * N ^ 2) ∧ ∀ J : Subgroup (GA D N), J ≤ intG D N → J.relIndex (intG D N) ≠ 0 → Finite (Cls D N J) ∧ Nat.card (Cls D N J) ≤ Nat.card (Cls D N (intG D N)) * J.relIndex (intG D N) := by
  first | exact @GlobalTheory.NormSum.cls_finite_card_le | exact GlobalTheory.NormSum.cls_finite_card_le | (intros; apply GlobalTheory.NormSum.cls_finite_card_le <;> assumption)
