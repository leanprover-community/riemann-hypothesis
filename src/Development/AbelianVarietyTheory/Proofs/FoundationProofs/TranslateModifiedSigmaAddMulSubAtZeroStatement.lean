module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaAddMulSubAtZero
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.U1_add_mul_U1_sub_at_zero_eq_wpF_sub : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P Q : ℂ, P ∉ Λ → Q ∉ Λ → U1 Λ (P + Q) (sgStar Λ) 0 * U1 Λ (P - Q) (sgStar Λ) 0 = (wpF Λ Q - wpF Λ P) * U1 Λ P (sgStar Λ) 0 ^ 2 * U1 Λ Q (sgStar Λ) 0 ^ 2 := by
  first | exact @GlobalTheory.translate_modifiedSigma_add_mul_sub_at_zero | exact GlobalTheory.translate_modifiedSigma_add_mul_sub_at_zero | (intros; apply GlobalTheory.translate_modifiedSigma_add_mul_sub_at_zero <;> assumption)
