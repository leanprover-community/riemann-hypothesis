module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeNotJointShapeSmallerPairs
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.lowestType_not_jointShape_smaller_pairs : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → ∀ μ', ¬ JointShape _ _ (al.length + de.length + t - i) (ga.length + be.length - i) (blattner (lamA al be ga de)) μ') ∧ (i ≤ al.length + de.length → i ≤ ga.length + be.length + t → ∀ μ', ¬ JointShape _ _ (al.length + de.length - i) (ga.length + be.length + t - i) (blattner (lamA al be ga de)) μ') ∧ ((¬ (∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2) ∨ ¬ (∃ a, lamA al be ga de a = -(((t : ℚ) + 1) / 2))) → i ≤ al.length + be.length → i ≤ ga.length + de.length → (∀ μ, ¬ JointShape (al.length + be.length - i) (ga.length + de.length - i) _ _ μ (blattner (lamA' t al be ga de))) ∧ ∀ μ, ¬ JointShape (al.length + be.length - i) (ga.length + de.length - i) _ _ μ (blattner (lamM' t al be ga de))) := by
  first | exact @GlobalTheory.LowestTypeDrop.lowestType_not_jointShape | exact GlobalTheory.LowestTypeDrop.lowestType_not_jointShape | (intros; apply GlobalTheory.LowestTypeDrop.lowestType_not_jointShape <;> assumption)
