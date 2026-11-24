module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationLinearHeckeStable
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

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], (∀ b b' F F', Rel X l b F → Rel X l b' F' → Rel X l (b + b') (F + F')) ∧ Rel X l 0 0 ∧ (∀ (c : ℤ_[l]) b F, Rel X l b F → Rel X l (c • b) (c • F)) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) b F, Rel X l b F → Rel X l (X.act l m b) (opP ℤ_[l] m F)) ∧ (∀ (N : ℕ) (T : Letter) b F, Rel X l b F → Rel X l (X.op N l T b) (opL ℤ_[l] N l T F)) := by
  first | exact @GlobalTheory.KZ.H3.rel_ops | exact GlobalTheory.KZ.H3.rel_ops | (intros; apply GlobalTheory.KZ.H3.rel_ops <;> assumption)
