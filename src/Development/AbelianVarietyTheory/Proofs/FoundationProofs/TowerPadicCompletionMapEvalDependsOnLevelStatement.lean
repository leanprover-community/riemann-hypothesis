module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerPadicCompletionMapEvalDependsOnLevel
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

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.towerPadicCompletionMap_eval_depends_on_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (n : ℕ), ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K, (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0, X.sl (ofSL γ) f = f) → φ f = ψ f) → AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ a) = AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l ψ a) := by
  first | exact @GlobalTheory.KZ.Tower.eval_kmap_levelRed | exact GlobalTheory.KZ.Tower.eval_kmap_levelRed | (intros; apply GlobalTheory.KZ.Tower.eval_kmap_levelRed <;> assumption)
