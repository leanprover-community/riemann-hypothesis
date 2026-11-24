module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymEdgeStableSubmoduleEqTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle

@[expose] public section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

theorem _root_.GlobalTheory.T.symEdge_stable_submodule_eq_top : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ (a : Fin n → Fin n → k), (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ (V : Submodule k (Fin n → k)), V ≠ ⊥ → (∀ w ∈ V, (fun j => ∑ i, if symEdge ρ κ i j then a i j * w i else 0) ∈ V) → (∀ i j : Fin n, i < j → ¬(ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ) → ∀ w ∈ V, Pi.single i (w j) ∈ V) → V = ⊤ := by
  first | exact @GlobalTheory.symEdge_span_eq_top | exact GlobalTheory.symEdge_span_eq_top | (intros; apply GlobalTheory.symEdge_span_eq_top <;> assumption)
