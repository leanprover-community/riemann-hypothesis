module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspace
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

open scoped NNReal

theorem _root_.GlobalTheory.T.latticeDetRelation_herbrand_eigenspace : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) = q → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) (∑ s ∈ Finset.univ.erase τ, (Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ ((a τ : C) - (a s : C))) := by
  first | exact @GlobalTheory.HerbrandBridge.exForm | exact GlobalTheory.HerbrandBridge.exForm | (intros; apply GlobalTheory.HerbrandBridge.exForm <;> assumption)
