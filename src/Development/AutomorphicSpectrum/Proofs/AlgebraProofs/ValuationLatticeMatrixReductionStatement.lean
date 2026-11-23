module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationLatticeMatrixReduction
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem _root_.GlobalTheory.T.valuation_lattice_matrix_reduction : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (τ : S) (r : S → ℕ) (W : Type) [AddCommGroup W] [Module C W] [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] (g : S → (Fin (p + q) → C) →ₗ[C] W) (v : Fin p → W) (U : Fin (p + q) → Fin (p + q) → C) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), Function.Injective a → (∀ f : S → Fin (p + q) → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0) → (∀ s, Module.finrank C (LinearMap.ker (g s)) = r s) → r τ = q → LinearIndependent C v → (∀ y, y ∈ Submodule.span w.valuationSubring (Set.range v) ↔ y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a (p + q), ∑ s, g s (f s) = y) → (∀ i, g τ (U (Fin.castAdd q i)) = v i) → (∀ j, g τ (U (Fin.natAdd p j)) = 0) → IsLatticeBasis w (fun j => U (Fin.natAdd p j)) (eigenQuot (W := fun _ => Fin (p + q) → C) (kerFil a (p + q) g) τ) → IsLatticeBasis w (fun i => ∑ j, A i j • U j) (eigenQuot (W := fun _ => Fin (p + q) → C) (freeLattice a (p + q)) τ) → ∃ ε : (w.valuationSubring)ˣ, A.det * (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))) ^ (p + q) = (ε : w.valuationSubring) * ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core.det_adapted_core | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core.det_adapted_core | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core.det_adapted_core <;> assumption)
