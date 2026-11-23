module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCocyclePeriodicNonvanishingSections
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real

theorem _root_.GlobalTheory.T.theta_cocycle_periodic_nonvanishing_sections : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm Θ : Matrix (Fin g) (Fin g) ℂ) (ι : Type) (U : ι → Set (Fin g → ℂ)) (a : ι → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ) (e : Λ → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i, DifferentiableOn ℂ (a i) (U i) ∧ ∀ z ∈ U i, a i z ≠ 0) → (∀ i (l : Λ), ∀ z ∈ U i, a i z = e l * cexp (π * (z ⬝ᵥ Hm.mulVec (star (l : (Fin g → ℂ))))) * a i (z + l)) → (∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j)) → (∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, k i j (z + l) = k i j z + (fderiv ℂ (a i) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a i z - fderiv ℂ (a j) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a j z)) → ∀ z w, Θ.mulVec (star z) ⬝ᵥ Hm.mulVec (star w) = Θ.mulVec (star w) ⬝ᵥ Hm.mulVec (star z) := by
  first | exact @GlobalTheory.PeriodSymm.period_symm | exact GlobalTheory.PeriodSymm.period_symm | (intros; apply GlobalTheory.PeriodSymm.period_symm <;> assumption)
