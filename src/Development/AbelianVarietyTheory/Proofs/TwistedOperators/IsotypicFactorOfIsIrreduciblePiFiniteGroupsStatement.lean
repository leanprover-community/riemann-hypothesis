module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
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


theorem _root_.GlobalTheory.T.isotypic_factor_of_isIrreducible_pi_finite_groups : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  first | exact @GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | exact GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | (intros; apply GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi <;> assumption)
