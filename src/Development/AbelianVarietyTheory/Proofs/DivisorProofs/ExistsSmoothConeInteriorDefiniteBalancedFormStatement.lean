module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_smoothCone_interior_definite_balancedForm : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ β ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < β x x) → ∃ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (k : ℕ) (c : Fin r → ℕ), IsCone bar φ γ ∧ 0 < k ∧ (∀ j, 0 < c j) ∧ k • β = ∑ j, c j • γ j := by
  first | exact @GlobalTheory.Poinc.Cover.exists_cone | exact GlobalTheory.Poinc.Cover.exists_cone | (intros; apply GlobalTheory.Poinc.Cover.exists_cone <;> assumption)
