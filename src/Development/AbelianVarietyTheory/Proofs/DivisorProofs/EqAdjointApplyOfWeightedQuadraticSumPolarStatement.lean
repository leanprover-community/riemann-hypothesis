module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdjointApplyOfWeightedQuadraticSumPolar
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

@[expose] public section

open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.eq_adjoint_apply_of_weightedQuadraticSum_polar : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → ∀ z z' : Fin 8 → X₀, (∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + z) - qW W β (fun a => ∑ b, E a b • y b) - qW W β z = qW W β (y + z') - qW W β y - qW W β z') → z' = fun a => ∑ b, E' a b • z b := by
  first | exact @GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar | exact GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar | (intros; apply GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar <;> assumption)
