module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightInvariantMulEqFinprodComponents
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

open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.rightInvariant_mul_eq_finprod_components : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ) (a : Γ → ℂ), (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 → (∀ v g h, c v g = 1 → c v h = h → a (g * h) = a g * a h) → ∀ g, a g = ∏ᶠ v, a (c v g) := by
  first | exact @GlobalTheory.finprod_components_of_rightInvariant_mul | exact GlobalTheory.finprod_components_of_rightInvariant_mul | (intros; apply GlobalTheory.finprod_components_of_rightInvariant_mul <;> assumption)
