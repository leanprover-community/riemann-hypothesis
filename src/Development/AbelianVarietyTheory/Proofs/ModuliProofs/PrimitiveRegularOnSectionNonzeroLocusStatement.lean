module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimitiveRegularOnSectionNonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.primitive_regular_on_section_nonzeroLocus : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (I : Type) (O : I → P₀.A.left.Opens) (c : ∀ i i', Γ(P₀.A.left, O i ⊓ O i')) (h : I → (Fin P₀.g → ℂ) → ℂ), ⨆ i, O i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i} ∧ ∀ (l : u.Λ) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → h i (z + l) = h i z) → (∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') → valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z) → ∀ i (n : ℕ) (σ : (lbPow P₀.L n).Sec), Out.nonzeroLocus σ ≤ O i → ∃ a : Γ(P₀.A.left, Out.nonzeroLocus σ), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus σ → valAt' (u.ex z).left (Out.nonzeroLocus σ) a = h i z := by
  first | exact @GlobalTheory.primitive_regular_on_nonzeroLocus | exact GlobalTheory.primitive_regular_on_nonzeroLocus | (intros; apply GlobalTheory.primitive_regular_on_nonzeroLocus <;> assumption)
