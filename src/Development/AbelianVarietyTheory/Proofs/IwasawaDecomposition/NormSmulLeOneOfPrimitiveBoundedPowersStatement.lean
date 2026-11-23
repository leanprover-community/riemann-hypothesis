module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSmulLeOneOfPrimitiveBoundedPowers
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


theorem _root_.GlobalTheory.T.norm_smul_le_one_of_primitive_bounded_powers : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂] (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂), (∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) → (∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ N₂ x) → (∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) → (∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y) → (∀ x, N₂ (Δ x) ≤ N₁ x) → (∀ x y, N₂ (i x * j y) = N₁ x * N₁ y) → ∀ y : B₁, (∃ K : ℝ, ∀ k : ℕ, N₁ (y ^ k) ≤ K) → N₂ (Δ y - i y - j y) ≤ 1 → ∀ a : C, ‖a‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → N₁ (a • y) ≤ 1 := by
  first | exact @GlobalTheory.NearlyPrimitive.norm_smul_le_one | exact GlobalTheory.NearlyPrimitive.norm_smul_le_one | (intros; apply GlobalTheory.NearlyPrimitive.norm_smul_le_one <;> assumption)
