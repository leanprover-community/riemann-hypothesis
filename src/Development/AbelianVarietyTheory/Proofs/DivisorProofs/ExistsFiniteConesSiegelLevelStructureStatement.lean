module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesSiegelLevelStructure
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_finite_cones_siegel_level_structure : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) → (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) → ∃ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ i, IsCone id φ (γ i)) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → ∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j := by
  first | exact @GlobalTheory.Poinc.Cells.exists_finite_cones | exact GlobalTheory.Poinc.Cells.exists_finite_cones | (intros; apply GlobalTheory.Poinc.Cells.exists_finite_cones <;> assumption)
