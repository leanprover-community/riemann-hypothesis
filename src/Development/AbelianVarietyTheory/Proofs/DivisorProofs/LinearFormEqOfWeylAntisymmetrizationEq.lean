module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAlternatingOfAdjacentSwapBlocksStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem linForm_eq_of_antisymm_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  intro ι _ m L hL Q Q' h
  have sq : ∀ u : ℤˣ, ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
    intro u
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have key : ∀ P : MvPolynomial (Root m) ℝ,
      L (antisymm P) = (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) * L P := by
    intro P

    simp only [GlobalTheory.GoodMetric.antisymm, map_sum, map_zsmul]
    rw [Finset.sum_congr rfl (fun w _ => by
      rw [GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks ι m L hL w P, zsmul_eq_mul, ← mul_assoc, sq, one_mul])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ∀ τ, Equiv.Perm (Fin (m τ)))).ne'
  have e := congrArg L h
  rw [key, key] at e
  exact mul_left_cancel₀ hc e

end GlobalTheory.FlagPush
