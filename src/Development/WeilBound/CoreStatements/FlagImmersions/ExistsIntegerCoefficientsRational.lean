module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
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
import Mathlib.Tactic.Linter.Style
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem exists_clear_denominators_bis {J : Type} [Fintype J] (c : J → ℚ) :
    ∃ (q : ℕ) (n : J → ℤ), 0 < q ∧ ∀ j, (n j : ℚ) = q * c j := by
  classical
  refine ⟨∏ i, (c i).den, fun j => (c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ), ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => (c i).den_pos)
  · intro j
    obtain ⟨k, hk⟩ : (c j).den ∣ ∏ i, (c i).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    show (((c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ) : ℤ) : ℚ) = ((∏ i, (c i).den : ℕ) : ℚ) * c j
    rw [hk, Nat.mul_div_cancel_left _ (c j).den_pos]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

end RootFieldNumerics

theorem RootFieldNumerics.exists_integer_coefficients_rational : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j := by
  intro Ψ _ N M lam s hlam
  classical
  choose f hf using hlam
  let c : Option (Ψ × Fin N) → ℚ := fun j => match j with
    | some r => -f r.1 r.2
    | none => s / M.kA
  obtain ⟨q, n, hq, hn⟩ := RootFieldNumerics.exists_clear_denominators_bis c
  refine ⟨q, n, hq, fun j => ?_⟩
  have h : ((n j : ℚ) : ℝ) = ((q * c j : ℚ) : ℝ) := by rw [hn j]
  push_cast at h
  rw [h]
  congr 1
  cases j with
  | none => simp [c, RootModel.coef]
  | some r => simp [c, RootModel.coef, hf]
