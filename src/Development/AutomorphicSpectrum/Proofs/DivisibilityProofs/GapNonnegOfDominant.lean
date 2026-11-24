module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem gap_nonneg_of_dominant {Ψ : Type} [Fintype Ψ] {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N)
    {mu : Wt Ψ N} (hd : Dominant mu) (τ : Ψ) : 0 ≤ gap j mu τ := by
  have h1 : j - 1 < N := by omega
  have hle : mu τ ⟨j, hjN⟩ ≤ mu τ ⟨j - 1, h1⟩ := hd τ ⟨j - 1, h1⟩ ⟨j, hjN⟩ (by rw [Fin.mk_le_mk]; omega)
  simp only [gap, ent, dif_pos h1, dif_pos hjN]
  exact sub_nonneg.mpr hle

theorem NefThreshold.mono {Ψ : Type} [Fintype Ψ] {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N)
    {mu : Wt Ψ N} (hd : Dominant mu) {b b' : ℝ} (hb : b ≤ b') (h : NefThreshold j b mu) :
    NefThreshold j b' mu := by
  intro τ
  have hg : 0 ≤ gap j mu τ := gap_nonneg_of_dominant hj1 hjN hd τ
  calc 4 * (Fintype.card Ψ : ℝ) * ‖mu‖ ≤ (b - 2) * gap j mu τ := h τ
    _ ≤ (b' - 2) * gap j mu τ := mul_le_mul_of_nonneg_right (by linarith) hg

theorem RootTower.nefFib_of_nefThreshold :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.ModelNefStatement → T.M2 →
      ∀ (B : ℕ) (c : T.Comp) (mu : Wt Ψ N), Dominant mu → NefThreshold T.j B mu →
        (T.M B c).NefFib mu 0 := by
  intro Ψ _ _ N T h1 h2 B c mu hd hB p hp
  by_cases hS : T.InS B p
  · exact h1 B c p hS mu hd
  · have hBp : B < p := by
      by_contra hc
      exact hS (show p.Prime ∧ (p ≤ B ∨ p ∈ T.bad) from ⟨hp, Or.inl (not_lt.mp hc)⟩)
    refine h2 B c p hp hS mu hd ?_
    exact NefThreshold.mono T.j_pos T.j_lt hd (by exact_mod_cast hBp.le) hB

end GlobalTheory.CompanionTheory.Ar.Top
