module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Formalism.DegreeFormula.PointDegree.FlagDeg
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flagDeg_eq_weyl : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (lam : Wt Ψ N), flagDeg lam = ((dimFl Ψ N).factorial : ℝ) * ∏ τ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1) ∧ (RegDominant lam → 0 < flagDeg lam) ∧ (Dominant lam → 0 ≤ flagDeg lam) := by
  intro Ψ _ _ N lam
  have hf : flagDeg lam = ((dimFl Ψ N).factorial : ℝ) *
      ∏ τ, ∏ i : Fin N, ∏ k : Fin N,
        (if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1) :=
    Formalism.DegreeFormula.flagDegFormula_statement Ψ N lam
  have hD : (0 : ℝ) < ((dimFl Ψ N).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hki : ∀ i k : Fin N, i < k → (0 : ℝ) < (k : ℝ) - (i : ℝ) := by
    intro i k h
    have h' : ((i : ℕ) : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast h
    exact sub_pos.mpr h'
  refine ⟨hf, fun hr => ?_, fun hd => ?_⟩
  · rw [hf]
    refine mul_pos hD (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      Finset.prod_pos fun k _ => ?_)
    split_ifs with h
    · exact div_pos (sub_pos.mpr (hr τ i k h)) (hki i k h)
    · exact one_pos
  · rw [hf]
    refine mul_nonneg hD.le (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ =>
      Finset.prod_nonneg fun k _ => ?_)
    split_ifs with h
    · exact div_nonneg (sub_nonneg.mpr (hd τ i k h.le)) (hki i k h).le
    · exact zero_le_one

end GlobalTheory.CompanionTheory.Ar.Top
