module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

namespace FlagDiffPrime

variable {σ : Type} [DecidableEq σ]

def collapse (a b : σ) : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
  aeval fun i => if i = a then X b else X i

theorem collapse_X_sub (a b : σ) : collapse a b (X a - X b : MvPolynomial σ ℚ) = 0 := by
  simp [collapse]

theorem dvd_sub_collapse (a b : σ) (Q : MvPolynomial σ ℚ) :
    (X a - X b : MvPolynomial σ ℚ) ∣ Q - collapse a b Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [collapse]
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul]
    have e : p * X i - collapse a b p * collapse a b (X i) =
        (p - collapse a b p) * X i + collapse a b p * (X i - collapse a b (X i)) := by ring
    rw [e]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    by_cases h : i = a
    · rw [h]; simp [collapse]
    · simp [collapse, h]

theorem collapse_eq_zero_of_dvd (a b : σ) {P : MvPolynomial σ ℚ}
    (h : (X a - X b : MvPolynomial σ ℚ) ∣ P) : collapse a b P = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, collapse_X_sub, zero_mul]

theorem dvd_of_collapse_eq_zero (a b : σ) {P : MvPolynomial σ ℚ}
    (h : collapse a b P = 0) : (X a - X b : MvPolynomial σ ℚ) ∣ P := by
  simpa [h] using dvd_sub_collapse a b P

theorem proof : FlagDiffPrime.Statement := by
  intro σ _ a b hab
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_ne_zero]
    exact fun h => hab (X_injective h)
  · intro hu
    have hu' := hu.map (collapse a b)
    rw [collapse_X_sub] at hu'
    exact not_isUnit_zero hu'
  · intro A B h
    have h0 := collapse_eq_zero_of_dvd a b h
    rw [map_mul, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact Or.inl (dvd_of_collapse_eq_zero a b h0)
    · exact Or.inr (dvd_of_collapse_eq_zero a b h0)

end FlagDiffPrime

end

end RestTerms

end GroundTheory.Heights₂.Heights
