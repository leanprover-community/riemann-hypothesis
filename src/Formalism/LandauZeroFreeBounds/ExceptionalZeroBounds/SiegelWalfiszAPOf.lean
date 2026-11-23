module

public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma chebyshev_progression_orthogonality (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x : ℝ) :
    (q.totient : ℂ) * ((psiAP q a x : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChi χ x := by
  have hu : IsUnit ((a : ZMod q)) := (ZMod.isUnit_iff_coprime a q).mpr ha
  unfold psiAP psiChi
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q,
      χ ((a : ZMod q)⁻¹) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) =
      ((Λ n : ℝ) : ℂ) * (if (a : ZMod q) = n then (q.totient : ℂ) else 0) := by
    intro n
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod q), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun χ _ => by ring)
  simp_rw [key]
  rw [Complex.ofReal_sum, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hiff : (n ≡ a [MOD q]) ↔ (a : ZMod q) = n := by
    rw [eq_comm, ZMod.natCast_eq_natCast_iff]
  by_cases h : n ≡ a [MOD q]
  · rw [if_pos h, if_pos (hiff.mp h)]; ring
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; simp

end Formalism.ZeroFreeDirichlet
