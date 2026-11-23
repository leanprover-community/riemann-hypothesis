module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

private theorem sum_shift_mul_neg_indicator_eq_ite (N : ℕ) (m n : Fin N) :
    ∑ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0))
      = if n = m then 1 else 0 := by
  have e1 : ∀ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0))
      = (if k = m then (if n ≤ k then (1:ℤ) else 0) else 0) - (if (k:ℕ) + 1 = m then (if n ≤ k then (1:ℤ) else 0) else 0) := by
    intro k
    by_cases h1 : (k:ℕ) + 1 = m
    · have : k ≠ m := by intro h; subst h; omega
      split_ifs <;> simp_all
    · split_ifs <;> simp_all
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases m with ⟨m, hm⟩
  rcases n with ⟨n, hn⟩
  cases m with
  | zero =>
    have : ∀ k : Fin N, ¬ ((k:ℕ) + 1 = 0) := fun k => by omega
    simp only [this, if_false, Finset.sum_const_zero, sub_zero, Fin.le_def, Fin.mk.injEq]
    split_ifs <;> omega
  | succ m =>
    rw [Finset.sum_eq_single ⟨m, by omega⟩]
    · simp only [Fin.le_def, Fin.mk.injEq]
      split_ifs <;> omega
    · intro b _ hb
      have hb' : (b:ℕ) ≠ m := fun h => hb (Fin.ext h)
      have : ¬ ((b:ℕ) + 1 = ((⟨m + 1, hm⟩ : Fin N) : ℕ)) := by simp only [Fin.val_mk]; omega
      rw [if_neg this]
    · simp

theorem h_fundinv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') := by
  intro Ψ _ _ N r r'
  refine ⟨?_, fun π => ?_⟩
  · obtain ⟨p, m⟩ := r
    obtain ⟨q, n⟩ := r'
    rw [Fintype.sum_prod_type]
    simp only [rootOnFund, fundOnRoot]
    rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (by simp)]
    by_cases hq : q = p
    · subst hq
      simp only [if_true, true_and, Prod.mk.injEq]
      rw [sum_shift_mul_neg_indicator_eq_ite N m n]
      by_cases h : n = m
      · simp [h]
      · simp [h, Ne.symm h]
    · have : ¬ (p = q) := fun h => hq h.symm
      simp [hq, this]
  · simp [rootOnFund, fundOnRoot, π.injective.eq_iff]

end PositivityTheory.UnitarySelfGeneration
