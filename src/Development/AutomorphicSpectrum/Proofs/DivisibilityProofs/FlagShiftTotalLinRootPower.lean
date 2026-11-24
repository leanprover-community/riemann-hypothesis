module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.LinPow

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_C_mul (c : ℝ) (F : RP Ψ N) : degFl (C c * F) = c * degFl F := by
  unfold degFl
  simp_rw [coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem pderiv_linRoot (u : Wt Ψ N) (τ : Ψ) (i : Fin N) :
    pderiv (τ, i) (linRoot u) = -C (u τ i) := by
  simp [linRoot, pderiv_X, Pi.single_apply]

theorem pderiv_linRoot_pow (u : Wt Ψ N) (τ : Ψ) (i : Fin N) (D : ℕ) :
    pderiv (τ, i) (linRoot u ^ (D + 1)) =
      C (-(((D : ℝ) + 1) * u τ i)) * linRoot u ^ D := by
  rw [Derivation.leibniz_pow, pderiv_linRoot]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
  simp only [map_neg, map_mul, map_add (f := _), map_natCast, map_one]
  push_cast
  ring

private lemma degFl_sum' {ι : Type*} (s : Finset ι) (f : ι → RP Ψ N) :
    degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  unfold degFl
  simp_rw [coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem degFl_sum_pderiv (u : Wt Ψ N) (τ : Ψ) (s : Finset (Fin N)) :
    degFl (∑ i ∈ s, pderiv (τ, i) (linRoot u ^ (dimFl Ψ N + 1))) =
      -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ s, u τ i) := by
  rw [degFl_sum']
  simp_rw [pderiv_linRoot_pow, degFl_C_mul]
  simp only [flagDeg]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.CompanionTheory.Ar.Top.LinPow

theorem GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ) (u : Wt Ψ N), Sh j τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u τ i) ∧ Tot τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i, u τ i) := by
  intro Ψ _ _ N j τ u
  exact ⟨GlobalTheory.CompanionTheory.Ar.Top.LinPow.degFl_sum_pderiv u τ _,
    GlobalTheory.CompanionTheory.Ar.Top.LinPow.degFl_sum_pderiv u τ Finset.univ⟩
