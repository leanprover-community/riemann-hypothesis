module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem substF_scalar_X {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (p : ι × Fin N × Fin n) :
    substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (X p)
      = C (if p.1 = τ₀ then ζ else 1) * X p := by
  rw [substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
  · obtain ⟨a, b⟩ := p
    by_cases h : a = τ₀
    · subst h; simp
    · simp [h]
  · intro l _ hl
    by_cases h : p.1 = τ₀ <;> simp [h, Matrix.one_apply_ne hl]
  · simp
  · intro k _ hk
    simp [Matrix.one_apply_ne hk]
  · simp

theorem mapDomain_fst_apply {ι : Type} [DecidableEq ι] {N n : ℕ} (k : ι × Fin N × Fin n →₀ ℕ) (τ₀ : ι) :
    Finsupp.mapDomain Prod.fst k τ₀ = ∑ p ∈ k.support, if p.1 = τ₀ then k p else 0 := by
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  rw [Finsupp.single_apply]

theorem substF_scalar_monomial {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow, substF_scalar_X, mul_pow, Finset.prod_mul_distrib]
  rw [mapDomain_fst_apply, smul_eq_C_mul, ← Finset.prod_pow_eq_pow_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← map_pow]
  split_ifs <;> simp

end GlobalTheory.CompactHowe
