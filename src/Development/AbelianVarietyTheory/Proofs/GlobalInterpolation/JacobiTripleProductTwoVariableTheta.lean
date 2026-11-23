module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteProductStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductLimitStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

theorem tripleProduct : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  intro τ z
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hτ : 0 < (τ : ℂ).im := τ.2
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) hτ
  have hs0 : s ≠ 0 := exp_ne_zero _
  have hx0 : x ≠ 0 := exp_ne_zero _
  have ht1 : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  obtain ⟨hP, hP0, -⟩ := qPoch_tendsto (s ^ 2) ht1
  have hT := GlobalTheory.T.jacobi_triple_product_limit (τ : ℂ) z hτ
  rw [(multipliable_tpFactor τ z).hasProd_iff_tendsto_nat]
  have key : ∀ n : ℕ, ∏ k ∈ Finset.range n, GlobalTheory.ThetaWeberRoad.tpFactor τ z k =
      qPoch (s ^ 2) n * ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
        finCoeff (cexp (π * I * (τ : ℂ)) ^ 2) n j * jacobiTheta₂_term j z τ := by
    intro n
    rw [Finset.prod_congr rfl (fun k _ => tpFactor_eq τ z k), Finset.prod_mul_distrib]
    have hf := GlobalTheory.T.jacobiTriple_finite_product s x hs0 hs1 hx0 n
    simp only [hs, hx] at hf
    simp only [hf, jacobiTheta₂_term_eq_zpow]
    rfl
  simp_rw [key]
  have := hP.mul hT
  rwa [mul_left_comm, mul_inv_cancel₀ hP0, mul_one] at this

end GlobalTheory.JacobiTriple
