module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedWeierstrassPTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem isAlgebraic_of_isIntegral_natCast_mul (n : ℕ) (hn : n ≠ 0) (z : ℂ)
    (h : IsIntegral ℤ ((n : ℂ) * z)) : IsAlgebraic ℚ z := by
  have h1 : IsIntegral ℚ ((n : ℂ) * z) := h.tower_top
  have h2 : IsIntegral ℚ (algebraMap ℚ ℂ ((n : ℚ)⁻¹)) := isIntegral_algebraMap
  have h3 := h2.mul h1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have : algebraMap ℚ ℂ ((n : ℚ)⁻¹) * ((n : ℂ) * z) = z := by
    rw [map_inv₀, map_natCast, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  rw [this] at h3
  exact h3.isAlgebraic

theorem qAll_isAlgebraic_torsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N),
    QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧
      (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  intro N _ x
  have hN : N ≠ 0 := NeZero.ne N
  have hx : N • x = 0 := by
    funext i
    simp [nsmul_eq_mul]
  have hc := fun k => GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N x k (Nat.pos_of_ne_zero hN) hx
  refine ⟨⟨cP N x, GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N x, fun k => ?_⟩, ⟨cD N x, GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N x, fun k => ?_⟩,
    fun h0 => ⟨cB N x, GlobalTheory.T.weierstrass_division_value_q_expansion N x h0, fun k => ?_⟩⟩
  · refine isAlgebraic_of_isIntegral_natCast_mul (12 * N ^ 2) (by positivity) _ ?_
    have := (hc k).2.2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 3) (by positivity) _ ?_
    have := (hc k).2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 2) (by positivity) _ ?_
    have := (hc k).1
    push_cast
    exact this

end GlobalTheory.WpFam
