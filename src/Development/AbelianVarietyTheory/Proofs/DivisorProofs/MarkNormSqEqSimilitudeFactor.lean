module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitudeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem Pair.mark_norm_sq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), P.Mark μ →
    ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  intro p _ G P μ hμ
  obtain ⟨v, _, x, hx, hpos⟩ := hμ
  obtain ⟨_, _, hlaw⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P v
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hH
  set A := G.psi v (P.γ : G.C) with hA
  set q : ℂ := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0] at hpos; simp at hpos
  have key : star x ⬝ᵥ ((Aᴴ * H * A) *ᵥ x) = (star μ * μ) * q := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hx, dotProduct_mulVec, ← star_mulVec, hx, mulVec_smul, star_smul,
      smul_dotProduct, dotProduct_smul, hq]
    simp only [smul_eq_mul]; ring
  rw [hlaw, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at key
  have hc : star μ * μ = ((P.c : ℚ) : ℂ) := by
    have := mul_right_cancel₀ hq0 key.symm
    exact this
  have h2 : ((‖μ‖ ^ 2 : ℝ) : ℂ) = ((((P.c : ℚ) : ℝ)) : ℂ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    push_cast
    exact hc
  exact_mod_cast h2

end GlobalTheory.LKMid
