module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def euclBall {n : ℕ} (x : Fin n → ℂ) (ρ : ℝ) : Set (Fin n → ℂ) :=
  {y | Real.sqrt (euclPot (y - x)) < ρ}

theorem mem_euclBall_iff {n : ℕ} (x y : Fin n → ℂ) (ρ : ℝ) :
    y ∈ euclBall x ρ ↔ dist (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 x) < ρ := by
  rw [EuclideanSpace.dist_eq]
  simp [euclBall, euclPot, dist_eq_norm]

theorem mem_euclBall_self {n : ℕ} (x : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) : x ∈ euclBall x ρ := by
  simp [euclBall, euclPot, hρ]

def RegLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → 0 < r → r ≤ s →
      s ^ (2 * d) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y ≤
        r ^ (2 * d) * ∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
