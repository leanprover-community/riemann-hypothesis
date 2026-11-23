module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLogDensNonneg
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def radialTransform (d : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  a t * t ^ d - ∫ τ in (0 : ℝ)..t, a τ * ((d : ℝ) * τ ^ (d - 1))

theorem radialTransform_zero (a : ℝ → ℝ) : radialTransform 0 a = a := by
  funext t
  simp [radialTransform]

theorem integral_const_mul_dpow (e : ℕ) (c t : ℝ) :
    ∫ τ in (0 : ℝ)..t, c * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) = c * t ^ (e + 1) := by
  simp only [Nat.add_sub_cancel]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  field_simp
  ring

theorem radialTransform_eq_zero_of_const (e : ℕ) (a : ℝ → ℝ) {t₀ t : ℝ}
    (ha : ∀ τ ∈ Set.Icc 0 t₀, a τ = a 0) (ht : t ∈ Set.Icc 0 t₀) :
    radialTransform (e + 1) a t = 0 := by
  have hint : ∫ τ in (0 : ℝ)..t, a τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      ∫ τ in (0 : ℝ)..t, a 0 * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le ht.1] at hτ
    rw [ha τ ⟨hτ.1, hτ.2.trans ht.2⟩]
  rw [radialTransform, hint, integral_const_mul_dpow, ha t ht]
  ring

def RegRadialWeight.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (a : ℝ → ℝ) (t₀ T : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → ContDiff ℝ ∞ a → 0 < t₀ → (∀ t ∈ Set.Icc 0 t₀, a t = a 0) → (∀ t, T ≤ t → a t = 0) →
    (∫ τ in (0 : ℝ)..T, a τ * ((d : ℝ) * τ ^ (d - 1))) = 0 →
      ∫ y, chartDens J A (fun z => a (euclPot (z - x))) (vecCons (logReg u ε) fun _ => euclPot) y =
        ∫ y, chartDens J A (fun z => radialTransform d a (euclPot (z - x)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
