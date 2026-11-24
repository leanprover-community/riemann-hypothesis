module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory

variable {J : Type} [Fintype J]

def secFun (b : MvPolynomial J ℚ) (z : J → ℂ) : ℂ :=
  eval z (map (algebraMap ℚ ℂ) b)

def wgt (m : ConeMetric (C := ℂ) (ι := J)) (n : ℕ) (z : J → ℂ) : ℝ :=
  (m.ρ z ^ (2 * n))⁻¹

def logRatio (m₀ m₁ : ConeMetric (C := ℂ) (ι := J)) (z : J → ℂ) : ℝ :=
  Real.log (m₁.ρ z / m₀.ρ z)

theorem _root_.ReciprocityTheory.ChartRestriction.G.Geo.ConeMetric.nonneg
    (m : ConeMetric (C := ℂ) (ι := J)) (z : J → ℂ) :
    0 ≤ m.ρ z := by
  by_cases hz : z = 0
  · subst hz
    have h := m.smul 0 0
    rw [zero_smul, norm_zero, zero_mul] at h
    exact le_of_eq h.symm
  · exact (m.pos z hz).le

def interp (m₀ m₁ : ConeMetric (C := ℂ) (ι := J)) (t : ℝ) :
    ConeMetric (C := ℂ) (ι := J) where
  ρ z := m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t
  pos z hz := mul_pos (Real.rpow_pos_of_pos (m₀.pos z hz) _) (Real.rpow_pos_of_pos (m₁.pos z hz) _)
  smul c z := by
    rw [m₀.smul, m₁.smul, Real.mul_rpow (norm_nonneg c) (m₀.nonneg z),
      Real.mul_rpow (norm_nonneg c) (m₁.nonneg z)]
    have key : ‖c‖ ^ (1 - t) * ‖c‖ ^ t = ‖c‖ := by
      rcases eq_or_lt_of_le (norm_nonneg c) with h | h
      · rw [← h]
        by_cases ht : t = 0
        · simp [ht]
        · simp [Real.zero_rpow ht]
      · rw [← Real.rpow_add h]
        simp
    calc ‖c‖ ^ (1 - t) * m₀.ρ z ^ (1 - t) * (‖c‖ ^ t * m₁.ρ z ^ t)
        = (‖c‖ ^ (1 - t) * ‖c‖ ^ t) * (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) := by ring
      _ = ‖c‖ * (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) := by rw [key]

def mixPot (m₀ m₁ : ConeMetric (C := ℂ) (ι := J)) (D i : ℕ) : Fin D → (J → ℂ) → ℝ :=
  fun j z => if j.val < i then Real.log (m₁.ρ z) else Real.log (m₀.ρ z)

def purePot (m : ConeMetric (C := ℂ) (ι := J)) (D : ℕ) : Fin D → (J → ℂ) → ℝ :=
  fun _ z => Real.log (m.ρ z)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
