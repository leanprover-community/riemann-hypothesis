module

public import Mathlib.Basic.ENNReal.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.Basic.ENNReal.Real

@[expose] public section

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {r : ℕ} {κ τ : ℝ}

theorem frames_ineqs {pw pw₁ s K ρ F : ℝ} (X : ENNReal) (hs : 0 ≤ s) (hK : 0 ≤ K) (hρ : 0 < ρ)
    (h1 : ρ ≤ F) (h2 : ρ⁻¹ ≤ F) (he : pw₁ * s = K * ρ * pw) :
    ENNReal.ofReal pw₁ * (ENNReal.ofReal s * X) ≤ ENNReal.ofReal (K * F) * (ENNReal.ofReal pw * X) ∧
      ENNReal.ofReal K * (ENNReal.ofReal pw * X) ≤ ENNReal.ofReal F * (ENNReal.ofReal pw₁ * (ENNReal.ofReal s * X)) := by
  have hF : 0 < F := lt_of_lt_of_le hρ h1
  rw [← mul_assoc (ENNReal.ofReal pw₁), ← ENNReal.ofReal_mul' hs, he]
  by_cases hp : pw ≤ 0
  · have h0 : K * ρ * pw ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hK hρ.le) hp
    rw [ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_of_nonpos hp]
    simp
  · push Not at hp
    constructor
    · rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hK hF.le)]
      gcongr ENNReal.ofReal ?_ * _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK) hp.le
    · rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hF.le]
      gcongr ENNReal.ofReal ?_ * _
      have : 1 ≤ F * ρ := by
        have := mul_le_mul_of_nonneg_right h2 hρ.le
        rwa [inv_mul_cancel₀ hρ.ne'] at this
      nlinarith [mul_nonneg hK hp.le]

end Formalism.MainNotions.FrameBoundFromBesselTorus
