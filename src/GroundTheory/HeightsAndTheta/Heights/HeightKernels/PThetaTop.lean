module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

theorem ThetaBound.proof (hG : GaussianSum.Statement) (hMean : ThetaMean.Statement)
    (hMaj : ThetaNormMajorant.Statement) (hSplit : ThetaFirstCoordSplit.Statement)
    (hConst : ThetaConstants.Statement) : ThetaBound.Statement := by
  obtain ⟨C₃, hC₃, hG⟩ := hG
  obtain ⟨C, hC, hK⟩ := hConst C₃ hC₃
  refine ⟨C, hC, ?_⟩
  intro g _ X Y ρ a b _ hY hR _ _
  refine ⟨hMean g X Y a b hY, fun u₁ u₂ => ?_⟩
  set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ))
  have hdet : Y.det⁻¹ ≤ ρ ^ 2 * (2 * (g : ℝ)) ^ (g - 1) := by
    have h := hR.det_le
    rwa [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h
  have hg : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have h1 := hMaj g X Y a b u₁ u₂ hY
  have h2 := hSplit g Y ρ a u₁ hY hR.pos hR.first
  have h3 := (hG g Y ρ hY hR.pos hR.min (a + u₁)).2
  have h4 := hK g ρ Y.det hg hR.pos hY.det_pos hR.sq_le hdet
  have he : 0 ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) := (exp_pos _).le
  calc thetaNorm X Y a b u₁ u₂ ≤ ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) := h1
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) *
          ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := h2
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) *
          ((C₃ * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g) :=
        mul_le_mul_of_nonneg_left h3 he
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) * (((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
          exp (g * log (1 + 1 / ρ) + C * g * log (2 * g))) :=
        mul_le_mul_of_nonneg_left h4 he
    _ = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
          exp (-(π / (2 * ρ ^ 2)) * δ ^ 2 + (g * log (1 + 1 / ρ) + C * g * log (2 * g))) := by
        rw [exp_add (-(π / (2 * ρ ^ 2)) * δ ^ 2)]; ring

end GroundTheory.Heights₂.Heights
