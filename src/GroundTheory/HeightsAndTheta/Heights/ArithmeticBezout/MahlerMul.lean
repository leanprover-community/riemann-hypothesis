module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
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

open MeasureTheory Set MvPolynomial

noncomputable section

namespace LogInt

variable {n k : ℕ}

def ballSet (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j => u (i, j)) < 1}

theorem measurableSet_ballSet (h : HermNorm n) : MeasurableSet (ballSet h k) := by
  have e : ballSet h k = ⋂ i, {u : Fin k × Fin n → ℂ | h.norm (fun j => u (i, j)) < 1} := by
    ext u; simp [ballSet]
  rw [e]
  exact MeasurableSet.iInter fun i => measurableSet_lt (measurable_groupNorm h i) measurable_const

theorem ballSet_subset_polydisc (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballSet h k ⊆ polydisc _ C := by
  intro u hu
  simp only [polydisc, mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

theorem normT_univ (h : HermNorm n) (u : Fin k × Fin n → ℂ) :
    normT h Finset.univ u = fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij := by
  funext ij
  simp [normT]

theorem integrableOn_log_mahler (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ) (hf : f ≠ 0) :
    IntegrableOn (fun u : Fin k × Fin n → ℂ =>
        Real.log ‖eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f‖)
        (ballSet h k) ∧
      ∀ᵐ u ∂(volume.restrict (ballSet h k)),
        eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f ≠ 0 := by
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  obtain ⟨h1, h2⟩ := logNormT h C hC0 hC Finset.univ f hf
  simp only [normT_univ] at h1 h2
  exact ⟨h1.mono_set (ballSet_subset_polydisc h C hC0 hC),
    ae_restrict_of_ae_restrict_of_subset (ballSet_subset_polydisc h C hC0 hC) h2⟩

end LogInt

theorem mahlerMul : MahlerMul.Statement := by
  intro n k h f g hf hg
  obtain ⟨i1, z1⟩ := LogInt.integrableOn_log_mahler h f hf
  obtain ⟨i2, z2⟩ := LogInt.integrableOn_log_mahler h g hg
  unfold mahler sphereMean
  change ⨍ u in LogInt.ballSet h k, _ = (⨍ u in LogInt.ballSet h k, _) + ⨍ u in LogInt.ballSet h k, _
  rw [setAverage_eq, setAverage_eq, setAverage_eq, ← smul_add, ← integral_add i1 i2]
  congr 1
  refine setIntegral_congr_ae (LogInt.measurableSet_ballSet h) ?_
  have := (ae_restrict_iff' (LogInt.measurableSet_ballSet h)).mp (z1.and z2)
  filter_upwards [this] with u hu hB
  obtain ⟨h1, h2⟩ := hu hB
  rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)]

end

end GroundTheory.Heights₂.Heights
