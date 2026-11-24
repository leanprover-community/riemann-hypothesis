module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyLelongMono
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarWirtinger
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarLelongMono
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLinearNoetherNormalization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.RingTheory.Nullstellensatz
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

theorem zeroSetEuc_subsingleton_of_dim_zero {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((0 : ℕ) : WithBot ℕ∞))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ zeroSetEuc J) :
    ∀ y ∈ zeroSetEuc J, y = z := by
  have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) := Ring.krullDimLE_iff.2 (le_of_eq hdim)
  have hmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
  obtain ⟨p, hp⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton (K := ℂ)).1 hmax
  have hcoord : ∀ w ∈ zeroSetEuc J, ∀ i, w i = p i := by
    intro w hw i
    have hmem : (X i - C (p i) : MvPolynomial (Fin n) ℂ) ∈ J := by
      rw [hp, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    have := hw _ hmem
    simp only [map_sub, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  intro y hy
  ext i
  rw [hcoord y hy i, hcoord z hz i]

theorem VarietyLelongMono.proof (hN : ComplexSets.LinearNoetherNormalization.Statement)
    (hW : VarWirtinger.Statement) (hM : VarLelongMono.Statement) : VarietyLelongMono.Statement := by
  intro n d J hJ hdim z hz r s hr hrs
  rcases d with _ | d
  · have hsub := zeroSetEuc_subsingleton_of_dim_zero J hJ hdim hz
    have hpt : ∀ ρ : ℝ, 0 < ρ → zeroSetEuc J ∩ Metric.ball z ρ = {z} := by
      intro ρ hρ
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => hsub y h.1
      · rintro rfl
        exact ⟨hz, Metric.mem_ball_self hρ⟩
    rw [hpt r hr, hpt s (hr.trans_le hrs)]
    simp [Measure.hausdorffMeasure_zero_singleton]
  · obtain ⟨A, hA⟩ := hN n (d + 1) J hdim
    obtain ⟨c, hc, hWc⟩ := hW d
    have hball : ∀ ρ : ℝ, (fun x : Fin n → ℂ => WithLp.toLp 2 x) ⁻¹' Metric.ball z ρ =
        euclBall (WithLp.ofLp z) ρ := by
      intro ρ
      ext y
      rw [Set.mem_preimage, mem_euclBall_iff, Metric.mem_ball]
    have hμ : ∀ ρ : ℝ, μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ) =
        ENNReal.ofReal (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) ρ).indicator fun _ => 1)
          (fun _ => euclPot) y) := by
      intro ρ
      rw [← hball ρ]
      exact (hWc n J A hJ hdim hA _ measurableSet_ball Metric.isBounded_ball).2
    have key := hM n d J A (WithLp.ofLp z) r s hJ hdim hA hr hrs
    rw [hμ r, hμ s, ← ENNReal.ofReal_mul (pow_nonneg (hr.le.trans hrs) _),
      ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    apply ENNReal.ofReal_le_ofReal
    calc s ^ (2 * (d + 1)) * (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) r).indicator fun _ => 1)
          (fun _ => euclPot) y)
        = c * (s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) r).indicator fun _ => 1)
          (fun _ => euclPot) y) := by ring
      _ ≤ c * (r ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) s).indicator fun _ => 1)
          (fun _ => euclPot) y) := mul_le_mul_of_nonneg_left key hc.le
      _ = r ^ (2 * (d + 1)) * (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) s).indicator fun _ => 1)
          (fun _ => euclPot) y) := by ring

end

end GroundTheory.Heights₂.Heights
