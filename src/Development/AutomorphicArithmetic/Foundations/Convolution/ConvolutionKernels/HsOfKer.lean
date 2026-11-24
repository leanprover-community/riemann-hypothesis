module

public import GroundTheory.AutomorphicForms.HilbertSchmidt
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GroundTheory.Automorphic
open scoped InnerProductSpace

private theorem UpperTheory.ConvolutionTheory.K.hsOfKer_countable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H] {ι : Type*} {b : ι → H}
    (hb : Orthonormal ℂ b) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (b i) (1 / 2)) ?_
    (fun _ => Metric.isOpen_ball) (fun _ => Metric.nonempty_ball.2 (by norm_num))
  intro i j hij
  refine Metric.ball_disjoint_ball ?_
  have h0 : ⟪b i, b j⟫_ℂ = 0 := hb.2 hij
  have h := norm_sub_sq (𝕜 := ℂ) (b i) (b j)
  rw [h0, hb.1 i, hb.1 j] at h
  simp only [map_zero] at h
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (b i - b j)]

private theorem UpperTheory.ConvolutionTheory.K.hsOfKer_sq {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {E : Type*} [NormedAddCommGroup E] (f : X → E) (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem UpperTheory.ConvolutionTheory.K.hsOfKer :
    ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] [TopologicalSpace.SeparableSpace (Lp ℂ 2 ν)]
      (A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (k : X → Lp ℂ 2 ν), MemLp k 2 ν →
      (∀ φ, (A φ : X → ℂ) =ᵐ[ν] fun x => ⟪k x, φ⟫_ℂ) → IsHilbertSchmidt A := by
  intro X _ ν _ _ A k hk hA
  let b := stdHilbertBasis ℂ (Lp ℂ 2 ν)
  haveI := UpperTheory.ConvolutionTheory.K.hsOfKer_countable b.orthonormal
  rw [isHilbertSchmidt_iff b]
  have h1 : ∀ i, ‖A (b i)‖ₑ ^ 2 = ∫⁻ x, ‖⟪b i, k x⟫_ℂ‖ₑ ^ 2 ∂ν := by
    intro i
    rw [Lp.enorm_def, eLpNorm_congr_ae (hA (b i)),
      UpperTheory.ConvolutionTheory.K.hsOfKer_sq _ _ (hk.aestronglyMeasurable.inner aestronglyMeasurable_const)]
    simp only [enorm_inner_comm (k _)]
  simp only [h1]
  rw [← lintegral_tsum]
  · simp only [← enorm_sq_eq_tsum b]
    rw [← UpperTheory.ConvolutionTheory.K.hsOfKer_sq ν k hk.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hk
  · intro i
    exact ((aestronglyMeasurable_const.inner hk.aestronglyMeasurable).enorm).pow_const 2
