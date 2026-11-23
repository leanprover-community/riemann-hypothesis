module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanNorms
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
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

theorem Weight.lerp_self_zero {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) : W.lerp W 0 = W := by
  cases W
  simp only [Weight.lerp, zero_mul, add_zero]

theorem SupNormAgainstL2.proof (h : UniformBergmanBound.Statement) : SupNormAgainstL2.Statement := by
  intro D X _ _ _ _ _ A L W dV hW
  obtain ⟨C, hC⟩ := h A L W W dV hW hW
  refine ⟨⟨Real.sqrt C, fun n hn s hs x => ?_⟩, fun n s hs M hM => ?_⟩
  · set V : Submodule ℂ (Fin A.n → X → ℂ) := ℂ ∙ s
    have hV : V ≤ L.sections n := (Submodule.span_singleton_le_iff_mem _ _).2 hs
    have hB := hC n hn 0 ⟨le_rfl, zero_le_one⟩ V hV x
    rw [Weight.lerp_self_zero] at hB
    set r := ptNormSq W n s x / sectionL2NormSq W dV n s
    have hr0 : 0 ≤ r := div_nonneg (ptNormSq_nonneg W n s x) (sectionL2NormSq_nonneg W dV n s)
    have hbdd : BddAbove (range fun v : V => ptNormSq W n (v : Fin A.n → X → ℂ) x /
        sectionL2NormSq W dV n v) := by
      refine ⟨r, ?_⟩
      rintro _ ⟨⟨v, hv⟩, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      simp only [ptNormSq_smul, sectionL2NormSq_smul]
      rcases eq_or_ne c 0 with rfl | hc
      · simpa using hr0
      · rw [mul_div_mul_left _ _ (by positivity)]
    have hle : r ≤ bergman W dV V n x :=
      le_ciSup hbdd (⟨s, Submodule.mem_span_singleton_self s⟩ : V)
    have hrC : r ≤ C * (n : ℝ) ^ D := hle.trans hB
    rcases (sectionL2NormSq_nonneg W dV n s).eq_or_lt with h0 | hpos
    · rw [ptNormSq_eq_zero_of_l2NormSq_eq_zero W dV hs h0.symm x, Real.sqrt_zero]
      positivity
    · have hpt : ptNormSq W n s x ≤ C * ((n : ℝ) ^ D * sectionL2NormSq W dV n s) := by
        rw [← mul_assoc, ← div_le_iff₀ hpos]; exact hrC
      calc Real.sqrt (ptNormSq W n s x)
          ≤ Real.sqrt (C * ((n : ℝ) ^ D * sectionL2NormSq W dV n s)) := Real.sqrt_le_sqrt hpt
        _ = Real.sqrt C * Real.sqrt ((n : ℝ) ^ D) * Real.sqrt (sectionL2NormSq W dV n s) := by
          rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_mul (by positivity), mul_assoc]
  · have := dV.isProb
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure dV.μ
    have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans (hM x₀)
    have hpt : ∀ y, ptNormSq W n s y ≤ M ^ 2 := fun y => by
      have h1 := Real.sq_sqrt (ptNormSq_nonneg W n s y)
      have h2 := hM y
      nlinarith [Real.sqrt_nonneg (ptNormSq W n s y)]
    have hl2 : sectionL2NormSq W dV n s ≤ M ^ 2 := by
      calc sectionL2NormSq W dV n s ≤ ∫ _ : X, M ^ 2 ∂dV.μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun y => ptNormSq_nonneg W n s y)
              (integrable_const _) (Eventually.of_forall hpt)
        _ = M ^ 2 := by simp
    calc Real.sqrt (sectionL2NormSq W dV n s) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt hl2
      _ = M := Real.sqrt_sq hM0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
