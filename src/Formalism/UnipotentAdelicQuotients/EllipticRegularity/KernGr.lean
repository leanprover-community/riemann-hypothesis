module

public import Formalism.UnipotentAdelicQuotients.EllReg
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

lemma gr_zero {d : ℕ} (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ b x‖ ≤ L)
    (x0 y : E d) (r : ℝ) (hr : 0 < r) : ‖b (x0 + r • y) - b x0‖ ≤ L * (r * ‖y‖) := by
  have hd : Differentiable ℝ b := hb.differentiable (by simp)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hd x) (fun x _ => hL x)
    convex_univ (Set.mem_univ x0) (Set.mem_univ (x0 + r • y))
  rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at this

lemma gr_pos {d : ℕ} (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (k : ℕ) (hk0 : 0 < k) (M : ℝ)
    (hM : ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ M) (x0 y : E d) (r : ℝ) (hr : 0 < r) :
    ‖iteratedFDeriv ℝ k (fun y => b (x0 + r • y) - b x0) y‖ ≤ M * r ^ k := by
  have hk : k ≠ 0 := hk0.ne'
  have hkle : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by exact_mod_cast (ENat.natCast_lt_top k).le
  obtain ⟨g, hg⟩ : ∃ g : E d →L[ℝ] E d, g = r • ContinuousLinearMap.id ℝ (E d) := ⟨_, rfl⟩
  have hshift : ContDiff ℝ ∞ (fun z => b (x0 + z)) := hb.comp (contDiff_const.add contDiff_id)
  have hfun : (fun y => b (x0 + r • y) - b x0) = ((fun z => b (x0 + z)) ∘ g) - fun _ => b x0 := by
    funext y; simp [hg]
  rw [hfun, iteratedFDeriv_sub_apply (((hshift.comp g.contDiff).of_le hkle).contDiffAt)
    contDiffAt_const, iteratedFDeriv_const_of_ne hk, Pi.zero_apply, sub_zero,
    g.iteratedFDeriv_comp_right hshift y hkle, iteratedFDeriv_comp_add_left]
  have hgn : ‖g‖ ≤ r := by
    rw [hg]
    refine (norm_smul_le r _).trans ?_
    rw [Real.norm_of_nonneg hr.le]
    exact mul_le_of_le_one_right hr.le ContinuousLinearMap.norm_id_le
  calc _ ≤ ‖iteratedFDeriv ℝ k b (x0 + g y)‖ * ∏ _i : Fin k, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ M * r ^ k := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul (hM _) (pow_le_pow_left₀ (norm_nonneg _) hgn k) (by positivity)
        ((norm_nonneg _).trans (hM 0))

end

end ZetaZeros.D.EllReg
