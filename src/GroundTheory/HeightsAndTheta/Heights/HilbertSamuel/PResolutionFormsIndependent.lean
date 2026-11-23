module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionFormsIndependent
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamStA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

theorem ResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    ResolutionFormsIndependent.Statement := by
  intro D Ω _ _ κ _ d n r b hb a ha
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set F : (Ix κ → ℂ) → ℂ := fun z => ∑ k, a k * secFun (b k) z with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_secFun _)

  have hoff : ∀ z, z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨y, c, hc, hyz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 : resPt d y = c () • z := by
      funext p
      simp [resPt, hyz]
    have h2 : F (resPt d y) = 0 := ha y
    rw [h1, hF] at h2
    simp only at h2
    rw [sum_secFun_smul hb.1] at h2
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ (hc ()))

  have hpts : ∀ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x), F z = 0 := by
    intro z hz
    have hcl := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hz
    have hsub : {z' | z' ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧
        eval z' (map (Int.castRingHom ℂ) g) ≠ 0} ⊆ {z' | F z' = 0} := by
      intro z' hz'
      exact hoff z' hz'.1 hz'.2
    exact closure_minimal hsub (isClosed_eq hFc continuous_const) hcl

  have : IsProbabilityMeasure d.dV := d.vol.1
  obtain ⟨y₀⟩ : Nonempty d.R.X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := d.dV)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact zero_ne_one h1
  have hz₀ : resPt d y₀ ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := d.R.mem y₀ y₀ (d.R.mem_U y₀)
  refine coeff_eq_zero_of_vanish (linIndep_rat_of_isSecBasis hb) fun z hz => ?_
  by_cases h0 : z = 0
  · have h1 := hpts _ hz₀
    rw [hF] at h1
    simp only at h1
    rw [h0, ← zero_smul ℂ (resPt d y₀), sum_secFun_smul hb.1, h1, mul_zero]
  · refine hpts z ⟨fun k => ?_, hz⟩
    by_contra hk
    push Not at hk
    exact h0 (funext fun p => by obtain ⟨⟨⟩, i⟩ := p; exact hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
