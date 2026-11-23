module

public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.L2NormScaling
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section


namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData

namespace BM

theorem smooth_admissible_form_one_side : CompanionTheory.Lime.BM.AtFormAdmOneOfSteps := by
  intro hSch hBC hNI hBB hSh hKF hZ hZD hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => DDSmoothness.fdeg_eq hd hSd hx
  have hmu := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hAs : ∀ v : H, IsAdm σ w0 v → v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    intro v hv
    rcases hv with hv | hv
    · exact DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 v hv
    · exact hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, hx1, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have hK := hKF hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS l hl hx1 hid
    have hI : ∀ v : H, IsAdm σ w0 v → ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
        be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
      intro v hv x hx
      rcases hv with hv | hv
      · exact hid x hx v hv
      · exact hK v hv x hx
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x hx v hv, hI v hv x hx⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v hv (l v)).1
    rw [hI v hv v (hAs v hv)] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine DDSmoothness.l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hI v hv _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x hx _ hg)]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    have h0 := hZ hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have h0D := hZD hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨fun _ => 0, DDSmoothness.bessel_zero, fun x hx v hv => ⟨hBC1 x hx v hv, ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    have hz0 : be z c π σ μW μN x v = 0 := by
      rcases hv with hv | hv
      · exact h0D v hv x hx
      · exact h0 v hv x hx
    rw [hz0]
    ext ξ; simp

end BM

end UnipotentHaarMeasurability

end Formalism.FourierDecayAlt.P

end
