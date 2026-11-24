module

public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.tensCont :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : CompactlySupportedContinuousMap (archGroup K n) ℂ) (e : CompactlySupportedContinuousMap (AdelicGLn.FiniteAdelicGL K n) ℂ),
    (Continuous fun x : normOneGL (K := K) (n := n) => kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n))) ∧
    (HasCompactSupport fun x : normOneGL (K := K) (n := n) => kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n))) ∧
    ∀ x : normOneGL (K := K) (n := n), kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n)) ≠ 0 →
      ∃ a ∈ tsupport β, ∃ h ∈ tsupport e, x = archP K n a * MultiplicityOne.finProj K n h := by
  intro K _ _ n hn β e
  have key : ∀ x : normOneGL (K := K) (n := n), kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) *
      e (finPart K n (x : AdelicGLn.AdelicGL K n)) ≠ 0 →
      ∃ a ∈ tsupport β, ∃ h ∈ tsupport e, x = archP K n a * MultiplicityOne.finProj K n h := by
    intro x hx
    have hk := left_ne_zero_of_mul hx
    have he := right_ne_zero_of_mul hx
    obtain ⟨s, hs⟩ : ∃ s, β (infPart K n (x : AdelicGLn.AdelicGL K n) * zInf K n s) ≠ 0 := by
      by_contra h0
      simp only [not_exists, ne_eq, not_not] at h0
      exact hk (by simp [kbar, h0])
    refine ⟨_, subset_tsupport _ hs, _, subset_tsupport _ he, ?_⟩
    have hf : ∀ h, MultiplicityOne.finProj K n h = retractOne (finEmb K n h) := fun h => rfl
    rw [archimedeanProjection_mul_positiveScalar hn, hf, ← retract_infEmb, ← retractOne_mul,
      infEmb_infPart_mul_finEmb_finPart, retractOne_coe]
  refine ⟨?_, ?_, key⟩
  · exact ((continuous_kbar hn β.continuous β.hasCompactSupport).comp
      (continuous_infPart.comp continuous_subtype_val)).mul
      (e.continuous.comp (continuous_finPart.comp continuous_subtype_val))
  · have hC : IsCompact ((fun p : archGroup K n × AdelicGLn.FiniteAdelicGL K n =>
        archP K n p.1 * MultiplicityOne.finProj K n p.2) '' (tsupport β ×ˢ tsupport e)) :=
      (β.hasCompactSupport.isCompact.prod e.hasCompactSupport.isCompact).image
        ((continuous_archP.comp continuous_fst).mul
          (MultiplicityOne.continuous_finProj.comp continuous_snd))
    set_option synthInstance.maxHeartbeats 200000 in
      refine HasCompactSupport.intro hC fun x hx => ?_
    by_contra hne
    obtain ⟨a, ha, h, hh, rfl⟩ := key x hne
    exact hx ⟨(a, h), ⟨ha, hh⟩, rfl⟩
