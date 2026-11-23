module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Summand
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.integral_quotient_rightTranslate_eq_and_integrable_iff :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (h : GA E r → ℂ), AutomorphicForm.IsLeftInvariant h → ∀ g ∈ normOneGL (K := E) (n := r),
      (∫ y : RightCosetSpace (rationalGLOne (K := E) (n := r)), h (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g) ∂(quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) = ∫ y : RightCosetSpace (rationalGLOne (K := E) (n := r)), h ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) ∂(quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r))) ∧
      (Integrable (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => h (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g)) (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) ↔ Integrable (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => h ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r)) (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r))) := by
  intro E _ _ r h hh g hg
  have e1 : (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => h ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r)) =
      CuspidalSpectrum.cuspQuot hh := by
    funext y
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  have e2 : (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => h (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g)) =
      CuspidalSpectrum.cuspQuot hh ∘ rightMul (rationalGLOne (K := E) (n := r)) ⟨g, hg⟩ := by
    funext y
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  have hm := measurePreserving_rightMul (Γ := rationalGLOne (K := E) (n := r)) (mu1 E r) ⟨g, hg⟩
  have he : MeasurableEmbedding (rightMul (rationalGLOne (K := E) (n := r)) ⟨g, hg⟩) :=
    by
      set_option synthInstance.maxHeartbeats 200000 in
        exact (rightMulHomeomorph (rationalGLOne (K := E) (n := r)) ⟨g, hg⟩).measurableEmbedding
  rw [e1, e2]
  exact ⟨hm.integral_comp he _, hm.integrable_comp_emb he⟩
