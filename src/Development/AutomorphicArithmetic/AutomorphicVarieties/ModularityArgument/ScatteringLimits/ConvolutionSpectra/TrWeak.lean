module

public import GroundTheory.AutomorphicForms.TraceClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.ScatteringLimits
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.trWeak :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (l : Filter ι) (A : ι → H →L[ℂ] H) (A₀ Z : H →L[ℂ] H), IsTraceClass Z → (∀ i, ‖A i‖ ≤ 1) →
      (∀ x y, Tendsto (fun i => ⟪x, A i y⟫_ℂ) l (𝓝 ⟪x, A₀ y⟫_ℂ)) → Tendsto (fun i => trace (A i ∘L Z)) l (𝓝 (trace (A₀ ∘L Z))) := by
  intro H _ _ _ ι l A A₀ Z hZ hA hw
  obtain ⟨S, T, hS, hT, rfl⟩ := hZ.exists_comp
  let b := stdHilbertBasis ℂ H
  have e : ∀ B : H →L[ℂ] H, trace (B ∘L S ∘L T) = ∑' m, ⟪ContinuousLinearMap.adjoint T (b m), B (S (b m))⟫_ℂ := fun B => by
    have h1 : trace ((B ∘L S) ∘L T) = trace (T ∘L (B ∘L S)) := trace_comp_comm_of_isHilbertSchmidt (hS.comp_left B) hT
    have h2 := ((isTraceClass_comp hT (hS.comp_left B)).hasSum_trace b).tsum_eq
    simp only [ContinuousLinearMap.adjoint_inner_left]
    exact h1.trans h2.symm
  simp only [e]
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖ContinuousLinearMap.adjoint T (b m)‖ ^ 2 + ‖S (b m)‖ ^ 2)
    ((hT.adjoint.hasSum_norm_sq b).summable.add (hS.hasSum_norm_sq b).summable) (fun m => hw _ _) (Eventually.of_forall fun i m => ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  have h3 : ‖A i (S (b m))‖ ≤ ‖S (b m)‖ := by simpa using (A i).le_of_opNorm_le (hA i) (S (b m))
  nlinarith [sq_nonneg (‖ContinuousLinearMap.adjoint T (b m)‖ - ‖S (b m)‖), norm_nonneg (ContinuousLinearMap.adjoint T (b m)),
    norm_nonneg (S (b m)), mul_le_mul_of_nonneg_left h3 (norm_nonneg (ContinuousLinearMap.adjoint T (b m)))]
