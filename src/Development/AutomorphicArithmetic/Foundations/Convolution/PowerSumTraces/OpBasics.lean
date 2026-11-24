module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

private theorem compact_of_restrict {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) (hW : IsClosed (W : Set H)) (A : H →L[ℂ] H) (T : W →L[ℂ] W)
    (hT : IsCompactOperator T) (h : W.subtypeL ∘L T = A ∘L W.subtypeL) :
    IsCompactOperator (A ∘L prj W) := by
  have hmem : ∀ v, prj W v ∈ W := fun v => by
    have h1 : prj W v ∈ W.topologicalClosure := W.topologicalClosure.starProjection_apply_mem v
    rwa [hW.submodule_topologicalClosure_eq] at h1
  let P := (prj W).codRestrict W hmem
  have hP : W.subtypeL ∘L P = prj W :=
    ContinuousLinearMap.subtypeL_comp_codRestrict _ _ _
  have e : A ∘L prj W = (W.subtypeL ∘L T) ∘L P := by
    rw [h, ContinuousLinearMap.comp_assoc, hP]
  rw [e]
  exact (hT.clm_comp W.subtypeL).comp_clm P

theorem UpperTheory.ConvolutionTheory.C.opBasics :
    UpperTheory.ConvolutionTheory.C.OpBasics := by
  intro K _ _ n μ _ f
  refine ⟨fun V hV v hv => ?_, fun v hv => ?_, ?_⟩
  · exact UnitaryRep.IsInvariant.integrated_mem _ μ hV.closed hV.inv _ hv
  · exact UnitaryRep.IsInvariant.integrated_mem _ μ (isClosed_cuspidalL2 μ)
      (isInvariant_cuspidalL2 μ) _ hv
  · exact compact_of_restrict _ (isClosed_cuspidalL2 μ) _ _ (isCompactOperator_cuspRep μ f)
      (subtypeL_comp_integrated μ _)
