module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open scoped InnerProductSpace

theorem UpperTheory.integralOperator_fixed_invariant_of_left_invariant_kernel :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (π : UnitaryRep G H) (τ : Representation ℂ G S) (m : Measure G) [m.IsMulLeftInvariant] (φ : G → ℂ) (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S) (U : Subgroup G), IsOp π m φ T → IsIntegralOp m τ φ A → (∀ u ∈ U, ∀ g, φ (u * g) = φ g) → (∀ v, T v ∈ fixU π U) ∧ (∀ x, A x ∈ fixedVectors τ U) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ B : H →L[ℂ] H, (∀ g v, π g (B v) = B (π g v)) → (∀ g v, π g (ContinuousLinearMap.adjoint B v) = ContinuousLinearMap.adjoint B (π g v)) → ∀ v, T (B v) = B (T v)) ∧ ∀ f : S →ₗ[ℂ] H, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x) := by
  intro G H S _ _ _ _ _ _ _ _ _ _ π τ m _ φ T A U hT hA hφ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v u hu
    refine ext_inner_left ℂ fun y => ?_
    rw [UnitaryRep.inner_map_right, hT, hT]
    rw [← integral_mul_left_eq_self (fun g => φ g * ⟪y, π g v⟫_ℂ) u]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * ⟪π u⁻¹ y, π g v⟫_ℂ = φ (u * g) * ⟪y, π (u * g) v⟫_ℂ
    rw [hφ u hu g, UnitaryRep.map_mul_apply, UnitaryRep.inner_map_right π u]
  · intro x u hu
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    have h1 : l (τ u (A x)) = (l ∘ₗ τ u) (A x) := rfl
    rw [map_sub, h1, (hA x (l ∘ₗ τ u)).2, (hA x l).2, sub_eq_zero]
    rw [← integral_mul_left_eq_self (fun g => φ g * l (τ g x)) u]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * l (τ u (τ g x)) = φ (u * g) * l (τ (u * g) x)
    rw [hφ u hu g, map_mul, Module.End.mul_apply]
  · intro D hD hinv v hv
    have hc : D.topologicalClosure = D := hD.submodule_topologicalClosure_eq
    rw [← hc, ← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro y hy
    rw [hT]
    have : ∀ g, φ g * ⟪y, π g v⟫_ℂ = 0 := fun g => by
      rw [(Submodule.mem_orthogonal' D y).1 hy _ (hinv g v hv), mul_zero]
    simp [this]
  · intro B hB _ v
    refine ext_inner_left ℂ fun y => ?_
    rw [hT, ← ContinuousLinearMap.adjoint_inner_left, hT]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * ⟪y, π g (B v)⟫_ℂ = φ g * ⟪ContinuousLinearMap.adjoint B y, π g v⟫_ℂ
    rw [hB, ContinuousLinearMap.adjoint_inner_left]
  · intro f hf x
    refine ext_inner_left ℂ fun y => ?_
    have h1 : ⟪y, f (A x)⟫_ℂ = ((innerSL ℂ y).toLinearMap ∘ₗ f) (A x) := rfl
    rw [hT, h1, (hA x _).2]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * ⟪y, π g (f x)⟫_ℂ = φ g * ⟪y, f (τ g x)⟫_ℂ
    rw [hf.map]
