module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicInverse
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicJacobianNeZero
public import Mathlib.Analysis.Analytic.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicInverse

theorem analyticAt_of_differentiableOn {k : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin k → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin k → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  refine AnalyticAt.pi fun i => ?_
  refine analyticOnNhd_of_continuousOn_of_separately hU
    ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx
  have hfz : DifferentiableAt ℂ (fun w => f w i) z :=
    differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i
  have hu : DifferentiableAt ℂ (Function.update z j) (z j) :=
    (hasFDerivAt_update z (z j)).differentiableAt
  have hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j)) := by
    rwa [Function.update_eq_self]
  exact hfz'.comp (z j) hu

theorem exists_equiv (hJ : InjectiveHolomorphicJacobianNeZero.Statement) {k : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin k → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    {x : Fin k → ℂ} (hx : x ∈ U) :
    ∃ e : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ), HasStrictFDerivAt f (e : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) x := by
  have hdet := hJ k U f hU hf hinj x hx
  refine ⟨(LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv, ?_⟩
  have he : ((LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv :
      (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ f x := by
    ext1 v
    rfl
  rw [he]
  exact (analyticAt_of_differentiableOn hU hf hx).hasStrictFDerivAt

theorem proof (hJ : InjectiveHolomorphicJacobianNeZero.Statement) : InjectiveHolomorphicInverse.Statement := by
  intro k U f hU hf hinj
  have hleft : ∀ z ∈ U, Function.invFunOn f U (f z) = z := fun z hz =>
    hinj (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz (Function.invFunOn_eq ⟨z, hz, rfl⟩)
  refine ⟨?_, Function.invFunOn f U, ?_, hleft⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    rw [← he.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hU.mem_nhds hx)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    refine (he.to_local_left_inverse ?_).differentiableAt.differentiableWithinAt
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hleft z hz

end InjectiveHolomorphicInverse

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
