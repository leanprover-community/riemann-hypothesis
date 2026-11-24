module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHoloInjDerivInj
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalFlatNotInjective
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicKernelFibre
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem HoloInjDerivInj.proof : HoloInjDerivInj.Statement := by
  intro m f U hU hf hinj u hu
  have hdet : LinearMap.det (fderiv ℂ f u : (Fin m → ℂ) →ₗ[ℂ] Fin m → ℂ) ≠ 0 :=
    IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof
      IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof m U f hU hf.differentiableOn hinj u hu
  have hunit : IsUnit (fderiv ℂ f u : (Fin m → ℂ) →ₗ[ℂ] Fin m → ℂ) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  exact ((Module.End.isUnit_iff _).1 hunit).injective

end GroundTheory.Heights₂.Heights.LowerBoundFree
