module

public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.KernelAwayPrimes
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FamilyLogGammaSmallHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb

@[expose] public section

noncomputable section

namespace GlobalTheory.LiftTypePrime.Jets

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions GlobalTheory.GalTheta

variable {D : D7} {N N' : ℕ}

theorem taylor_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (α : Mono D N N') :
    TaylorLogMetric.taylor D (fun z => ∑ i ∈ s, c i * f i z) α = ∑ i ∈ s, c i * TaylorLogMetric.taylor D (f i) α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.ThetaConj.taylor_zero D α
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [← ih, ← GlobalTheory.ThetaConj.taylor_mul D _ (hf i)]
    exact GlobalTheory.ThetaConj.taylor_add D ((hf i).const_mul _) (by fun_prop) α

theorem applyAt0_comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (P : MvPolynomial (Idx D N N') ℂ) :
    applyAt0 D P (fun z => ∑ i ∈ s, c i * f i z) = ∑ i ∈ s, c i * applyAt0 D P (f i) := by
  unfold applyAt0
  simp only [taylor_sum s c f hf, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring

end GlobalTheory.LiftTypePrime.Jets

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions GlobalTheory.GalTheta Jets

end GlobalTheory.LiftTypePrime

end
