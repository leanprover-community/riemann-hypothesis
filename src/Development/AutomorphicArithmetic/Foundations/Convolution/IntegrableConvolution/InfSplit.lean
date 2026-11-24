module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GalSplit
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField GroundTheory.Global.InfinitePlace
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.L1.infSplit :
    UpperTheory.ConvolutionTheory.L1.InfSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm
  refine ⟨fun hF => ?_, fun p => ?_⟩
  · have h : ∀ v : InfinitePlace F, Nonempty (E →ₐ[F] v.Completion) := fun v => by
      haveI : IsAlgClosed v.Completion :=
        IsAlgClosed.of_ringEquiv ℂ _
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex (hF.isComplex v)).symm
      exact ⟨IsAlgClosed.lift⟩
    exact ⟨Pi.algHom F (fun v : InfinitePlace F => v.Completion) fun v => (h v).some⟩
  · obtain ⟨e, he, hs⟩ := UpperTheory.ConvolutionTheory.L1.galSplit F E σ hσ m hm (InfiniteAdeleRing F) (InfiniteAdeleRing E)
      (tensorInfiniteAdeleRingEquiv (K := F) (L := E)) p
    have hd : ∀ r i, e (infiniteAdeleRingMap (K := F) (L := E) r) i = r := fun r i => by
      have := he 1 r i
      rwa [tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul, map_one, map_one, one_mul] at this
    have hx : ∀ (x : E) i, e (algebraMap E (InfiniteAdeleRing E) x) i = p ((σ ^ (i : ℕ)) x) := fun x i => by
      have := he x 1 i
      rwa [tensorInfiniteAdeleRingEquiv_tmul', map_one, mul_one, mul_one] at this
    refine ⟨⟨e, ?_, ?_, hd, hs⟩, hx⟩
    · let b := Module.finBasis F E
      have h : ∀ y i, e y i = ∑ j, p ((σ ^ (i : ℕ)) (b j)) * adeleCoord b j y := fun y i => by
        conv_lhs => rw [← tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y]

        rw [map_sum, map_sum, Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => he _ _ _
      refine continuous_pi fun i => ?_
      simp_rw [h]
      exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_adeleCoord b j)
    · have h : ∀ a, e.symm a =
          ∑ i, infiniteAdeleRingMap (K := F) (L := E) (a i) * e.symm (Pi.single i 1) := fun a => by
        apply e.injective
        funext k

        rw [map_sum, Finset.sum_apply, RingEquiv.apply_symm_apply]
        simp_rw [map_mul, RingEquiv.apply_symm_apply, Pi.mul_apply, hd]
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          rw [Pi.single_eq_of_ne hj.symm, mul_zero]
        · simp
      have h' : (e.symm : _ → _) = fun a => ∑ i, infiniteAdeleRingMap (K := F) (L := E) (a i) * e.symm (Pi.single i 1) :=
        funext h
      rw [h']
      exact continuous_finsetSum _ fun i _ =>
        (continuous_infiniteAdeleRingMap.comp (continuous_apply i)).mul continuous_const
