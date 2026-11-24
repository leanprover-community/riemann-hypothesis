module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.JGenLinLie
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GroundTheory.Automorphic

private theorem UpperTheory.ConvolutionTheory.L1.jUnique_mem_of_e {n : ℕ} (S : Subalgebra ℂ (HarishChandra.U n))
    (h : ∀ a b, HarishChandra.e (a, b) ∈ S) (x : HarishChandra.U n) : x ∈ S := by
  induction x using HarishChandra.U.induction with
  | halg r => exact S.algebraMap_mem r
  | hι X =>
    rw [HarishChandra.ι_eq_sum_e]
    exact S.sum_mem fun a _ => S.smul_mem (h a.1 a.2) _
  | hmul a b ha hb => exact S.mul_mem ha hb
  | hadd a b ha hb => exact S.add_mem ha hb

theorem UpperTheory.ConvolutionTheory.L1.jUnique :
    UpperTheory.ConvolutionTheory.L1.JUnique := by
  intro K _ _ _ n τ
  obtain ⟨⟨j, hj⟩, hiff⟩ := UpperTheory.ConvolutionTheory.Dp.jGen K n τ
  refine ⟨⟨j, hj, fun j' hj' => ?_⟩, (UpperTheory.ConvolutionTheory.Dp.capZc K n τ).1⟩
  refine AlgHom.ext fun x => ?_
  exact UpperTheory.ConvolutionTheory.L1.jUnique_mem_of_e (AlgHom.equalizer j' j)
    (fun a b => ((hiff j').1 hj' a b).trans ((hiff j).1 hj a b).symm) x
