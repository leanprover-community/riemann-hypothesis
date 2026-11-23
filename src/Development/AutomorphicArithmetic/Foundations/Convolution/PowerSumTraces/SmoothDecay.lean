module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
public import Development.AutomorphicArithmetic.TwistedTraces.CuspDecayFinsetSum
public import Development.AutomorphicArithmetic.TwistedTraces.CuspDecayOfRankZero
public import Development.AutomorphicArithmetic.TwistedTraces.CuspDecayTensConvRealSmoothT
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsSumConvRealSmoothT
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsSumTensOfIsLeftSmooth
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem tens_sum_left {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n) {ι : Type} (s : Finset ι)
    (f : ι → TI K n) (e : TF K n) : tens (∑ i ∈ s, f i) e = ∑ i ∈ s, tens (f i) e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := ((UpperTheory.ConvolutionTheory.Tf.tensApply K n hn 0 e).2.2.2.2 (0 : ℂ)).1
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, (UpperTheory.ConvolutionTheory.Tf.tensApply K n hn (f i) e).2.2.1, ih]

theorem UpperTheory.ConvolutionTheory.C.smoothDecay :
    UpperTheory.ConvolutionTheory.C.SmoothDecay := by
  intro K _ _ n μ _ a ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact UpperTheory.cuspDecay_of_rank_zero K μ a
  obtain ⟨U, hU, m, F, e, hF, he, rfl⟩ := UpperTheory.exists_sum_tens_of_isLeftSmooth K n hn a ha
  refine UpperTheory.cuspDecay_finset_sum K n μ (Fin m) _ fun j => ?_
  let ν : Measure (archGroup K n) := Measure.haar
  obtain ⟨ι, _, κ, γ, hκ, hFj⟩ := UpperTheory.exists_sum_conv_real_smoothT K n ν (F j) (hF j)
  rw [hFj, tens_sum_left hn Finset.univ (fun i => conv ν (κ i) (γ i)) (e j)]
  exact UpperTheory.cuspDecay_finset_sum K n μ ι _ fun i =>
    UpperTheory.cuspDecay_tens_conv_real_smoothT K n hn μ ν (κ i) (γ i) (e j) U hU (hκ i).1 (hκ i).2 (he j)
