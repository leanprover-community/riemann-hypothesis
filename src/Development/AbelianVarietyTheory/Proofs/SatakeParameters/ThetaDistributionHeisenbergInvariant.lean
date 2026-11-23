module

public import Mathlib.LinearAlgebra.Trace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsNilpotentOfTracePow
public import Mathlib.Algebra.Lie.OfAssociative
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

namespace GlobalTheory.UnipNormalTrace

open Module

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem isNilpotent_of_trace_pow_eq_zero {K : Type} [Field K] [CharZero K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (h : ∀ k, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  first
  | exact @_root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow
  | exact _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow
  | (apply _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow ..)

end GlobalTheory.UnipNormalTrace
