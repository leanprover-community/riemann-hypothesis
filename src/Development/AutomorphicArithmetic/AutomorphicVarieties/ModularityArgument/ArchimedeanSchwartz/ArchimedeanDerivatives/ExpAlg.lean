module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ExpIndep
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Polynomial

namespace UpperTheory.V.Z.Inf

private theorem isExp_of_sum {ι : Type} (S : Finset ι) (t : ι → ℝ) (a : ι → ℂ) (f : ℂ → ℂ)
    (h : ∀ s, f s = ∑ i ∈ S, a i * Complex.exp (t i * s)) : IsExp f := by
  classical
  refine ⟨S.image t, fun r => ∑ i ∈ S.filter (fun i => t i = r), a i, fun s => ?_⟩
  rw [h s]
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (g := t) (fun i hi => Finset.mem_image_of_mem t hi)]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

theorem expAlg : ExpAlg := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro f ⟨T, a, h⟩
    have : f = fun s => ∑ t ∈ T, a t * Complex.exp (t * s) := funext h
    rw [this]
    fun_prop
  · rintro f g ⟨T, a, h⟩ ⟨U, b, h'⟩
    refine isExp_of_sum (T ×ˢ U) (fun p => p.1 + p.2) (fun p => a p.1 * b p.2) _ fun s => ?_
    rw [h, h', Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  · intro c
    exact ⟨{0}, fun _ => c, fun s => by simp⟩
  · rintro f z ⟨T, a, h⟩
    refine ⟨T, fun t => a t * Complex.exp (t * z), fun s => ?_⟩
    simp only [h]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_add, Complex.exp_add]
    ring
  · intro p t z
    refine isExp_of_sum (Finset.range (p.natDegree + 1)) (fun n => n * t)
      (fun n => p.coeff n * Complex.exp (n * (t * z))) _ fun s => ?_
    rw [eval_eq_sum_range]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

end UpperTheory.V.Z.Inf
