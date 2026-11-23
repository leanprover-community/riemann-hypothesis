module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Span
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem ker_smul_le_ideal_smul_of_free : ∀ (Λ : Type) [CommRing Λ] (t : Λ), (∀ x : Λ, t * x = 0 → x ∈ Ideal.span {t}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M], Module.Free Λ M → ∀ m : M, t • m = 0 → m ∈ Ideal.span {t} • (⊤ : Submodule Λ M) := by
  intro Λ _ t ht M _ _ hfree m hm
  let b := Module.Free.chooseBasis Λ M
  have hc : ∀ i, ∃ d, b.repr m i = t * d := by
    intro i
    have h0 : t * b.repr m i = 0 := by
      have := congrArg (fun x => b.repr x i) hm
      simpa using this
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (ht _ h0)
    exact ⟨d, by rw [← hd, mul_comm]⟩
  choose d hd using hc
  have hm' : m = t • ∑ i ∈ (b.repr m).support, d i • b i := by
    have e := b.linearCombination_repr m
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at e
    rw [Finset.smul_sum]
    conv_lhs => rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd i, mul_smul]
  rw [hm']
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top

end GlobalTheory
