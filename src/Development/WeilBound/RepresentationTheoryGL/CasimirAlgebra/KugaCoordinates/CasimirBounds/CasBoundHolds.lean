module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.StepFormula
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.CountCross
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.Expand
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.ReSwapSumLe
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace PositivityTheory.Rg.Cz

theorem casBound_holds : CasBound := by
  intro n Q _ _ C _ col b S hT hS f hf
  rw [cas_expand']
  have key : (star f ⬝ᵥ ((((n * S.card : ℕ) : ℂ) • (1 : Module.End ℂ (TV n ℂ Q)) +
      ∑ p ∈ S, ∑ q ∈ S.erase p, pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) f)).re =
      ((n * S.card : ℕ) : ℝ) * (star f ⬝ᵥ f).re +
        ∑ p ∈ S, ∑ q ∈ S.erase p, (star f ⬝ᵥ pm (Equiv.swap p q) f).re := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.sum_apply,
      dotProduct_add, dotProduct_smul, dotProduct_sum, Complex.add_re, Complex.re_sum, smul_eq_mul]
    simp
  rw [key]
  refine cas_count hT hS (fun p q => (star f ⬝ᵥ pm (Equiv.swap p q) f).re) _ ?_ ?_ ?_
  · intro p q
    simp only [Equiv.swap_comm]
  · intro p q hpq hne
    simp [hf p q hpq hne]
  · intro p _ c hc
    have h1 := re_swapSum_le' f (S.filter fun q => col q = c) p
      (by simp only [Finset.mem_filter, not_and]; exact fun _ h => hc h.symm)
      (by
        intro q hq q' hq' hne
        simp only [Finset.mem_filter] at hq hq'
        exact hf q q' (hq.2.trans hq'.2.symm) hne)
    simpa only [Complex.re_sum] using h1

end PositivityTheory.Rg.Cz
