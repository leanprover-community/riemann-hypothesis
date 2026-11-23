module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem deltaHom_unique_of_base : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (DQ : Delta l Q) (DC : Delta l C) (J : Ideal A) (JC : Ideal C) (i : A →+* Q) (w : Q) (tb : TopBasis i J (Digits l)), (∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] w) ^ n) → IsHausdorff JC C → ∀ h h' : Q →+* C, IsδMap DQ DC h → IsδMap DQ DC h' → J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h w = h' w → h = h' := by
  intro l _ A _ Q _ C _ DQ DC J JC i w tb hb hH h h' hδ hδ' hJ hi hw
  have hit : ∀ (g : Q →+* C), IsδMap DQ DC g → ∀ k x, g (DQ.δ^[k] x) = DC.δ^[k] (g x) := by
    intro g hg k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]
  have hbα : ∀ α, h (tb.b α) = h' (tb.b α) := by
    intro α
    simp only [hb, Finsupp.prod, map_prod, map_pow, hit h hδ, hit h' hδ', hw]
  ext x
  have key : ∀ n, h x - h' x ∈ JC ^ n := by
    intro n
    have hF : ∀ α, α ∉ (tb.fin x n).toFinset → tb.c α x ∈ J ^ n := by
      intro α hα
      by_contra hc
      exact hα ((tb.fin x n).mem_toFinset.2 hc)
    have hap := tb.approx x n _ hF
    have hs : h (∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) =
        h' (∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) := by

      simp only [map_sum, map_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← RingHom.comp_apply h i, hi, RingHom.comp_apply, hbα]
    have mem : ∀ g : Q →+* C, g.comp i = h.comp i →
        g (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) ∈ JC ^ n := by
      intro g hg
      have hm := Ideal.mem_map_of_mem g hap
      rw [Ideal.map_map, hg, Ideal.map_pow] at hm
      exact Ideal.pow_right_mono hJ n hm
    have e : h x - h' x = h (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) -
        h' (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) := by
      rw [map_sub, map_sub, hs]; ring
    rw [e]
    exact sub_mem (mem h rfl) (mem h' hi.symm)
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key n

end GlobalTheory.BSP
