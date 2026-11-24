module

public import Mathlib.Analysis.Complex.Exponential
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
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

namespace GlobalTheory.SummableExpNegAbsSum

theorem summable_int : Summable fun n : ℤ ↦ Real.exp (-|(n : ℝ)|) := by
  have h : Summable fun n : ℕ ↦ Real.exp (-(n : ℝ)) := Real.summable_exp_neg_nat
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h

theorem summable_exp_neg_sum_abs {ι : Type} [inst : Fintype ι] :
    Summable fun (m : ι → ℤ) ↦ Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) := by
  classical
  set g : ℤ → ℝ := fun n ↦ Real.exp (-|(n : ℝ)|) with hg
  have hgpos : ∀ n, 0 ≤ g n := fun n => (Real.exp_pos _).le
  have hgs : Summable g := summable_int
  have hprod : ∀ m : ι → ℤ, Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) = ∏ i : ι, g (m i) := by
    intro m
    simp only [hg]
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  simp_rw [hprod]
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' n : ℤ, g n)
    (fun m => Finset.prod_nonneg fun i _ => hgpos _) fun s => ?_
  set T : ι → Finset ℤ := fun i => s.image (fun m : ι → ℤ => m i) with hT
  have hsub : s ⊆ Fintype.piFinset T := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hm
  calc ∑ m ∈ s, ∏ i : ι, g (m i)
      ≤ ∑ m ∈ Fintype.piFinset T, ∏ i : ι, g (m i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
          Finset.prod_nonneg fun i _ => hgpos _
    _ = ∏ i : ι, ∑ n ∈ T i, g n := (Finset.prod_univ_sum T (fun _ n => g n)).symm
    _ ≤ ∏ _i : ι, ∑' n : ℤ, g n := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun _ _ => hgpos _)
          fun i _ => ?_
        exact hgs.sum_le_tsum _ fun _ _ => hgpos _

end GlobalTheory.SummableExpNegAbsSum
