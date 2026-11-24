module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.genMul_of :
    GenericMulOfProd := by
  intro K _ n α hα t hcard hmem hprod
  classical
  by_cases hn : Nonempty (Fin n)
  · let g := Function.invFun α
    have hg : ∀ x ∈ t, α (g x) = x := fun x hx => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 (hmem x hx)
      exact Function.invFun_eq ⟨i, rfl⟩
    let u := t.map g
    have hu : u.map α = t := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id t]
      exact Multiset.map_congr rfl hg
    have key := hα (fun i => u.count i) ?_ ?_
    · have hu1 : u = Finset.univ.val := Multiset.ext.2 fun i => by
        rw [key i, Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ i)]
      rw [← hu, hu1]
    · rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
      simp [u, hcard]
    · calc ∏ i, α i ^ u.count i = (u.map α).prod := by
            rw [Finset.prod_multiset_map_count]
            exact (Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
              rw [Multiset.count_eq_zero.2 (by simpa using hi), pow_zero])).symm
        _ = t.prod := by rw [hu]
        _ = ∏ i, α i := by rw [hprod, Finset.prod_eq_multiset_prod]
  · have h0 : (Finset.univ : Finset (Fin n)).val = 0 := by
      rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hn)]
      rfl
    rw [h0, Multiset.map_zero] at hcard ⊢
    exact Multiset.card_eq_zero.1 hcard
