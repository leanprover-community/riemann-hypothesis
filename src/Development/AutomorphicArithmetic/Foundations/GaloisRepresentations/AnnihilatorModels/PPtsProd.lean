module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptsProd_of :
    PtsProd := by
  intro B B' _ _ ρ ι J _ _ I _ a v
  have hf : ∀ c : ι → B, Polynomial.map (MvPolynomial.map ρ) (form c) = form (fun k => ρ (c k)) := by
    intro c

    simp [form, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  have key : ∀ (m : J → Multiset (ι → B')) (s : Finset J),
      (Multiset.map form (∑ j ∈ s, a j • m j)).prod = ∏ j ∈ s, (Multiset.map form (m j)).prod ^ a j := by
    intro m s
    classical
    refine Finset.induction_on s (by simp) ?_
    intro j s hj ih
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Multiset.map_add (f := _), Multiset.prod_add, ih,
      Multiset.map_nsmul, Multiset.prod_nsmul]
  simp only [pts, mapP]
  rw [key, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Polynomial.map_pow, Polynomial.map_prod, Multiset.map_map]
  congr 1
  rw [Finset.prod_eq_multiset_prod]
  simp [Function.comp_def, hf]
