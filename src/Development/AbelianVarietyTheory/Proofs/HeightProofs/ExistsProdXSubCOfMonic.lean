module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

open Polynomial

namespace GlobalTheory.MonicRootsProduct

theorem exists_prod_X_sub_C_of_monic (p : ℂ[X]) (hm : p.Monic) :
    ∃ r : Fin p.natDegree → ℂ, ∏ j, (X - C (r j)) = p := by
  classical
  have hc : p.roots.toList.length = p.natDegree := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  refine ⟨fun j => p.roots.toList[(j : ℕ)]'(by rw [hc]; exact j.2), ?_⟩
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm
    IsAlgClosed.card_roots_eq_natDegree
  rw [← Multiset.coe_toList p.roots, Multiset.map_coe, Multiset.prod_coe,
    ← Fin.prod_univ_fun_getElem] at hprod
  exact (Fintype.prod_equiv (finCongr hc.symm) _ _ (fun j => rfl)).trans hprod

theorem exists_roots {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ, ∏ j : Fin δ, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  have hdeg := Polynomial.degree_sum_fin_lt c
  have hmon : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).Monic := Polynomial.monic_X_pow_add hdeg
  have hd : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).natDegree = δ := by
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_of_monic _ hmon
  exact ⟨fun j => r (Fin.cast hd.symm j),
    (Fintype.prod_equiv (finCongr hd.symm) _ _ (fun j => rfl)).trans hr⟩

end GlobalTheory.MonicRootsProduct
