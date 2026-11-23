module

public import GroundTheory.LocalFields.Different
public import GroundTheory.LocalFields.LowerIndex
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MinpolyProductMap
public import GroundTheory.LocalFields.LowerIndexQuotient
public import GroundTheory.LocalFields.Monogenic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]


variable {K L} in
theorem map_minpoly_eq_prod {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    (minpoly 𝒪[K] x).map (algebraMap 𝒪[K] 𝒪[L]) =
      ∏ σ : L ≃ₐ[K] L, (X - C (integerAlgEquiv K L σ x)) :=
  _root_.UpperTheory.Reformulated.B.MinpolyProductMap.map_minpoly_eq_prod hx


variable {K L} in
theorem aeval_derivative_minpoly_eq_prod [DecidableEq (L ≃ₐ[K] L)] {x : 𝒪[L]}
    (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    aeval x (derivative (minpoly 𝒪[K] x)) =
      ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (x - integerAlgEquiv K L σ x) := by
  rw [← eval_map_algebraMap, ← derivative_map, map_minpoly_eq_prod hx, derivative_prod_finset,
    eval_finsetSum, Finset.sum_eq_single (1 : L ≃ₐ[K] L)]
  · rw [eval_mul, derivative_X_sub_C, eval_one, mul_one, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  · intro σ _ hσ
    rw [eval_mul, eval_prod]
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (i := 1) ?_ ?_) _
    · exact Finset.mem_erase.mpr ⟨Ne.symm hσ, Finset.mem_univ _⟩
    · simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem differentExponent_eq_sum_lowerIndex [DecidableEq (L ≃ₐ[K] L)] :
    (differentExponent K L : ℕ∞) =
      ∑ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), lowerIndex K L σ := by
  obtain ⟨x, hx⟩ := exists_integer_adjoin_eq_top (K := K) (L := L)
  rw [differentExponent_eq_addVal hx, aeval_derivative_minpoly_eq_prod hx, addVal_prod]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [lowerIndex_eq_addVal_of_adjoin_eq_top hx, ← AddValuation.map_neg, neg_sub]

theorem differentExponent_eq_sum_card_lowerRamificationGroup {N : ℕ}
    (hN : lowerRamificationGroup K L N = ⊥) :
    differentExponent K L =
      ∑ i ∈ Finset.range N, (Nat.card (lowerRamificationGroup K L i) - 1) := by
  classical
  have h := differentExponent_eq_sum_lowerIndex K L
  have hσ : ∀ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), lowerIndex K L σ =
      (((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card : ℕ∞) := by
    intro σ hσ
    have hne : σ ≠ 1 := Finset.ne_of_mem_erase hσ
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hne)
    have hnN : n ≤ N := by
      by_contra hlt'
      have hlt := not_le.mp hlt'
      have hmem : σ ∈ lowerRamificationGroup K L N := by
        rw [mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn]
        exact_mod_cast hlt
      rw [hN, Subgroup.mem_bot] at hmem
      exact hne hmem
    have hfilter : (Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i) =
        Finset.range n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range,
        mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn, Nat.cast_le]
      omega
    rw [← hn, hfilter, Finset.card_range]
  rw [Finset.sum_congr rfl hσ] at h
  have hswap : ∑ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L),
      ((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card =
      ∑ i ∈ Finset.range N, (Nat.card (lowerRamificationGroup K L i) - 1) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.card_filter, Finset.filter_erase, Finset.card_erase_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_mem _⟩), ← Fintype.card_subtype,
      Nat.card_eq_fintype_card]
  rw [← hswap]
  exact_mod_cast h

end GroundTheory.LocalField
