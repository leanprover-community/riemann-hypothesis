module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

theorem UpperTheory.V.Z.Int.rootBound :
    UpperTheory.V.Z.Int.RootBound := by
  intro l _ ι S c hc h b hb
  by_contra hlt
  have hlt' : c < ‖ι.symm b‖ := not_le.mp hlt
  have hroot : Polynomial.eval b (S.map fun t => Polynomial.X - Polynomial.C t).prod = 0 := by
    rw [Polynomial.eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨Polynomial.X - Polynomial.C b, Multiset.mem_map.mpr ⟨b, hb, rfl⟩, by simp⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, Polynomial.eval_finsetSum, Finset.sum_range_succ'] at hroot
  have hn : 0 < S.card := Multiset.card_pos_iff_exists_mem.mpr ⟨b, hb⟩
  have h0 : S.esymm 0 = 1 := by simp [Multiset.esymm]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, pow_zero, one_mul, Nat.sub_zero, h0] at hroot
  have hK := congrArg ι.symm hroot

  simp only [map_add (f := _), map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at hK
  have heq : ‖ι.symm b‖ ^ S.card = ‖∑ j ∈ Finset.range S.card, (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1)))‖ := by
    rw [eq_neg_of_add_eq_zero_left hK, norm_neg, norm_pow]
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hn.ne')
    (fun j => (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1))))
  have hi' : i + 1 ≤ S.card := Finset.mem_range.mp hi
  have hj := h (i + 1) (by omega) hi'
  have hj' : ‖ι.symm (S.esymm (i + 1))‖ ≤ c ^ (i + 1) := hj
  have hpos : 0 < ‖ι.symm b‖ := lt_of_le_of_lt hc hlt'
  have hcp : c ^ (i + 1) < ‖ι.symm b‖ ^ (i + 1) := pow_lt_pow_left₀ hlt' hc (by omega)
  have hterm : ‖(-1 : PadicAlgCl l) ^ (i + 1) * (ι.symm (S.esymm (i + 1)) * ι.symm b ^ (S.card - (i + 1)))‖
      < ‖ι.symm b‖ ^ S.card := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow]
    calc ‖ι.symm (S.esymm (i + 1))‖ * ‖ι.symm b‖ ^ (S.card - (i + 1))
        < ‖ι.symm b‖ ^ (i + 1) * ‖ι.symm b‖ ^ (S.card - (i + 1)) :=
          mul_lt_mul_of_pos_right (lt_of_le_of_lt hj' hcp) (pow_pos hpos _)
      _ = ‖ι.symm b‖ ^ S.card := by rw [← pow_add]; congr 1; omega
  exact absurd (heq.le.trans hle) (not_le.mpr hterm)
