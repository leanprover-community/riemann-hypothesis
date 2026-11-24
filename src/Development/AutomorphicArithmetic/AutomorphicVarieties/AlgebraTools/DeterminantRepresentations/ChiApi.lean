module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Expand
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

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.chiApi :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G),
    D.lam 0 y = 1 ∧ D.lam n y = D.D A y ∧ (D.chi y).Monic ∧ (D.chi y).natDegree ≤ n ∧
    D.chi y = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i y) * X ^ (n - i) := by
  intro n A G _ _ D y
  have hsum : D.chi y = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i y) * X ^ (n - i) := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y (Polynomial A) X (-1)
    have h1 : MonoidAlgebra.single 1 (X : Polynomial A) +
        (-1 : Polynomial A) • (MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A))) y =
        MonoidAlgebra.single 1 X - (MonoidAlgebra.mapRingHom G C) y := by
      rw [neg_one_smul, ← sub_eq_add_neg, Polynomial.algebraMap_eq]
    rw [h1] at key
    unfold UpperTheory.V.W.GDet.chi
    rw [key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.algebraMap_eq, C_mul, C_pow, C_neg, C_1]
    ring
  have h0 : D.lam 0 y = 1 := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y A 1 0
    rw [zero_smul, add_zero, ← MonoidAlgebra.one_def, map_one] at key
    rw [Finset.sum_eq_single 0] at key
    · simpa using key.symm
    · intro b _ hb
      simp [zero_pow hb]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  have hn : D.lam n y = D.D A y := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y A 0 1
    rw [Finset.sum_eq_single n] at key
    · simp only [MonoidAlgebra.single_zero, zero_add, one_smul, Nat.sub_self, pow_zero, one_pow,
        mul_one, Algebra.algebraMap_self, RingHom.id_apply] at key
      rw [← key]
      congr 1
      ext g
      simp [MonoidAlgebra.mapRingHom]
    · intro b hb hbn
      have : n - b ≠ 0 := by
        have := Finset.mem_range.mp hb
        omega
      simp [zero_pow this]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  have hdeg : (D.chi y).natDegree ≤ n := by
    rw [hsum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    omega
  have hcoeff : (D.chi y).coeff n = 1 := by
    rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
    · simp [h0]
    · intro b hb hb0
      have : n ≠ n - b := by
        have := Finset.mem_range.mp hb
        omega
      rw [Polynomial.coeff_C_mul_X_pow, if_neg this]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  exact ⟨h0, hn, Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hdeg hcoeff, hdeg, hsum⟩
