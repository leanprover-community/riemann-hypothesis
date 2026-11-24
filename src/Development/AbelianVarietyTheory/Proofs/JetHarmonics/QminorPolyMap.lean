module

public import Formalism.RealPlaceAnalysis.StatementE
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

open Formalism.REAL Finset

namespace GlobalTheory


open Finset in
theorem _root_.GlobalTheory.qminor_polyMap (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (s : ℂ) :
    ∃ c : ℕ → A, ∀ u : ℂ, _root_.Formalism.REAL.qminor E a b (u - s) = ∑ i ∈ Finset.range (t + 1), u ^ i • c i := by
  classical
  let F : Equiv.Perm (Fin t) → Fin t → Polynomial A := fun σ k =>
    Polynomial.C (if a (σ k) = b k then (1 : A) else 0) * Polynomial.X +
      Polynomial.C ((if a (σ k) = b k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) +
        E (a (σ k)) (b k))
  let P : Polynomial A :=
    ∑ σ, Polynomial.C (((Equiv.Perm.sign σ : ℤ) : A)) * (List.ofFn (F σ)).prod
  have hdeg : P.natDegree < t + 1 := by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_)
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_list_prod_le _).trans ?_
    have h1 : ∀ k, (F σ k).natDegree ≤ 1 := fun k =>
      (Polynomial.natDegree_add_le _ _).trans
        (max_le ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le) (by simp))
    rw [List.map_ofFn, List.sum_ofFn]
    calc ∑ k, (Polynomial.natDegree ∘ F σ) k ≤ ∑ _k : Fin t, 1 := Finset.sum_le_sum fun k _ => h1 k
      _ = t := by simp
  refine ⟨fun i => P.coeff i, fun u => ?_⟩
  have hcomm : ∀ (p : Polynomial A) (k : ℕ),
      Commute ((RingHom.id A) (p.coeff k)) (algebraMap ℂ A u) := fun p k =>
    Algebra.commute_algebraMap_right u _
  have hF : ∀ σ k, Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) (F σ k) =
      _root_.Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (a (σ k)) (b k) := by
    intro σ k
    unfold _root_.Formalism.REAL.Tm
    simp only [F, Polynomial.eval₂_add, Polynomial.eval₂_mul_X, Polynomial.eval₂_C,
      RingHom.id_apply]
    split_ifs with h
    · rw [one_mul, ← add_assoc, ← map_add (f := _)]
      congr 2
      ring
    · simp
  have hP : Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) P = _root_.Formalism.REAL.qminor E a b (u - s) := by
    unfold _root_.Formalism.REAL.qminor
    simp only [P, Polynomial.eval₂_finsetSum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Polynomial.eval₂_mul_noncomm _ _ (hcomm _), Polynomial.eval₂_C,
      Polynomial.eval₂_list_prod_noncomm _ _ _ (fun p _ => hcomm p), List.map_ofFn]
    simp only [Function.comp_def, hF, RingHom.id_apply]
  rw [← hP, Polynomial.eval₂_eq_sum_range' _ hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes _ _).symm

end GlobalTheory
