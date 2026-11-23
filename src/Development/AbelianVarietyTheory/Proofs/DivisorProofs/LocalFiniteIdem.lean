module

public import Formalism.RealPlaceAnalysis.StatementE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTraceStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix
open Formalism.REAL (qdet qminor Tm)

namespace GlobalTheory.CentreFin

section Alg
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_mem {k : ℕ} {E : Fin k → Fin k → A} {S : Subalgebra ℂ A} (h : ∀ a b, E a b ∈ S) (u : ℂ) : qdet E u ∈ S := by
  unfold qdet qminor
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem commute_qdet {k : ℕ} {E : Fin k → Fin k → A} {x : A} (h : ∀ a b, Commute x (E a b)) (u : ℂ) :
    Commute x (qdet E u) :=
  ((Subalgebra.mem_centralizer_iff ℂ).1 (qdet_mem (S := Subalgebra.centralizer ℂ {x})
    (fun a b => (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact h a b) u) x rfl)

theorem exists_coef {k : ℕ} (E : Fin k → Fin k → A) (s : ℂ) {B : Subalgebra ℂ A} (hB : ∀ u, qdet E u ∈ B) :
    ∃ c : ℕ → A, c k = 1 ∧ (∀ j ≤ k, c j ∈ B) ∧ (∀ u, qdet E (u - s) = ∑ j ∈ Finset.range (k + 1), u ^ j • c j) ∧
      (∑ i, E i i = 0 ∨ ∃ j ≤ k, ∃ t : ℂ, ∑ i, E i i = c j + t • (1 : A)) := by
  cases k with
  | zero => exact ⟨fun _ => 1, rfl, fun _ _ => one_mem _, fun u => by simp [qdet, qminor], Or.inl (by simp)⟩
  | succ m =>
    obtain ⟨c, t, h1, h2, h3⟩ := GlobalTheory.T.shifted_capelli_determinant_subleading_coeff_trace A m E s
    refine ⟨c, h1, fun j hj => ?_, h3, Or.inr ⟨m, m.le_succ, -t, by rw [h2, neg_smul, add_neg_cancel_right]⟩⟩
    exact GlobalTheory.coeff_mem_of_poly_values_mem A (Subalgebra.toSubmodule B) _ c (fun u => h3 u ▸ hB _) j (Nat.lt_succ_of_le hj)

end Alg

section Loc
variable {n : ℕ} {J p q : Matrix (Fin n) (Fin n) ℂ}

end Loc

end GlobalTheory.CentreFin

end
