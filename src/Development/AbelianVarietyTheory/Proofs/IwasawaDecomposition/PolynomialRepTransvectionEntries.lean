module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem eval_transvection_polynomial_X_entry {n : ℕ} (i j : Fin n) (c : ℂ) (a b : Fin n) :
    Polynomial.eval c ((transvection i j (Polynomial.X : Polynomial ℂ)) a b) = transvection i j c a b := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

theorem eval_transvection_polynomial_neg_X_entry {n : ℕ} (i j : Fin n) (c : ℂ) (a b : Fin n) :
    Polynomial.eval c ((transvection i j (-Polynomial.X : Polynomial ℂ)) a b) = transvection i j (-c) a b := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

theorem eval_aeval_mv {σ : Type} (g : σ → Polynomial ℂ) (Q : MvPolynomial σ ℂ) (s : ℂ) :
    Polynomial.eval s (MvPolynomial.aeval g Q) = MvPolynomial.eval (fun v => (g v).eval s) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

theorem polyRep_transvection_entries_poly :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ →
      ∀ (i j : Fin n), i ≠ j → ∃ P : ι → ι → Polynomial ℂ, ∀ (s : ℂ) (B : GL (Fin n) ℂ),
        B.val = transvection i j s → ∀ a b, Φ B a b = (P a b).eval s := by
  intro n ι _ _ Φ hΦ i j hij
  choose Q hQ using hΦ.poly
  let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Polynomial ℂ :=
    Sum.elim (fun p => transvection i j (Polynomial.X : Polynomial ℂ) p.1 p.2)
      (fun p => transvection i j (-Polynomial.X : Polynomial ℂ) p.1 p.2)
  refine ⟨fun a b => MvPolynomial.aeval g (Q a b), ?_⟩
  intro s B hB a b
  have hinv : (B⁻¹).val = transvection i j (-s) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hB]
    have := transvection_mul_transvection_same (R := ℂ) i j hij s (-s)
    rw [this, add_neg_cancel, transvection_zero]
  rw [hQ a b B, eval_aeval_mv]
  congr 2
  funext v
  rcases v with p | p
  · simp [g, eval_transvection_polynomial_X_entry, hB]
  · simp [g, eval_transvection_polynomial_neg_X_entry, hinv]

end GlobalTheory
