module

public import Formalism.FormalDegreeBessel.StatementDS
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

lemma dslowk_split {α : Type*} (s : Finset α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    (s.filter p).card =
      (s.filter fun x => p x ∧ q x).card + (s.filter fun x => p x ∧ ¬ q x).card := by
  have hd : Disjoint (s.filter fun x => p x ∧ q x) (s.filter fun x => p x ∧ ¬ q x) :=
    Finset.disjoint_filter.2 fun x _ h1 h2 => h2.2 h1.2
  rw [← Finset.card_disjUnion _ _ hd]
  congr 1
  ext x
  simp only [Finset.mem_disjUnion, Finset.mem_filter]
  tauto

lemma dslowk_lowK_eq {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK ε lam a = lam a + (((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)) - 2 * rhoC ε a := by
  have e1 : (univ.filter fun b : Fin n => a < b).card =
      (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card :=
    dslowk_split _ _ _
  have e2 : (univ.filter fun b : Fin n => b < a).card =
      (univ.filter fun b => b < a ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card :=
    dslowk_split _ _ _
  have c1 : (univ.filter fun b : Fin n => a < b).card + (a : ℕ) + 1 = n := by
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    have := a.isLt
    omega
  have c2 : (univ.filter fun b : Fin n => b < a).card = (a : ℕ) := by
    rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
  rw [e1] at c1
  rw [e2] at c2
  have r1 := congrArg (Nat.cast (R := ℝ)) c1
  have r2 := congrArg (Nat.cast (R := ℝ)) c2
  push_cast at r1 r2
  unfold lowK rhoN rhoC
  simp only [Pi.add_apply, Pi.sub_apply]
  linarith

theorem low_k_integrable_holds : LowKInt := by
  intro n ε lam h a
  obtain ⟨m, hm⟩ := h a
  refine ⟨m + n - 1 - a - ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) +
    ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
  rw [dslowk_lowK_eq]
  unfold rhoC
  push_cast
  linarith

end Formalism.QuantumDeterminants
