module

public import Mathlib.Algebra.Group.End
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Sigma
public import Mathlib.Order.Sum.Order
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem lexSumSplit_strictMono : ∀ (s : ℕ) (t : Fin (s + 1) → ℕ), StrictMono fun c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) => (Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a))) (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c) : Σₗ a, Fin (t a)) := by
  intro s t a b hab
  induction a using Lex.rec with | _ a => ?_
  induction b using Lex.rec with | _ b => ?_
  rcases a with j | x <;> rcases b with j' | x'
  · have h : j < j' := Sum.Lex.inl_lt_inl_iff.mp hab
    simp only [ofLex_toLex, Sum.elim_inl]
    exact Sigma.Lex.right _ _ h
  · simp only [ofLex_toLex, Sum.elim_inl, Sum.elim_inr]
    exact Sigma.Lex.left _ _ (Fin.succ_pos _)
  · exact absurd hab (not_lt_of_gt (Sum.Lex.inl_lt_inr _ _))
  · have h : x < x' := Sum.Lex.inr_lt_inr_iff.mp hab
    simp only [ofLex_toLex, Sum.elim_inr]
    induction x using Lex.rec with | _ x => ?_
    induction x' using Lex.rec with | _ x' => ?_
    rcases x with ⟨i, j⟩
    rcases x' with ⟨i', j'⟩
    change Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨i, j⟩ : Σ a : Fin s, Fin (t a.succ)) ⟨i', j'⟩ at h
    change Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨i.succ, j⟩ : Σ a, Fin (t a)) ⟨i'.succ, j'⟩
    rcases h with ⟨_, _, hi⟩ | ⟨_, _, hj⟩
    · exact Sigma.Lex.left _ _ (Fin.succ_lt_succ_iff.mpr hi)
    · exact Sigma.Lex.right _ _ hj

end GlobalTheory
