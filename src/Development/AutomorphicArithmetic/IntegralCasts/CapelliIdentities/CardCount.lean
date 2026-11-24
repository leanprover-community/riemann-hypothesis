module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Continuity
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin

@[expose] public section

namespace ListOfFnPermExistsEquivPerm

open Finset in
private theorem card_count {α : Type} [DecidableEq α] :
    ∀ {n : ℕ} (v : Fin n → α) (a : α), #{i | v i = a} = (List.ofFn v).count a
  | 0, v, a => by simp
  | n + 1, v, a => by
    have ih := card_count (fun i : Fin n => v i.succ) a
    rw [Fin.card_filter_univ_succ', List.ofFn_succ, List.count_cons, ih]
    by_cases h : v 0 = a <;> simp [h, add_comm]

end ListOfFnPermExistsEquivPerm

theorem UpperTheory.Reformulated.B.Yde7.main :
    ∀ {α : Type} {n : ℕ} (v w : Fin n → α),
      (List.ofFn v).Perm (List.ofFn w) → ∃ (s : Equiv.Perm (Fin n)), v = w ∘ (⇑s : Fin n → Fin n) := by
  intro α n v w h
  classical
  have hc : ∀ c, Fintype.card {i // v i = c} = Fintype.card {i // w i = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert (ListOfFnPermExistsEquivPerm.card_count v c).trans ((h.count_eq c).trans (ListOfFnPermExistsEquivPerm.card_count w c).symm)
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm
