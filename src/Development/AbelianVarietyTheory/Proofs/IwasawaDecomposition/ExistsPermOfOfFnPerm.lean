module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Card
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace GlobalTheory.FiberCardPermutation

theorem card_fiber_eq_count {α : Type} [DecidableEq α] {n : ℕ} (v : Fin n → α) (c : α) :
    Fintype.card {i : Fin n // v i = c} = Multiset.count c (List.ofFn v : Multiset α) := by
  rw [← Fin.univ_val_map, Multiset.count_map, Fintype.card_subtype]
  simp only [Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun _ _ => eq_comm)

theorem exists_perm_of_ofFn_perm {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : List.Perm (List.ofFn v) (List.ofFn w)) :
    ∃ σ : Equiv.Perm (Fin n), v = w ∘ (⇑σ : Fin n → Fin n) := by
  classical
  have hm : (List.ofFn v : Multiset α) = (List.ofFn w : Multiset α) := Multiset.coe_eq_coe.mpr h
  have hc : ∀ c : α, Fintype.card {i : Fin n // v i = c} = Fintype.card {i : Fin n // w i = c} := by
    intro c
    have h1 := card_fiber_eq_count v c
    have h2 := card_fiber_eq_count w c
    rw [hm, ← h2] at h1
    convert h1
  refine ⟨Equiv.ofFiberEquiv (f := v) (g := w) (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map (f := v) (g := w) _ i).symm

end GlobalTheory.FiberCardPermutation
