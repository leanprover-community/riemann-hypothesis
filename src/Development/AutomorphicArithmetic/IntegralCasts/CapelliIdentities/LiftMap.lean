module

public import Mathlib.Data.Multiset.MapFold
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

@[expose] public section

theorem UpperTheory.Reformulated.B.Qk56.lift_map :
    ∀ {α β : Type} (f : α → β) (B : Multiset α)
    (t : Multiset β), (∀ x ∈ t, x ∈ Multiset.map f B) → ∃ (t' : Multiset α), Multiset.map f t' = t ∧ ∀ x ∈ t', x ∈ B := by
  intro α β f B t
  induction t using Multiset.induction_on with
  | empty => exact fun _ => ⟨0, Multiset.map_zero f, fun x hx => absurd hx (Multiset.notMem_zero x)⟩
  | cons b s ih =>
    intro h
    obtain ⟨s', hs', hB⟩ := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    obtain ⟨a, ha, hab⟩ := Multiset.mem_map.1 (h b (Multiset.mem_cons_self b s))
    refine ⟨a ::ₘ s', by rw [Multiset.map_cons, hab, hs'], fun x hx => ?_⟩
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact hB x hx
