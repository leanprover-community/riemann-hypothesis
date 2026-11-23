module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.StabGen

open GlobalTheory.TensHead

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stabClosure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) : Submodule ℂ M :=
  sInf {N | Rel ≤ N ∧ Stab Op N ∧ S ⊆ N}

theorem rel_le_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Rel ≤ stabClosure Op Rel S :=
  le_sInf fun _ hN => hN.1

theorem subset_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    S ⊆ stabClosure Op Rel S := fun _ hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.2.2 hx

theorem stab_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Stab Op (stabClosure Op Rel S) := by
  intro g hg x hx
  rw [stabClosure, Submodule.mem_sInf] at hx ⊢
  intro N hN
  exact hN.2.1 g hg x (hx N hN)

theorem closure_le {Op : Set (Module.End ℂ M)} {Rel N : Submodule ℂ M} {S : Set M}
    (h1 : Rel ≤ N) (h2 : Stab Op N) (h3 : S ⊆ N) : stabClosure Op Rel S ≤ N :=
  sInf_le ⟨h1, h2, h3⟩

theorem closure_mono {Op : Set (Module.End ℂ M)} {Rel : Submodule ℂ M} {S T : Set M}
    (h : S ⊆ T) : stabClosure Op Rel S ≤ stabClosure Op Rel T :=
  closure_le (rel_le_closure Op Rel T) (stab_closure Op Rel T)
    (h.trans (subset_closure Op Rel T))

noncomputable def chainSet [DecidableEq M] (pick : Finset M → M) : ℕ → Finset M
  | 0 => ∅
  | n + 1 => insert (pick (chainSet pick n)) (chainSet pick n)

theorem exists_finset_generating (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) :
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N →
      (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  classical
  obtain ⟨L, hL⟩ := hL
  by_contra hne
  push_neg at hne
  have hx : ∀ F : Finset M, ∃ x, x ∉ stabClosure Op Rel (F : Set M) := by
    intro F
    obtain ⟨N, h1, h2, h3, h4⟩ := hne F
    by_contra h
    push_neg at h
    exact h4 (eq_top_iff.2 fun x _ => closure_le h1 h2 h3 (h x))
  choose pick hpick using hx
  have hD : StrictMono fun n => stabClosure Op Rel (↑(chainSet pick n) : Set M) := by
    refine strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne ?_ ?_
    · exact closure_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))
    · intro h
      apply hpick (chainSet pick n)
      have hmem : pick (chainSet pick n) ∈ stabClosure Op Rel (↑(chainSet pick (n + 1)) : Set M) :=
        subset_closure Op Rel _ (by simp [chainSet])
      rw [← h] at hmem
      exact hmem
  have := hL (L + 1) (fun j => stabClosure Op Rel (↑(chainSet pick j) : Set M))
    (fun a b hab => hD hab) (fun j => ⟨rel_le_closure _ _ _, stab_closure _ _ _⟩)
  omega

end GlobalTheory.StabGen
