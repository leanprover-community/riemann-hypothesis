module

public import Mathlib.RingTheory.Finiteness.Defs
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

namespace GlobalTheory.CommonSmulMembership

theorem exists_common_smul_mem {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (P : Submonoid O) {L L' : Submodule O M} (hL : Submodule.FG L)
    (h : ∀ v ∈ L, ∃ s ∈ P, s • v ∈ L') : ∃ s ∈ P, ∀ v ∈ L, s • v ∈ L' := by
  classical
  obtain ⟨S, rfl⟩ := hL
  choose f hfP hf using h
  let g : S → O := fun x => f x (Submodule.subset_span x.2)
  refine ⟨∏ x : S, g x, P.prod_mem (fun x _ => hfP _ _), ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    have hx' : x ∈ S := hx
    rw [← Finset.prod_erase_mul Finset.univ g (Finset.mem_univ (⟨x, hx'⟩ : S)), mul_smul]
    exact L'.smul_mem _ (hf x _)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L'.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact L'.smul_mem a hx

end GlobalTheory.CommonSmulMembership
