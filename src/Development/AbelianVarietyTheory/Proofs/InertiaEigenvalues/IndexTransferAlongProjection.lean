module

public import Mathlib.GroupTheory.Index
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory

theorem index_transfer_along_projection {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (L : AddSubgroup M) (T p : M →+ M) (Φ : M →+ N) (h : N →+ N)
    (hpL : ∀ y ∈ L, p y ∈ L) (hTp : ∀ y, T (p y) = p (T y))
    (hT1 : ∀ y, T (y - p y) = y - p y) (hΦ : ∀ y, Φ y = 0 → p y = 0)
    (hΦT : ∀ y, Φ (T y) = h (Φ y)) :
    (L.map T).relIndex L = ((L.map Φ).map h).relIndex (L.map Φ) := by
  have key : ∀ y ∈ L, (y ∈ L.map T ↔ Φ y ∈ (L.map Φ).map h) := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Φ x, ⟨x, hx, rfl⟩, (hΦT x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
      have h0 : Φ (T x - y) = 0 := by rw [map_sub, hΦT, hxy, sub_self]
      have hp : p (T x) = p y := by
        have := hΦ _ h0
        rwa [map_sub, sub_eq_zero] at this
      refine ⟨p x + (y - p y), L.add_mem (hpL x hx) (L.sub_mem hy (hpL y hy)), ?_⟩
      show T (p x + (y - p y)) = y
      rw [map_add (f := _), hT1, hTp, hp]
      abel
  let ψ : L →+ L.map Φ :=
    (Φ.comp L.subtype).codRestrict (L.map Φ) (fun x => ⟨x.1, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hc : (L.map T).addSubgroupOf L =
      (((L.map Φ).map h).addSubgroupOf (L.map Φ)).comap ψ := by
    ext ⟨y, hy⟩
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact key y hy
  unfold AddSubgroup.relIndex
  rw [hc, AddSubgroup.index_comap_of_surjective _ hψ]

end GlobalTheory
