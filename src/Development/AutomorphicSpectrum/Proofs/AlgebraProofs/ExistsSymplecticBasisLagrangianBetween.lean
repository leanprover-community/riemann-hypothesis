module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_saturation_torsionFree {Λ : Type*} [AddCommGroup Λ] (W : Submodule ℤ Λ) :
    ∃ S : Submodule ℤ Λ, (∀ x, x ∈ S ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W) ∧
      Module.IsTorsionFree ℤ (Λ ⧸ S) := by
  refine ⟨{ carrier := {x | ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W}
            add_mem' := ?_, zero_mem' := ⟨1, one_ne_zero, by simp⟩, smul_mem' := ?_ },
    fun x => Iff.rfl, ?_⟩
  · rintro a b ⟨k, hk, ha⟩ ⟨l, hl, hb⟩
    refine ⟨k * l, mul_ne_zero hk hl, ?_⟩
    rw [smul_add]
    refine W.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact W.smul_mem _ ha
    · rw [mul_smul]; exact W.smul_mem _ hb
  · rintro c a ⟨k, hk, ha⟩
    exact ⟨k, hk, by rw [smul_comm]; exact W.smul_mem _ ha⟩
  · rw [GlobalTheory.isTorsionFree_quotient_iff]
    rintro r x hr ⟨k, hk, hx⟩
    exact ⟨k * r, mul_ne_zero hk hr, by rw [mul_smul]; exact hx⟩

theorem exists_symplecticBasis_lagrangian_between : ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (B : LinearMap.BilinForm ℤ Λ), (∀ x, B x x = 0) → Function.Bijective B → Module.finrank ℤ Λ = 2 * g → ∀ W : Submodule ℤ Λ, (∀ x, (∀ y ∈ W, B x y = 0) → ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W) → ∃ bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, (∀ i j, B (bas (.inl i)) (bas (.inl j)) = 0 ∧ B (bas (.inr i)) (bas (.inr j)) = 0 ∧ B (bas (.inl i)) (bas (.inr j)) = if i = j then 1 else 0) ∧ (∀ i, ∃ k : ℤ, k ≠ 0 ∧ k • bas (.inl i) ∈ W) ∧ ∀ x, (∀ y ∈ W, B x y = 0) → x ∈ Submodule.span ℤ (Set.range fun i => bas (.inl i)) := by
  intro g Λ _ _ _ B hB hp hg W hW
  have hA : B.IsAlt := hB
  obtain ⟨S, hS, hSt⟩ := exists_saturation_torsionFree W
  have hmem : ∀ x, x ∈ B.orthogonal S ↔ ∀ y ∈ W, B x y = 0 := by
    intro x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h y hy
      exact hA.isRefl _ _ (h y ((hS y).2 ⟨1, one_ne_zero, by simpa using hy⟩))
    · intro h y hy
      obtain ⟨k, hk, hy⟩ := (hS y).1 hy
      have := h _ hy
      rw [map_smul, smul_eq_mul] at this
      exact hA.isRefl _ _ ((mul_eq_zero.1 this).resolve_left hk)
  have hoo : B.orthogonal (B.orthogonal S) = S :=
    GlobalTheory.orthogonal_orthogonal_of_isTorsionFree_quotient hA hp.2 hSt
  have hiso : B.orthogonal S ≤ B.orthogonal (B.orthogonal S) := by
    rw [hoo]
    intro x hx
    exact (hS x).2 (hW x ((hmem x).1 hx))
  let v := Module.finBasis ℤ (B.orthogonal S)
  obtain ⟨m, b, hb, hv⟩ := GlobalTheory.exists_isSymplecticBasis_extend hA hp
    (GlobalTheory.isTorsionFree_quotient_orthogonal B S) hiso v
  have hc := GlobalTheory.IsSymplecticBasisOfType.finrank_eq b
  have hc' : Fintype.card (Fin (Module.finrank ℤ (B.orthogonal S)) ⊕ Fin m) = g := by omega
  let σ := Fintype.equivFinOfCardEq hc'
  have hb' := hb.reindex σ
  have hl : ∀ i, (b.reindex (σ.sumCongr σ)) (.inl i) = b (.inl (σ.symm i)) := by
    intro i; simp
  refine ⟨b.reindex (σ.sumCongr σ), fun i j => ⟨hb'.left_left i j, hb'.right_right i j,
    hb'.left_right i j⟩, fun i => ?_, fun x hx => ?_⟩
  · refine (hS _).1 (hoo.le ((hb.orthogonal_eq_span hv).ge ?_))
    rw [hl]
    exact Submodule.subset_span (Or.inl ⟨_, rfl⟩)
  · have hx' := (hmem x).2 hx
    have h1 : x = ∑ i, v.repr ⟨x, hx'⟩ i • (v i : Λ) := by
      have := congrArg Subtype.val (v.sum_repr ⟨x, hx'⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [h1]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨σ (.inl i), ?_⟩)
    simp only [hl, Equiv.symm_apply_apply, hv]

end GlobalTheory.CompanionTheory.Ar.Flat
