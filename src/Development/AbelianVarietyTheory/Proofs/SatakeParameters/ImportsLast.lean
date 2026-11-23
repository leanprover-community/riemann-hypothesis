module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.TransportLemma

theorem transport {V : Type} [AddCommGroup V] [Module ℂ V] [DecidableEq V] (T : V ≃+ V)
    {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V}
    (hS : Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S)
    (h₁ : ∀ x : V, (T : V → V) x ∈ M₁ ↔ x ∈ Λ₁)
    (h₂ : ∀ x : V, (T : V → V) x ∈ M₂ ↔ x ∈ Λ₂) :
    Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → V) S) := by
  obtain ⟨hmem, hinj, hcov⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact (h₂ s).mpr (hmem s hs)
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have h : (T : V → V) (s - t) ∈ M₁ := by
      rw [map_sub]; exact hxy
    rw [hinj s hs t ht ((h₁ _).mp h)]
  · intro y hy
    have hy' : T.symm y ∈ Λ₂ := (h₂ _).mp (by simpa using hy)
    obtain ⟨s, hs, hd⟩ := hcov _ hy'
    refine ⟨(T : V → V) s, Finset.mem_image_of_mem _ hs, ?_⟩
    have h : (T : V → V) (T.symm y - s) ∈ M₁ := (h₁ _).mpr hd
    rw [map_sub] at h
    simpa using h

theorem main : ∀ {V : Type} [inst : AddCommGroup V] [Module ℂ V] [inst_2 : DecidableEq V] (T : V ≃+ V) {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V}, Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S → (∀ (x : V), (T : V → V) x ∈ M₁ ↔ x ∈ Λ₁) → (∀ (x : V), (T : V → V) x ∈ M₂ ↔ x ∈ Λ₂) → Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → V) S) :=
  @transport

end GlobalTheory.TransportLemma
