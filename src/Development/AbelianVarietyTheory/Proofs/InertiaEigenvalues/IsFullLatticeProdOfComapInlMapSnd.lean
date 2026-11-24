module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem isLat_of_comap_inl_of_map_snd (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A))
    (h₁ : IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)))
    (h₂ : IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A))) : IsLat K.O K.E M := by
  obtain ⟨f₁, s₁⟩ := h₁
  obtain ⟨f₂, s₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd K.O B₁.A B₂.A) f₂ ?_
    have : M ⊓ LinearMap.ker (LinearMap.snd K.O B₁.A B₂.A) =
        (M.comap (LinearMap.inl K.O B₁.A B₂.A)).map (LinearMap.inl K.O B₁.A B₂.A) := by
      ext ⟨a, b⟩
      simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
        Submodule.mem_comap, LinearMap.inl_apply]
      constructor
      · rintro ⟨hM, rfl⟩
        exact ⟨a, hM, rfl⟩
      · rintro ⟨c, hc, he⟩
        rw [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨hc, rfl⟩
    rw [this]
    exact f₁.map _
  · set S := Submodule.span K.E (M : Set (B₁.A × B₂.A)) with hS
    have hinl : ∀ a : B₁.A, ((a, 0) : B₁.A × B₂.A) ∈ S := by
      intro a
      have ha : a ∈ Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A) := by
        rw [s₁]; trivial
      have hle : (Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A)).map
          (LinearMap.inl K.E B₁.A B₂.A) ≤ S := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨c, hc, rfl⟩
        exact hc
      exact hle ⟨a, ha, rfl⟩
    have hsnd : S.map (LinearMap.snd K.E B₁.A B₂.A) = ⊤ := by
      rw [hS, Submodule.map_span, ← s₂]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd K.E B₁.A B₂.A) := by rw [hsnd]; trivial
    obtain ⟨y, hy, hyb⟩ := hb
    have : ((a, b) : B₁.A × B₂.A) = y + (a - y.1, 0) := by
      ext
      · simp
      · simp [← hyb]
    rw [this]
    exact S.add_mem hy (hinl _)

end GlobalTheory.UnitLemma
