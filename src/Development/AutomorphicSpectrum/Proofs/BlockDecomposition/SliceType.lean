module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.SliceTypePf

theorem restrict_left {A B : Type} [One B] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : A => f (k, 1)) ∈ W₁ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, h₁, w₂, -, rfl⟩ := h
    have : (fun k : A => w₁ k * w₂ 1) = w₂ 1 • w₁ := by
      funext k
      simp [mul_comm]
    simpa [this] using W₁.smul_mem _ h₁
  | zero => exact W₁.zero_mem
  | add f g _ _ hf hg => exact W₁.add_mem hf hg
  | smul c f _ hf => exact W₁.smul_mem c hf

theorem restrict_right {A B : Type} [One A] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : B => f (1, k)) ∈ W₂ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, -, w₂, h₂, rfl⟩ := h
    have : (fun k : B => w₁ 1 * w₂ k) = w₁ 1 • w₂ := by
      funext k
      simp
    simpa [this] using W₂.smul_mem _ h₂
  | zero => exact W₂.zero_mem
  | add f g _ _ hf hg => exact W₂.add_mem hf hg
  | smul c f _ hf => exact W₂.smul_mem c hf

theorem main : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  intro E _ _ _ a b K₁ K₂ W₁ W₂ F hF
  obtain ⟨hl, hk⟩ := hF
  refine ⟨?_, ?_⟩
  · rintro φ m₂ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl u hu 1 K₂.one_mem (g, m₂)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_left W₁ W₂ _ (hk (g, m₂))
      simpa [hφ, Prod.mk_mul_mk] using this
  · rintro φ m₁ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl 1 K₁.one_mem u hu (m₁, g)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_right W₁ W₂ _ (hk (m₁, g))
      simpa [hφ, Prod.mk_mul_mk] using this

end GlobalTheory.CompanionTheory.EGlue.SliceTypePf

end
