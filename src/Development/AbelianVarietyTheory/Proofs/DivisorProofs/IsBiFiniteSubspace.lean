module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

private lemma span_add_le {H : Type} [Group H] (K : Subgroup H) (f f' : H → ℂ) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (f + f') (k * g * k')} ≤
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f (k * g * k')} ⊔
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f' (k * g * k')} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  refine Submodule.mem_sup.2 ⟨_, Submodule.subset_span ⟨k, hk, k', hk', rfl⟩, _,
    Submodule.subset_span ⟨k, hk, k', hk', rfl⟩, ?_⟩
  funext g; simp

private lemma span_smul_le {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (f : H → ℂ) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (c • f) (k * g * k')} ≤
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f (k * g * k')} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  have : (fun g => (c • f) (k * g * k')) = c • fun g => f (k * g * k') := by funext g; simp
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, hk, k', hk', rfl⟩)

private lemma span_zero_le {H : Type} [Group H] (K : Subgroup H) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (0 : H → ℂ) (k * g * k')} ≤ ⊥ := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_bot]
  rfl

theorem isBiFinite_subspace : ∀ (H : Type) [Group H] (K : Subgroup H), IsBiFinite K (0 : H → ℂ) ∧
    (∀ f f' : H → ℂ, IsBiFinite K f → IsBiFinite K f' → IsBiFinite K (f + f')) ∧
    ∀ (c : ℂ) (f : H → ℂ), IsBiFinite K f → IsBiFinite K (c • f) := by
  intro H _ K
  refine ⟨?_, fun f f' hf hf' => ?_, fun c f hf => ?_⟩
  · unfold IsBiFinite
    exact Submodule.finiteDimensional_of_le (span_zero_le K)
  · unfold IsBiFinite at *
    exact Submodule.finiteDimensional_of_le (span_add_le K f f')
  · unfold IsBiFinite at *
    exact Submodule.finiteDimensional_of_le (span_smul_le K c f)

end GlobalTheory
