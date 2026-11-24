module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionTensorPullbackRingHomBijective
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Set

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_const_addEquiv_of_range_eq : ∀ (n g : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Countable Λ] [AddCommGroup Λ'] [Countable Λ'] (B : Set (Fin n → ℂ)), IsOpen B → IsPreconnected B → B.Nonempty → ∀ (P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))) (P' : (Fin n → ℂ) → (Λ' →+ (Fin g → ℂ))), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → (∀ x, DifferentiableOn ℂ (fun b => P' b x) B) → (∀ b ∈ B, Function.Injective (P b) ∧ Function.Injective (P' b) ∧ (P b).range = (P' b).range) → ∃ T : Λ' ≃+ Λ, ∀ b ∈ B, ∀ x, P' b x = P b (T x) := by
  intro n g Λ Λ' _ _ _ _ B hB hc hne P P' hP hP' h
  have h1 : ∀ x : Λ', ∃ y : Λ, ∀ b ∈ B, P' b x = P b y := fun x =>
    exists_const_of_section_mem_range n g Λ B hB hc hne P (fun b => P' b x) hP (hP' x)
      (fun b hb => by rw [(h b hb).2.2]; exact ⟨x, rfl⟩)
  have h2 : ∀ y : Λ, ∃ x : Λ', ∀ b ∈ B, P b y = P' b x := fun y =>
    exists_const_of_section_mem_range n g Λ' B hB hc hne P' (fun b => P b y) hP' (hP y)
      (fun b hb => by rw [← (h b hb).2.2]; exact ⟨y, rfl⟩)
  choose f hf using h1
  choose k hk using h2
  obtain ⟨b₀, hb₀⟩ := hne
  obtain ⟨hi, hi', -⟩ := h b₀ hb₀
  refine ⟨{ toFun := f, invFun := k, left_inv := ?_, right_inv := ?_, map_add' := ?_ }, ?_⟩
  · intro x
    apply hi'
    rw [← hk _ b₀ hb₀, ← hf _ b₀ hb₀]
  · intro y
    apply hi
    rw [← hf _ b₀ hb₀, ← hk _ b₀ hb₀]
  · intro x x'
    apply hi
    rw [map_add (f := _), ← hf _ b₀ hb₀, ← hf _ b₀ hb₀, ← hf _ b₀ hb₀, map_add (f := _)]
  · intro b hb x
    exact hf x b hb

end GlobalTheory.CompanionTheory.Ar.Flat
