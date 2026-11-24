module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open UpperTheory.Gal.LocalSmoothExtension

open scoped Classical in
private lemma hexp_finite {F : Type} [Field F] [NumberField F] {n : ℕ} (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ)
    (lam : (F →+* ℂ) → Fin n → ℕ) : {h : Fin n → ℕ | IsHExp t₀ ε lam h}.Finite := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Set.toFinite _
  · let i₀ : Fin n := ⟨0, hn⟩
    let c : ℕ := ∑ τ ∈ (Finset.univ.erase t₀).erase (NumberField.ComplexEmbedding.conjugate t₀),
      ε τ * ∑ j, lam τ j
    let h₁ : Fin n → ℕ := fun i => ((n - 1) * lam (NumberField.ComplexEmbedding.conjugate t₀) i₀ + c) +
      (lam t₀ i + (n - 1 - (i : ℕ)))
    let h₂ : Fin n → ℕ := fun i => (lam t₀ i₀ + c) +
      (∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j + (i : ℕ))
    refine (Set.toFinite ({h₁, h₂} : Set (Fin n → ℕ))).subset ?_
    rintro h (⟨m, hm, hh⟩ | ⟨m, hm, hh⟩)
    · left
      funext i
      rw [hh i, ← hm i₀]
    · right
      funext i
      rw [hh i, ← hm i₀]

theorem UpperTheory.Gal.LocalSmoothExtension.unifBound_of :
    UnifBound := by
  intro F _ _ n I _ t ε lam κ
  have hb : ∀ (π : (F →+* ℂ) → (F →+* ℂ)) (i : I), ∃ b, ∀ h : Fin n → ℕ,
      IsHExp (t i) ε (fun τ => lam (π τ)) h → κ (fun τ => lam (π τ)) i h ≤ b := by
    intro π i
    obtain ⟨b, hb⟩ := ((hexp_finite (t i) ε (fun τ => lam (π τ))).image
      (κ (fun τ => lam (π τ)) i)).bddAbove
    exact ⟨b, fun h hh => hb ⟨h, hh, rfl⟩⟩
  choose b hb using hb
  obtain ⟨k, hk⟩ := Finite.exists_le (fun q : ((F →+* ℂ) → (F →+* ℂ)) × I => b q.1 q.2)
  refine ⟨k, fun σ i h hh => ?_⟩
  exact (hb (fun τ => (σ.symm : ℂ →+* ℂ).comp τ) i h hh).trans
    (hk ((fun τ => (σ.symm : ℂ →+* ℂ).comp τ), i))
