module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.TfLoc

theorem sigmaGL_incl_fixed {k E : Type*} [Field k] [Field E] [Algebra k E] {n : ℕ}
    (σ : E ≃ₐ[k] E) (γ : GL (Fin n) k) :
    sigmaGL σ (incl γ : GL (Fin n) E) = incl γ := by
  apply Units.ext
  ext i j
  show σ (algebraMap k E ((γ : Matrix (Fin n) (Fin n) k) i j)) =
    algebraMap k E ((γ : Matrix (Fin n) (Fin n) k) i j)
  exact σ.commutes _

theorem commute_of_normGL_eq {k E : Type*} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] {n : ℕ} (σ : E ≃ₐ[k] E)
    (δ : GL (Fin n) E) (γ : GL (Fin n) k) (hN : normGL σ δ = incl γ) :
    Commute (δ : Matrix (Fin n) (Fin n) E) (incl γ : GL (Fin n) E) := by
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hθ δ
  have h' : sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ := h
  rw [hN, sigmaGL_incl_fixed] at h'
  have hc : δ * (incl γ : GL (Fin n) E) = incl γ * δ := by
    calc δ * (incl γ : GL (Fin n) E) = δ * (δ⁻¹ * incl γ * δ) := by rw [← h']
      _ = incl γ * δ := by group
  have := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) hc
  simpa [Commute, SemiconjBy] using this

theorem norm_commutes_of_separable : PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 := by
  intro hA1 k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ n δ γ hN hsep
  have hc := commute_of_normGL_eq σ δ γ hN
  exact ⟨hc, hA1 E n _ hsep _ hc⟩

end GlobalTheory.CompanionTheory.TfLoc
