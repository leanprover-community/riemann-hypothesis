module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAdaptedAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

section Lin

variable {a b : ℕ}

end Lin

section GS

end GS

section Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Emb

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)


theorem exists_adapted_at (hF : R.form = F.form) (hS : R.HasSig F.σ j j') (τ : Ψ) :
    ∃ A : Matrix (Fin (j + j')) (Sg j j') ℂ, Aᴴ * C.sgr τ * A = sgI j j' ∧
      (∀ v : Fin j → ℂ, C.pPart R τ (A *ᵥ Sum.elim v 0) = 0) ∧
      (∀ v : Fin j' → ℂ, C.pBar R τ (A *ᵥ Sum.elim 0 v) = 0) :=
  by apply _root_.UpperTheory.Reformulated.B.Gwb8.exists_adapted_at <;> assumption

end Lat

theorem exists_isAdapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F)
    (R : RiemLat E g Λ), R.form = F.form → R.HasSig F.σ j j' → ∃ A, C.IsAdapted R A := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R hF hS
  choose A h1 h2 h3 using exists_adapted_at C R hF hS
  exact ⟨A, ⟨h1, h2, h3⟩⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted
