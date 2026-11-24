module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_emb_through_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : Nat.Primes)
    (κ : c.F →+* ℂ_[p]) (s : E →+* ℂ_[p]), ∃ τ : E →+* ℂ, s = κ.comp (inE c τ) := by
  intro E _ _ _ H l c p κ s
  haveI : CharZero ℂ_[p] := charZero_of_injective_ringHom κ.injective
  have hinj : Function.Injective (fun τ : E →+* ℂ => κ.comp (inE c τ)) := by
    intro τ τ' h
    ext a
    have h1 : κ (inE c τ a) = κ (inE c τ' a) := RingHom.congr_fun h a
    have h2 := κ.injective h1
    exact congrArg (fun x : c.F => (x : ℂ)) h2
  have hle : Nat.card (E →+* ℂ_[p]) ≤ Nat.card (E →+* ℂ) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, NumberField.Embeddings.card E ℂ,
      NumberField.Embeddings.card E ℂ_[p]]
  haveI : Finite (E →+* ℂ_[p]) := inferInstance
  obtain ⟨τ, hτ⟩ := (hinj.bijective_of_nat_card_le hle).2 s
  exact ⟨τ, hτ.symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
