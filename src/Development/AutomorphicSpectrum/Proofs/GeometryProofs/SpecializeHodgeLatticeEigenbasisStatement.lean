module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenbasis
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.specialize_hodge_lattice_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g p q : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
    (x₁ : Fin p → Fin g → R') (x₂ : Fin q → Fin g → R') (hu : ∀ i, u i ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    IsAdapted ρH σ b₁ b₂ u → (∀ i, b₁ i = comb ℓ (x₁ i)) → (∀ i, b₂ i = comb ℓ (x₂ i)) →
    IsAdapted ρHC σC (fun i k => ψ (x₁ i k)) (fun i k => ψ (x₂ i k)) (fun i => ev ⟨u i, hu i⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isAdapted_eval | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isAdapted_eval | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isAdapted_eval <;> assumption)
