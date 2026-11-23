module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeExtendScalars
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.hodge_lattice_extend_scalars : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs)) (bar : 𝓞 E ≃+* 𝓞 E)
    (R R' : Subring Ω) (hR : R ≤ R') (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HLx : Submodule R (Vs × Module.Dual Ω Vs)) (HLy : Submodule R' (Vs × Module.Dual Ω Vs))
    (C A : Type) [Field C] [CommRing A] [Algebra A C] (ψ : R' →+* C),
    (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) →
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    HodgeAt ρH HLx ℓ t → HodgeAt ρH HLy ℓ t →
    (∀ r : R, ψ ⟨r, hR r.2⟩ ∈ (algebraMap A C).range) →
    ∃ (ρC : 𝓞 E →+* Module.End C (Fin g → C))
      (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
      (ev : HLy →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
      (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C))),
      (∀ a y, (ρHC a y).1 = ρC a y.1) ∧ (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) ∧
      Tied ℓ ψ ρ ρC ∧ IsEval ℓ ψ ρH ρHC HLy ev ∧
      HV.map ((LinearMap.fst C (Fin g → C) (Module.Dual C (Fin g → C))).restrictScalars A) = stdLat A C g ∧
      (∀ f : Module.Dual C (Fin g → C), ((0 : Fin g → C), f) ∈ HV ↔
        ∀ e ∈ stdLat A C g, f e ∈ (algebraMap A C).range) ∧
      ∀ ht : ∀ i, t i ∈ HLy, HT.IsFreeOn ρHC HV (fun i => ev ⟨t i, ht i⟩) := by
  exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists.exists_eval
