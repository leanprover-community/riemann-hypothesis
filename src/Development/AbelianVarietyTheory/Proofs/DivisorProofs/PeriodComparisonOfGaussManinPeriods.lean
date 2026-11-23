module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem periodComparison_of_gaussManinPeriods (h : GlobalTheory.Published.GaussManinPeriods) : GlobalTheory.Published.PeriodComparison := by
  obtain ⟨ε, h⟩ := h
  refine ⟨ε, fun A _ g hA hs L hL u ↦ ?_⟩
  have hp : IsGrpPullback A A (spMap ((AlgHom.id ℂ ℂ : ℂ →ₐ[ℂ] ℂ) : ℂ →+* ℂ)) (𝟙 _) :=
    haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
    (isGrpPullback_of_iso (Iso.refl A)).congr (Cris.spMap_id ℂ).symm rfl
  obtain ⟨V, u', τ, Q', Q, -, -, -, hQ, -⟩ := h ℂ A g hA hs Empty Set.univ (fun _ ↦ AlgHom.id ℂ ℂ)
    isOpen_univ trivial (fun _ ↦ differentiableOn_const _) (fun _ ↦ A) (fun _ ↦ 𝟙 _) (fun _ ↦ hp)
    (fun _ ↦ GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) (by simp) hp) (fun _ ↦ L) (fun _ ↦ hL)
    A (𝟙 _) hp L hL u
  exact ⟨Q, hQ⟩

end GlobalTheory.PeriodFamily
