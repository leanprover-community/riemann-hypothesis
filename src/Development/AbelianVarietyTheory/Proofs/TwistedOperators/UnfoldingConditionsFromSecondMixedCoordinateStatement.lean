module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsFromSecondMixedCoordinate
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

namespace I195MixedCoordinates_5f138841817cdbc027192222

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_5f138841817cdbc027192222

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.unfolding_conditions_from_second_mixedCoordinate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vT : VolM D σ V₀.rank) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ), p.Is dV dW x ψ → ∀ (β₂ : Mx D V₀.rank σ → ℂ) (g : WO V₀ W₀ → ℂ) (g' : WO V₀ W → ℂ), VacG ψ V₀ W₀ p.Γ₀ g → IsThetaFunO ψ V₀ W g' → (∀ y', (_root_.I195MixedCoordinates_5f138841817cdbc027192222.target dW) V₀ ψ vT.μ vT.𝓕 g' y' = β₂ y' • g) → (∀ η ∈ p.B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β₂ (z + b) = β₂ z) → (∀ z, β₂ z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ p.B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η) → (∀ ξ ∈ p.B₁, heisO ψ V₀ W (dW.incX V₀ ξ) g' = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • g') ∧ (∀ η ∈ p.B₂, heisO ψ V₀ W (dW.incY V₀ η) g' = g') ∧ IsLatVac (heisO ψ V₀ W) (p.Γ₀.map (dW.inc0 V₀)) g' := by
  first | exact @GlobalTheory.MixCondT.main | exact GlobalTheory.MixCondT.main | (intros; apply GlobalTheory.MixCondT.main <;> assumption)
