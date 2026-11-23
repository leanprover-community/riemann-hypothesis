module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPeriodsIsTameThetaFunctional
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.thetaLift_periods_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (G : GA D W → ℂ), RapidDec W G → (∀ (ρ : ℕ) (B : BesL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om B.V W), IsWeilDatumO ψ B.V W χ χ' om → ∀ φ, RapidDec B.A φ → Tame ψ B.V W fun Φ => B.per ψ φ (liftS om vW.μ vW.𝓕 G Φ)) ∧ ∀ (ρ : ℕ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om J.W W), IsWeilDatumO ψ J.W W χ χ' om → ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (χ₁ χ₂ : (AE D)ˣ →* Circle) (omz : Om J.W₀ L'), IsWeilDatumO ψ J.W₀ L' χ₁ χ₂ omz → ∀ φ Φ₀, RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ L' Φ₀ → Tame ψ J.W W fun Φ => J.per ψ ζ' omz φ (liftS om vW.μ vW.𝓕 G Φ) Φ₀ := by
  first | exact @GlobalTheory.LiftTame.lift_periods_tame | exact GlobalTheory.LiftTame.lift_periods_tame | (intros; apply GlobalTheory.LiftTame.lift_periods_tame <;> assumption)
