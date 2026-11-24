module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
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

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

structure GroupDict (F : UnivFam (E := E) Ψ j j' n g Λ) where

  h : HermitianForm (maximalRealSubfield E) E (Fin (j + j') → E)

  e : Λ →+ (Fin (j + j') → E)
  e_inj : Function.Injective e
  e_smul : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x

  Dn : ℕ
  integral : IsDIntegral h Dn e.range
  orth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0

  M : Majorant h (Pi.basisFun E (Fin (j + j')))

  κ : ℝ
  κ_pos : 0 < κ

  π : archUnitary h (Pi.basisFun E (Fin (j + j'))) → Fin n → ℂ
  π_cont : Continuous π
  π_range : Set.range π = ballDom F.q
  π_fibre : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ M.stab
  len : ∀ a x, (F.R (π a)).normSq x = κ * M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (e x))) ^ 2

  α : latticeStab h e.range ≃* autGrp (E := E) F.form
  α_eq : ∀ γ x, e ((α γ).1 x) = ((γ : h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (e x)
  α_act : ∀ (γ : latticeStab h e.range) a,
    (F.R (π a)).EqvBy (F.R (π (archEmbed h (Pi.basisFun E (Fin (j + j'))) γ * a))) (α γ).1
  act : ∀ a₀, ∃ (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ A (ballDom F.q) ∧
    DifferentiableOn ℂ G (ballDom F.q) ∧ (∀ a, π (a₀ * a) = A (π a)) ∧
    ∀ t ∈ ballDom F.q, ballPot F.q (A t) = ballPot F.q t + (G t).re

end GlobalTheory.CompanionTheory.Ar.Cusp
