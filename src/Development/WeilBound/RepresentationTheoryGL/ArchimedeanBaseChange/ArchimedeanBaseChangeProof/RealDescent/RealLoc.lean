module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped ComplexConjugate InnerProductSpace ContDiff

namespace PositivityTheory.RgBcC.Real

open PositivityTheory.RgTw (Mat G th IsThetaOp)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def IsLefK (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V) : Prop :=
  (∀ k, T * E.ρ k = E.ρ k * T) ∧ T * T = 1 ∧
    ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → (Function.Injective fun a => z a ^ 2) →
      LinearMap.trace ℂ E.V (E.ρ k : E.V →ₗ[ℂ] E.V) = (∏ a, ∏ b, (1 + z a / z b)) * conj (weylChar lam z) ^ 2 ∧
      LinearMap.trace ℂ E.V ((E.ρ k * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
        (∏ a, ∏ b, (1 + z a / z b)) * conj (weylChar lam fun a => z a ^ 2)

section

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U))

def uG (k : Matrix.unitaryGroup (Fin n) ℂ) : G n := Unitary.toUnits k


open Classical in
def piM (g : Mat n) : U →L[ℂ] U := if h : IsUnit g then π h.unit else 0

def IsInvT (E : KMod n) (t : (E.V →L[ℂ] ℂ) →L[ℂ] U) : Prop := ∀ k ξ, t (ξ ∘L E.ρ k⁻¹) = π (uG k) (t ξ)

def HasInf (χ : Inf n) : Prop :=
  ∀ S : Submodule ℂ U, FiniteDimensional ℂ S → (∀ k, ∀ v ∈ S, π (uG k) v ∈ S) → ∀ v ∈ S, ∀ w,
    ContDiffOn ℝ ∞ (fun g => ⟪w, piM π g v⟫_ℂ) (GLs n) ∧ IsEig χ fun g => ⟪w, piM π g v⟫_ℂ

end

end PositivityTheory.RgBcC.Real
