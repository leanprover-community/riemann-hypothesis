module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace UpperTheory.RealTr

open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

abbrev UK (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

section U

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U))

def coef (w v : U) : Mat n → ℂ := fun g => ⟪w, piM π g v⟫_ℂ

def IsOpK [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (B : ((E.V →L[ℂ] ℂ) →L[ℂ] U) →ₗ[ℂ] ((E.V →L[ℂ] ℂ) →L[ℂ] U)) : Prop :=
  ∀ t ξ, B t ξ = ∫ y : G n, π y (t (ξ ∘L k y.val)) ∂μ

end U

def KerReg (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  Continuous (fun y : G n => k y.val) ∧ HasCompactSupport (fun y : G n => k y.val) ∧
    ∀ y ∈ GLs n, ∀ k₁ k₂ : UK n, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂

section Alg

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def e1 (D : Mat n →ₗ[ℝ] Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D (Matrix.single a b 1) - Complex.I • D (Matrix.single a b Complex.I))

def e2 (D : Mat n →ₗ[ℝ] Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  -((1 / 2 : ℂ) • (D (Matrix.single b a 1) + Complex.I • D (Matrix.single b a Complex.I)))

end Alg

end UpperTheory.RealTr
