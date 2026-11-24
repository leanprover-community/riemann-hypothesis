module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def Hyp (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ) : Prop :=
  IsField A.K ∧ IsField A.L ∧ IsStdChar ψ ∧ SelfDual μ (A.kerL ψ x) ∧
    ∀ s : A.Kˣ, ((∃ y, A.NL y = s) → ω s = 1) ∧ ((¬ ∃ y, A.NL y = s) → ω s = -1)

def nOp (A : Et F E) (ψ : AddChar F ℂ) (x z : A.K) (φ : A.L → ℂ) : A.L → ℂ :=
  fun y => A.psiK ψ (z * x * A.NL y) * φ y

def mOp (A : Et F E) (ω : A.K → ℂ) (s : A.Kˣ) (φ : A.L → ℂ) : A.L → ℂ :=
  fun y => ω s * (A.absK s : ℂ) * φ ((s : A.K) • y)

def fOp (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (φ : A.L → ℂ) : A.L → ℂ :=
  fourB μ (A.kerL ψ x) φ

def gaussInt (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K) (S : Set A.L) : ℂ :=
  ∫ y in S, A.psiK ψ (u * x * A.NL y) ∂μ

def IsStableGauss (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K) (G : ℂ) : Prop :=
  ∃ Λ₀ : AddSubgroup A.L, IsOpen (Λ₀ : Set A.L) ∧ IsCompact (Λ₀ : Set A.L) ∧
    ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) → IsCompact (Λ : Set A.L) → Λ₀ ≤ Λ →
      gaussInt A ψ x μ u Λ = G

end GlobalTheory.JR.WeilQuad
