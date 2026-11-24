module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

variable {m n : ℕ}

def ptsOver (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : Set (EuclideanSpace ℂ (Fin n)) :=
  {y | y ∈ S ∧ linProj π y = w}

def cntOver (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : ℝ≥0∞ :=
  (((ptsOver S π w).encard : ℕ∞) : ℝ≥0∞)

def IsScaleStable (S : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∀ y ∈ S, ∀ t : ℂ, t ≠ 0 → t • y ∈ S

def gaussM (m n : ℕ) : Measure (Fin m → Fin n → ℂ) :=
  (volume : Measure (Fin m → Fin n → ℂ)).withDensity matGauss

def planeMass (n e : ℕ) : ℝ≥0∞ :=
  Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
    {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}

def fibrePts {e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  ptsOver S π (firstCoordVec (e + 1))

def fsSum {e : ℕ} (h : HermNorm n) (u : Fin n → ℂ) (S : Set (EuclideanSpace ℂ (Fin n)))
    (π : Fin (e + 1) → Fin n → ℂ) : ℝ :=
  ∑ᶠ y ∈ fibrePts S π, fsLog h u (h.pointOf y)

def coefRows {e : ℕ} (h : HermNorm n) (π : Fin (e + 1) → Fin n → ℂ) : Fin e × Fin n → ℂ :=
  fun ij => ((h.mat)⁻¹ *ᵥ π ij.1.succ) ij.2


open Classical in
def logGap (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) : ℝ≥0∞ :=
  if y = 0 then 0
  else if ∑ j, u j * h.pointOf y j = 0 then ⊤
  else ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y))

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
