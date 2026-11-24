module

public import Formalism.PeriodIntegrals.FockDegreeTwoParts
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

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW

def Harm2 {p q r s : ℕ} (P : Pol p q r s) : Prop :=
  ∀ Z : Mat r s, IsPC Z → minusPart (fockAct2 p q r s Z) P = 0

def FirstHalf : Prop := ∀ p q r s : ℕ,
  ∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
    (∀ Z : Mat r s, IsPC Z → minusPart ((fockAct2 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d

def SecondHalf : Prop := ∀ p q r s : ℕ,
  ∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
    (∀ Z : Mat p q, IsPC Z → minusPart ((fockAct1 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d

theorem oneDeg_of_halves (h1 : FirstHalf) (h2 : SecondHalf) : PI.FockDegreeTwoParts.OneDeg :=
  fun p q r s => ⟨h1 p q r s, h2 p q r s⟩

def posOp {p q r s : ℕ} (a b : Ix p q) : Module.End ℂ (Pol p q r s) :=
  ∑ c : Ix r s, if linePos ((a, c) : Ln p q r s) = true then
    LinearMap.mulLeft ℂ (X ((a, c) : Ln p q r s)) ∘ₗ (pderiv ((b, c) : Ln p q r s)).toLinearMap
  else 0

def negOp {p q r s : ℕ} (a b : Ix p q) : Module.End ℂ (Pol p q r s) :=
  ∑ c : Ix r s, if linePos ((a, c) : Ln p q r s) = true then 0
  else LinearMap.mulLeft ℂ (X ((a, c) : Ln p q r s)) ∘ₗ (pderiv ((b, c) : Ln p q r s)).toLinearMap

def kShift (r s : ℕ) {p q : ℕ} : Ix p q → ℚ
  | .inl _ => cPair r s
  | .inr _ => -cPair r s

def lowOp {p q r s : ℕ} (c d : Ix r s) : Module.End ℂ (Pol p q r s) :=
  ∑ a : Ix p q, if linePos ((a, d) : Ln p q r s) = true then
    (pderiv ((a, c) : Ln p q r s)).toLinearMap ∘ₗ (pderiv ((a, d) : Ln p q r s)).toLinearMap
  else 0

def InnerFacts : Prop := ∀ (σ : Type) (P Q Q' : MvPolynomial σ ℂ) (c : ℂ),
  fockInner P (Q + Q') = fockInner P Q + fockInner P Q' ∧
  fockInner P (c • Q) = c * fockInner P Q ∧
  fockInner Q P = starRingEnd ℂ (fockInner P Q) ∧
  ((fockInner P P).im = 0 ∧ 0 ≤ (fockInner P P).re) ∧
  (fockInner P P = 0 → P = 0) ∧
  ∀ l : σ, fockInner (X l * P) Q = fockInner P (pderiv l Q)

def OpsK : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b →
  fockAct1 p q r s (Eab a b) =
    posOp a b - negOp b a +
      (if a = b then (((kShift r s a : ℚ) : ℂ) • (1 : Module.End ℂ (Pol p q r s))) else 0)

def HarmIff : Prop := ∀ p q r s : ℕ, ∀ P : Pol p q r s,
  Harm2 P ↔ ∀ c d : Ix r s, ¬ sameBlock c d → lowOp (p := p) (q := q) c d P = 0

def HwHarmDeg : Prop := ∀ p q r s : ℕ, ∀ (μ : Ix p q → ℚ) (e : ℕ) (v : Pol p q r s),
  v ∈ homog (Ix p q × Ix r s) e → IsHW (fockAct1 p q r s) μ v → Harm2 v →
    (e : ℚ) = degW (cPair r s) μ

def Reduction : Prop := HwHarmDeg → FirstHalf

def Swap : Prop := FirstHalf → SecondHalf

theorem oneDeg_of (hT : HwHarmDeg) (hR : Reduction) (hS : Swap) : PI.FockDegreeTwoParts.OneDeg :=
  oneDeg_of_halves (hR hT) (hS (hR hT))

end PI.FockOneDegW
