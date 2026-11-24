module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt
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

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def hinv (T : Matrix (Fin n) (Fin n) ℂ) : E n := fun i j => (T i j).re + (T i j).im

def ip (y y' : E n) : ℝ := ∑ a, ∑ b, y a b * y' a b

def qX (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : E n := hinv (gramX ε x)

def detQ (ε : Fin m → Bool) : PX m n := (Matrix.of fun i j => Qp ε i j).det

def FP (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (y : E n) : ℂ :=
  ∫ x, evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x))

def AlgA : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool), (∀ (y : E n) (x : Fin m → Fin n → ℂ),
      (herm y * gramX ε x).trace = (ip y (qX ε x) : ℂ)) ∧
    (∀ x : Fin m → Fin n → ℂ, herm (qX ε x) = gramX ε x) ∧ (∀ y : E n, hinv (herm y) = y) ∧
    (∀ x : Fin m → Fin n → ℂ, evX (detQ ε) x = (gramX ε x).det) ∧ Continuous (qX (n := n) ε)

def IntG : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, Integrable (fun x => evX P x * gs c x)

def DerivF : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (P : PX m n) (N : ℕ),
    Continuous (FP ε c t P) ∧
    Delta^[N] (FP ε c t P) = FP ε c t ((MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε) ^ N * P)

def MollId : Prop :=
  ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure X) [SFinite μ] (Ψ : X → ℂ) (qq : X → E n), Integrable Ψ μ →
    Measurable qq → ∀ t : ℝ, t ≠ 0 →
    Integrable (fun y : E n => ∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) →
    ∀ ψ : E n → ℂ, Continuous ψ → HasCompactSupport ψ →
      ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ β, ψ β * (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * Complex.exp (-(Complex.I * t * ip β y)))

end PositivityTheory.Rg.Sw.WR.D
