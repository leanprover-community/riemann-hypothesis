module

public import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
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

open MvPolynomial

namespace FockRL

def FockLinL : Prop := ∀ (σ : Type) (c : ℂ) (P₁ P₂ Q : MvPolynomial σ ℂ),
  FockH1Action.fockInner (c • P₁ + P₂) Q = (starRingEnd ℂ) c * FockH1Action.fockInner P₁ Q + FockH1Action.fockInner P₂ Q

def FockLinR : Prop := ∀ (σ : Type) (c : ℂ) (P Q₁ Q₂ : MvPolynomial σ ℂ),
  FockH1Action.fockInner P (c • Q₁ + Q₂) = c * FockH1Action.fockInner P Q₁ + FockH1Action.fockInner P Q₂

def FockXAdj : Prop := ∀ (σ : Type) (l : σ) (P Q : MvPolynomial σ ℂ),
  FockH1Action.fockInner (X l * P) Q = FockH1Action.fockInner P (pderiv l Q)

def PMSplit : Prop := ∀ (σ : Type) (R L : Module.End ℂ (MvPolynomial σ ℂ)),
  (∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ FockH1Action.homog σ d → R P ∈ FockH1Action.homog σ (d + 2)) →
  (∀ (e : ℕ) (P : MvPolynomial σ ℂ),
    homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P)) →
  ∀ P : MvPolynomial σ ℂ, FockH1Action.plusPart (R + L) P = R P ∧ FockH1Action.minusPart (R + L) P = L P

def SameSign {p q r s : ℕ} (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) : Prop :=
  ∀ l l', M l l' ≠ 0 → FockH1Action.linePos l = FockH1Action.linePos l'

def OppSign {p q r s : ℕ} (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) : Prop :=
  ∀ l l', M l l' ≠ 0 → FockH1Action.linePos l ≠ FockH1Action.linePos l'

def AdjPair {p q r s : ℕ} (M M' : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) : Prop :=
  ∀ l l', FockH1Action.linePos l = true → FockH1Action.linePos l' = false → M' l' l = (starRingEnd ℂ) (M l l')

def KCStep : Prop := ∀ (p q r s : ℕ) (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ),
  SameSign M → ∀ (d : ℕ), ∀ P ∈ FockH1Action.homog (FockH1Action.Ln p q r s) d,
    FockH1Action.omAct p q r s M P ∈ FockH1Action.homog (FockH1Action.Ln p q r s) d

def PCStep : Prop := ∀ (p q r s : ℕ) (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ),
  OppSign M → ∀ P : FockH1Action.Pol p q r s,
    FockH1Action.omAct p q r s M P =
      FockH1Action.plusPart (FockH1Action.omAct p q r s M) P + FockH1Action.minusPart (FockH1Action.omAct p q r s M) P

def AdjStep : Prop := ∀ (p q r s : ℕ) (M M' : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ),
  OppSign M → OppSign M' → AdjPair M M' → ∀ P Q : FockH1Action.Pol p q r s,
    FockH1Action.fockInner (FockH1Action.plusPart (FockH1Action.omAct p q r s M) P) Q =
      - FockH1Action.fockInner P (FockH1Action.minusPart (FockH1Action.omAct p q r s M') Q)

def MatStep : Prop := ∀ (p q r s : ℕ),
  (∀ Z : FockH1Action.Mat p q, FockH1Action.fockAct1 p q r s Z =
      FockH1Action.omAct p q r s (Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s))) ∧
  (∀ Z : FockH1Action.Mat r s, FockH1Action.fockAct2 p q r s Z =
      FockH1Action.omAct p q r s (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z)) ∧
  (∀ Z : FockH1Action.Mat p q, FockH1Action.IsKC Z →
      SameSign (Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s))) ∧
  (∀ Z : FockH1Action.Mat r s, FockH1Action.IsKC Z →
      SameSign (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z)) ∧
  (∀ Z : FockH1Action.Mat p q, FockH1Action.IsPC Z →
      OppSign (Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s))) ∧
  (∀ Z : FockH1Action.Mat r s, FockH1Action.IsPC Z →
      OppSign (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z)) ∧
  (∀ Z : FockH1Action.Mat p q, FockH1Action.IsPC Z → FockH1Action.IsPC (FockH1Action.conjR Z)) ∧
  (∀ Z : FockH1Action.Mat r s, FockH1Action.IsPC Z → FockH1Action.IsPC (FockH1Action.conjR Z)) ∧
  (∀ Z : FockH1Action.Mat p q,
      AdjPair (Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s))
        (Matrix.kroneckerMap (fun x y : ℂ => x * y) (FockH1Action.conjR Z) (1 : FockH1Action.Mat r s))) ∧
  (∀ Z : FockH1Action.Mat r s,
      AdjPair (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z)
        (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) (FockH1Action.conjR Z)))

end FockRL
