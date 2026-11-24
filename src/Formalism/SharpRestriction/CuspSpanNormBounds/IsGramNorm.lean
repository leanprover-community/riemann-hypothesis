module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedMirrorLevelOperator
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

@[expose] public section

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.QuantumDeterminants Formalism.MainNotions.S.LevR

section Val

variable {k r : ℕ}

def wbEmb (k r : ℕ) (x : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun p =>
  if h : r ≤ p.val ∧ p.val ≤ r + k then x ⟨p.val - r, by omega⟩ else 0

def PtRepC (B : LocBessel k r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (B.c.re = 0 → IsPtRep B γ g) ∧ (B.c.re ≠ 0 → IsPtRepO B γ g)

def HasRep (B : LocBessel k r) (γ : Point ℂ (r + 1)) : Prop :=
  PtLastOk r (Tz k r B.z) (Tz k r B.z') γ ∧ ∃ g, PtRepC B γ g

def IsGramRef (B : LocBessel k r) (n n' : Fin (k + 1) → ℂ) (ι : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  herm (Hb k) n (wbPart k r B.z) = 0 ∧ herm (Hb k) n n = 1 ∧
  herm (Hb k) n' (wbPart k r B.z') = 0 ∧ herm (Hb k) n' n' = 1 ∧
  ∀ x y : Fin (k + 1) → ℂ, herm (Hb k) x (wbPart k r B.z') = 0 → herm (Hb k) x n' = 0 →
    herm (Hb k) y (wbPart k r B.z') = 0 → herm (Hb k) y n' = 0 →
    herm (Hb k) (ι *ᵥ x) (wbPart k r B.z) = 0 ∧ herm (Hb k) (ι *ᵥ x) n = 0 ∧
      herm (Hb k) (ι *ᵥ x) (ι *ᵥ y) = herm (Hb k) x y

def IsGramNorm (B : LocBessel k r)
    (n n' : Fin (k + 1) → ℂ) (ι : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∃ t : ℝ, 0 < t ∧ omG k r B.z B.z' g = ((t : ℂ) * Dmin k r B.z B.z' g (Fin.last (r + 1))) • n) ∧
  (∃ t : ℝ, 0 < t ∧ omG' k r B.z B.z' g = ((t : ℂ) * star (Dmin k r B.z B.z' g (Fin.last (r + 1)))) • n') ∧
  ∀ x : Fin (k + 1) → ℂ, herm (Hb k) x (wbPart k r B.z') = 0 → herm (Hb k) x n' = 0 →
    g *ᵥ wbEmb k r x = wbEmb k r (ι *ᵥ x)

end Val

structure ValMap (k r : ℕ) where

  V : ∀ (B : LocBessel k r),
    (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp)) → List (ℂ × ℕ) → (B.Wq →L[ℂ] B.Wp)

  rep : LocBessel k r → List (ℂ × ℕ) → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

  n : LocBessel k r → Fin (k + 1) → ℂ
  n' : LocBessel k r → Fin (k + 1) → ℂ
  ι : LocBessel k r → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ

  ref_ok : ∀ B : LocBessel k r, 0 < k → IsGramRef B (n B) (n' B) (ι B)

  rep_ok : ∀ (B : LocBessel k r) (γ : Point ℂ (r + 1)), HasRep B γ →
    PtRepC B γ (rep B γ.1) ∧ IsGramNorm B (n B) (n' B) (ι B) (rep B γ.1)

  val : ∀ (B : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp)) (γ : Point ℂ (r + 1))
    (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)),
    B.c ≠ 0 → (B.c.re = 0 ∨ B.c.im = 0) → SmoothOnH (Hpk k r) F → HasRep B γ →
    IsRootMeas B γ (rep B γ.1) μR → IsOrbQuot B (rep B γ.1) μR ν → V B F γ.1 = OrbInt B F (rep B γ.1) ν

  val0 : ∀ (B : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp)) (γ : Point ℂ (r + 1)),
    ¬ HasRep B γ → V B F γ.1 = 0

end Formalism.MainNotions.S
