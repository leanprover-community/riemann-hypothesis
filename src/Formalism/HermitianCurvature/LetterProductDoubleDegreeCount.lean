module

public import Formalism.HermitianCurvature.StatementLE
public import Formalism.HermitianCurvature.StatementQ
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

namespace Formalism.FourierDecayAlt.C7

open Finset Matrix

open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

def LamInterlaces (k r : ℕ) (u : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ i : Fin (k + 2 * r + 1),
    (i.val + 1 ≤ k → lam i < u (i.val + 1)) ∧ (i.val + 2 ≤ k → u (i.val + 2) < lam i)

def Between (u u' : ℕ → ℝ) (l : ℕ) (Y : ℝ) : Prop :=
  min (u l) (u' l) < -Y ∧ -Y < max (u l) (u' l)

def LamSide : Prop :=
  ∀ (k r : ℕ) (u u' : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k →
    LamInterlaces k r u lam → LamInterlaces k r u' lam → Between u u' l Y →
    ∀ i : Fin (k + 2 * r + 1), (l ≤ i.val + 1 → lam i < min (u l) (u' l)) ∧
      (i.val + 1 < l → max (u l) (u' l) < lam i)

def RhoSide : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k → I.Interlaces k u u' ρ → Between u u' l Y →
    ∀ i ∈ Icc 1 (k - 1), (l ≤ i → ρ i < -Y) ∧ (i < l → -Y < ρ i)

def PSign : Prop :=
  ∀ (k r : ℕ) (u u' ρ : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k →
    LamInterlaces k r u lam → LamInterlaces k r u' lam → I.Interlaces k u u' ρ → Between u u' l Y →
    0 < (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s) ∧ 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ Y ∧
      |∏ s, (Y + lam s)| = (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s)

def principalHermitianLattice {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  B.beta D (w.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F) F

def RootsOutJoint : Prop :=
  ∀ (S : LE.Sys) (u u' : ℕ → ℝ) (l : ℕ), 1 ≤ l → l ≤ S.k →
    LamInterlaces S.k S.r u S.lam → LamInterlaces S.k S.r u' S.lam →
    (∀ Y ∈ Set.Icc S.α S.β, Between u u' l Y) → S.RootsOut

end

end Formalism.FourierDecayAlt.C7
