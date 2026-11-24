module

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
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Formalism.HermitianCurvature.BesselNonvanishingReduction

@[expose] public section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BpJoin

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData BranchingSupport

def Pst {n : ℕ} (lam : Fin n → ℝ) (c : ℝ) (y : ℝ) : ℝ := ∏ s, (|y + lam s| + c)

def GridNum (C b c : ℝ) (P : M.Par) (l : ℕ) (lam : Fin (2 * P.r + P.k + 1) → ℝ) : Prop :=
  1 ≤ c ∧ c + 2 ≤ b ∧ (P.k : ℝ) ≤ b ∧ |P.u l| ≤ b ∧ |P.u' l| ≤ b ∧ (∀ s, |lam s| ≤ b) ∧
  (∀ s t, s < t → lam t + 2 * c ≤ lam s) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u (s.val + 2) + 1 / 2 ≤ lam s)) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u' (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u' (s.val + 2) + 1 / 2 ≤ lam s)) ∧
  b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T ∧ b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T'

def StdNum (C b c : ℝ) (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) : Prop :=
  (∀ l ∈ Icc 1 P.k, GridNum C b c P l lam) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    lam s + 1 / 2 ≤ P.u (s.val + 1) ∧ P.u (s.val + 2) + 1 / 2 ≤ lam s ∧
    lam s + 1 / 2 ≤ P.u' (s.val + 1) ∧ P.u' (s.val + 2) + 1 / 2 ≤ lam s)

def Cases (P : M.Par) (n₀ : ℕ) : Prop :=
  (n₀ = 0 ∧ ∃ l ∈ Icc 1 P.k, ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u l - P.u' l|) ∨
  (n₀ = 30 * (P.r + 1) ^ 2 + 6 ∧ (∀ i ∈ Icc 1 P.k, P.u i = P.u' i) ∧
    ∃ l, 1 ≤ l ∧ l < P.k ∧ 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1))

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def EigDec {k r : ℕ} (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (mu : Fin (2 * r + k + 1) → ℝ) : Prop :=
  B.CkOn ⊤ (B.GV k r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧
    ∀ y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (y : ℂ) f g = ((∏ s, (y + mu s) : ℝ) : ℂ) • f g

end BpJoin
