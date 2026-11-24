module

public import Formalism.QuotientMetricDivisors.Statement
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

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def plc (w : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)

def ramw (w : HeightOneSpectrum (𝓞 K)) : ℤ := vw w ((plc w : ℕ) : K)

def ellw (w : HeightOneSpectrum (𝓞 K)) : ℝ := (plc w : ℝ) / Real.sqrt (ramw w : ℝ)

end Defs

def RamBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)),
    (plc w).Prime ∧ 1 ≤ ramw w ∧ plc (conjPl w) = plc w ∧ ramw (conjPl w) = ramw w ∧
      2 / ellw w ^ 2 = (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)

def PlaceSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (X : ℕ → ℝ), (∀ p, 0 ≤ X p) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * X (plc w)) ≤ ∑ p ∈ S.image plc, Real.log (p : ℝ) * X p

def DepthCases : Prop :=
  ∀ (e ec F : ℝ),
    (∀ a : ℝ, e ≤ F + a + 1 → ec ≤ F + a + 1 → e + ec - 2 * F ≤ 2 * a + 2) ∧
    (e = 0 → ec = 0 → 0 ≤ F → e + ec - 2 * F ≤ 0) ∧
    (∀ s T β : ℝ, e ≤ s + T + 1 → ec ≤ s + T + 1 → -(2 * β) ≤ F → F ≤ 0 →
      e + ec - 2 * F ≤ 2 * (s + T + 1) + 4 * β) ∧
    (∀ s T : ℝ, e ≤ s + T + 1 → ec ≤ s + T + 1 → F = 0 → e + ec - 2 * F ≤ 2 * s + 2 * T + 2) ∧
    (∀ T nn nnc g2 : ℝ, e ≤ 2 * T - nn → ec ≤ 2 * T - nnc → nn + nnc = -(2 * F) →
      e + ec - 2 * F + 2 * g2 ≤ 4 * T + 2 * g2)

def ShareNum : Prop :=
  ∀ (dK d0 d U δq ep y del : ℝ), 0 < U → 0 < δq → 0 ≤ dK → 0 ≤ d0 → 0 ≤ ep → ep ≤ y → y ≤ 1 / 8 →
    0 ≤ del → del ≤ 1 / 4 → (1 - ep) * dK ≤ U * d0 → (1 - y) * U ≤ δq → (1 - del) * d0 ≤ d →
      dK / δq ≤ 2 * d

def UnipNum : Prop :=
  ∀ (f r d dK δq : ℝ), 0 ≤ f → 1 ≤ r → 0 ≤ d → dK / δq ≤ 3 * d →
    f * r * (r - 1) / 2 * (d + dK / δq) ≤ 2 * f * r ^ 2 * d

def BudgetNum : Prop :=
  ∀ (dK δq D B : ℝ), 0 < δq → 0 < D → 0 ≤ B → dK / δq ≤ 3 * D →
    2 * (2 * (dK * B)) / (δq * D) ≤ 12 * B

def errGood (Y X2 A1 A2 kw T : ℝ) (th add : ℕ → ℝ) (p : ℕ) : ℝ :=
  if (p : ℝ) ≤ Y then
    2 * (A1 / (p : ℝ) + kw * th p + T * add p + (if X2 < (p : ℝ) then A2 / (p : ℝ) ^ 2 else 0)) + 2
  else 0

end Formalism.EigenvalueLevelCeiling
