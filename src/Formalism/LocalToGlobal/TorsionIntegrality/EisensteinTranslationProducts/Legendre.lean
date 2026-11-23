module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def ZetaSummable : Prop :=
  ∀ (L : PeriodPair) (z : ℂ),
    Summable (fun l : L.lattice => 1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)

def ZetaHasDeriv : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → HasDerivAt (wZeta L) (-(L.weierstrassP z)) z

def ZetaOdd : Prop := ∀ (L : PeriodPair) (z : ℂ), wZeta L (-z) = -wZeta L z

def ZetaQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice → z ∉ L.lattice → wZeta L (z + ω) = wZeta L z + wEta L ω

def SigmaSummable : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), Summable (fun l : L.lattice => ‖wFactor (l : ℂ) z - 1‖)

def SigmaProdLU : Prop :=
  ∀ L : PeriodPair, HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z)
    (fun z => ∏' l : L.lattice, wFactor (l : ℂ) z) Set.univ

def SigmaEntire : Prop := ∀ L : PeriodPair, Differentiable ℂ (wSigma L)

def SigmaOdd : Prop := ∀ (L : PeriodPair) (z : ℂ), wSigma L (-z) = -wSigma L z

def SigmaZero : Prop := ∀ (L : PeriodPair) (z : ℂ), wSigma L z = 0 ↔ z ∈ L.lattice

def SigmaSimple : Prop :=
  ∀ L : PeriodPair, deriv (wSigma L) 0 = 1 ∧ ∀ z ∈ L.lattice, deriv (wSigma L) z ≠ 0

def SigmaLogDeriv : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → HasDerivAt (wSigma L) (wZeta L z * wSigma L z) z

def SigmaQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice →
    wSigma L (z + ω) = semiChar L ω * Complex.exp (wEta L ω * (z + ω / 2)) * wSigma L z

def EtaEisenstein : Prop :=
  ∀ L : PeriodPair,
    wEta L L.ω₁ = L.ω₁ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 ∧
    wEta L L.ω₂ = L.ω₂ * ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2

def Legendre : Prop :=
  ∀ L : PeriodPair,
    wEta L L.ω₁ * L.ω₂ - wEta L L.ω₂ * L.ω₁
      = (if 0 < (L.ω₂ / L.ω₁).im then 1 else -1) * (2 * (Real.pi : ℂ) * Complex.I)

end Formalism.L2.Th1.F
