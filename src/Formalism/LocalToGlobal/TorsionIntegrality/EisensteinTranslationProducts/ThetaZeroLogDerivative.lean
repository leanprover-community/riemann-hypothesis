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

def altE (L : PeriodPair) (x y : ℂ) : ℝ := (herm L x y).im

def AreaPos : Prop := ∀ L : PeriodPair, 0 < area L

def EtaSplit : Prop :=
  ∀ (L : PeriodPair) (x : ℂ), wEta L x = s2 L * x + ((Real.pi : ℂ) / (area L : ℂ)) * conj x

def AltEInt : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ), x ∈ L.lattice → y ∈ L.lattice → ∃ k : ℤ, altE L x y = k

def AltEBasis : Prop :=
  ∀ L : PeriodPair, altE L L.ω₁ L.ω₂ = if 0 < (L.ω₂ / L.ω₁).im then -1 else 1

def SemiCharMul : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ), x ∈ L.lattice → y ∈ L.lattice →
    semiChar L (x + y)
      = semiChar L x * semiChar L y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L x y : ℂ))

def SgStarQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice →
    sgStar L (z + ω) = semiChar L ω
      * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * sgStar L z

def SgStarFixed : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice → semiChar L ω * opU L ω (sgStar L) z = sgStar L z

def SgStarBasic : Prop :=
  ∀ L : PeriodPair, Differentiable ℂ (sgStar L) ∧ (∀ z, sgStar L (-z) = -sgStar L z) ∧
    (∀ z, sgStar L z = 0 ↔ z ∈ L.lattice) ∧
    deriv (sgStar L) 0 = 1 ∧ iteratedDeriv 3 (sgStar L) 0 = -3 * s2 L

def OpUMul : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ) (F : ℂ → ℂ) (z : ℂ),
    opU L x (opU L y F) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x y : ℂ)) * opU L (x + y) F z

def OpUComm : Prop :=
  ∀ (L : PeriodPair) (F : ℂ → ℂ) (z : ℂ), opU L 0 F z = F z ∧ ∀ x y : ℂ,
    opU L x (opU L y F) z
      = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE L x y : ℂ)) * opU L y (opU L x F) z

def ThetaZeroConstant : Prop :=
  ∀ (L : PeriodPair) (t : ℂ), opU L t (sgStar L) 0
      = sgStar L t * Complex.exp (-(Real.pi : ℂ) * herm L t t / 2) ∧
    (t ∉ L.lattice → opU L t (sgStar L) 0 ≠ 0)

def ThetaZeroBasic : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    Differentiable ℂ (th0 L (ω₀ / 2)) ∧ th0 L (ω₀ / 2) 0 = 1 ∧
    (∀ z, th0 L (ω₀ / 2) (-z) = th0 L (ω₀ / 2) z) ∧
    (∀ z, th0 L (ω₀ / 2) z = 0 ↔ z + ω₀ / 2 ∈ L.lattice) ∧
    ∀ ω ∈ L.lattice, ∀ z, th0 L (ω₀ / 2) (z + ω)
      = semiChar L ω * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω ω₀ : ℂ))
        * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * th0 L (ω₀ / 2) z

def ThetaZeroClass : Prop :=
  ∀ (L : PeriodPair) (t ω z : ℂ), ω ∈ L.lattice → t ∉ L.lattice → th0 L (t + ω) z = th0 L t z

def ThetaZeroLogDerivative : Prop :=
  ∀ (L : PeriodPair) (ω₀ z : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → z + ω₀ / 2 ∉ L.lattice →
    HasDerivAt (th0 L (ω₀ / 2))
      ((wZeta L (z + ω₀ / 2) - wZeta L (ω₀ / 2) - s2 L * z) * th0 L (ω₀ / 2) z) z

end Formalism.L2.Th1.F
