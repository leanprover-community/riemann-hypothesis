module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative
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

def fT (L : PeriodPair) (t z : ℂ) : ℂ := opU L t (sgStar L) z / sgStar L z

def thetaZeroCharacter (L : PeriodPair) (ω₀ ω : ℂ) : ℂ :=
  semiChar L ω * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω ω₀ : ℂ))

def FtQuasi : Prop :=
  ∀ (L : PeriodPair) (t ω z : ℂ), ω ∈ L.lattice →
    fT L t (z + ω) = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE L ω t : ℂ)) * fT L t z

def OpUTh0 : Prop :=
  ∀ (L : PeriodPair) (t x z : ℂ),
    opU L x (th0 L t) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x t : ℂ)) * opU L (x + t) (sgStar L) z
        / opU L t (sgStar L) 0

def ThetaZeroLine : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (F : ℂ → ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → Differentiable ℂ F →
    (∀ ω ∈ L.lattice, ∀ z, F (z + ω) = thetaZeroCharacter L ω₀ ω
      * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * F z) →
    ∀ z, F z = F 0 * th0 L (ω₀ / 2) z

end Formalism.L2.Th1.F
