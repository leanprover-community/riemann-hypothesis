module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def wZeta (L : PeriodPair) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)

def wFactor (l z : ℂ) : ℂ := (1 - z / l) * Complex.exp (z / l + z ^ 2 / (2 * l ^ 2))

def wSigma (L : PeriodPair) (z : ℂ) : ℂ := z * ∏' l : L.lattice, wFactor (l : ℂ) z

def wEta (L : PeriodPair) : ℂ →ₗ[ℝ] ℂ :=
  L.basis.constr ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)]

def area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|

def s2 (L : PeriodPair) : ℂ :=
  (wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁) / (L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁)

def sgStar (L : PeriodPair) (z : ℂ) : ℂ := wSigma L z * Complex.exp (-(s2 L) * z ^ 2 / 2)

def herm (L : PeriodPair) (z w : ℂ) : ℂ := z * conj w / (area L : ℂ)

def opU (L : PeriodPair) (x : ℂ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F (z + x) * Complex.exp (-(Real.pi : ℂ) * herm L z x - (Real.pi : ℂ) * herm L x x / 2)


open Classical in
def semiChar (L : PeriodPair) (ω : ℂ) : ℂ := by
  classical
  exact if ω / 2 ∈ L.lattice then 1 else -1

def th0 (L : PeriodPair) (t : ℂ) (z : ℂ) : ℂ := opU L t (sgStar L) z / opU L t (sgStar L) 0

end Formalism.L2.Th1.F
