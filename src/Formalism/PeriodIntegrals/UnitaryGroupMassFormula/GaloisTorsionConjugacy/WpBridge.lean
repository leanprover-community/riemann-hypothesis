module

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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.GalTorsConj.W

open PI.GalTorsConj

def addX {K : Type*} [Field K] (x y x₂ y₂ : K) : K :=
  ((y - y₂) / (x - x₂)) ^ 2 / 4 - x - x₂

def addY {K : Type*} [Field K] (x y x₂ y₂ : K) : K :=
  (y - y₂) / (x - x₂) * (x - addX x y x₂ y₂) - y

def dblX {K : Type*} [Field K] (x y g : K) : K :=
  ((6 * x ^ 2 - g / 2) / y) ^ 2 / 4 - 2 * x

def dblY {K : Type*} [Field K] (x y g : K) : K :=
  (6 * x ^ 2 - g / 2) / y * (x - dblX x y g) - y

def AddLaw : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice → z - w ∉ L.lattice →
    z + w ∉ L.lattice →
    L.weierstrassP (z + w) = addX (L.weierstrassP z) (L.derivWeierstrassP z)
        (L.weierstrassP w) (L.derivWeierstrassP w) ∧
    L.derivWeierstrassP (z + w) = addY (L.weierstrassP z) (L.derivWeierstrassP z)
        (L.weierstrassP w) (L.derivWeierstrassP w)

def DblLaw : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → 2 * z ∉ L.lattice →
    L.weierstrassP (2 * z) = dblX (L.weierstrassP z) (L.derivWeierstrassP z) L.g₂ ∧
    L.derivWeierstrassP (2 * z) = dblY (L.weierstrassP z) (L.derivWeierstrassP z) L.g₂

def POnto : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ), y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ →
    ∃ z, z ∉ L.lattice ∧ L.weierstrassP z = x ∧ L.derivWeierstrassP z = y

end PI.GalTorsConj.W

end
