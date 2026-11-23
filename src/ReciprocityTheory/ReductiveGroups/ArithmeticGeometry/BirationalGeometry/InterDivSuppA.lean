module

public import Mathlib.RingTheory.Ideal.Height
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodA
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem mvPolynomialInt_dimFormula {σ : Type*} [Finite σ] (P Q : Ideal (MvPolynomial σ ℤ))
    [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ Q) + ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) =
      ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by

  haveI : IsJacobsonRing ℤ := int_isJacobsonRing
  haveI := DimF.finiteRingKrullDim_mvPolynomialInt_quot P
  haveI : (Q.map (Ideal.Quotient.mk P)).IsPrime := DimF.isPrime_map_mk h
  have key := DimF.dim_quot_add_height (A := MvPolynomial σ ℤ ⧸ P)
    (DimF.height_eq_of_isMaximal_int P) (Q.map (Ideal.Quotient.mk P))

  rw [← key, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE h)]

end ReciprocityTheory.ChartRestriction.G.Geo
