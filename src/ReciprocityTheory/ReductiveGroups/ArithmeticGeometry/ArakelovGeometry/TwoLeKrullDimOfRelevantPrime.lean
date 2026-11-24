module

public import Mathlib.RingTheory.KrullDimension.Basic
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
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Dim

variable {R : Type*} [CommRing R]

theorem krullDim_quotient_add_one_le {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : q < p) : ringKrullDim (R ⧸ p) + 1 ≤ ringKrullDim (R ⧸ q) := by
  obtain ⟨r, hrp, hrq⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk q r ∈ nonZeroDivisors (R ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective h.le) hr
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hrp)

end Dim

section Kill

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

end Kill

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
