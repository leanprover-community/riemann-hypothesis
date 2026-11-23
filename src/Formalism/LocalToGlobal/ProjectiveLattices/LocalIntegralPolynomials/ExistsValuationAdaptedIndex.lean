module

public import Mathlib.Algebra.MvPolynomial.Basic
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
public import Mathlib.Algebra.MvPolynomial.CommRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.LocAlg

open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial

variable {Ω : Type} [Field Ω] {D N : ℕ}

variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}

def intPoly (σ : Type) (W : Subring Ω) : Subring (MvPolynomial σ Ω) where
  carrier := {P | ∀ e, P.coeff e ∈ W}
  mul_mem' := by
    intro P Q hP hQ e
    classical
    rw [coeff_mul]
    exact sum_mem fun d _ => W.mul_mem (hP _) (hQ _)
  one_mem' := by
    intro e
    classical
    rw [coeff_one]
    split_ifs
    exacts [W.one_mem, W.zero_mem]
  add_mem' := by
    intro P Q hP hQ e
    rw [MvPolynomial.coeff_add]
    exact W.add_mem (hP e) (hQ e)
  zero_mem' := by
    intro e
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact W.zero_mem
  neg_mem' := by
    intro P hP e
    rw [MvPolynomial.coeff_neg]
    exact W.neg_mem (hP e)

theorem C_mem_intPoly {σ : Type} {W : Subring Ω} {a : Ω} (ha : a ∈ W) : (C a : MvPolynomial σ Ω) ∈ intPoly σ W := by
  intro e
  classical
  rw [coeff_C]
  split_ifs
  exacts [ha, W.zero_mem]

theorem X_mem_intPoly {σ : Type} {W : Subring Ω} (s : σ) : (X s : MvPolynomial σ Ω) ∈ intPoly σ W := by
  intro e
  classical
  rw [coeff_X']
  split_ifs
  exacts [W.one_mem, W.zero_mem]

end Formalism.L2.Pj.LocAlg
