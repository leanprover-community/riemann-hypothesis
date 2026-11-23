module

public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Matrix
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace BigA

open Complex Matrix ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

theorem projPerp_self {N : ℕ} (g0 : Fin N → ℂ) (h : g0 ≠ 0) : projPerp g0 *ᵥ g0 = 0 := by
  have hs : (sqNorm g0 : ℂ) ≠ 0 := by
    exact_mod_cast (sqNorm_pos h).ne'
  have e : star g0 ⬝ᵥ g0 = (sqNorm g0 : ℂ) := by
    simp [sqNorm, dotProduct, Complex.normSq_eq_conj_mul_self]
  funext i
  simp only [projPerp, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]
  rw [show (vecMulVec g0 (star g0) *ᵥ g0) i = g0 i * (star g0 ⬝ᵥ g0) by
    simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_assoc], e]
  field_simp
  ring

end BigA

end ReciprocityTheory.ChartRestriction.G.AR.Up
