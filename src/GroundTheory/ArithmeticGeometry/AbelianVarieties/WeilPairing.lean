module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsPic
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
import Mathlib.RingTheory.LocalProperties.Reduced
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine AddSubgroup

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic]

theorem divisorOf_pow {f : W.toAffine.FunctionField} (hf : f ≠ 0) (k : ℕ) :
    divisorOf W (f ^ k) = k • divisorOf W f := by
  induction k with
  | zero => rw [pow_zero, divisorOf_one, zero_smul]
  | succ k ih => rw [pow_succ, divisorOf_mul W (pow_ne_zero k hf) hf, ih, succ_nsmul]

theorem divisorOf_prod {ι' : Type*} (s : Finset ι') (φ : ι' → W.toAffine.FunctionField)
    (hφ : ∀ i ∈ s, φ i ≠ 0) : divisorOf W (∏ i ∈ s, φ i) = ∑ i ∈ s, divisorOf W (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, divisorOf_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      divisorOf_mul W (hφ a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hφ i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hφ i (Finset.mem_insert_of_mem hi)]



variable {W}

variable (W)

variable {W}


end GroundTheory.Arith.Abelian
