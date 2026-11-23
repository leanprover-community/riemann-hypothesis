module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem schurYClr_of : Comparison₂ → MixDet → SchurYClr ∧ SchurYOffClr := by
  intro hT hM
  constructor
  · intro R _ _ n lam g y
    simp only [hT R]
    have h := hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun a => y ^ shift lam a) (fun _ => 1)
    simp only [Matrix.of_apply, prod_const_one, mul_one] at h
    calc ∑ i, altn (shift lam) (scaleAt y i g)
        = ∑ i, (Matrix.of fun a j => (if j = i then y ^ shift lam a else 1) * g j ^ shift lam a).det := by
          refine sum_congr rfl fun i _ => ?_
          unfold altn
          congr 1
          ext a j
          simp only [Matrix.of_apply, scaleAt]
          split_ifs <;> simp [mul_pow]
      _ = _ := by
          rw [h]
          simp only [altn, shift]
          ring
  · intro R _ _ n lam g y
    simp only [hT R]
    have h := hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun _ => 1) (fun a => y ^ shift lam a)
    simp only [Matrix.of_apply, one_mul, prod_pow_eq_pow_sum] at h
    calc ∑ i, altn (shift lam) (scaleOff y i g)
        = ∑ i, (Matrix.of fun a j => (if j = i then 1 else y ^ shift lam a) * g j ^ shift lam a).det := by
          refine sum_congr rfl fun i _ => ?_
          unfold altn
          congr 1
          ext a j
          simp only [Matrix.of_apply, scaleOff]
          split_ifs <;> simp [mul_pow]
      _ = _ := by
          rw [h]
          simp only [altn, shift]
          ring

end UpperTheory.Gal.Schur
