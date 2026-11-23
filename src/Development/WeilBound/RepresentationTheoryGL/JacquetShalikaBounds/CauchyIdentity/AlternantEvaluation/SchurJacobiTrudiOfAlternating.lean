module

public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset GroundTheory.Automorphic GroundTheory.Automorphic.Spherical AddMonoidAlgebra

namespace PositivityTheory.RgJS

namespace SchurJacobiTrudiEvaluation

variable {m : ℕ}

def hL (m p : ℕ) : LaurentRing m := ∑ k ∈ Finset.Nat.antidiagonalTuple m p, monomial (fun i => (k i : ℤ))

def hLZ (m : ℕ) (z : ℤ) : LaurentRing m := if z < 0 then 0 else hL m z.toNat

def jL (m : ℕ) (l : Fin m → ℕ) : LaurentRing m := (Matrix.of fun i j : Fin m => hLZ m ((l j : ℤ) - j + i)).det

private theorem evalAt_monomial_eq_prod_zpow (z : Fin m → ℂˣ) (v : Fin m → ℤ) :
    evalAt z (monomial v) = ∏ i, ((z i : ℂ) ^ v i) := by
  rw [evalAt_apply]
  simp [monomialChar]

theorem evalAt_monomial_nat (z : Fin m → ℂˣ) (k : Fin m → ℕ) :
    evalAt z (monomial (fun i => (k i : ℤ))) = ∏ i, (z i : ℂ) ^ k i := by
  rw [evalAt_monomial_eq_prod_zpow]
  simp

theorem evalAt_hL (z : Fin m → ℂˣ) (p : ℕ) : evalAt z (hL m p) = hN p (fun i => (z i : ℂ)) := by
  unfold hL hN

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact evalAt_monomial_nat z k

theorem evalAt_hLZ (z : Fin m → ℂˣ) (w : ℤ) : evalAt z (hLZ m w) = hZ w (fun i => (z i : ℂ)) := by
  unfold hLZ hZ
  split_ifs
  · simp
  · exact evalAt_hL z _

theorem evalAt_jL (z : Fin m → ℂˣ) (l : Fin m → ℕ) : evalAt z (jL m l) = jt (fun i => (z i : ℂ)) l := by
  unfold jL jt
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [evalAt_hLZ]

theorem evalAt_alternant_nat (z : Fin m → ℂˣ) (μ : Fin m → ℕ) :
    evalAt z (alternant fun i => (μ i : ℤ)) = altN (fun i => (z i : ℂ)) μ := by
  rw [alternant_eq_det, AlgHom.map_det]
  unfold altN
  congr 1
  ext a b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [evalAt_monomial_eq_prod_zpow, Fintype.prod_eq_single a]
  · simp
  · intro i hi
    simp [Pi.single_apply, hi]

theorem staircase_eq : staircase m = fun i => ((stair m i : ℕ) : ℤ) := by
  funext i
  simp only [staircase, stair]
  have := i.isLt
  omega

end SchurJacobiTrudiEvaluation

open SchurJacobiTrudiEvaluation in
theorem schur_jacobi_trudi_of_alternating : AltJT → SchurJT := by
  intro h m z l
  have key : alternant (staircase m) * schur (fun i => (l i : ℤ)) = alternant (staircase m) * jL m l := by
    rw [alternant_mul_schur]
    apply eq_of_forall_evalAt
    intro w
    rw [map_mul, evalAt_jL, staircase_eq]
    have e : (fun i => (l i : ℤ)) + (fun i => ((stair m i : ℕ) : ℤ)) = fun i => (((l + stair m) i : ℕ) : ℤ) := by
      funext i
      simp
    rw [e, evalAt_alternant_nat, evalAt_alternant_nat]
    exact h m _ l
  rw [mul_left_cancel₀ alternant_staircase_ne_zero key]
  exact evalAt_jL z l

end PositivityTheory.RgJS
