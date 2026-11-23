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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.schurY_of :
    SchurYClr → VdmSplit → SchurY := by
  intro hOff hSplit R _ _ n lam g y hu
  have hv : IsUnit (vdm g) := by
    unfold vdm
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : i < j := by simpa using hj
    simpa using (hu i j (ne_of_gt hij)).neg
  have hScale : ∀ i, vdm (scaleAt y i g) =
      (-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (y * g i - g k) := by
    intro i
    rw [hSplit R n (scaleAt y i g) i]
    congr 1
    · congr 1
      unfold vdmAway
      refine Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => ?_
      have ha' : a ≠ i := Finset.ne_of_mem_erase ha
      have hb' : b ≠ i := Finset.ne_of_mem_erase hb
      simp [scaleAt, ha', hb']
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : k ≠ i := Finset.ne_of_mem_erase hk
      simp [scaleAt, hk']
  have key : ∀ i, (∏ k ∈ univ.erase i, (g k - y * g i) * Ring.inverse (g k - g i)) *
      ∏ k ∈ univ.erase i, (g i - g k) = ∏ k ∈ univ.erase i, (y * g i - g k) := by
    intro i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [show g i - g k = -(g k - g i) by ring, mul_neg, mul_assoc,
      Ring.inverse_mul_cancel _ (hu i k hki), mul_one]
    ring
  apply hv.mul_right_cancel
  have hR : sch lam g * (∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ)))) * vdm g =
      sch lam g * vdm g * ∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ))) := by ring
  rw [hR, ← hOff R n lam g y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hScale i, hSplit R n g i, ← key i]
  ring
