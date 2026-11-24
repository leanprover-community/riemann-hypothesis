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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.offClrPow_of :
    SchurYOffClr → VdmSplit → PairCount → OffClrPow := by
  intro hS hV hP R _ _ n lam g y
  have key : ∀ i : Fin n, vdm (scaleOff y i g) = y ^ (n - 1).choose 2 *
      ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) := by
    intro i
    have h1 : vdmAway i (scaleOff y i g) = y ^ (n - 1).choose 2 * vdmAway i g := by
      rw [← (hP n i).2, ← Finset.prod_pow_eq_pow_sum]
      unfold vdmAway
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a ha => ?_
      have ha' : a ≠ i := (Finset.mem_erase.mp ha).1
      calc ∏ b ∈ (Finset.Ioi a).erase i, (scaleOff y i g a - scaleOff y i g b)
          = ∏ b ∈ (Finset.Ioi a).erase i, (y * (g a - g b)) := by
            refine Finset.prod_congr rfl fun b hb => ?_
            have hb' : b ≠ i := (Finset.mem_erase.mp hb).1
            simp [scaleOff, ha', hb', mul_sub]
        _ = y ^ ((Finset.Ioi a).erase i).card * ∏ b ∈ (Finset.Ioi a).erase i, (g a - g b) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
    have h2 : ∏ k ∈ univ.erase i, (scaleOff y i g i - scaleOff y i g k) =
        ∏ k ∈ univ.erase i, (g i - y * g k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [scaleOff, hk']
    rw [hV R n (scaleOff y i g) i, h1, h2]
    ring
  have hL : y ^ (n - 1).choose 2 * ∑ i, sch lam (scaleOff y i g) *
      ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      ∑ i, sch lam (scaleOff y i g) * vdm (scaleOff y i g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key i]
    ring
  have hR : ∀ i : Fin n, y ^ (∑ k ∈ univ.erase i, (lam k + (n - 1 - (k : ℕ)))) =
      y ^ (n - 1).choose 2 * y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)) := by
    intro i
    rw [Finset.sum_add_distrib, (hP n i).1, ← pow_add]
    congr 1
    omega
  rw [hL, hS R n lam g y, Finset.sum_congr rfl fun i _ => hR i, ← Finset.mul_sum]
  ring
