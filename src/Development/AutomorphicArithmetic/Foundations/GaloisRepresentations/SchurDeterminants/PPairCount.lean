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
import Mathlib.Tactic.Basify
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

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.pairCount_of :
    PairSplit → PairCount := by
  intro hP n i
  have hS : ∑ a : Fin n, (n - 1 - (a : ℕ)) = n.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun a => n - 1 - a), Finset.sum_range_reflect (fun a => a) n,
      Finset.sum_range_id, Nat.choose_two_right]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have hC : (m + 1).choose 2 = m.choose 2 + m := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have hi : (i : ℕ) ≤ m := by have := i.isLt; omega
  simp only [Nat.add_sub_cancel] at hS ⊢
  refine ⟨?_, ?_⟩
  · have h1 := Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun k => m - (k : ℕ))
      (Finset.mem_univ i)
    omega
  · have h := hP (Multiplicative ℕ) (m + 1) (fun _ _ => Multiplicative.ofAdd 1) i
    apply_fun Multiplicative.toAdd at h
    simp [toAdd_prod] at h
    omega
