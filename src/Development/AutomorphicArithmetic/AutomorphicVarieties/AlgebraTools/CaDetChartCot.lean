module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.chartGen_cotInd :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι B) (m l : ι → B) (c : ι),
      CotInd B (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) → l c = 1 →
      CotInd B (Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c)) := by
  intro B _ _ ι _ _ z m l c hx hl
  have hmem := hx.mem
  refine ⟨?_, ?_⟩
  · intro k
    rcases k with i | j
    · simp only [Sum.elim_inl, Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hmem (Sum.inl (i, j)))
    · simp only [Sum.elim_inr]
      exact Ideal.sub_mem _ (hmem (Sum.inr j.1)) (Ideal.mul_mem_left _ _ (hmem (Sum.inr c)))
  · intro a ha
    let b : ι × ι ⊕ ι → B := Sum.elim (fun ij => a (Sum.inl ij.1) * l ij.2)
      (fun j => if h : j = c then -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1)
        else a (Sum.inr ⟨j, h⟩))
    have key : ∑ k, b k * Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m k
        = ∑ k, a k * Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c) k := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => b (Sum.inr j) * m j) c]
      simp only [b, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct, dite_true]
      have e : ∀ j : {j // j ≠ c}, (if h : (j : ι) = c then
          -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1) else a (Sum.inr ⟨j, h⟩)) * m j
          = a (Sum.inr j) * m j := fun j => by rw [dite_eq_right j.2]
      rw [Finset.sum_congr rfl (fun j _ => e j)]
      have e2 : ∀ i, ∑ j, a (Sum.inl i) * l j * z i j = a (Sum.inl i) * ∑ j, z i j * l j := by
        intro i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [Finset.sum_congr rfl (fun i _ => e2 i)]
      have e3 : ∑ j : {j // j ≠ c}, a (Sum.inr j) * (m j - l j * m c)
          = ∑ j : {j // j ≠ c}, a (Sum.inr j) * m j - (∑ k : {k // k ≠ c}, a (Sum.inr k) * l k) * m c := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [e3]
      ring
    have hb : ∀ k, b k ∈ maximalIdeal B := hx.indep b (by rw [key]; exact ha)
    intro k
    rcases k with i | j
    · have := hb (Sum.inl (i, c))
      simpa [b, hl] using this
    · have := hb (Sum.inr j.1)
      simpa [b, j.2] using this
