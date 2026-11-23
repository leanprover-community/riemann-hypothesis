module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

theorem unitriangular_inv_close {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) (t : E) (ht : t ∈ L.O) (hlow : ∀ i j, j < i → M i j = 0) (hdiag : ∀ i, M i i = 1) (hcl : ∀ i j, ∃ o ∈ L.O, (M - 1) i j = t * o) : ∃ Mi : Matrix (Fin n) (Fin n) E, Mi * M = 1 ∧ M * Mi = 1 ∧ ∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o := by
  have hMO : ∀ i j, M i j ∈ L.O := by
    intro i j
    obtain ⟨o, ho, he⟩ := hcl i j
    have : M i j = t * o + (1 : Matrix (Fin n) (Fin n) E) i j := by
      rw [← he]; simp
    rw [this]
    refine L.O.add_mem (L.O.mul_mem ht ho) ?_
    by_cases h : i = j
    · subst h; simp [L.O.one_mem]
    · simp [h, L.O.zero_mem]
  let f : L.O →+* E := L.O.subtype
  let M' : Matrix (Fin n) (Fin n) L.O := Matrix.of fun i j => ⟨M i j, hMO i j⟩
  have hM' : f.mapMatrix M' = M := by
    ext i j; rfl
  have hdet : M'.det = 1 := by
    apply Subtype.ext
    have h1 : f M'.det = (f.mapMatrix M').det := RingHom.map_det f M'
    have h2 : M.det = 1 := by
      rw [Matrix.det_of_upperTriangular (M := M) (fun i j hij => hlow i j hij)]
      simp [hdiag]
    change f M'.det = f 1
    rw [h1, hM', h2, map_one]
  have hu : IsUnit M'.det := by rw [hdet]; exact isUnit_one
  refine ⟨f.mapMatrix M'⁻¹, ?_, ?_, ?_⟩
  · rw [← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
  · rw [← hM', ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
  · intro i j
    set Mi := f.mapMatrix M'⁻¹ with hMi
    have hinv : Mi * M = 1 := by
      rw [hMi, ← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
    have key : Mi - 1 = -(Mi * (M - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one]; abel
    choose o ho he using hcl
    refine ⟨-(∑ k, (M'⁻¹ i k : E) * o k j), ?_, ?_⟩
    · exact L.O.neg_mem (L.O.sum_mem fun k _ => L.O.mul_mem (M'⁻¹ i k).2 (ho k j))
    · rw [key, Matrix.neg_apply, Matrix.mul_apply]
      simp only [he]
      rw [mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hMi, f]
      ring

end GlobalTheory
