module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def eAB : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ixA ixB
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private theorem cp_block {K : Type} [Field K] (X : M4 K) (h : IsBlock X) :
    X.charpoly = (X.submatrix ixA ixA).charpoly * (X.submatrix ixB ixB).charpoly := by
  have e : Matrix.reindex eAB.symm eAB.symm X =
      Matrix.fromBlocks (X.submatrix ixA ixA) (X.submatrix ixA ixB) 0 (X.submatrix ixB ixB) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact h (ixB i) (ixA j) (by revert i j; decide)
    · rfl
  rw [← Matrix.charpoly_reindex eAB.symm, e, Matrix.charpoly_fromBlocks_zero₂₁]

private theorem det_two {K : Type} [Field K] [IsAlgClosed K] (A : Matrix (Fin 2) (Fin 2) K) :
    ∃ a ∈ A.charpoly.roots, ∃ b ∈ A.charpoly.roots, A.det = a * b := by
  have hc : A.charpoly.roots.card = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]; simp
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 hc
  refine ⟨a, by simp [hab], b, by simp [hab], ?_⟩
  rw [Matrix.det_eq_prod_roots_charpoly, hab]; simp

theorem UpperTheory.V.Ws.pureDet :
    ∀ {K : Type} [Field K] [IsAlgClosed K] (ι : K →+* ℂ) (X : M4 K), IsBlock X →
          (∀ x ∈ X.charpoly.roots, ∀ y ∈ X.charpoly.roots, ‖ι x‖ = ‖ι y‖) →
          ‖ι (X.submatrix ixA ixA).det‖ = ‖ι (X.submatrix ixB ixB).det‖ := by
  intro K _ _ ι X hX h
  have hr : X.charpoly.roots =
      (X.submatrix ixA ixA).charpoly.roots + (X.submatrix ixB ixB).charpoly.roots := by
    rw [cp_block X hX, roots_mul (mul_ne_zero (Matrix.charpoly_monic _).ne_zero (Matrix.charpoly_monic _).ne_zero)]
  obtain ⟨a, ha, b, hb, hA⟩ := det_two (X.submatrix ixA ixA)
  obtain ⟨c, hc, d, hd, hB⟩ := det_two (X.submatrix ixB ixB)
  rw [hr] at h
  rw [hA, hB, map_mul, map_mul, norm_mul, norm_mul,
    h a (Multiset.mem_add.2 (Or.inl ha)) c (Multiset.mem_add.2 (Or.inr hc)),
    h b (Multiset.mem_add.2 (Or.inl hb)) d (Multiset.mem_add.2 (Or.inr hd))]
