module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CoefId

lemma prod_prs_eq_iter {n : ℕ} (f : Fin n × Fin n → ℂ) :
    ∏ p ∈ prs n, f p = ∏ i : Fin n, ∏ j ∈ Ioi i, f (i, j) := by
  apply Finset.prod_finset_product
  intro p
  simp [prs]

lemma det_rev_vandermonde {n : ℕ} (v : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => v i ^ (n - 1 - (j : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) *
        ∏ p ∈ prs n, (v p.2 - v p.1) := by
  have h : (Matrix.of fun i j : Fin n => v i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde v).submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := by
    ext i j
    have : n - 1 - (j : ℕ) = n - (j + 1) := by omega
    simp [Matrix.vandermonde_apply, Fin.val_rev, this]
  rw [h, Matrix.det_permute', Matrix.det_vandermonde, prod_prs_eq_iter]

theorem det_vandermonde_sq {n : ℕ} (z : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det =
      (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det *
        ∏ p ∈ prs n, (z p.1 + z p.2) := by
  rw [det_rev_vandermonde (fun i => z i ^ 2), det_rev_vandermonde z, mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  ring

end GlobalTheory.CompanionTheory.CoefId
