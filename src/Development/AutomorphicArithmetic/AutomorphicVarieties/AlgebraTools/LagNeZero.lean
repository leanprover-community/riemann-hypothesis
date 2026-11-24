module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagMap
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.aeval_mulVec_eigen {k ι : Type} [CommRing k] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) (t : k) (v : ι → k) (hv : M *ᵥ v = t • v) (q : k[X]) :
    (aeval M q) *ᵥ v = q.eval t • v := by
  induction q using Polynomial.induction_on with
  | C c => simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
  | add p q hp hq => rw [map_add (f := _), Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial n c h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, h,
      eval_mul (q := X), eval_X, smul_smul, mul_comm]

private theorem UpperTheory.V.AlgebraTools.lag_ne_zero_field {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι]
    (a : ι → k) (P : Matrix ι ι k) (hu : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hP : P.charpoly = ∏ i, (X - C (a i))) (i : ι) : lag a P i ≠ 0 := by
  intro h0
  have h1 := (eq_lag_iff a P i (fun j hj => hu i j hj.symm) (lag a P i)).1 rfl
  rw [h0, smul_zero] at h1
  have hroot : P.charpoly.eval (a i) = 0 := by
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hv' : P *ᵥ v = a i • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.mulVec_diagonal]
  have h2 := UpperTheory.V.AlgebraTools.aeval_mulVec_eigen P (a i) v hv' (∏ j ∈ Finset.univ.erase i, (X - C (a j)))
  rw [← h1, Matrix.zero_mulVec, eval_prod] at h2
  rcases smul_eq_zero.1 h2.symm with h | h
  · obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.1 h
    have := (hu i j (Finset.ne_of_mem_erase hj).symm).ne_zero
    apply this
    simpa using hj0
  · exact hv0 h

theorem UpperTheory.V.AlgebraTools.lag_ne_zero :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → R) (P : Matrix ι ι R), (∀ i j, i ≠ j → IsUnit (a i - a j)) → P.charpoly.map (residue R) = ∏ i, (X - C (residue R (a i))) → ∀ i, lag a P i ≠ 0 := by
  intro R _ _ ι _ _ a P hu hP i h0
  have h := lag_map (residue R) (residue R).mapMatrix a P
    (fun c => by
      ext x y
      by_cases hxy : x = y <;> simp [Matrix.algebraMap_matrix_apply, hxy]) hu i
  rw [h0, map_zero] at h
  refine UpperTheory.V.AlgebraTools.lag_ne_zero_field (fun j => residue R (a j)) ((residue R).mapMatrix P)
    (fun i j hij => by simpa only [map_sub] using (hu i j hij).map (residue R)) ?_ i h.symm
  rw [RingHom.mapMatrix_apply, Matrix.charpoly_map, hP]
