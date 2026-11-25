module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqMulDiagonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix

namespace GlobalTheory.SplitHecke

theorem finrank_range_reduction (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (p : O) (hp : Irreducible p) (n j : ℕ) (a : GL (Fin n) K)
    (A : Matrix (Fin n) (Fin n) O) (hj : j ≤ n) (h : Hk O p j a) (hA : A.map (algebraMap O K) = a.1) :
    Module.finrank (IsLocalRing.ResidueField O)
      (LinearMap.range (A.map (IsLocalRing.residue O)).mulVecLin) + j = n := by
  classical
  obtain ⟨-, h2, u, hu⟩ := h
  obtain ⟨B, hB⟩ := intM_iff.1 h2
  have inj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hAB : A * B = p • (1 : Matrix (Fin n) (Fin n) O) := by
    apply Matrix.map_injective inj
    change (A * B).map (algebraMap O K) = (p • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O K)
    rw [Matrix.map_mul, hA, hB, Matrix.mul_smul, Units.mul_inv]
    ext i k
    by_cases e : i = k <;> simp [e]
  have hdet : Associated A.det (p ^ j) := by
    have : A.det = p ^ j * u := by
      apply inj
      rw [← hu, ← hA, RingHom.map_det]
      rfl
    rw [this]
    exact (associated_mul_unit_left _ _ u.isUnit)
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := GlobalTheory.SmithBetween.smith_between O p hp n j hj A B hAB hdet
  set r := IsLocalRing.residue O with hr
  have hP' : IsUnit (P.map r).det := by
    have := hP.map r
    rwa [RingHom.map_det] at this
  have hQ' : IsUnit (Q.map r).det := by
    have := hQ.map r
    rwa [RingHom.map_det] at this
  have hp0 : r p = 0 := (IsLocalRing.residue_eq_zero_iff p).2 hp.not_isUnit
  have h3 : A.map r * Q.map r = P.map r *
      Matrix.diagonal (fun i : Fin n => if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_mul, Matrix.diagonal_map (map_zero r)]
    congr 2
    funext i
    split_ifs <;> simp [hp0]
  have h4 := congrArg Matrix.rank h3
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP',
    Matrix.rank_diagonal] at h4
  have h5 : Fintype.card {i : Fin n // (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0}
      = n - j := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin n =>
        (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0)
        = Finset.univ.filter fun i : Fin n => i.1 < n - j := by
      ext i
      by_cases e : i.1 < n - j <;> simp only [Finset.mem_filter, Finset.mem_univ, e, ite_true, ite_false, true_and, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]
    rw [this, Fin.card_filter_val_lt]
    omega
  have h6 : (A.map r).rank = n - j := by
    rw [h4]
    convert h5
  rw [Matrix.finrank_range_mulVecLin]
  change (A.map r).rank + j = n
  omega

end GlobalTheory.SplitHecke
