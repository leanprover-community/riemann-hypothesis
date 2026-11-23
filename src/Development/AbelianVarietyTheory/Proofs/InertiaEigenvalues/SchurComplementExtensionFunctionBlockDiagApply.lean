module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
public import GroundTheory.AutomorphicForms.FourierWhittaker.UMatColXEqFromBlocks
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem schurSquareMatrixToBlocks_blockDiagonal_one {R : Type} [CommRing R] (m r : ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    blk (GroundTheory.Automorphic.FourierWhittaker.blockMat (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      Matrix.fromBlocks h 0 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blk, eqv, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, Matrix.one_apply, Fin.ext_iff]
  all_goals
    have hi := i.isLt
    have hj := j.isLt
    try intro
    split_ifs <;> first | rfl | (exfalso; omega) | omega

theorem schurF_blockGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ)
    (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (h : GA E (m + 1)) :
    schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      β h * b₁ 1 * (χ 0 : ℂ) := by
  classical
  have hb := schurSquareMatrixToBlocks_blockDiagonal_one (R := Ad E) m r (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))
  have hD : Dof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 1 := by
    rw [Dof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₂]
  have hA : Aof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = h := by
    rw [Aof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₁]
  have hB : Bof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Bof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₂]
  have hC : Cof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Cof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₁]
  have hmk : mkGL (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) = h :=
    Units.ext (coe_mkGL (Matrix.isUnits_det_units h))
  have hmk1 : mkGL (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) = 1 :=
    Units.ext (by rw [coe_mkGL (by simp)]; rfl)
  have hpsi : psi (0 : Ad E) = 1 := by
    simp [psi]
  have hchi : chiF (m := m) (r := r) χ 0 = (χ 0 : ℂ) := by
    have h0 : (fun i j => pInf E ((0 : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) i j)) = 0 := by
      funext i j; simp
    rw [chiF, h0]
    simp [zero_mem]
  rw [schurF, if_pos (by rw [hD]; simp), Xof, Scof, Yof, hA, hB, hC, hD]
  simp only [inv_one, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, sub_zero, Matrix.zero_apply]
  rw [hpsi, hmk, hmk1, hchi, one_mul]

end GlobalTheory.SchurExt
