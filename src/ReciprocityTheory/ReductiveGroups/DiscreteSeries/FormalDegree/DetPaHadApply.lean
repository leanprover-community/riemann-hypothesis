module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HasDerivAtMexpCommAddBracket
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def detPaCj (P Q : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun W := P * W * Q
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp

def detPaRow (t : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi (fun j => (t j • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp (LinearMap.proj j))

def detPaHad (s : Fin n → Fin n → ℂ) : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  LinearMap.pi (fun i => (detPaRow (s i)).comp (LinearMap.proj i))

theorem detPaRow_det (t : Fin n → ℂ) : LinearMap.det (detPaRow t) = ∏ j, t j := by
  unfold detPaRow
  rw [LinearMap.det_pi]
  simp

theorem detPaHad_det (s : Fin n → Fin n → ℂ) : LinearMap.det (detPaHad s) = ∏ i, ∏ j, s i j := by
  unfold detPaHad
  rw [LinearMap.det_pi]
  simp [detPaRow_det]

theorem detPa {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      ∏ i, ∏ j, shc (pev y i - pev y j) ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hmem : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ((pmat_isHermitian y).eigenvectorUnitary).2
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hmem
  set s : Fin n → Fin n → ℂ := fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) with hs
  let H : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ := detPaHad s
  let T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (detPaCj U Uᴴ).comp (H.comp (detPaCj Uᴴ U))
  have hT : ∀ W, T W = shcAd y W := by
    intro W
    simp only [T, H, LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, shcAd]
    congr 2
  have hC : shcAd y = ⇑(LinearMap.toContinuousLinearMap (T.restrictScalars ℝ)) := by
    funext W; exact (hT W).symm
  rw [hC, ContinuousLinearMap.fderiv, LinearMap.coe_toContinuousLinearMap, LinearMap.det_restrictScalars]
  have hAB : LinearMap.det (detPaCj U Uᴴ) * LinearMap.det (detPaCj Uᴴ U) = 1 := by
    rw [← LinearMap.det_comp]
    have : (detPaCj U Uᴴ).comp (detPaCj Uᴴ U) = LinearMap.id := by
      ext W : 1
      simp only [LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc, hU2, Matrix.mul_one]
    rw [this, LinearMap.det_id]
  have hdet : LinearMap.det T = ∏ i, ∏ j, s i j := by
    simp only [T]
    rw [LinearMap.det_comp, LinearMap.det_comp]
    have hH : LinearMap.det H = ∏ i, ∏ j, s i j := detPaHad_det s
    rw [hH, mul_left_comm, hAB, mul_one]
  rw [hdet, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Algebra.norm_complex_apply, hs, Complex.normSq_ofReal, sq]

end ReciprocityTheory.ChartRestriction.DS
