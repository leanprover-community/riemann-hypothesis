module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompS
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatA
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem diag_single_diag (u v : Fin n → ℂ) (r s : Fin n) (c : ℂ) :
    diagonal u * single r s c * diagonal v = single r s (u r * c * v s) := by
  ext i k
  rw [mul_diagonal, diagonal_mul, single_apply, single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    ring
  · simp

theorem inG_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, star (d1 a) * d1 a = 1) (h2 : ∀ a, star (d2 a) * d2 a = 1) :
    InG (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n) := by
  unfold InG
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  have hK : Dᴴ * fromBlocks (-(2 * Complex.I) • 1) 0 0 ((2 * Complex.I) • 1) * D =
      fromBlocks (-(2 * Complex.I) • 1) 0 0 ((2 * Complex.I) • 1) := by
    rw [hD, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [diagonal_conjTranspose]
    exact ⟨funext fun a => h1 a, funext fun a => h2 a⟩
  calc (Cm n * D * CmI n)ᴴ * JJ n * (Cm n * D * CmI n)
      = (CmI n)ᴴ * (Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D) * CmI n := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (CmI n)ᴴ * ((Cm n)ᴴ * JJ n * Cm n) * CmI n := by rw [cmH_JJ_cm, hK]
    _ = (Cm n * CmI n)ᴴ * JJ n * (Cm n * CmI n) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [cm_mul_cmI, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem prod_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) :
    Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n *
      (Cm n * fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) * CmI n) = 1 := by
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'
  have hDD : D * D' = 1 := by
    rw [hD, hD', fromBlocks_multiply, ← fromBlocks_one]
    simp [diagonal_mul_diagonal, h1, h2]
    done
  calc Cm n * D * CmI n * (Cm n * D' * CmI n) = Cm n * D * (CmI n * Cm n) * D' * CmI n := by
        simp only [Matrix.mul_assoc]
    _ = Cm n * (D * D') * CmI n := by
        rw [cmI_mul_cm, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hDD, Matrix.mul_one, cm_mul_cmI]

theorem inv_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) :
    (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n)⁻¹ =
      Cm n * fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) * CmI n := by
  exact Matrix.inv_eq_right_inv (prod_conjDiag d1 d2 h1 h2)

theorem cmI_N_cm (E : Matrix (Fin n) (Fin n) ℂ) :
    CmI n * fromBlocks 0 E 0 0 * Cm n = ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks E E (-E) (-E) := by
  rw [CmI, Cm, Matrix.smul_mul, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_multiply]
  congr 1
  simp
  done

theorem conj_nU (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) (r s : Fin n) :
    Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n * nU (single r s 1) *
        (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n)⁻¹ - 1 =
      Cm n * (((2 * Complex.I)⁻¹ : ℂ) • fromBlocks (single r s (d1 r * (d1 s)⁻¹)) (single r s (d1 r * (d2 s)⁻¹))
        (-single r s (d2 r * (d1 s)⁻¹)) (-single r s (d2 r * (d2 s)⁻¹))) * CmI n := by
  rw [inv_conjDiag d1 d2 h1 h2]
  have hn : nU (single r s (1 : ℂ)) = 1 + fromBlocks 0 (single r s 1) 0 0 := by
    rw [nU, ← fromBlocks_one, fromBlocks_add]
    simp
  rw [hn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, prod_conjDiag d1 d2 h1 h2, add_sub_cancel_left]
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'
  calc Cm n * D * CmI n * fromBlocks 0 (single r s 1) 0 0 * (Cm n * D' * CmI n)
      = Cm n * (D * (CmI n * fromBlocks 0 (single r s 1) 0 0 * Cm n) * D') * CmI n := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [cmI_N_cm]
        congr 2
        rw [Matrix.mul_smul, Matrix.smul_mul, hD, hD', fromBlocks_multiply, fromBlocks_multiply]
        simp [diag_single_diag]
        done

end PositivityTheory.Rg.Sw.LVs.TC
