module

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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem exists_dual_of_anisotropic_orthogonal (E : Type) [Field E] [StarRing E] (n m : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin m) (Fin m) E) (x : Fin n → E)
    (A : Matrix (Fin n) (Fin m) E) (hn : m + 1 = n) (hJ : Jᴴ = J) (hdet : J'.det ≠ 0)
    (hβ : star x ⬝ᵥ (J *ᵥ x) ≠ 0) (hx : star x ᵥ* (J * A) = 0) (hA : Aᴴ * J * A = J') :
    ∃ (u : Fin n → E) (A' : Matrix (Fin m) (Fin n) E), A' * A = 1 ∧ A' *ᵥ x = 0 ∧
      u ᵥ* A = 0 ∧ u ⬝ᵥ x = 1 ∧ vecMulVec x u + A * A' = 1 ∧ Aᴴ *ᵥ (J *ᵥ x) = 0 := by
  have h6 : Aᴴ *ᵥ (J *ᵥ x) = 0 := by
    have := congrArg star hx
    rw [Matrix.star_vecMul, star_star, Matrix.conjTranspose_mul, hJ, star_zero,
      ← Matrix.mulVec_mulVec] at this
    exact this
  obtain ⟨u, hu⟩ : ∃ u : Fin n → E, u = (star x ⬝ᵥ (J *ᵥ x))⁻¹ • (star x ᵥ* J) := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : Matrix (Fin m) (Fin n) E, A' = J'⁻¹ * Aᴴ * J := ⟨_, rfl⟩
  have h1 : A' * A = 1 := by
    rw [hA', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA]
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)
  have h2 : A' *ᵥ x = 0 := by
    rw [hA', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h6, Matrix.mulVec_zero]
  have h3 : u ᵥ* A = 0 := by
    rw [hu, Matrix.smul_vecMul, Matrix.vecMul_vecMul, hx, smul_zero]
  have h4 : u ⬝ᵥ x = 1 := by
    rw [hu, smul_dotProduct, ← Matrix.dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hβ]
  refine ⟨u, A', h1, h2, h3, h4, ?_, h6⟩
  subst hn
  let C : Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
    Matrix.of fun i j => (Fin.cons (x i) (fun k => A i k) : Fin (m + 1) → E) j
  let C' : Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
    Matrix.of fun i j => (Fin.cons (u j) (fun k => A' k j) : Fin (m + 1) → E) i
  have hCC : C' * C = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa [C, C', Matrix.mul_apply, dotProduct] using h4
    · have := congrFun h3 j
      simpa [C, C', Matrix.mul_apply, dotProduct, Matrix.vecMul, (Fin.succ_ne_zero j).symm] using this
    · have := congrFun h2 i
      simpa [C, C', Matrix.mul_apply, dotProduct, Matrix.mulVec, Fin.succ_ne_zero i] using this
    · have := congrFun (congrFun h1 i) j
      simpa [C, C', Matrix.mul_apply, Matrix.one_apply] using this
  have hCC' : C * C' = 1 := mul_eq_one_comm.mp hCC
  rw [← hCC']
  ext i j
  simp [C, C', Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMulVec_apply]

end GlobalTheory.StabUnfold
