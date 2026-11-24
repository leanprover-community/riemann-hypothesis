module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
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

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.dSigma :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (Y : Matrix (Fin n) (Fin n) F) (g : G), (∀ g, χ (D.σ g) = χ g) → dTw χ D.r Y (D.σ g) = (dTw χ D.r Yᵀ g)ᵀ := by
  intro F G _ _ n D χ Y g hχ
  have e1 : D.r (D.σ g) = (D.μ g : F) • (D.r g⁻¹)ᵀ := by
    have h : (D.r g⁻¹)ᵀ * (D.r g)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.transpose_one]
    calc D.r (D.σ g) = (D.r g⁻¹)ᵀ * ((D.r g)ᵀ * D.r (D.σ g)) := by
          rw [← Matrix.mul_assoc, h, Matrix.one_mul]
      _ = _ := by rw [D.form, Matrix.mul_smul, Matrix.mul_one]
  have e2 : D.r (D.σ g)⁻¹ = (D.μ g⁻¹ : F) • (D.r g)ᵀ := by
    have h : (D.r g)ᵀ * (D.r g⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one]
    rw [← map_inv]
    calc D.r (D.σ g⁻¹) = (D.r g)ᵀ * ((D.r g⁻¹)ᵀ * D.r (D.σ g⁻¹)) := by
          rw [← Matrix.mul_assoc, h, Matrix.one_mul]
      _ = _ := by rw [D.form, Matrix.mul_smul, Matrix.mul_one]
  have e3 : ((D.μ g : F) * D.μ g⁻¹) • (1 : Matrix (Fin n) (Fin n) F) = 1 := by
    have h : D.r (D.σ g) * D.r (D.σ g)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [e1, e2, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.transpose_mul, ← map_mul, mul_inv_cancel,
      map_one, Matrix.transpose_one, smul_smul] at h
    exact h
  have key : D.r (D.σ g) * Y * D.r (D.σ g)⁻¹ = (D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ := by
    rw [e1, e2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show ((D.μ g : F) * D.μ g⁻¹) • ((D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ)
        = (((D.μ g : F) * D.μ g⁻¹) • (1 : Matrix (Fin n) (Fin n) F)) * ((D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ) by
      rw [Matrix.smul_mul, Matrix.one_mul], e3, Matrix.one_mul]
  simp only [dTw, hχ, key, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]
