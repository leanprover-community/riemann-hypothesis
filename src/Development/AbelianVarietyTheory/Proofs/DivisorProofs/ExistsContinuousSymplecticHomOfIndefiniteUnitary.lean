module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Upqcpt
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section

namespace GlobalTheory.ColAction

theorem sympl_eq_neg_dotProduct {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, Finset.sum_neg_distrib, mul_comm]
  ring

theorem mem_symplecticGroup_of_sympl {l : Type} [Fintype l] [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (M *ᵥ u) (M *ᵥ v) = sympl u v) : M ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff']
  ext a b
  have key : ∀ u v, (M *ᵥ u) ⬝ᵥ (Matrix.J l ℝ *ᵥ (M *ᵥ v)) = u ⬝ᵥ ((Mᵀ * Matrix.J l ℝ * M) *ᵥ v) := by
    intro u v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Mᵀ, Matrix.vecMul_transpose]
  have := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_neg_dotProduct, sympl_eq_neg_dotProduct, neg_inj, key] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem signed_sum_eq_trace {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) :
    ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) = Matrix.trace (Jm P Q * X * Jm R S * Yᴴ) := by
  have e : Jm P Q * X * Jm R S =
      Matrix.of fun a b => ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) a * X a b * ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) b := by
    ext a b
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [Fintype.sum_sum_type, lineSign]

theorem signed_sum_mul_transpose {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) (k : Mat R S)
    (hk : kᴴ * Jm R S * k = Jm R S) :
    ∑ a, ∑ b, lineSign a b * (X * kᵀ) a b * star ((Y * kᵀ) a b) = ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) := by
  have hJ : (Jm R S)ᵀ = Jm R S := by
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal]
  have e : (kᵀ)ᴴ = k.map star := by ext i j; simp
  have hk' : kᵀ * Jm R S * (kᵀ)ᴴ = Jm R S := by
    have := congrArg Matrix.transpose hk
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ, Matrix.conjTranspose_transpose] at this
    rw [e, Matrix.mul_assoc, this]
  rw [signed_sum_eq_trace, signed_sum_eq_trace, Matrix.conjTranspose_mul]
  congr 1
  calc Jm P Q * (X * kᵀ) * Jm R S * ((kᵀ)ᴴ * Yᴴ) = Jm P Q * X * (kᵀ * Jm R S * (kᵀ)ᴴ) * Yᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hk']

end GlobalTheory.ColAction
