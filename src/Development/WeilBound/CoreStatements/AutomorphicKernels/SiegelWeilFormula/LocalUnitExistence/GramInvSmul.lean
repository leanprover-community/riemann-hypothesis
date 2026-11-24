module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtWitt
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

set_option linter.unusedSectionVars false

section Generic

variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι] (c : S →ₐ[R] S)

theorem map_mul_c (A B : Matrix ι ι S) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul

theorem gram_inv {H J : Matrix ι ι S} (M : GL ι S) (hM : M.1ᵀ * H * M.1.map c = J) :
    (M⁻¹).1ᵀ * J * (M⁻¹).1.map c = H := by
  subst hM
  have h1 : (M⁻¹).1ᵀ * M.1ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h2 : M.1.map c * (M⁻¹).1.map c = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.Ldexb.map_mul_c c, Units.mul_inv]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  calc (M⁻¹).1ᵀ * (M.1ᵀ * H * M.1.map c) * (M⁻¹).1.map c
      = ((M⁻¹).1ᵀ * M.1ᵀ) * H * (M.1.map c * (M⁻¹).1.map c) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem conj_mem {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) {y : GL ι S}
    (hy : y ∈ UG c H₀) : M * y * M⁻¹ ∈ UG c H := by
  have hy' : (y : Matrix ι ι S)ᵀ * H₀ * (y : Matrix ι ι S).map c = H₀ := hy
  have hmid : (y : Matrix ι ι S)ᵀ * (M.1ᵀ * H * M.1.map c) * (y : Matrix ι ι S).map c
      = M.1ᵀ * H * M.1.map c := by
    rw [hM, Matrix.mul_smul, Matrix.smul_mul, hy']
  have key : (M⁻¹).1ᵀ * ((y : Matrix ι ι S)ᵀ * (M.1ᵀ * H * M.1.map c) * (y : Matrix ι ι S).map c)
      * (M⁻¹).1.map c = H := by
    rw [hmid]
    exact PositivityTheory.SiegelWeilFormula.Ldexb.gram_inv c M rfl
  show ((M * y * M⁻¹ : GL ι S) : Matrix ι ι S)ᵀ * H * ((M * y * M⁻¹ : GL ι S) : Matrix ι ι S).map c = H
  simp only [Units.val_mul, Matrix.transpose_mul, PositivityTheory.SiegelWeilFormula.Ldexb.map_mul_c]
  simpa only [Matrix.mul_assoc] using key

theorem gram_inv_smul {H H₀ : Matrix ι ι S} (M : GL ι S) (s : Sˣ) (hM : M.1ᵀ * H * M.1.map c = (s : S) • H₀) :
    (M⁻¹).1ᵀ * H₀ * (M⁻¹).1.map c = ((s⁻¹ : Sˣ) : S) • H := by
  have h := PositivityTheory.SiegelWeilFormula.Ldexb.gram_inv c M hM
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  rw [← h, smul_smul, Units.inv_mul, one_smul]

def cj {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z : UG c H₀) : UG c H :=
  ⟨M * z.1 * M⁻¹, conj_mem c M s hM z.2⟩

theorem cj_val {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z : UG c H₀) :
    (cj c M s hM z).1 = M * z.1 * M⁻¹ := rfl

theorem cj_mul {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z z' : UG c H₀) :
    cj c M s hM (z * z') = cj c M s hM z * cj c M s hM z' := by
  apply Subtype.ext
  show M * ((z : GL ι S) * (z' : GL ι S)) * M⁻¹ = (M * (z : GL ι S) * M⁻¹) * (M * (z' : GL ι S) * M⁻¹)
  group

theorem cj_inv {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z : UG c H₀) :
    cj c M s hM z⁻¹ = (cj c M s hM z)⁻¹ := by
  apply Subtype.ext
  show M * (z : GL ι S)⁻¹ * M⁻¹ = (M * (z : GL ι S) * M⁻¹)⁻¹
  group

end Generic

section Unitary

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem diag_unitary (d : ι → ℂ) (hd : ∀ i, star (d i) * d i = 1) (X : Matrix ι ι ℂ) (hX : X * Xᴴ = 1) :
    (Matrix.diagonal d * X * Matrix.diagonal (star d)) * (Matrix.diagonal d * X * Matrix.diagonal (star d))ᴴ = 1 := by
  have h1 : Matrix.diagonal (star d) * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hd i
  have h2 : Matrix.diagonal d * Matrix.diagonal (star d) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hd i
  have e : (Matrix.diagonal d * X * Matrix.diagonal (star d))ᴴ
      = Matrix.diagonal d * (Xᴴ * Matrix.diagonal (star d)) := by
    simp only [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_star, Matrix.mul_assoc]
  rw [e]
  calc Matrix.diagonal d * X * Matrix.diagonal (star d) * (Matrix.diagonal d * (Xᴴ * Matrix.diagonal (star d)))
      = Matrix.diagonal d * X * (Matrix.diagonal (star d) * Matrix.diagonal d) * Xᴴ * Matrix.diagonal (star d) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal d * Matrix.diagonal (star d) := by
        rw [h1, Matrix.mul_one, Matrix.mul_assoc (Matrix.diagonal d) X, hX, Matrix.mul_one]
    _ = 1 := h2

end Unitary

end PositivityTheory.SiegelWeilFormula.Ldexb

end
