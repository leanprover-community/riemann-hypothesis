module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.GoodAwayEx
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Cx

variable {n : ℕ}

def wM {R : Type} [CommRing R] (n : ℕ) (e : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := Matrix.fromBlocks 0 1 (e • 1) 0

theorem wM_sq {R : Type} [CommRing R] (e : R) : wM n e * wM n e = e • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
  rw [wM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  simp

theorem wM_four {R : Type} [CommRing R] (e : R) (he : e * e = 1) : wM n e * wM n e * wM n e * wM n e = 1 := by
  rw [Matrix.mul_assoc (wM n e * wM n e), wM_sq, smul_mul_smul_comm, Matrix.one_mul, he, one_smul]

theorem dZ_mul (a b : ℂ) : dZ n a * dZ n b = dZ n (a * b) := by
  simp [dZ, Matrix.fromBlocks_multiply, smul_smul]
  rw [mul_comm]

theorem dZ_one : dZ n 1 = 1 := by
  simp [dZ, Matrix.fromBlocks_one]

theorem dZ_conj_nU {ζ : ℂ} (h : ζ ≠ 0) (x : Matrix (Fin n) (Fin n) ℂ) : dZ n ζ⁻¹ * nU x * dZ n ζ = nU (ζ • x) := by
  simp [dZ, nU, Matrix.fromBlocks_multiply, smul_smul, mul_inv_cancel₀ h]

theorem dZ_conj_nb {ζ : ℂ} (h : ζ ≠ 0) (c : Matrix (Fin n) (Fin n) ℂ) :
    dZ n ζ⁻¹ * nbLoc c * dZ n ζ = nbLoc (ζ⁻¹ • c) := by
  simp [dZ, nbLoc, Matrix.fromBlocks_multiply, smul_smul, mul_inv_cancel₀ h]

theorem weyl_cube_conj_unipotent (e : ℂ) (he : e * e = 1) (x : Matrix (Fin n) (Fin n) ℂ) :
    wM n e * wM n e * wM n e * nU x * wM n e = nbLoc (e • x) := by
  rw [wM_sq]
  simp [wM, nU, nbLoc, Matrix.fromBlocks_multiply, smul_smul, he]
  rw [Matrix.fromBlocks_smul]
  simp [smul_smul, he]

end Cx

end PositivityTheory.SiegelWeilFormula

end
