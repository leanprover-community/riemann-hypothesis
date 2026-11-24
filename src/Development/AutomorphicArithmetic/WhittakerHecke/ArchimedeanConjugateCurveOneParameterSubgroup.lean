module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem nC_zero' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : nC (0 : Cinf E) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nC]

private theorem nC_add' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : Cinf E) :
    nC (a + b) = nC a * nC b := by
  apply Units.ext
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [nC, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem nC_val' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (t : ℝ) (z : Cinf E) :
    (nC (t • z)).val = 1 + t • (!![0, z; 0, 0] : Matrix (Fin 2) (Fin 2) (Cinf E)) := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [nC]

private theorem cv_val' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E)
    (k : GL (Fin 2) (A E)) (t : ℝ) : (cv D k t).val = 1 + t • XB D k := by
  have h : ((kInf k)⁻¹).val * (kInf k).val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [cv, XB, Units.val_mul, nC_val', mul_add, add_mul, mul_one, h, Matrix.mul_smul, Matrix.smul_mul]

theorem UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (k : GL (Fin 2) (A E)),
        cv D k 0 = 1 ∧ (∀ s t, cv D k (s + t) = cv D k s * cv D k t) ∧ HasDerivAt (fun t => toL (cv D k t).val) (toL (XB D k)) 0 ∧
        Continuous fun k : GL (Fin 2) (A E) => toL (XB D k) := by
  intro E _ _ _ D k
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cv, nC_zero']
  · intro s t
    simp only [cv, add_smul, nC_add']
    group
  · have h : (fun t : ℝ => toL (cv D k t).val) =
        fun t : ℝ => toL (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) + t • toL (XB D k) := by
      funext t
      rw [cv_val']
      rfl
    rw [h]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (XB D k))).const_add
      (toL (1 : Matrix (Fin 2) (Fin 2) (Cinf E)))
  · have hK : Continuous fun k : GL (Fin 2) (A E) => kInf k := ContAut.continuous_map_pInf E 2
    have h1 : Continuous fun k : GL (Fin 2) (A E) => (kInf k).val := Units.continuous_val.comp hK
    have h2 : Continuous fun k : GL (Fin 2) (A E) => ((kInf k)⁻¹).val :=
      Units.continuous_val.comp hK.inv
    exact (h2.matrix_mul continuous_const).matrix_mul h1
