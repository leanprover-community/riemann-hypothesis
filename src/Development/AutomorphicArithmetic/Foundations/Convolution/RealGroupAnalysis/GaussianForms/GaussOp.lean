module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.FtBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuadraticFormShiftExpand
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuaternaryFormUnitScaling
import GroundTheory.AutomorphicForms.ReductionMeasure
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Compactness.Paracompact

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem quadraticForm_neg (δ : F) (y : V4 F) : q4 δ (-y) = q4 δ y := by
  simp only [q4, Pi.neg_apply]
  ring

private theorem quaternaryForm_neg_right (δ : F) (y v : V4 F) : B4 δ (-y) (-v) = B4 δ y v := by
  simp only [B4, Pi.neg_apply]
  ring

theorem UpperTheory.ConvolutionTheory.R2.C.gaussOp :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ (b : (A F)ˣ) (c : ℂ), IsIdx δ (b : A F) c → ∀ (φ : S4 F) (v : V4 F),
    Pc δ (b : A F) φ.1 v = c * ft4 δ (fun y => ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 y) v := by
  intro F _ _ δ hδ b c hc φ v
  have hmem := (pcMem F δ).2 hδ b φ.1 φ.2
  have h2 := (ftBasic F δ hδ _ hmem).2.1 (-v)
  rw [neg_neg] at h2
  rw [← h2]
  have e1 : ∀ y, ft4 δ (Pc δ (b : A F) φ.1) y * ψ (B4 δ y (-v)) =
      c * ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 (-y) * ψ (B4 δ y (-v)) := fun y => by
    rw [idxFt F δ b c hc φ y]
  conv_lhs => rw [ft4]
  simp only [e1]
  rw [← integral_neg_eq_self _ (adeleMeasurePi F)]
  simp only [neg_neg, quadraticForm_neg, quaternaryForm_neg_right]
  rw [ft4, ← integral_const_mul]
  congr 1
  funext y
  ring
