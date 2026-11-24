module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.fixTr :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K) (f : GL (Fin 2) (A K) → ℂ) (d : GL (Fin 2) (A K)), KAt v d →
      (Fix v f → Fix v fun g => f (g * d)) ∧ ∀ B, EigAt v B f → EigAt v B fun g => f (g * d) := by
  intro K _ _ v f d hd
  have hl := (lcLaws K v).2.2.2.2.2.2 d
  set x := Matrix.GeneralLinearGroup.map (cp v) d with hx
  have hd' : x ∈ GlobalTheory.LFun.KGL v (n := 2) := hd
  refine ⟨fun hf g k hk => ?_, fun B hB g => ?_⟩
  · show f (g * lc v k * d) = f (g * d)
    rw [mul_assoc, hl, ← mul_assoc, hf _ _ (mul_mem (mul_mem (inv_mem hd') hk) hd')]
  · have h := hB (g * d * lc v x⁻¹)
    convert h using 2 with y
    have h1 := h.inv y x hd'
    show f (g * lc v y * d) = f (g * d * lc v x⁻¹ * lc v y)
    change f (g * d * lc v x⁻¹ * lc v (y * x)) = f (g * d * lc v x⁻¹ * lc v y) at h1
    rw [← h1, mul_assoc g, hl, mul_assoc x⁻¹, map_mul]
    simp only [mul_assoc]
