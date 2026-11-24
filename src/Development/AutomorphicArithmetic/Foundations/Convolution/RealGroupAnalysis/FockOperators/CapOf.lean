module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CapLam
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.LamEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), (∀ O, LieLift O W M π) → (∀ O, MoveE O W M π) → St.Cap W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h1 h2 τ m hm u Φ hΦ
  obtain ⟨O⟩ := opsEx F
  obtain ⟨Λ, hΛ⟩ := lamEx F E D W M π
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, hf, φ, hφ, e⟩ := h
    obtain rfl : Φ = Λ f φ := Subtype.ext (e.trans (hΛ f hf φ hφ).symm)
    rw [capLam F E D W M π O Λ hΛ (h1 O) (h2 O) τ u f hf φ hφ]
    have := hm.2 u f hf
    rw [show pl F τ = InfinitePlace.mk (τ.comp (algebraMap F E)) from rfl, this, map_smul, LinearMap.smul_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]
