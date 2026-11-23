module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.EqOfBelowSelf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
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
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.splt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (w : P E) (i : Kv v ≃+* Kv w), Continuous i →
      (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
      ∃ θ : Kv v, Splt D v θ ((lc w).comp (Matrix.GeneralLinearGroup.map i.toRingHom)) := by
  intro F E _ _ _ _ _ D v w i hc hal
  obtain ⟨θ, hsq, hne, hk⟩ := UpperTheory.ConvolutionTheory.R2.I.place F E D v w i hc hal
  obtain ⟨-, -, -, -, hlc, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws E w
  have hone : ∀ a b : Fin 2, i ((1 : Matrix (Fin 2) (Fin 2) (Kv v)) a b) =
      (1 : Matrix (Fin 2) (Fin 2) (Kv w)) a b := by
    intro a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨θ, hsq, hne, ?_, ?_⟩
  · intro x a b
    have e : (Matrix.GeneralLinearGroup.map i.toRingHom x).val a b = i (x.val a b) := rfl
    change (lc w (Matrix.GeneralLinearGroup.map i.toRingHom x)).val a b = _
    rw [hlc, e, ← hone, ← map_sub, hk]
  · intro x
    exact ⟨locGL E 2 w (Matrix.GeneralLinearGroup.map i.toRingHom x), rfl⟩
