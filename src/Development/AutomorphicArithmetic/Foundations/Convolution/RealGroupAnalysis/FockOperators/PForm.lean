module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PsiShift
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private lemma p_form {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F) (δ : F)
    (w : InfinitePlace F) (i : Fin 4) : ∃ (c : ℂ) (k : Fin 4), O.p δ w i = c • O.x w k := by
  fin_cases i
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

private lemma p_comm {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F) (δ : F)
    (w w' : InfinitePlace F) (i j : Fin 4) :
    O.p δ w i * O.p δ w' j = O.p δ w' j * O.p δ w i := by
  obtain ⟨c, k, h⟩ := p_form O δ w i
  obtain ⟨c', k', h'⟩ := p_form O δ w' j
  have hx : O.x w k * O.x w' k' = O.x w' k' * O.x w k := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    change (O.x w k (O.x w' k' φ)).1 v = (O.x w' k' (O.x w k φ)).1 v
    rw [O.x_apply, O.x_apply, O.x_apply, O.x_apply, mul_left_comm]
  rw [h, h']
  simp only [smul_mul_smul, hx, mul_comm c c']

theorem UpperTheory.ConvolutionTheory.R2.Fo.dComm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w w' i j, O.d w i * O.d w' j = O.d w' j * O.d w i := by
  intro F E _ _ _ _ _ _ _ D W O w w' i j
  have hinv : W.Om (wW F) * W.Om (wW F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have key : O.d w i * O.d w' j * W.Om (wW F) = O.d w' j * O.d w i * W.Om (wW F) := by
    calc O.d w i * O.d w' j * W.Om (wW F)
        = O.d w i * (O.d w' j * W.Om (wW F)) := mul_assoc _ _ _
      _ = O.d w i * (W.Om (wW F) * O.p D.δ w' j) := congrArg (O.d w i * ·) (dW F E D W O w' j)
      _ = (O.d w i * W.Om (wW F)) * O.p D.δ w' j := (mul_assoc _ _ _).symm
      _ = (W.Om (wW F) * O.p D.δ w i) * O.p D.δ w' j := congrArg (· * O.p D.δ w' j) (dW F E D W O w i)
      _ = W.Om (wW F) * (O.p D.δ w i * O.p D.δ w' j) := mul_assoc _ _ _
      _ = W.Om (wW F) * (O.p D.δ w' j * O.p D.δ w i) := by rw [p_comm O D.δ w w' i j]
      _ = (W.Om (wW F) * O.p D.δ w' j) * O.p D.δ w i := (mul_assoc _ _ _).symm
      _ = (O.d w' j * W.Om (wW F)) * O.p D.δ w i := congrArg (· * O.p D.δ w i) (dW F E D W O w' j).symm
      _ = O.d w' j * (W.Om (wW F) * O.p D.δ w i) := mul_assoc _ _ _
      _ = O.d w' j * (O.d w i * W.Om (wW F)) := congrArg (O.d w' j * ·) (dW F E D W O w i).symm
      _ = O.d w' j * O.d w i * W.Om (wW F) := (mul_assoc _ _ _).symm
  calc O.d w i * O.d w' j
      = O.d w i * O.d w' j * (W.Om (wW F) * W.Om (wW F)⁻¹) := by rw [hinv, mul_one]
    _ = O.d w i * O.d w' j * W.Om (wW F) * W.Om (wW F)⁻¹ := (mul_assoc _ _ _).symm
    _ = O.d w' j * O.d w i * W.Om (wW F) * W.Om (wW F)⁻¹ := by rw [key]
    _ = O.d w' j * O.d w i * (W.Om (wW F) * W.Om (wW F)⁻¹) := mul_assoc _ _ _
    _ = O.d w' j * O.d w i := by rw [hinv, mul_one]
