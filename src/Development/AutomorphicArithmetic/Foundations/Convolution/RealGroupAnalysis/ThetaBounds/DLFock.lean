module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OpsFock
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
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.dLFock :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (Y : Lie E 2), ∀ φ ∈ Fock D.δ, O.dL D Y φ ∈ Fock D.δ := by
  intro F E _ _ _ _ _ _ _ D O Y φ hφ
  let S : Subalgebra ℂ (Module.End ℂ (S4 F)) :=
    { carrier := {z | ∀ φ ∈ Fock D.δ, z φ ∈ Fock D.δ}
      mul_mem' := fun hx hy φ h => hx _ (hy φ h)
      add_mem' := fun hx hy φ h => add_mem (hx φ h) (hy φ h)
      algebraMap_mem' := fun c φ h => Submodule.smul_mem _ c h }
  have hx : ∀ w i, O.x w i ∈ S := fun w i ψ hψ => (opsFock F E D O w i ψ hψ).1
  have hd : ∀ w i, O.d w i ∈ S := fun w i ψ hψ => (opsFock F E D O w i ψ hψ).2
  have hX : ∀ τ a b, O.X D τ a b ∈ S := fun τ a b => by
    fin_cases a <;> fin_cases b
    · exact hx _ _
    · exact add_mem (hx _ _) (S.smul_mem (hx _ _) _)
    · exact sub_mem (hx _ _) (S.smul_mem (hx _ _) _)
    · exact hx _ _
  have hD : ∀ τ a b, O.DX D τ a b ∈ S := fun τ a b => by
    fin_cases a <;> fin_cases b
    · exact hd _ _
    · exact S.smul_mem (add_mem (hd _ _) (S.smul_mem (hd _ _) _)) _
    · exact S.smul_mem (sub_mem (hd _ _) (S.smul_mem (hd _ _) _)) _
    · exact hd _ _
  refine (?_ : O.dL D Y ∈ S) φ hφ
  refine sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ => S.smul_mem (sub_mem (neg_mem ?_) ?_) _
  · split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact sum_mem fun b _ => mul_mem (hX _ _ _) (hD _ _ _)
