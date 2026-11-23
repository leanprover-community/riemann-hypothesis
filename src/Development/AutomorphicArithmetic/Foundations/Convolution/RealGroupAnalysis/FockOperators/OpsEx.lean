module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.ContinuousPlaceEmbedReal
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XEx
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.opsEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Nonempty (Ops F) := by
  intro F _ _ _
  have hd : ∀ (w : InfinitePlace F) (i : Fin 4) (φ : S4 F), ∃ φ' : S4 F, ∀ v,
      HasDerivAt (fun t : ℝ => φ.1 (v + Pi.single i (at1 w t))) (φ'.1 v) 0 := by
    intro w i φ
    obtain ⟨φ', h, hs⟩ := dEx F w i φ.1 φ.2
    exact ⟨⟨φ', h⟩, hs⟩
  choose dd hdd using hd
  refine ⟨{
    x := fun w i =>
      { toFun := fun φ => ⟨fun v => cw w (v i) * φ.1 v, xEx F w i φ.1 φ.2⟩
        map_add' := fun φ ψ => by
          apply Subtype.ext
          funext v
          change cw w (v i) * (φ.1 v + ψ.1 v) = cw w (v i) * φ.1 v + cw w (v i) * ψ.1 v
          rw [mul_add]
        map_smul' := fun c φ => by
          apply Subtype.ext
          funext v
          change cw w (v i) * (c * φ.1 v) = c * (cw w (v i) * φ.1 v)
          rw [mul_left_comm] }
    d := fun w i =>
      { toFun := dd w i
        map_add' := fun φ ψ => by
          apply Subtype.ext
          funext v
          have h1 := (hdd w i φ v).add (hdd w i ψ v)
          exact (hdd w i (φ + ψ) v).unique h1
        map_smul' := fun c φ => by
          apply Subtype.ext
          funext v
          have h1 := (hdd w i φ v).const_mul c
          exact (hdd w i (c • φ) v).unique h1 }
    x_apply := fun w i φ v => rfl
    d_spec := fun w i φ v => hdd w i φ v }⟩
