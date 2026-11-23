module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.sgnEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ a : (A F)ˣ, IsSgn a ∧ a * a = 1 ∧ ab a = 1 := by
  intro F _ _ _
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set s : TR.Rinf F := fun w => if w = w₀ then -1 else 1 with hs
  have hss : s * s = 1 := by
    funext w
    by_cases h : w = w₀ <;> simp [hs, h]
  have hx : ((TR.infEq F s, 1) : A F) * (TR.infEq F s, 1) = 1 := by
    have h1 : TR.infEq F s * TR.infEq F s = 1 := by rw [← map_mul, hss, map_one]
    exact Prod.ext h1 (mul_one _)
  let a : (A F)ˣ := ⟨(TR.infEq F s, 1), (TR.infEq F s, 1), hx, hx⟩
  have haa : a * a = 1 := Units.ext hx
  refine ⟨a, ⟨rfl, w₀, fun w => ?_⟩, haa, ?_⟩
  · change (TR.infEq F).symm (TR.infEq F s) w = _
    rw [RingEquiv.symm_apply_apply]
  · have h1 : IdeleGroup.ideleModule F (a * a) = 1 := by rw [haa, map_one]
    rw [map_mul] at h1
    have h2 : ab a * ab a = 1 := by
      have := congrArg (fun r : {r : ℝ // 0 < r} => (r : ℝ)) h1
      simpa [ab] using this
    have h3 : 0 < ab a := (IdeleGroup.ideleModule F a).2
    nlinarith
