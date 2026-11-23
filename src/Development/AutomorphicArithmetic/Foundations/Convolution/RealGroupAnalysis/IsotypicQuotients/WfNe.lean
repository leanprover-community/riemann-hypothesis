module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.InfDec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfCusp
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
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
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfNe :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.WfNe F := by
  intro F _ _ _ π
  obtain ⟨f, hf, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨x, hx⟩ : ∃ x, Wf f.1 x ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨φ, rfl⟩ := Fb.mem_range_ofCusp.2 (π.cusp f hf)
    exact h0 (Subtype.ext (eq_zero_of_Wf φ.2 (cuspZero F π _ hf).1 hn))
  obtain ⟨g, s, k, y, hg, rfl⟩ := infDec F x
  refine ⟨TR.act (.cpt k) (TR.act (.fin y) f), π.stable _ _ (π.stable _ _ hf), g, hg, fun h => hx ?_⟩
  unfold Wf at h ⊢
  rw [← mul_zero ((ω s : ℂˣ) : ℂ), ← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  have e : ∀ z : GL (Fin 2) (A F), gl (nU b) * (Matrix.GeneralLinearGroup.scalar (Fin 2) s * z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) s * (gl (nU b) * z) := fun z => by
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Units.ext ((Matrix.scalar_commute (s : A F) (fun _ => mul_comm _ _) _).eq.symm)
  simp only
  rw [e, hω f hf, mul_assoc, ← mul_assoc (gl (nU b)), ← mul_assoc (gl (nU b))]
  rfl
