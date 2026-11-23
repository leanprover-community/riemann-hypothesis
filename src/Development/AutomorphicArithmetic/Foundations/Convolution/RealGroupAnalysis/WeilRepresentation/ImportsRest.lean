module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.FromGL
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RedDet
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
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.red :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], St.Red F := by
  intro F _ _ _
  obtain ⟨t₀, ht₀, h⟩ := Reduction.exists_reduced (K := F)
  refine ⟨Real.sqrt t₀, Real.sqrt_pos.2 ht₀, fun g => ?_⟩
  obtain ⟨γ, b, hb, k, hk, he, hr⟩ := h 2 (gl g)
  obtain ⟨γ', b', hb', he', h0, h1⟩ := M.redDet F g γ b hb k he
  obtain ⟨x, a, k', hk', hg, ha, ha'⟩ := M.fromGL F (ratS F γ' * g) b' hb' k hk he'
  refine ⟨γ', x, a, k', hk', hg, ?_⟩
  have := hr 0 1 rfl
  rw [← h1, ← h0, ha', ← ha, Reduction.adeleAbs_units] at this
  change t₀ * (ab a)⁻¹ ≤ ab a at this
  have hp := M.ab_pos a
  rw [mul_inv_le_iff₀ hp] at this
  exact Real.sqrt_le_iff.2 ⟨hp.le, by rwa [pow_two]⟩
