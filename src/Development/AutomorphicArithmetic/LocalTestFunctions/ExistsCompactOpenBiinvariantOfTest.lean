module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_compactOpen_biinvariant_of_test :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K) (φ : Gw n w → ℂ), Test φ →
          ∃ J : Subgroup (Gw n w), CO J ∧ J ≤ GLnLocal.integralGL (w.adicCompletion K) n ∧ ∀ k ∈ J, ∀ x, φ (k * x) = φ x ∧ φ (x * k) = φ x := by
  intro K _ _ n w φ hφ
  obtain ⟨U, hU, hf⟩ := GlobalTheory.Orb.exists_biinvariant (G := Gw n w) (f := φ) ⟨hφ.1, hφ.2⟩
  refine ⟨U ⊓ GLnLocal.integralGL (w.adicCompletion K) n, ⟨?_, ?_⟩, inf_le_right,
    fun k hk x => hf k hk.1 x⟩
  · rw [Subgroup.coe_inf]
    exact (GLnLocal.isCompact_integralGL (w.adicCompletion K) n).inter_left
      (U.isClosed_of_isOpen hU)
  · rw [Subgroup.coe_inf]
    exact hU.inter (GLnLocal.isOpen_integralGL (w.adicCompletion K) n)
