module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Pointwise

private theorem iwCoset_eq_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    iwCoset w ν = ((GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) *
        ({Cartan.diagPow (w.adicCompletion K) n ν} : Set (Gw n w))) *
      (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Set.mul_mem_mul (Set.mul_mem_mul ha rfl) hb
  · rintro ⟨x, ⟨a, ha, d, rfl, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

private theorem isOpen_iwCoset {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    IsOpen (iwCoset w ν) := by
  rw [iwCoset_eq_mul]
  exact (GLnLocal.isOpen_iwahori (w.adicCompletion K) n).mul_left

private theorem isCompact_iwCoset {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    IsCompact (iwCoset w ν) := by
  rw [iwCoset_eq_mul]
  have hI := GLnLocal.isCompact_iwahori (w.adicCompletion K) n
  exact (hI.mul isCompact_singleton).mul hI

theorem UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K),
        CO (GLnLocal.iwahori (w.adicCompletion K) n) ∧
        (∀ U : Subgroup (Gw n w), IsOpen (U : Set (Gw n w)) → U ≤ GLnLocal.integralGL (w.adicCompletion K) n → CO U) ∧
        ∀ ν : Fin n → ℤ, Test ((iwCoset w ν).indicator 1 : Gw n w → ℂ) ∧
          ∀ u ∈ GLnLocal.iwahori (w.adicCompletion K) n, ∀ g : Gw n w,
            (iwCoset w ν).indicator (1 : Gw n w → ℂ) (u * g) = (iwCoset w ν).indicator (1 : Gw n w → ℂ) g := by
  intro K _ _ n w
  refine ⟨⟨GLnLocal.isCompact_iwahori _ n, GLnLocal.isOpen_iwahori _ n⟩, ?_, ?_⟩
  · intro U ho hle
    exact ⟨(GLnLocal.isCompact_integralGL _ n).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ ho) hle, ho⟩
  · intro ν
    have hc := isCompact_iwCoset w ν
    have hclopen : IsClopen (iwCoset w ν) := ⟨hc.isClosed, isOpen_iwCoset w ν⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact ((LocallyConstant.const (Gw n w) (1 : ℂ)).indicator hclopen).isLocallyConstant
    · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _
    · intro u hu g
      have hiff : u * g ∈ iwCoset w ν ↔ g ∈ iwCoset w ν := by
        constructor
        · rintro ⟨a, ha, b, hb, h⟩
          refine ⟨u⁻¹ * a, mul_mem (inv_mem hu) ha, b, hb, ?_⟩
          calc g = u⁻¹ * (u * g) := (inv_mul_cancel_left u g).symm
            _ = _ := by rw [h]; simp only [mul_assoc]
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨u * a, mul_mem hu ha, b, hb, by simp only [mul_assoc]⟩
      by_cases hg : g ∈ iwCoset w ν
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg)]
        rfl
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hiff.1 h))]
