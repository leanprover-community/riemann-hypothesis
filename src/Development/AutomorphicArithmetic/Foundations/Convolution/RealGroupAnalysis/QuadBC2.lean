module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Cap
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.DatEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Exp
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsExtra
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsFurther
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsSide
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTail
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.MeasEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.WeilEx
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
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.quadBC2 : UpperTheory.V.Z.Bc.QuadBC2 := by
  intro F E _ _ _ _ _ _ _ h2 π hreg
  obtain ⟨D⟩ := datEx F E h2
  obtain ⟨W⟩ := weilEx F E D
  obtain ⟨M⟩ := measEx F
  by_cases h0 : ThetaLiftTrivialOrbitTermsVanish W M π
  · right
    have hne : span W M π ≠ ⊥ := by
      obtain ⟨f, hf, φ, hφ, h, hW⟩ := ne F E D W M π
      obtain ⟨Φ, hΦ⟩ := smooth F E D W M π f hf φ hφ
      intro hb
      have hm : Φ ∈ span W M π := Submodule.subset_span ⟨f, hf, φ, hφ, hΦ⟩
      rw [hb, Submodule.mem_bot] at hm
      apply hW
      rw [← exp F E D W M π f hf φ hφ h, ← hΦ, hm]
      simp [WE]
    obtain ⟨P, hP⟩ := irr F E D W M π hreg h0 hne
    exact ⟨P, fun τ m hm => ⟨hm.1, fun u Φ hΦ => cap F E D W M π τ m hm u Φ (hP hΦ)⟩,
      split F E D W M π h0 P hP, unr F E D W M π h0 P hP⟩
  · exact Or.inl ⟨W.η, W.quad, dih F E D W M π hreg h0⟩
