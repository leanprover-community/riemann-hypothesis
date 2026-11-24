module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.HeckeFixedSplitPlace
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.HeckeVecFst
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.SatakeConjugateInverse
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.TjZeroAct
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

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.satRead₂ :
    UpperTheory.Zero.ConvolutionTheory.EB.SatRead₂ := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ f hf _ hL _ w hw hwZ hs t ht
  have h := hkAct E a b l₁ l₂ D A S Z L hS hZ f hL w hw hwZ
  obtain ⟨B₁, B₂, h1, h2, h3, h4⟩ := sat2Ex E a b w _ _ (pairRtT a b w) f t hf (fun i => ((h 0 i).2 hs).1)
    fun p i => (((h p i).2 hs).2).symm.trans (congrFun (ht p) i)
  have hi : ∀ B, inv (inv B) = B := fun B => by simp [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv, Multiset.map_map]
  refine ⟨inv B₁, inv B₂, by simpa [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv] using h1, by simpa [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv] using h2, by simpa only [hi] using h3, ?_, ?_⟩
  · rintro φ ⟨i, m, e⟩
    exact (sat2Slice E a b _ _ _ _ (sat2Back E a b w _ _ _ hs (h4 i))).1 φ m e
  · rintro φ ⟨i, m, e⟩
    exact (sat2Slice E a b _ _ _ _ (sat2Back E a b w _ _ _ hs (h4 i))).2 φ m e
