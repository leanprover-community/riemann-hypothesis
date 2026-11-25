module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
open scoped Matrix.Norms.Elementwise
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem translations_strongly_continuous :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
      (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod →
      ∀ x : Lp V 2 μ, Continuous (fun h : G n => rR μ V h x) ∧
        Continuous (fun y : G n => lT μ V y x) := by
  intro n _ _ μ _ V _ _ _ hU x
  have := (hU n μ).1
  constructor
  · let g : G n → C(G n, G n) := fun h => ⟨fun y => y * h, continuous_id.mul continuous_const⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.mul continuous_fst)
    have hm : ∀ h, MeasurePreserving (g h) μ μ := fun h => measurePreserving_mul_right μ h
    have key := Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    refine key.congr fun h => ?_
    have hm' : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
    simp only [rR, dif_pos hm']
    rfl
  · let g : G n → C(G n, G n) := fun y => ⟨fun z => y⁻¹ * z, continuous_const.mul continuous_id⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.inv.mul continuous_snd)
    have hm : ∀ y, MeasurePreserving (g y) μ μ := fun y => measurePreserving_mul_left μ y⁻¹
    have key := Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    exact key

end GlobalTheory.CompanionTheory.PresSobA
