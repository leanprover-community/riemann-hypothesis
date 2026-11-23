module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartLeviThGe

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential HoloMap)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe (compat_chart levi_base_indep)

noncomputable section

def C2ConvOn {E : ℕ} {Z : Type} [TopologicalSpace Z] (A : FinHolAtlas E Z) (V : Set Z)
    (g : ℝ → Z → ℝ) (φ : Z → ℝ) : Prop :=
  ∀ (k : Fin A.n) (K : Set (Fin E → ℂ)), IsCompact K →
    K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V →
    TendstoUniformlyOn (fun t y => g t ((A.chart k).symm y)) (fun y => φ ((A.chart k).symm y))
        (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fderiv ℝ fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fderiv ℝ fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K

def C2ConvergencePullback.Statement : Prop :=
  ∀ {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (B : FinHolAtlas D Y)
    (A : FinHolAtlas E Z) (f : Y → Z), HoloMap B A f →
    ∀ (V : Set Z), IsOpen V → ∀ (g : ℝ → Z → ℝ) (φ : Z → ℝ) (φ' : Y → ℝ),
      A.SmoothOn V φ → (∀ y ∈ f ⁻¹' V, φ' y = φ (f y)) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (g t)) →
      C2ConvOn A V g φ → C2ConvOn B (f ⁻¹' V) (fun t => g t ∘ f) φ'

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
