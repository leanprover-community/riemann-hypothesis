module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameWeightSingularWeightSmoothLeviNonneg
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

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.frameWeight_singularWeight_smooth_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ δ : ℝ, (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → (∀ y ∈ U, y ∉ A.zeroSet s) → SmoothR n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y) ∧ SmoothR n (fun y : U => z y) (fun y : U => psi A L s y) ∧ ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y) := by
  first | exact @GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg | exact GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg | (intros; apply GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg <;> assumption)
