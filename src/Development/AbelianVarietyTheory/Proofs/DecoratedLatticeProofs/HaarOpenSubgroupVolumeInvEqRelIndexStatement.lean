module

public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarOpenSubgroupVolumeInvEqRelIndex
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.haar_open_subgroup_volume_inv_eq_relIndex : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (H L : Subgroup G), H ≤ L → IsOpen (H : Set G) → IsCompact (L : Set G) → μ (L : Set G) = 1 → (μ (H : Set G)).toReal⁻¹ = (H.relIndex L : ℝ) := by
  first | exact @GlobalTheory.OpenVolIndex.measure_toReal_inv_eq_relIndex | exact GlobalTheory.OpenVolIndex.measure_toReal_inv_eq_relIndex | (intros; apply GlobalTheory.OpenVolIndex.measure_toReal_inv_eq_relIndex <;> assumption)
