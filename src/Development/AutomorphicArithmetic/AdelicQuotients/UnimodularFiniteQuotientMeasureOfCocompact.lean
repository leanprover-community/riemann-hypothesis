module

public import GroundTheory.AutomorphicForms.QuotientMeasure
public import GroundTheory.AutomorphicForms.TraceFormulaWeil
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.unimodular_finite_quotientMeasure_of_cocompact :
    ∀ (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (Λ : Subgroup T) [DiscreteTopology Λ] (ν : Measure T) [ν.IsHaarMeasure],
        (∃ C : Set T, IsCompact C ∧ ∀ t : T, ∃ g ∈ Λ, ∃ y ∈ C, t = g * y) →
        ν.IsMulRightInvariant ∧ ν.IsInvInvariant ∧ quotientMeasure Λ ν Set.univ < ⊤ := by
  intro T _ _ _ _ _ _ _ _ Λ _ ν _ hC
  obtain ⟨C, hC, h⟩ := hC
  haveI : CompactSpace (RightCosetSpace Λ) := by
    refine ⟨(hC.image (RightCosetSpace.continuous_mk Λ)).of_isClosed_subset isClosed_univ ?_⟩
    intro x _
    obtain ⟨t, rfl⟩ := RightCosetSpace.mk_surjective Λ x
    obtain ⟨g, hg, y, hy, rfl⟩ := h t
    exact ⟨y, hy, (RightCosetSpace.mk_mul_of_mem hg y).symm⟩
  haveI hr : ν.IsMulRightInvariant := RightCosetSpace.isMulRightInvariant_of_compactSpace Λ ν
  haveI := RightCosetSpace.isFiniteMeasure (Γ := Λ) ν
  exact ⟨hr, ⟨RightCosetSpace.inv_eq_self_of_isMulRightInvariant ν⟩, measure_lt_top _ _⟩
