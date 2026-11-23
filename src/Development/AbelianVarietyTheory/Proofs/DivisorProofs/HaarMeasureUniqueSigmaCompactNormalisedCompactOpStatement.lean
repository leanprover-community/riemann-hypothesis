module

public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureUniqueSigmaCompactNormalisedCompactOp
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich

@[expose] public section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.haarMeasure_unique_sigmaCompact_normalised_compactOpen : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (K : ℕ → Set G), (∀ j, IsCompact (K j) ∧ MeasurableSet (K j)) → (⋃ j, K j) = Set.univ →
    ∀ (s : Set G) (c : ENNReal), IsOpen s → IsCompact s → s.Nonempty → ν s = c * μ s → ν = c • μ := by
  first | exact @GlobalTheory.haar_unique_of_sigmaCompact_normalised | exact GlobalTheory.haar_unique_of_sigmaCompact_normalised | (intros; apply GlobalTheory.haar_unique_of_sigmaCompact_normalised <;> assumption)
