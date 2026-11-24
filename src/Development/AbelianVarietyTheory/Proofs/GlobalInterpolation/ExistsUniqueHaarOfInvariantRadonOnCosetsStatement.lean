module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosets
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

@[expose] public section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

theorem _root_.GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)], IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ → ∃! dg : Measure G, dg.IsHaarMeasure ∧ QuotientFormula H dg ν μ := by
  first | exact @GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon | exact GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon | (intros; apply GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon <;> assumption)
