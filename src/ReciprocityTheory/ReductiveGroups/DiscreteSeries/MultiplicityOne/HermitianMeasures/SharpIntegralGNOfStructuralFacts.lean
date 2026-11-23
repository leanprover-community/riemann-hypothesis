module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem nRecHaar_of_structural_facts (h : UnitaryGroupStructuralFacts) : NRecHaar := by
  exact h.1.2.2.2.1
theorem nilpotent_basis_of_hypotheses (h : UnitaryGroupStructuralFacts) : NBase := by
  exact h.1.2.2.2.2.1
theorem compact_unitary_of_hypotheses (h : UnitaryGroupStructuralFacts) : CompactW := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem norm_lower_bound_of_hypotheses (h : UnitaryGroupStructuralFacts) : GNLower := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem haar_unique_of_hypotheses (h : UnitaryGroupStructuralFacts) : HaarUnique := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem closedN_of_structural_facts (h : UnitaryGroupStructuralFacts) : ClosedN := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem closed_unitary_of_hypotheses (h : UnitaryGroupStructuralFacts) : ClosedW := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem exists_haar_W_of_structural_facts (h : UnitaryGroupStructuralFacts) : HaarWExists := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem haar_exists_nilpotent_of_hypotheses (h : UnitaryGroupStructuralFacts) : HaarNExists := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
