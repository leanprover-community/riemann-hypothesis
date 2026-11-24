module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationBoundDetPowerFactor
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedModuleWeightLemmaOfInterfaces
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.LaurentDegreesSubstitutionSubset
import Formalism.SharpRestriction.GrowthBounds.RootWeights.SpecialiseGenericMatrixInverse
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.SumFinsuppAntidiagEqSumPiFinset
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightEntryRestrictionMem
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

noncomputable section

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem generated_module_weight_lemma_part_b : GeneratedModuleWeightDescription :=
  generated_module_weight_lemma_of_interfaces transvectionExpansion torus_acts_through_weight binomial_stable_contains_components twist_exponents_are_weight_entries generic_monomials_specialise

theorem valuationsAdditive_D7 (D : Formalism.BasicNotions.D7) : ValuationsAdditive D := valuations_additive_of_generated_weight_description D generated_module_weight_lemma_part_b

end Formalism.MainNotions.G.GLWeightTheory
