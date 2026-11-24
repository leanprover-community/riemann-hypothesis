module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNeZeroOfResidueNeZero
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CoarseLabelFactorisation
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantMultihomogeneous
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrobeniusReductionProduct
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LateVectorsDistinctTops
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SegmentProductDegreeDetermined
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ThresholdPowerBoundOfCounts
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopDegreeComparison
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopOccursInAtMostTwoSegments
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.WordOrderBoundOfNumericBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AllowedLettersOfLateRows
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroOfInjectiveTops
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopCountLowerBoundsOfOccurrence

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem discriminant_nonzero_mod_uniformiser : DiscriminantNonzeroModUniformiser := discriminant_nonzero_of_injective_tops late_vectors_distinct_tops

theorem generator_modulo_uniformiser_of_adm (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) (hC : 32 ≤ C₀) : GeneratorModuloUniformiser C₀ := by
  have hV1 : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D := hAdm.2.2.2.2.2.2.2.1.1
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  have hB12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have h41b : TopCountLowerBounds C₀ := top_count_lower_bounds_of_occurrence C₀ hC top_occurs_in_at_most_two_segments
  have hW3 := column_conditions_of_numeric_bounds D hV1 hA3 C₀ late_row_injective ell_degree_le_power_bound (power_exceeds_max_multiplicity C₀) (threshold_power_bound_of_counts C₀ h41b oldest_letter_in_segment)
  have hW4 := word_order_bound_of_numeric_bound D hA3 C₀ late_row_injective (order_numeric_bound_of_oldest C₀ oldest_letter_in_segment)
  have hW2 := allowed_letters_of_late_rows D hA3 C₀ late_row_injective
  have hWord := column_word_reduction_of_four D hB12 C₀ (frobenius_reduction_product C₀) hW2 hW3 hW4
  exact generator_of_segment_reductions C₀ coarse_label_factorisation top_degree_comparison discriminant_multihomogeneous (discriminant_ne_zero_of_residue_ne_zero discriminant_nonzero_mod_uniformiser) h41b (segment_reduction_of_column_words D hB12 C₀ hWord)
    segment_image_multihomogeneous segment_product_degree_determined

theorem top_count_lower_bounds (C₀ : ℝ) (hC : 32 ≤ C₀) : TopCountLowerBounds C₀ := top_count_lower_bounds_of_occurrence C₀ hC top_occurs_in_at_most_two_segments

end Formalism.MainNotions.SelectionLemmas.Pf
