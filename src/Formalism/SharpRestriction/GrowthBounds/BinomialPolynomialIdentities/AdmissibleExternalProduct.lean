module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExistsIsotypicDecomposition
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProductOfHyps
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DisjointRestrictSupportOfDisjoint
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DominantOfIsHighestWeightVectorPolynomial
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.IsotypicSumInfStandardWordsOutsideEqBot
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RenameMulRenameMemSpanProductBasis
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SubProjectorProductMemStrict
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

@[expose] public section

namespace Formalism.MainNotions.G.ColumnFamilies

theorem externalProduct_basis : ExternalProductBasis := fun R _ N r K LL B => ⟨linearIndependent_productBasis R N r K LL B, span_productBasis_eq_multihomogeneous R N r K LL B⟩

theorem externalProductHyps (D : Formalism.BasicNotions.D7) : ExternalProductHyps := {
  p16 := externalProduct_basis
  e1 := determinant_divisibility
  e2 := polynomialHighestWeight_dominant D
  e3 := projectors_preserve_multidegree
  e5a := polynomialProjectors_commute_nested
  e5b := polynomialProjectors_commute_disjoint
  lowPl := restLowPl_of D (polynomialTypeSums_by_evaluation D) externalProduct_basis
  lowTan := restLowTan_of D (polynomialTypeSums_by_evaluation D) externalProduct_basis
  sum := restJointSum }

theorem admissible_externalProduct (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.PairedPathIndependence D := admissible_externalProduct_of_hyps D (externalProductHyps D)

end Formalism.MainNotions.G.ColumnFamilies
