module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsRetractionBasis
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudADef
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TheoremIOfLatticeFunctorComparison
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudA
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudB
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudC
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIso
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfWtPQCast
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem cloud_maps_of_contraction (hQ : ContractionStandardLattice) (hCD : CartanDomain) (hCO : CartanOnto) (hIncl : DualHeightInclusion) : RestCloudMaps :=
  restCloudMaps_of (restCloudLat_of (cloudOne_of hQ) hCO (cloudIso hCD hCO)) hIncl

theorem theorem_I_of_two_letter_clauses_contraction (D : Formalism.BasicNotions.D7) (h1 : ExplicitMapInjective) (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hQ : ContractionStandardLattice) : SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h11 : GradedLatticeStable D := hT.2.2.2.2.2.2.1
  have h13 : TypeDecompositionsCommute D := hT.2.2.2.2.2.2.2.2.1
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  exact theorem_I_of_explicit_minor_map D (tiePsi_of D h1 h2 h5 h11.2 h16.1) (cloud_maps_of_contraction hQ h11.1 h11.2 h13.2.1) hA

end Formalism.MainNotions.flipOneThree.Pf
