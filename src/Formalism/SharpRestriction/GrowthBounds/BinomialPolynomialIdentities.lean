module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissiblePolynomialBasisProv
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleWordBasis
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ToralGalois
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmFourteen
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleLowerSetSpan
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProduct
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LatticeGeneratedLowestWeight
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SplittingThirdPartHolds
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.BrCore
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

namespace Formalism.MainNotions.G.ColumnFamilies.Top

open Formalism.MainNotions.CovariantDegrees

theorem b9 (D : Formalism.BasicNotions.D7) : GlobalSectionsSchur D := global_sections_schur D
theorem b10 (D : Formalism.BasicNotions.D7) : BracketPolynomialSpan D := bracket_polynomial_span D
theorem b11 (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := adm_eleven D
theorem b15 (D : Formalism.BasicNotions.D7) : SaturatedLowerSetSpan D := admissible_lowerSet_span D
theorem b19 (D : Formalism.BasicNotions.D7) : WeylDualityLattice D := admissible_lattice_biduality D
theorem a2 (D : Formalism.BasicNotions.D7) : PathColumnBasis D := admissible_polynomial_basis D

end Formalism.MainNotions.G.ColumnFamilies.Top
