module

public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmFourteen
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProduct
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissiblePolynomialBasisProv
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleWordBasis
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths
public import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
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

open Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.G.GLWeightTheory

theorem splitting_third_part_holds (D : Formalism.BasicNotions.D7) : DefiniteRankOne D := by
  intro p _ O _ _ _ _ N n _ LL B th M
  exact ⟨lemma_A3_over_domain LL B D word_valuation_bounds (valuation_field D).1 (admissible_standardPath_basis D) (admissible_word_basis D) O th M,
    lemma_A3_over_field LL B D word_valuation_bounds (valuation_field D).1 (admissible_standardPath_basis D) (admissible_word_basis D) (Formalism.MainNotions.G.FF O) th M⟩

theorem splitting_package_holds (D : Formalism.BasicNotions.D7) : Conclusion2 D :=
  ⟨automorphicSideConclusion_of_pathBasis D (admissible_standardPath_basis D), splitting_third_part_holds D, prvB1_of_D7 D, lemma_B2 D,
    nested_sets_lemma_of_admitted D (adm_fourteen D) (admissible_externalProduct D), coefficientDependence D, canonical_translate_jet_identity D⟩

end Formalism.MainNotions.G.ColumnFamilies
