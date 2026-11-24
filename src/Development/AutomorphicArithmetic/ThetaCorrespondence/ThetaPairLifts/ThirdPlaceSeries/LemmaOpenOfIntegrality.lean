module

public import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceAnnihilatesCharacterPart
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePrimeLemmasTheorem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisConditionFourOf
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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



section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory
theorem lemma_open_of_integrality_alt (D : D7) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) : TypePrimeCongruences.CongruenceModules.SupplierRemainingLemmas D :=
  fun i _ _ _ r ρ hr =>
    ⟨LargeLevelLemmas.span_lemma_clause i r (_root_.Formalism.MainNotions.N.galois_condition_one_of_alt D i r h41 hr),
      fun π _ _ => ⟨LargeLevelLemmas.eigenspace_lemma_clause i r ρ π, LargeLevelLemmas.relation_lemma_clause i r ρ π⟩⟩
theorem typePrimeCongruences_forall : ∀ D : D7, _root_.Formalism.MainNotions.TypePrimeCongruences.TypePrimeLemmasStatement D :=
  fun D hA => TypePrimeCongruences.CongruenceModules.supplier_of_choice_and_lemmas D hA.2.2.2 (_root_.GlobalTheory.lemma_open_of_integrality_alt D hA.2.1)
end GlobalTheory
end
