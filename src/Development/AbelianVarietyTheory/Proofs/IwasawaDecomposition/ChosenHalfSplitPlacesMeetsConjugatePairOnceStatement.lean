module

public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChosenHalfSplitPlacesMeetsConjugatePairOnce
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.chosenHalf_splitPlaces_meets_conjugatePair_once : ∀ (D : D7) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), (∀ v, NG.OverPl (Pq v) v) →
    ∀ S : Finset (PlE D.host), (∀ P ∈ S, IsSplitPl D.host P) →
    (∀ P ∈ S, ∃ P' ∈ qpOf D Pq S, P' = P ∨ IsConjPl D.host P P') ∧ ∀ P ∈ qpOf D Pq S, ∀ P' ∈ qpOf D Pq S, ¬ IsConjPl D.host P P' := by
  first | exact @GlobalTheory.ChosenHalf.qpOf_half | exact GlobalTheory.ChosenHalf.qpOf_half | (intros; apply GlobalTheory.ChosenHalf.qpOf_half <;> assumption)
