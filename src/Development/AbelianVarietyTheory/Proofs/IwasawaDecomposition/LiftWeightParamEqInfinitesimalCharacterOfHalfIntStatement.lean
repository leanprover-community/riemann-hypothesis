module

public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.liftWeightParam_eq_infinitesimalCharacter_of_halfInt : ∀ (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ), (∃ z : ℤ, sh = (z : ℂ) + 1 / 2) →
    ∃ lam : DomWeight R.nV, NG.infOf lam.w = NG.paramV R h j sh := by
  first | exact @GlobalTheory.WtComb.paramV_eq_infOf | exact GlobalTheory.WtComb.paramV_eq_infOf | (intros; apply GlobalTheory.WtComb.paramV_eq_infOf <;> assumption)
