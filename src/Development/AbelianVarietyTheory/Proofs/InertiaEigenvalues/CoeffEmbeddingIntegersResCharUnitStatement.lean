module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEmbeddingIntegersResCharUnit
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.Divisibility.ClassSum
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.coeffEmbedding_integers_resChar_unit : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl), (∀ a : 𝓞 D.what₂.LL, B.ec j w (a : D.what₂.LL) ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range) ∧ ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal ∧ ∀ (a : 𝓞 D.what₂.LL) (z : B.Oc j w), algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) z = B.ec j w (a : D.what₂.LL) → (a ∈ (D.plEq w).asIdeal ↔ ¬ IsUnit z) := by
  first | exact @GlobalTheory.NLocPlace.ec_int_resChar_unit | exact GlobalTheory.NLocPlace.ec_int_resChar_unit | (intros; apply GlobalTheory.NLocPlace.ec_int_resChar_unit <;> assumption)
