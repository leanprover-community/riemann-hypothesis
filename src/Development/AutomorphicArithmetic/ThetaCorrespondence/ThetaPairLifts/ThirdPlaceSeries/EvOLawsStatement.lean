module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.eventually_conjunction_mono_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (P₁ P₂ : D7 → Prop), (_root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₂ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup fun D' => P₁ D' ∧ P₂ D') ∧ ((∀ D', P₁ D' → P₂ D') → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₂) ∧ (_root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L ∧ P₁ (withLoc L)) ∧ ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big' L → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L := by
  first | exact @_root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt | exact _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt | (intros; apply _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt <;> assumption)
end
