module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterValuesIntegralUnitsAtPlace
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
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.twistCharacterValues_integral_units_at_place : ∀ (D : D7) (C : NChoice D) (X : CoefIn D.what₂) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)), (∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w) ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w)))) → PsiInt X ψ0 := by
  first | exact @GlobalTheory.HeckeLocN.psiInt_of_embW | exact GlobalTheory.HeckeLocN.psiInt_of_embW | (intros; apply GlobalTheory.HeckeLocN.psiInt_of_embW <;> assumption)
