module

public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContragredientPolynomialWeightUniqueHighestWeigh
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.contragredient_polynomialWeight_unique_highestWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', e.comp (emb t) ≠ ComplexEmbedding.conjugate (e.comp (emb t'))) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (lam : ι → DomWeight n), Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam), (∀ γ x, T (ρ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) → ∀ (t : ι) (lam0 : Fin n → ℤ), NX.HWAtF c ρ.dual (emb t) lam0 → lam0 = (lam t).w := by
  first | exact @GlobalTheory.mtRatDual_hw | exact GlobalTheory.mtRatDual_hw | (intros; apply GlobalTheory.mtRatDual_hw <;> assumption)
