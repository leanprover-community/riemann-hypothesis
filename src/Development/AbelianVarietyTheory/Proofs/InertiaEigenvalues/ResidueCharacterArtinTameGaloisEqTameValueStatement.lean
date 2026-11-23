module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.residue_character_artin_tame_galois_eq_tame_value : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (rc : Recip D D.nd.Om), rc.Good → ∀ (R : Type) [CommRing R] (f : R →+* ℂ) (φ : G D.host.E D.nd.Om →* Rˣ), IsOpen (φ.ker : Set (G D.host.E D.nd.Om)) → ∀ (PP : Pl D.host.E) (m : ℕ), ((m : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A PP → ∀ σ ∈ Ine (F := D.host.E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1) → Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP → ∀ c : (kP PP)ˣ →* Circle, IsResAt (GlobalTheory.SeriesTie.charOf rc f φ) PP c → ∀ (e : ℤ) (u : 𝓞 D.host.E), u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((c z : Circle) : ℂ) ^ e = f (NX.tameVal φ PP e u).1 := by
  first | exact @GlobalTheory.TameResRead.res_zpow_eq_tameVal | exact GlobalTheory.TameResRead.res_zpow_eq_tameVal | (intros; apply GlobalTheory.TameResRead.res_zpow_eq_tameVal <;> assumption)
