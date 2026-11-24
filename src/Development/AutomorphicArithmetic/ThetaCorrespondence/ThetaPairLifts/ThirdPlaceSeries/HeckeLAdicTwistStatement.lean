module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicParameterAbove
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicTwist
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_galois_character_of_algebraic_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (i : D.nd.Loc) (χ : D.naut.CG 1) (s : ℝ), (∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infG χ ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ))) := by
  first | exact @_root_.GlobalTheory.GalPin.heckeLAdicTwist_alt | exact _root_.GlobalTheory.GalPin.heckeLAdicTwist_alt | (intros; apply _root_.GlobalTheory.GalPin.heckeLAdicTwist_alt <;> assumption)
end
