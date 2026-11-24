module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinitePlaceOverLOfHostEmbeddingQbar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
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
noncomputable section
namespace GlobalTheory.ConjGal
open Formalism.BasicNotions.Loc GlobalTheory.Pst
section Local
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces B)
end Local
end GlobalTheory.ConjGal
namespace GlobalTheory.ConjGal
open Formalism.BasicNotions.Loc
section W
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
end W
theorem main_alt_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → ∀ Pm : GL (Fin a) (Qbar (D.nd.l i)), (∀ g, ρ' g = Pm⁻¹ * ρ g * Pm) → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ' w ↔ D.naut.IsdRW i ρ w) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → D.naut.wdOf i ρ' w = D.naut.wdOf i ρ w) ∧ (∀ τ, (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w) → D.naut.jumpsW i ρ' τ = D.naut.jumpsW i ρ τ)) := by
  intro hB hL D P i a ρ ρ' hρ Pm hc
  refine ⟨fun w hw => ?_, fun w h₁ => ?_, fun τ hτ => ?_⟩
  · rw [(P.wdOf i _ ρ' w).2.2.2.1, (P.wdOf i _ ρ w).2.2.2.1]
    exact dR_conj D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc hρ w hw
  · rw [(P.wdOf i _ ρ' w).1, (P.wdOf i _ ρ w).1]
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · have d₁ := (P.wdOf i _ ρ w).2.2.2.1.1 (h₁.resolve_left (not_not.2 hw))
      exact wd_conj_above D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) hB ρ ρ' Pm hc hρ w hw d₁
    · exact wd_conj_away D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc w hw
  · obtain ⟨w₀, -, -⟩ := GlobalTheory.PlaceOfEmb.exists_place_of_emb D (D.nd.l i) τ
    rw [(P.wdOf i _ ρ' w₀).2.2.2.2 τ, (P.wdOf i _ ρ w₀).2.2.2.2 τ]
    exact jumps_conj D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc hρ τ fun w hw =>
      (P.wdOf i _ ρ w).2.2.2.1.1 (hτ w hw)
end GlobalTheory.ConjGal
end
end
