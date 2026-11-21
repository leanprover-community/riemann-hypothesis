import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisExtra
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsobaricRigidOfPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieAutAndSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisCompatibilityOfJumpsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisCompatibilityOfJumps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqAlgebraMapOfCharpoly
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightDirectSumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightDirectSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightTwistCharacterStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightTwistCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NOProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsAOfJumpCount
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalRepRankTwo

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent
namespace GlobalTheory.WeilDeligne.InertiaSplit
variable {l : ℕ} [Fact l.Prime]
end GlobalTheory.WeilDeligne.InertiaSplit
namespace GlobalTheory.WeilDeligne.InertiaSplit
variable {l : ℕ} [Fact l.Prime]
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end GlobalTheory.WeilDeligne.InertiaSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.WeilDeligne.InertiaSplit.decomp_away_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ p q : D.naut.LP w, D.naut.wdOf i ρ w = D.naut.lpSum p q → ∃ U U' : Submodule (Qbar (D.nd.l i)) (Fin a → Qbar (D.nd.l i)), IsCompl U U' ∧ Module.finrank (Qbar (D.nd.l i)) U = D.naut.lpDim p ∧ Module.finrank (Qbar (D.nd.l i)) U' = D.naut.lpDim q ∧ (∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), (∀ v ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))).mulVec v ∈ U) ∧ (∀ v ∈ U', ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))).mulVec v ∈ U')) ∧ (D.naut.mono0 q → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), ∀ c : Qbar (D.nd.l i), D.naut.inePol q σ = (X - C (D.naut.iotaQC i c)) ^ D.naut.lpDim q → ∀ v ∈ U', ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))).mulVec v = c • v)) := by
  intro _ hL D P i a ρ hρ w hw p q hpq
  have hw' : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hw
  have e1 := congrArg (P.T.e w) hpq
  rw [(P.wdOf i a ρ w).1, P.wd.away _ _ ρ w hw', P.T.sum] at e1
  obtain ⟨U, U', hC, h1, h2, h3, h4⟩ :=
    GlobalTheory.WeilDeligne.InertiaSplit.split_away hw' (D.naut.iotaQC i) ρ hρ _ _ e1
  refine ⟨U, U', hC, by rw [h1, P.T.dim], by rw [h2, P.T.dim], h3,
    fun hm σ hσ c hc => h4 ((P.T.mono0 w q).1 hm) σ hσ c ?_⟩
  rw [← P.T.inePol w q σ hσ, hc, P.T.dim]
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

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
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc
end GlobalTheory.SumRepAdd
namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc
section Gen
variable {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k'] {a b : ℕ}
end Gen
end GlobalTheory.SumRepAdd
namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc
section W
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
end W
end GlobalTheory.SumRepAdd
namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc
section W2
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
end W2
theorem main_alt_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a b (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ' → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w ↔ D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ' w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (D.naut.wdOf i ρ w) (D.naut.wdOf i ρ' w)) ∧ (∀ τ, (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') τ = D.naut.jumpsW i ρ τ + D.naut.jumpsW i ρ' τ)) := by
  intro hB hL D P i a b ρ ρ' hρ hρ'
  refine ⟨fun w hw => ?_, fun w h₁ h₂ => ?_, fun τ hτ => ?_⟩
  · rw [(P.wdOf i _ _ w).2.2.2.1, (P.wdOf i _ ρ w).2.2.2.1, (P.wdOf i _ ρ' w).2.2.2.1]
    exact dR_sum D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' hρ hρ' w hw
  · rw [(P.wdOf i _ _ w).1, (P.wdOf i _ ρ w).1, (P.wdOf i _ ρ' w).1]
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · have d₁ := (P.wdOf i _ ρ w).2.2.2.1.1 (h₁.resolve_left (not_not.2 hw))
      have d₂ := (P.wdOf i _ ρ' w).2.2.2.1.1 (h₂.resolve_left (not_not.2 hw))
      exact wd_sum_above D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) hB ρ ρ' hρ hρ' w hw d₁ d₂
    · exact wd_sum_away D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' hρ hρ' w hw
  · obtain ⟨w₀, -, -⟩ := exists_place D (D.nd.l i) τ
    rw [(P.wdOf i _ _ w₀).2.2.2.2 τ, (P.wdOf i _ ρ w₀).2.2.2.2 τ, (P.wdOf i _ ρ' w₀).2.2.2.2 τ]
    exact jumps_sum D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' hρ hρ' τ fun w hw =>
      ⟨(P.wdOf i _ ρ w).2.2.2.1.1 (hτ w hw).1, (P.wdOf i _ ρ' w).2.2.2.1.1 (hτ w hw).2⟩
end GlobalTheory.SumRepAdd
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_weight_direct_sum_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a b (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ' → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w ↔ D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ' w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (D.naut.wdOf i ρ w) (D.naut.wdOf i ρ' w)) ∧ (∀ τ, (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') τ = D.naut.jumpsW i ρ τ + D.naut.jumpsW i ρ' τ)) := by
  atlas_forward_decl _root_.GlobalTheory.SumRepAdd.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwistGal
theorem galois_twist_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w)) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w)) ∧ (∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c))) := by
  intro hB hL D P i a ρ χ hρ hχ
  have htc : Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) :=
    GlobalTheory.TwistGal.cont_twGL ρ χ hρ hχ
  have hdR : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) {b : ℕ} (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))),
      Continuous (fun g => ((r g : GL (Fin b) (Qbar (D.nd.l i))) : Matrix (Fin b) (Fin b) (Qbar (D.nd.l i)))) →
      (D.naut.IsdRW i r w ↔ GlobalTheory.Pst.IsdRAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
    intro w hw b r hr
    rw [(P.wdOf i b r w).2.2.2.1]
    exact GlobalTheory.T.deRham_galoisSide_iff_deRham_at_localEmbedding D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) w hw (D.nd.O i) (D.nbr i w hw) (D.nbr_ind i w hw) b r hr
  have p1 : ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w) := by
    intro w hw h
    rw [hdR w hw χ hχ] at h
    rw [hdR w hw _ htc, hdR w hw ρ hρ]
    rw [GlobalTheory.Pst.resDec, GlobalTheory.TwistGal.comp_twGL]
    exact GlobalTheory.T.deRham_characterTwist_iff_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ D.host.E D.nd.Om _ (D.nd.O i) (D.nbr i w hw) a (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w) (GlobalTheory.Pst.resDec D.nd.plOm.1 χ w) (hρ.comp continuous_subtype_val) (hχ.comp continuous_subtype_val) h
  have p3 : ∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c) := by
    intro τ c h hc
    have w0 : HeightOneSpectrum (𝓞 D.host.E) := PI.CompDegEF.plOf τ
    rw [(P.wdOf i 1 χ w0).2.2.2.2 τ] at hc
    rw [(P.wdOf i a _ w0).2.2.2.2 τ, (P.wdOf i a ρ w0).2.2.2.2 τ]
    refine GlobalTheory.T.hodgeTateJumps_twist_by_deRham_character D P.T P.wd i (D.naut.iotaQC i) a ρ χ hρ hχ τ c (fun w hw => ?_) hc
    obtain ⟨h1, h2⟩ := h w hw
    exact ⟨(P.wdOf i a ρ w).2.2.2.1.1 h1, (P.wdOf i 1 χ w).2.2.2.1.1 h2⟩
  have pst : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) {b : ℕ} (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))),
      Continuous (fun g => ((r g : GL (Fin b) (Qbar (D.nd.l i))) : Matrix (Fin b) (Fin b) (Qbar (D.nd.l i)))) →
      D.naut.IsdRW i r w → ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
      (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw →
      GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w) := by
    intro w hw b r hr hd O _ _ _ Bw hj
    exact hB.isPstAt (D.locT (D.nd.l i)) Bw _ (hr.comp continuous_subtype_val)
      ((GlobalTheory.T.deRham_galoisSide_iff_deRham_at_localEmbedding D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) w hw O Bw hj b r hr).1 ((P.wdOf i b r w).2.2.2.1.1 hd))
  have p2 : ∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w) := by
    intro w h1 h2
    rw [(P.wdOf i a _ w).1, (P.wdOf i a ρ w).1, (P.wdOf i 1 χ w).1]
    have hd : D.naut.lpDim (P.wd.wdOf (D.nd.l i) (D.naut.iotaQC i) χ w) = 1 := P.wd.wdOf_dim _ _ χ w
    apply (P.T.e w).injective
    rw [P.T.char w _ _ hd]
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · have d1 : D.naut.IsdRW i ρ w := h1.resolve_left (not_not.2 hw)
      have d2 : D.naut.IsdRW i χ w := h2.resolve_left (not_not.2 hw)
      have d3 := (p1 w hw d2).2 d1
      obtain ⟨L1, B1, j1, e1⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w hw
      obtain ⟨L2, B2, j2, e2⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) ρ w hw
      obtain ⟨L3, B3, j3, e3⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) χ w hw
      rw [e1, e2, e3]
      have T0 : Nonempty (LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i))) := ⟨D.locT (D.nd.l i)⟩
      have hN := D.nbr_ind i w hw
      rw [GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
          _ (D.nd.O i) B1 (D.nbr i w hw) j1 hN a _ (htc.comp continuous_subtype_val)
          (pst w hw _ htc d3 _ B1 j1) (pst w hw _ htc d3 _ (D.nbr i w hw) hN),
        GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
          _ (D.nd.O i) B2 (D.nbr i w hw) j2 hN a _ (hρ.comp continuous_subtype_val)
          (pst w hw _ hρ d1 _ B2 j2) (pst w hw _ hρ d1 _ (D.nbr i w hw) hN),
        GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
          _ (D.nd.O i) B3 (D.nbr i w hw) j3 hN 1 _ (hχ.comp continuous_subtype_val)
          (pst w hw _ hχ d2 _ B3 j3) (pst w hw _ hχ d2 _ (D.nbr i w hw) hN)]
      have q3 := pst w hw _ htc d3 _ (D.nbr i w hw) hN
      rw [GlobalTheory.Pst.resDec, GlobalTheory.TwistGal.comp_twGL] at q3 ⊢
      exact GlobalTheory.T.fontaineParameter_twist_potentiallySemistable (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
        (D.nd.O i) (D.nbr i w hw) hN a _ _ (hρ.comp continuous_subtype_val) (hχ.comp continuous_subtype_val)
        (pst w hw _ hρ d1 _ (D.nbr i w hw) hN) (pst w hw _ hχ d2 _ (D.nbr i w hw) hN) q3
    · rw [P.wd.away _ _ _ w hw, P.wd.away _ _ _ w hw, P.wd.away _ _ _ w hw]
      exact GlobalTheory.T.weilDeligneParamOfLadicRep_twist_det_awayFrom_l D.host.E D.nd.Om _ w (D.nd.plOm.2 w) (D.nd.l i) hw (D.naut.iotaQC i) a ρ χ hρ hχ
  exact ⟨p1, p2, p3⟩
end GlobalTheory.TwistGal
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_weight_twist_character_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w)) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w)) ∧ (∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c))) := by
  atlas_forward_decl _root_.GlobalTheory.TwistGal.galois_twist_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TieGalAssembly
theorem tieGal_of_jumpsCard_alt (hDR : GlobalTheory.Published.DeRhamPotSemistable) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (hJ : JumpsCard D.nd D.naut) : Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut :=
  ⟨GlobalTheory.CrysWD.crysIffWD D, potCrysIffWD D, hJ, fun i => ⟨_root_.GlobalTheory.WeilDeligne.InertiaSplit.decomp_away_alt hDR hL D P i, _root_.GlobalTheory.ConjGal.main_alt_alt hDR hL D P i,
    _root_.GlobalTheory.T.de_rham_weight_direct_sum_alt hDR hL D P i, _root_.GlobalTheory.T.de_rham_weight_twist_character_alt hDR hL D P i⟩⟩
theorem main_alt_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), JumpsCard D.nd D.naut → Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut :=
  fun hDR hL D P hJ => _root_.GlobalTheory.TieGalAssembly.tieGal_of_jumpsCard_alt hDR hL D P hJ
end GlobalTheory.TieGalAssembly
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tieGal_of_jumpsCard_of_deRhamPotSemistable : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), JumpsCard D.nd D.naut → Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut := by
  atlas_forward_decl _root_.GlobalTheory.TieGalAssembly.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsAClose
abbrev _root_.GlobalTheory.RowsAClose.mainTheorem : Prop :=  _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.RowsAAlt D
end GlobalTheory.RowsAClose
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
namespace UpperTheory.GalS
theorem galClose_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), AutomorphicGaloisAdmissible D.nd D.naut :=
  fun hP hL D P => _root_.UpperTheory.GalS.Prod.automorphic_galois_admissible_of_theta_local_inputs hP (_root_.UpperTheory.GalS.mergeP'_alt hP.fin hL hP.gal hP.car hP.clo) hL D P
theorem trivialLocalCondition_of_inputs (_ : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (_ : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (_ : JumpsCard D.nd D.naut) (i : D.nd.Loc) : UnusedSlot55 D.nd D.naut i := trivial
theorem a_close_main : _root_.GlobalTheory.RowsAClose.mainTheorem := by
  intro hP hL D P hJ
  have hlab := _root_.GlobalTheory.TieLabAt.main_alt_alt hL D P
  have hrig : IsobaricRigid D.nd D.naut := _root_.GlobalTheory.NPin.isobaricRigid_of_pin_alt hP.fin hP.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have haut := _root_.GlobalTheory.AutomorphismSplitting.tieAut_and_split_alt hP.fin hL D P
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D P.T, haut.1, _root_.GlobalTheory.T.tieGal_of_jumpsCard_of_deRhamPotSemistable hP.berger hL D P hJ⟩
  have ha2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D := _root_.UpperTheory.GalS.galClose_alt hP hL D P
  have ha7 : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D := _root_.UpperTheory.GalN.allCuspidalOpenBound_of_cuspU_character_choice hP.fin hP.gal hL D P
  refine ⟨hlab.1, GlobalTheory.RowClose.heckeSplitOne_of_charTied D P.cf P.C P.tp P.chr, htie0, ha2, han1, han2, ha5, ha7,
    _root_.UpperTheory.GalS.trivialLocalCondition_of_inputs hP hL D P hJ,
    haut.2⟩
end UpperTheory.GalS
end
end
