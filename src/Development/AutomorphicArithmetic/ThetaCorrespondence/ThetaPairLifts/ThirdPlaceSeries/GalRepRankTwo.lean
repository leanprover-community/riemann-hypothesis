import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InducesOfIsInduced
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGaloisCharacterOfAlgebraicStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGaloisCharacterOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepOneEqOfCharacterStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepOneEqOfCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneRankOneLocalParamStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneRankOneLocalParam
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm7OfAutomorphicCsdTemperedPurity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.RankOneChar
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.NPin
open GlobalTheory.CuspRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem cg_eq_ofChar_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (π : D.naut.CG 1), haveI := GlobalTheory.CuspRep.host_isCMField D.host;
    ((P.cg.e 1 π).1 : GlobalTheory.CuspRep.CG D.host.E 1) = GlobalTheory.CuspRep.CG.ofChar (P.chr.e1 π).1 := by
  intro _ hL D P π
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (P.cg.e 1 π)).1 with hχ'
  set χ := (P.chr.e1 π).1 with hχ
  have hloc : ∀ v, P.T.e v (D.naut.locG π v) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [P.cg.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [P.T.unr, hloc v]; exact _root_.GlobalTheory.RankOneComp.locParT_ofChar_unr_iff_unrAt hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (P.chr.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [HChar.loc_mul, HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := P.chr.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [P.T.frobEig _ _ hv, hloc v]; exact _root_.GlobalTheory.RankOneComp.frobEig_locParT_ofChar_of_unrAt hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  rw [← hchar, hχ', CGu.ofChar_equivChar]
end GlobalTheory.RankOneChar
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_rep_one_eq_of_character_choice : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (π : D.naut.CG 1), haveI := GlobalTheory.CuspRep.host_isCMField D.host; ((P.cg.e 1 π).1 : GlobalTheory.CuspRep.CG D.host.E 1) = GlobalTheory.CuspRep.CG.ofChar (P.chr.e1 π).1 := by
  atlas_forward_decl _root_.GlobalTheory.RankOneChar.cg_eq_ofChar_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.CuspRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.AwayLGC
theorem weil_deligne_rank_one_eq_local_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ), Continuous μ → IsLAdicOf art ι χ n μ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal), GlobalTheory.WeilDeligne.wdOf h hl ι (rk1 μ) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h := by
  intro hL E Ω _ _ _ _ _ _ l _ ι art hart χ n μ hμ hlad A w h hl
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, H.one]
  refine GlobalTheory.WeilDeligne.wdOf_eq_mk hl _ rfl fun g => ?_
  have e := hlad.loc_away (Or.inl hl) (a g) (g : G E Ω) (ha.glob art hart g)
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [Subsingleton.elim i 0]
  simp [GlobalTheory.WeilDeligne.toEndC_apply, GlobalTheory.TripleGal.rk1, Matrix.mulVec, dotProduct, e]
end GlobalTheory.AwayLGC
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.CuspRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_rank_one_local_param' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ), Continuous μ → IsLAdicOf art ι χ n μ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal), GlobalTheory.WeilDeligne.wdOf h hl ι (rk1 μ) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h := by
  atlas_forward_decl _root_.GlobalTheory.AwayLGC.weil_deligne_rank_one_eq_local_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GalPin
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.Pst GlobalTheory.CuspRep Formalism.BasicNotions.Loc
theorem heckeLAdicTwist_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (i : D.nd.Loc) (χ : D.naut.CG 1) (s : ℝ), (∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infG χ ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ))) := by
  intro hF hGA hCh hPa hL D P i χ s hint
  have := host_isCMField D.host
  set ψ : HChar D.host.E := (P.chr.e1 χ).1 with hψ
  set ν := GlobalTheory.HeckeGal.Model.absPow D.host.E s
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E s
  have hinf : ∀ τ, D.naut.infG χ τ = {expo ψ τ} := fun τ => by
    rw [P.cg.inf, CGu.infChar, _root_.GlobalTheory.T.cusp_rep_one_eq_of_character_choice hF hL D P χ, CG.infChar_ofChar]
  have hexpo : ∀ τ, expo (ψ * ν) τ = expo ψ τ + s := fun τ => by
    have h := (CG.hasInfChar_ofChar ψ τ).twist ν
    rw [CG.twist_ofChar, Multiset.map_singleton] at h
    have := h.infChar_eq
    rw [CG.infChar_ofChar] at this
    rw [← (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ]
    simpa using this
  have hint' : ∀ τ, ∃ k : ℤ, expo (ψ * ν) τ = k := fun τ => by
    obtain ⟨k, hk⟩ := hint τ (expo ψ τ) (by rw [hinf]; exact Multiset.mem_singleton_self _)
    exact ⟨k, by rw [hexpo, hk]⟩
  choose n hn using hint'
  have hAlg : IsAlgPos (ψ * ν) n := GlobalTheory.T.isAlgebraicHeckeCharOfWeight_of_integer_expo D.host.E (ψ * ν) n hn
  obtain ⟨art, ha⟩ := hGA D.host.E D.nd.Om
  obtain ⟨μ, hμc, hμ⟩ := ha.exists_isLAdicOf (D.naut.iotaQC i) hAlg
  have hpar : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG χ w) u) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar ψ) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [P.T.tw, P.cg.loc, ← _root_.GlobalTheory.T.cusp_rep_one_eq_of_character_choice hF hL D P χ]
    rfl
  have htw : ∀ w : PlE D.host, _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar (ψ * ν)) (D.nd.plOm.2 w) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar ψ) (D.nd.plOm.2 w)).lpTw s := fun w => by
    rw [← CG.twist_ofChar]
    exact _root_.GlobalTheory.HeightCounting.Blocks.local_parameter_twist_abs_pow hL hF _ hν _
  refine ⟨rk1 μ, ?_, fun w hw => ?_, fun w hw => ?_⟩
  · show Continuous fun g => ((rk1 μ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i)))
    exact (continuous_pi fun _ => Units.continuous_val.comp hμc).matrix_diagonal
  · have hl : (((D.nd.l i : ℕ)) : 𝓞 D.host.E) ∉ w.asIdeal := hw
    rw [(P.wdOf i 1 (rk1 μ) w).1]
    refine (P.T.e w).injective ?_
    rw [P.wd.away _ _ (rk1 μ) w hl, _root_.GlobalTheory.T.weil_deligne_rank_one_local_param' hL D.host.E D.nd.Om _ _ art ha _ n μ hμc hμ _ w (D.nd.plOm.2 w) hl, htw, hpar]
  · have hab := fun (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
        (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O) (hj : Induces Bw) =>
      (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hCh) D.host.E D.nd.Om (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
        (D.naut.iotaQC i) art ha (ψ * ν) n μ hAlg hμc hμ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) O Bw hj
    obtain ⟨hdR, hJ⟩ := GlobalTheory.T.deRham_jumps_of_continuous_lAdic_char D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) μ hμc
      (fun τ => {-n ((D.naut.iotaQC i).toRingHom.comp τ)}) w hw
      (fun O _ _ _ Bw hj => ⟨(hab O Bw hj).1, (hab O Bw hj).2.2.2⟩)
    refine ⟨(P.wdOf i 1 (rk1 μ) w).2.2.2.1.2 hdR, ?_, fun τ hτ => ?_⟩
    · rw [(P.wdOf i 1 (rk1 μ) w).1]
      refine (P.T.e w).injective ?_
      obtain ⟨LL, Bw, hj, he⟩ := P.wd.above _ _ (rk1 μ) w hw
      have hc : IsComp (ψ * ν) w ((ψ * ν).loc w) := ⟨ParLaws.isSmoothChar_loc _ w, fun x => rfl⟩
      rw [he, hpar, ← htw, hPa D.host.E D.nd.Om (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩ (D.naut.iotaQC i) art ha
        (ψ * ν) n μ hAlg hμc hμ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw hj _ hc _
        (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)), _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity]
      rfl
    · rw [(P.wdOf i 1 (rk1 μ) w).2.2.2.2 τ, hJ τ hτ, hinf, Multiset.map_singleton, Multiset.map_singleton,
        Int.cast_neg, ← hn, hexpo]
end GlobalTheory.GalPin
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_character_of_algebraic_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (i : D.nd.Loc) (χ : D.naut.CG 1) (s : ℝ), (∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infG χ ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ))) := by
  atlas_forward_decl _root_.GlobalTheory.GalPin.heckeLAdicTwist_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TempClose
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
theorem rankOneUnitary_of_charSide (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) : RankOneUnitary P.T := by
  intro π w σ _ α hα
  obtain ⟨ξ, hξ, -, hξu⟩ := GlobalTheory.HeckeComp.main D.host.E (P.chr.e1 π).1 w
  have he := _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp hAF hL D P π w ξ hξ
  rw [WDTie.eig, he] at hα
  unfold WD.inePol at hα
  split_ifs at hα with hσ
  · exact _root_.UpperTheory.Zero.LLC.IsRecT.recUnit (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)) ξ
      (Irr.ofDet 1 ξ hξ.1) (hξu (P.chr.e1 π).2) ⟨Representation.Equiv.refl _⟩ ⟨σ, hσ⟩ α hα
  · simp at hα
end GlobalTheory.TempClose
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.GalClose
open GlobalTheory.CuspRep
theorem rankOne_galois_closure_geometric_alt (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc)
    (π : D.naut.CG 1) (hr : D.naut.ralg π) :
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)),
      Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i)))) ∧ IsSSRep ρ ∧
      (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((1 - ((1 : ℕ) : ℝ)) / 2) ∧ D.naut.tempered (D.naut.locG π w)) ∧
      (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧
        (∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.jumpsInf i π τ) ∧
        D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((1 - ((1 : ℕ) : ℝ)) / 2)) := by
  have h0 : (1 - ((1 : ℕ) : ℝ)) / 2 = 0 := by norm_num
  obtain ⟨ρ, hc, h1, h2⟩ := _root_.GlobalTheory.T.exists_galois_character_of_algebraic_alt hPr.fin hPr.art hPr.chA hPr.chP hL D P i π 0 (fun τ z hz => by
    obtain ⟨n, hn⟩ := ((D.naut.ralg_def π).1 hr τ).2 z hz
    exact ⟨n, by rw [hn]; simp⟩)
  refine ⟨ρ, hc, isSSRep_rankOne ρ, fun w hw => ⟨by rw [h0]; exact h1 w hw, ?_⟩, fun w hw => ⟨(h2 w hw).1, fun τ hτ => ?_, by rw [h0]; exact (h2 w hw).2.1⟩⟩
  · exact GlobalTheory.RowTie.tempered_of_rank_le_one D P.T (_root_.GlobalTheory.TempClose.rankOneUnitary_of_charSide hPr.fin hL D P) 1 π le_rfl w
  · apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [(h2 w hw).2.2 τ hτ, D.naut.jumpsInf_def i π τ hr]
    simp
end GlobalTheory.GalClose
end
end
section
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.GalClose
open GlobalTheory.CuspRep
theorem purity_alt (hRP : GlobalTheory.Published.RegularAlgebraicPurity) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (a : ℕ) (π : D.naut.CG a) (hr : D.naut.ralg π) : ∃ w₀ : ℂ, ∀ τ : D.host.E →+* ℂ,
      D.naut.infG π (τ.comp (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom) =
        (D.naut.infG π τ).map (w₀ - ·) := by
  have := host_isCMField D.host
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · haveI := P.cg.zero
    exact isEmptyElim π
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  obtain ⟨w₀, hw⟩ := (hRP D.host.E a ha1 π₀ hr₀).1
  refine ⟨(w₀ : ℂ), fun τ => ?_⟩
  have hc : τ.comp (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom = (starRingEnd ℂ).comp τ :=
    RingHom.ext fun x => GlobalTheory.SplitRowProbe.conj_sqrt D.host τ x
  rw [hc, hinf, hinf, hw]
end GlobalTheory.GalClose
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS.Prod
open GlobalTheory GlobalTheory.GalFirstClause Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
theorem core_data_of_point (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) {a : ℕ}
    (π : D.naut.CG a) [IsCMField D.host.E] (π₀ : CuspSub D.host.E a)
    (hmk : CG.mk π₀ = (P.cg.e a π).1) {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {χ : HChar (maximalRealSubfield D.host.E)} {r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (D.host.E →+* Qbar l) → Multiset ℤ} (H : _root_.UpperTheory.GalS.IsGalUAlt π₀ χ ι r wt HT) :
    (∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      Aw (wdOf (D.nd.plOm.2 w) hl ι r) (P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))) := by
  have hloc0 : ∀ w : PlE D.host, P.T.e w (D.naut.locG π w) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w) := fun w => by
    rw [P.cg.loc, hmk]
    rfl
  have haw : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      Aw (wdOf (D.nd.plOm.2 w) hl ι r) (P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))) := fun w hl => by
    obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF _ a π₀ w
    rw [P.T.tw, hloc0, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ]
    exact H.aw hl (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL _) hσ
  exact haw
set_option maxHeartbeats 2000000 in
theorem galRep_rankTwo_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CarUAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (i : D.nd.Loc) (a : ℕ), 2 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))) ∧ (∀ w ∈ placesOver D.host.E (D.nd.l i), Nc D.nd D.naut (D.naut.locG π w) → D.naut.IsdRW i ρ w ∧ (∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.jumpsInf i π τ) ∧ UpperTheory.GalN.CuspA D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))) := by
  intro hF hC hL D P i a ha π hc hr
  have := host_isCMField D.host
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (P.cg.csd a π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  obtain ⟨r, wt, HT, H, hLG⟩ := hC D.host.E D.nd.Om (D.nd.l i) (D.naut.iotaQC i) a ha π₀ hc₀ hr₀
  have hcont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) := Units.continuous_val.comp H.cont
  have hloc : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG π w) u) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [P.T.tw, P.cg.loc, hmk]
    rfl
  have haw := _root_.UpperTheory.GalS.Prod.core_data_of_point hF hL D P π π₀ hmk H
  obtain ⟨K, ρ, hρc, hρ⟩ := finextRep (D.nd.l i) D.host.E D.nd.Om a r hcont
  have hncw : ∀ w, Nc D.nd D.naut (D.naut.locG π w) →
      NcW ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw ((1 - (a : ℝ)) / 2)) := fun w k => by
    rw [← hloc]; exact ncW_of_nc P.T ((nc_tw _ _).2 k)
  have hside : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), Nc D.nd D.naut (D.naut.locG π w) → P.wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w ∧
      ∀ τ : D.host.E →+* Qbar (D.nd.l i), (∀ (A : ValuationSubring D.nd.Om), IsPlaceOver A w →
        ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
          (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) A) O),
          Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Bw.LL.1, IsInduced Bw τ τ') →
        P.wd.jumpsW (D.nd.l i) (D.naut.iotaQC i) r τ = HT τ := by
    intro w hw hn
    have hni := _root_.UpperTheory.GalS.nice_of_loc_par hL hF (D.nd.plOm.2 w) (hncw w hn)
    obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge (D.nd.l i) D.host.E D.nd.Om w (D.nd.plOm.1 w) hw
      (D.nd.plOm.2 w)
    obtain ⟨Bw, hBj, hBLL, -, hBto⟩ := hLL L0 le_rfl
    have hind : Induces Bw := fun x => by rw [hBj]; exact hj x
    let LL' : FinExt (D.nd.l i) := supExt K Bw.LL
    have hK : K.1 ≤ LL'.1 := le_sup_left
    have hB : Bw.LL.1 ≤ LL'.1 := le_sup_right
    let ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1 := mapRep (IntermediateField.inclusion hK).toRingHom ρ
    have hρ' : mapRep (algebraMap ↥LL'.1 (Om (D.nd.l i))) ρ' = r := by
      rw [← hρ]
      ext g i k
      rfl
    have hρ'c : Continuous fun g => (ρ' g : Matrix (Fin a) (Fin a) ↥LL'.1) := by
      have hi : Continuous (IntermediateField.inclusion hK) :=
        continuous_induced_rng.2 continuous_subtype_val
      exact hρc.matrix_map hi
    have hmodel : IsModel Bw (resDec D.nd.plOm.1 r w) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
      ⟨hB, by rw [← hρ']; rfl⟩
    let φ : ↥(OL L0) →+* Qbar (D.nd.l i) := L0.1.val.toRingHom.comp (OL L0).val.toRingHom
    have hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om (D.nd.l i)) := fun x => (hBto x).symm
    have hcl := (P.wd.loc (D.nd.l i) (D.naut.iotaQC i) w hw _ Bw hind φ hφ).2 LL' hB a ρ' hρ'c
    rw [hρ'] at hcl
    have hab := H.above (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw hind
    have hdR : Bw.IsdRE (D.loc (D.nd.l i)) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
      (hmodel.isdRAt_iff (D.loc (D.nd.l i))).1 (hab.deRham hni)
    refine ⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩
    obtain ⟨τ₀, hτ₀⟩ := hτ _ (D.nd.plOm.2 w) _ Bw hind
    let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1 := (IntermediateField.inclusion hB).comp τ₀
    have hτ'' : IsInduced Bw τ τ'' := fun x => hτ₀ x
    have hJ := hab.jumps hni τ LL' τ'' hτ''
    ext n
    apply Nat.cast_injective (R := ℤ)
    rw [(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc (D.nd.l i)) hmodel hτ'' hJ n]
  refine ⟨r, hcont, H.ss, fun w hw => ?_, fun w hw hn => ⟨?_, fun τ hτw => ?_, ?_⟩⟩
  · refine relW_of_aw P.T ?_
    rw [(P.wdOf i a r w).1, P.wd.away _ _ r w hw]
    exact haw w hw
  · exact ((P.wdOf i a r w).2.2.2.1).2 (hside w hw hn).1
  · obtain ⟨w', hw', hτ⟩ := existsIsInduced (D.nd.l i) D.host.E D.nd.Om τ
    obtain rfl : w' = w := by
      obtain ⟨LL, Bw', hj', -⟩ := P.wd.above _ (D.naut.iotaQC i) r w' hw'
      obtain ⟨τ', h'⟩ := hτ _ (D.nd.plOm.2 w') _ Bw' hj'
      exact HeightOneSpectrum.ext (Ideal.ext fun x => (induces_of_isInduced (D.nd.plOm.2 w') hj' h' x).symm.trans (hτw x))
    rw [(P.wdOf i a r w').2.2.2.2 τ, (hside w' hw' hn).2 τ hτ]
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights, D.naut.jumpsInf_def i π τ hr, hinf]
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  · rw [(P.wdOf i a r w).1]
    obtain ⟨LL, Bw', hj', he⟩ := P.wd.above _ (D.naut.iotaQC i) r w hw
    obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hF _ _ π₀ w
    have h2 := hLG (D.loc _) (D.locA _)
      ⟨D.locT _⟩ w hw (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw' hj' σ₀ hσ₀ _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w))
    refine cuspA_of_ab P.T (by rw [D.naut.lpDim_tw, D.naut.locG_dim]; omega) ?_
    have e2 : _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (algNorm σ₀) =
        P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) := by
      rw [_root_.GlobalTheory.GalOfCusp.rec_algNorm_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)) σ₀, hloc, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ₀ (D.nd.plOm.2 w)]
      rfl
    rw [he, ← e2]
    exact h2 (by rw [e2]; exact ncW_of_nc P.T ((nc_tw _ _).2 hn))
theorem automorphic_galois_admissible_of_theta_local_inputs (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hC : _root_.UpperTheory.GalS.CarUAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) :
    AutomorphicGaloisAdmissible D.nd D.naut := by
  intro i
  refine ⟨fun a ha π hc hr => ?_, fun a π hr => _root_.GlobalTheory.GalClose.purity_alt hPr.clo hL D P a π hr, fun χ s hs => ?_⟩
  · rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · obtain rfl : a = 1 := by omega
      obtain ⟨ρ, c, s, o, u⟩ := _root_.GlobalTheory.GalClose.rankOne_galois_closure_geometric_alt hPr hL D P i π hr
      refine ⟨ρ, c, s, fun w hw => RelW.of_eq (o w hw).1, fun w hw _ => ⟨(u w hw).1, (u w hw).2.1, UpperTheory.GalN.CuspA.of_eq (u w hw).2.2⟩, fun _ w => ?_⟩
      by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
      · exact (u w hw).2.2
      · exact (o w hw).1
    · obtain ⟨ρ, c, s, o, u⟩ := _root_.UpperTheory.GalS.Prod.galRep_rankTwo_alt hPr.fin hC hL D P i a ha2 π hc hr
      exact ⟨ρ, c, s, o, fun w hw k => u w hw (k.resolve_left (by omega)), fun e => absurd e (by omega)⟩
  · exact _root_.GlobalTheory.T.exists_galois_character_of_algebraic_alt hPr.fin hPr.art hPr.chA hPr.chP hL D P i χ s hs
end UpperTheory.GalS.Prod
end
end
end
