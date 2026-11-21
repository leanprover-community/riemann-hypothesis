import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.NormLeOneOfInteger
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletionEmbeddingInducingHostEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterIndependentOfLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistableStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_galoisSide_iff_deRham_at_localEmbedding : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → (W.IsdRW l ι r w ↔ GlobalTheory.Pst.IsdRAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
  first | exact @GlobalTheory.DeRhamRead.isdRW_iff_isdRAt | exact GlobalTheory.DeRhamRead.isdRW_iff_isdRAt | (intros; apply GlobalTheory.DeRhamRead.isdRW_iff_isdRAt <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_characterTwist_iff_localEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Loc.Om l)) (c : ↥Gw →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsdRAt P Bw c → (GlobalTheory.Pst.IsdRAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) ↔ GlobalTheory.Pst.IsdRAt P Bw r) := by
  first | exact @GlobalTheory.TwistBridgeDR.isdRAt_twist_iff | exact GlobalTheory.TwistBridgeDR.isdRAt_twist_iff | (intros; apply GlobalTheory.TwistBridgeDR.isdRAt_twist_iff <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.TwistJumpsW
open Formalism.BasicNotions.Loc

theorem jumpsW_twist : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (i : D.nd.Loc) (ι : Qbar (D.nd.l i) ≃+* ℂ) (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → ∀ (τ : D.host.E →+* Qbar (D.nd.l i)) (c : ℤ), (∀ w, InducesW D.nd i τ w → W.IsdRW (D.nd.l i) ι ρ w ∧ W.IsdRW (D.nd.l i) ι χ w) → W.jumpsW (D.nd.l i) ι χ τ = {c} → W.jumpsW (D.nd.l i) ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (W.jumpsW (D.nd.l i) ι ρ τ).map (· + c) := by
  intro D T W i ι a ρ χ hρ hχ τ c hdR hc
  let w := PI.CompDegEF.plOf τ
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := PI.CompDegEF.natCast_mem_plIdeal τ
  have hIW : InducesW D.nd i τ w := fun x => Iff.rfl
  obtain ⟨hdρ, hdχ⟩ := hdR w hIW
  have hj : GlobalTheory.Pst.Induces (D.nbr i w hw) := D.nbr_ind i w hw
  obtain ⟨L₁, hL₁, hm₁⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) (G D.host.E D.nd.Om) a ρ hρ
    (D.nbr i w hw).LL
  obtain ⟨L, hL, hm⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) (G D.host.E D.nd.Om) 1 χ hχ L₁
  have hBL : (D.nbr i w hw).LL.1 ≤ L.1 := hL₁.trans hL
  obtain ⟨τ', hτ'⟩ := GlobalTheory.EmbExt.main D (D.nd.l i) w _ (D.nbr i w hw) hj τ hIW L hBL
  obtain ⟨ρ₁, cρ, rfl⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem ρ hρ L (fun g i j => hL (hm₁ g i j))
  obtain ⟨χ₁, cχ, rfl⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem χ hχ L hm
  obtain ⟨-, H⟩ := W.loc (D.nd.l i) ι w hw _ (D.nbr i w hw) hj
    ((algebraMap ↥(D.nbr i w hw).LL.1 (Om (D.nd.l i))).comp (D.nbr i w hw).toLL) (fun _ => rfl)
  let tw₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥L.1 := GlobalTheory.TwistAbove.twGL (Matrix.GeneralLinearGroup.det.comp χ₁) ρ₁
  have htw : Formalism.MainNotions.SumRepresentations.At.twGL (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) ρ₁)
      (Matrix.GeneralLinearGroup.det.comp (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) χ₁)) =
      mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) tw₁ := by
    refine MonoidHom.ext fun g => Units.ext ?_
    ext p q
    simp [tw₁, mapRep, Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  have ctw : Continuous (fun g => ((tw₁ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1)) := by
    have h1 : Continuous (fun g => ((χ₁ g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1).det) := cχ.matrix_det
    refine continuous_matrix fun p q => ?_
    refine (h1.mul (cρ.matrix_elem p q)).congr fun g => ?_
    simp [tw₁, GlobalTheory.TwistAbove.twGL_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [htw]
  have Hρ := H L hBL a ρ₁ cρ
  have Hχ := H L hBL 1 χ₁ cχ
  have Htw := H L hBL a tw₁ ctw
  have dρ := Hρ.2.1.1 hdρ
  have dχ := Hχ.2.1.1 hdχ
  have hcom := GlobalTheory.TwistAbove.twist_common (D.nbr i w hw) (ρ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)
    (χ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) (D.locT (D.nd.l i))
  have dtw : (D.nbr i w hw).IsdRE (D.loc (D.nd.l i)) L (tw₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    hcom.1 dρ dχ
  have mχ : ∀ n, (D.nbr i w hw).multE (D.loc (D.nd.l i)) L (χ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' n =
      if n = c then 1 else 0 := by
    intro n
    rw [← (Hχ.2.2.2 τ τ' hτ').2 dχ n, hc, Multiset.count_singleton]
    split_ifs <;> simp
  ext n
  have e1 := (Htw.2.2.2 τ τ' hτ').2 dtw n
  have e2 := hcom.2.2.2 τ' c dχ mχ (n - c)
  have e3 := (Hρ.2.2.2 τ τ' hτ').2 dρ (n - c)
  have e4 := Multiset.count_map_eq_count' (fun x : ℤ => x + c) (W.jumpsW (D.nd.l i) ι (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) ρ₁) τ)
    (add_left_injective c) (n - c)
  simp only [sub_add_cancel] at e2 e4
  rw [e4]
  exact_mod_cast e1.trans (e2.trans e3.symm)

end GlobalTheory.TwistJumpsW
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateJumps_twist_by_deRham_character : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (i : D.nd.Loc) (ι : Qbar (D.nd.l i) ≃+* ℂ) (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → ∀ (τ : D.host.E →+* Qbar (D.nd.l i)) (c : ℤ), (∀ w, InducesW D.nd i τ w → W.IsdRW (D.nd.l i) ι ρ w ∧ W.IsdRW (D.nd.l i) ι χ w) → W.jumpsW (D.nd.l i) ι χ τ = {c} → W.jumpsW (D.nd.l i) ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (W.jumpsW (D.nd.l i) ι ρ τ).map (· + c) := by
  atlas_forward_decl GlobalTheory.TwistJumpsW.jumpsW_twist
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParamOfLadicRep_twist_det_awayFrom_l : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((χ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf h hl ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) = (GlobalTheory.WeilDeligne.wdOf h hl ι ρ).lpChar (GlobalTheory.WeilDeligne.wdOf h hl ι χ) := by
  first | exact @GlobalTheory.WeilDeligne.wdOf_twGL_det | exact GlobalTheory.WeilDeligne.wdOf_twGL_det | (intros; apply GlobalTheory.WeilDeligne.wdOf_twGL_det <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistGal

theorem twGL_coe {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : kˣ) : k) • (ρ g : Matrix (Fin a) (Fin a) k) := by
  rw [Algebra.smul_def]
  rfl

theorem cont_twGL {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {a : ℕ}
    (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (hχ : Continuous fun g => ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) :
    Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k) := by
  simp only [twGL_coe]
  refine Continuous.smul (M := k) ?_ hρ
  exact hχ.matrix_det

theorem comp_twGL {Γ Γ' k : Type} [Group Γ] [Group Γ'] [CommRing k] {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (χ : Γ →* GL (Fin 1) k) (f : Γ' →* Γ) :
    (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)).comp f =
      Formalism.MainNotions.SumRepresentations.At.twGL (ρ.comp f) (Matrix.GeneralLinearGroup.det.comp (χ.comp f)) :=
  MonoidHom.ext fun _ => rfl

theorem galois_twist : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w)) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w)) ∧ (∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c))) := by
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
