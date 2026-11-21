import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterLabel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterTameStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGw
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterUnitValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterUnitValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_weil_mu_tame_of_is_true : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu := by
  first | exact @_root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw | exact _root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw | (intros; apply _root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TupleCharAtType
theorem xi_unrAt_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) :
    (P.tp.xi (D.nd.mu i)).UnrAt (D.naut.plGw k v) := by
  have hwg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hgp := D.host.g_prime k
  rw [D.nd.mu_w i, P.tp.xi_tw, D.nd.w_l i]
  have hdel : (P.cf.delAt (D.nd.l i)).UnrAt (D.naut.plGw k v) := by
    unfold CharFrame.delAt
    split_ifs
    · exact P.cf.isDel'.unr _ (natCast_notMem hgp D.host.pde'_prime (D.host.pde_ne_g k).2.symm hwg)
    · exact P.cf.isDel.unr _ (natCast_notMem hgp D.host.pde_prime (D.host.pde_ne_g k).1.symm hwg)
  have hpsi : (P.tp.psi (D.nd.w i)).UnrAt (D.naut.plGw k v) := by
    have hψ := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
    by_cases hl : D.nd.l i = D.host.g k
    · intro x _
      refine hψ.atl _ ?_ x
      unfold OverP
      rw [D.nd.w_l i, hl]
      exact hwg
    · refine (hψ.ram _).2 ?_
      rw [← P.Q_eq i]
      have hlp : (D.nd.l i).Prime := (D.nd.lPrime i).out
      have hS : D.naut.plGw k v ∈ D.nd.S i := by
        rw [D.nd.S_def i]
        refine ⟨?_, natCast_notMem hgp hlp (Ne.symm hl) hwg⟩
        fin_cases k
        · exact Or.inl hwg
        · exact Or.inr (Or.inl hwg)
      exact Finset.disjoint_left.mp (D.nd.SQ_disj i) hS
  intro x hx
  rw [HChar.loc_mul, hdel x hx, hpsi x hx, mul_one]
theorem mu_unit_value_eq_loc_k_mu0 : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal → (((S i _ hw).mu (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = (((P.cf.mu0 j).locK (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  intro hL D P S hS i k v hw j hj u hu hnot
  rw [(hS.mu i _ hw j hj).2 (Units.mk0 (u : D.host.E) hu)]
  have hx := _root_.GlobalTheory.TupleCharAtType.xi_unrAt_alt P i k v _ (isUnitAt_of_notMem u hu hnot)
  show (((P.cf.mu0 j * P.tp.xi (D.nd.mu i)).loc (D.naut.plGw k v) (atFin _ (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = _
  rw [HChar.loc_mul, hx, mul_one]
  rfl
end GlobalTheory.TupleCharAtType
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_mu_unit_eq_mu0_loc_k : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal → (((S i _ hw).mu (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = (((P.cf.mu0 j).locK (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  atlas_forward_decl _root_.GlobalTheory.TupleCharAtType.mu_unit_value_eq_loc_k_mu0
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.PendOf.tame_label_mu_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ChiTOk D P.cf → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu ∧ ∃ (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧ _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) := by
  intro hP hL D P hchi S hS i k v hw
  obtain ⟨u, hu0, hunit, hrep⟩ := GlobalTheory.T.exists_globalInteger_congr_tameGenerator_character D k v
  have hrep' : NX.TameRep (D.naut.plGw k v) 1 (D.ntypes.tg k v) u := by
    obtain ⟨ϖ, π, h1, h2, h3, h4⟩ := hrep
    exact ⟨D.nd.plOm.1 (D.naut.plGw k v), D.nd.plOm.2 (D.naut.plGw k v), D.ntypes.tg_mem k v, ϖ, π, h1, h2, h3,
      by rw [zpow_one]; exact h4⟩
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  obtain ⟨c, hc, hcv⟩ := hchi k v j u hu0 hrep'
  have htame := _root_.GlobalTheory.T.split_weil_mu_tame_of_is_true hL D P S hS i k v hw
  refine ⟨htame, (S i _ hw).mu_ok.1, c, hc, _root_.UpperTheory.Lit.Dz.dz_swap_compatible_alt hL D P.ty.grp k v _ _ htame u hu0 hrep c ?_⟩
  rw [_root_.GlobalTheory.T.split_mu_unit_eq_mu0_loc_k hL D P S hS i k v hw j (by simp only [j]; omega) u hu0 hunit]
  exact hcv.symm
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ChiTOk D P.cf → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu ∧ ∃ (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧ _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) := by
  first | exact @_root_.GlobalTheory.PendOf.tame_label_mu_alt | exact _root_.GlobalTheory.PendOf.tame_label_mu_alt | (intros; apply _root_.GlobalTheory.PendOf.tame_label_mu_alt <;> assumption)
end
end
end
