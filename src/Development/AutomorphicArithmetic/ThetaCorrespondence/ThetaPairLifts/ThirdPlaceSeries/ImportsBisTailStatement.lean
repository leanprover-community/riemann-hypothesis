import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyJoinOfAgreementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyJoinOfAgreement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessorStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSide
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormAtEachLocationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormAtEachLocation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvariantFormBoundedCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvariantFormBoundedCongruence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsThetaModStatement

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_module_at_successor : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (j : Fin D.R.m) (j' : ℕ) (hj : j.1 + 1 = j'), ∃ Y : RowMod D P.rep j', GlobalTheory.NJoin.IsCanon X j hj Y := by
  first | exact @_root_.GlobalTheory.RowModCanon.main_alt_alt | exact _root_.GlobalTheory.RowModCanon.main_alt_alt | (intros; apply _root_.GlobalTheory.RowModCanon.main_alt_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.VFormCls
open Formalism.IndefR.Bridge
end GlobalTheory.VFormCls
namespace GlobalTheory.VFormCls
end GlobalTheory.VFormCls
namespace GlobalTheory.VFormCls
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame Formalism.L2.Theta
end GlobalTheory.VFormCls
namespace GlobalTheory.VFormCls
open Formalism.IndefR Formalism.L2.Theta
end GlobalTheory.VFormCls
namespace GlobalTheory.VFormCls
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.L2.Theta
set_option maxHeartbeats 4000000 in
theorem core_data_of_point (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (hA : GlobalTheory.NJoin.Agree X P.M P.rep) (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k)
    (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) :
    ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) (T : Finset (GAf D.host.E D.R.nV))
      (β : (P.M μ k h1 h2).wt.W →ₗ⋆[ℂ] (P.M μ k h1 h2).wt.W →ₗ[ℂ] ℂ) (c : ℝ),
      GlobalTheory.CoefDuty.IsInvForm (P.M μ k h1 h2).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧
      (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧
      GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧
      (∀ x, (P.M μ k h1 h2).real x ∈ NG.TypeSp (P.M μ k h1 h2).wt.ρ J χ) ∧
      ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M μ k h1 h2).wt β J T
        ((P.M μ k h1 h2).real x) ((P.M μ k h1 h2).real y) := by
  subst hk
  obtain ⟨Fx, hmem, hext, hin⟩ := inner_eq X μ hμ j
  obtain ⟨N, hN, hopen⟩ := GlobalTheory.T.exists_principalCongruence_in_definiteLevel D P.cf P.C P.tp X P.M P.rep hA j (X.tupT μ)
  obtain ⟨Fb, hFb⟩ := GlobalTheory.T.definiteLevel_preimage_finitely_many_cosets D P.cf P.C P.tp X P.M P.rep hA j (X.tupT μ)
  have hcV := X.given.core.models.cV j
  have hφ := frame_bij (hA.PV j)
  set φ := (finHom (Vc D j)).rangeRestrict.comp (hA.PV j).ψ with hφdef
  set EV := levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ)) with hEV
  set eW := hA.eW μ hμ j with heW
  have hrat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
      ∃ γ, Bridge.ratF (Vc D j) γ = φ ((hA.a j)⁻¹ * h * hA.a j) := by
    intro h
    rw [hA.rat j h]
    constructor
    · rintro ⟨γ, hγ, e⟩
      exact ⟨⟨γ, hγ⟩, Subtype.ext e⟩
    · rintro ⟨γ, e⟩
      exact ⟨γ.1, γ.2, congrArg Subtype.val e⟩
  obtain ⟨T, hT, hsum⟩ := transport (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (Bridge.ratF (Vc D j)) (ratF_inj _) φ hφ
    (hA.a j) hrat EV.J (X.R.B.L j (X.tupT μ)).pres.y (X.R.B.L j (X.tupT μ)).pres.reps
  have hreal : ∀ x h, (P.M μ (j.1 + 1) h1 h2).real x h = eW (Fx x (φ ((hA.a j)⁻¹ * h))) := by
    intro x h
    rw [hA.real μ hμ j x h, ← hext x]
    have hin' : ((hA.PV j).ψ ((hA.a j)⁻¹ * h))⁻¹ ∈ GfC (Vc D j) := (GfC _).inv_mem ((hA.PV j).into _)
    show eW ((X.R.cV j).ρ ((hA.PV j).ψ ((hA.a j)⁻¹ * h))⁻¹ _) = _
    rw [hcV.1 _ hin']
    rfl
  let β : (P.M μ (j.1 + 1) h1 h2).wt.W →ₗ⋆[ℂ] (P.M μ (j.1 + 1) h1 h2).wt.W →ₗ[ℂ] ℂ :=
    ((innerₛₗ ℂ).comp eW.symm.toLinearMap).compl₂ eW.symm.toLinearMap
  have hβ : ∀ u v, β u v = inner ℂ (eW.symm u) (eW.symm v) := fun u v => rfl
  refine ⟨EV.J.comap φ, EV.χ.comp (φ.subgroupComap EV.J), T, β, (RealDat.nP X.F false)⁻¹, ⟨?_, ?_, ?_⟩, ?_, ?_, hT, ?_, ?_, ?_⟩
  · intro u v
    rw [hβ, hβ, inner_conj_symm]
  · intro u hu
    rw [hβ]
    exact (re_inner_self_pos (𝕜 := ℂ)).2 ((LinearEquiv.map_ne_zero_iff eW.symm).2 hu)
  · intro γ u v
    obtain ⟨γ', e⟩ := (hrat γ).1 γ.2
    have hw := hA.wt μ hμ j γ γ'.1 γ'.2 (congrArg Subtype.val e)
    have hs : ∀ w, eW.symm ((P.M μ (j.1 + 1) h1 h2).wt.ρ γ w) = (X.R.cV j).ρ γ'.1 (eW.symm w) := by
      intro w
      rw [LinearEquiv.symm_apply_eq, hw, LinearEquiv.apply_symm_apply]
    rw [hβ, hβ, hs, hs, hcV.2.1]
  · exact ⟨Fb, fun κ hκ => hFb κ hκ⟩
  · exact ⟨N, hN, fun κ hκ => hopen κ hκ⟩
  · unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  · intro x
    have hr : (P.M μ (j.1 + 1) h1 h2).real x ∈ NG.TypeSp (P.M μ (j.1 + 1) h1 h2).wt.ρ
        (P.M μ (j.1 + 1) h1 h2).J (P.M μ (j.1 + 1) h1 h2).χ := by
      rw [← (P.M μ (j.1 + 1) h1 h2).real_range]; exact LinearMap.mem_range_self _ _
    refine ⟨hr.1, fun κ => ?_⟩
    funext h
    show (P.M μ (j.1 + 1) h1 h2).real x (h * κ) = _
    rw [Pi.smul_apply, hreal, hreal, ← mul_assoc, map_mul]
    have hm := adForms_right (hmem x) (φ ((hA.a j)⁻¹ * h)) ⟨φ κ, κ.2⟩
    rw [hm]
    exact (eW.map_smul _ _).trans rfl
  · intro x y
    rw [hin x y, hsum (Fx x) (Fx y)]
    unfold GlobalTheory.CoefDuty.classSum
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hreal, hreal]
    simp only [hβ, LinearEquiv.symm_apply_apply]
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp),
    GlobalTheory.NJoin.Agree X P.M P.rep → ∀ i, ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ)
      (T : Finset (GAf D.host.E D.R.nV)) (β : (P.M.loc i).wt.W →ₗ⋆[ℂ] (P.M.loc i).wt.W →ₗ[ℂ] ℂ) (c : ℝ),
      GlobalTheory.CoefDuty.IsInvForm (P.M.loc i).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧
      (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧
      GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧ (∀ x, (P.M.loc i).real x ∈ NG.TypeSp (P.M.loc i).wt.ρ J χ) ∧
      ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M.loc i).wt β J T ((P.M.loc i).real x)
        ((P.M.loc i).real y) := by
  intro hL D P X hA i
  have hμ : Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hr := D.nd.j_range i
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i := ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  exact _root_.GlobalTheory.VFormCls.core_data_of_point hL D P X hA _ hμ j _ hj hr.1 hr.2
end GlobalTheory.VFormCls
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_form_bounded_congruence_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp), GlobalTheory.NJoin.Agree X P.M P.rep → ∀ i, ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) (T : Finset (GAf D.host.E D.R.nV)) (β : (P.M.loc i).wt.W →ₗ⋆[ℂ] (P.M.loc i).wt.W →ₗ[ℂ] ℂ) (c : ℝ), GlobalTheory.CoefDuty.IsInvForm (P.M.loc i).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧ (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧ GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧ (∀ x, (P.M.loc i).real x ∈ NG.TypeSp (P.M.loc i).wt.ρ J χ) ∧ ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M.loc i).wt β J T ((P.M.loc i).real x) ((P.M.loc i).real y) := by
  atlas_forward_decl _root_.GlobalTheory.VFormCls.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.FormAllLevels
theorem main_of_alt (pet : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), GlobalTheory.CoefDuty.IsInvForm a β → ∃ B, GlobalTheory.CoefDuty.IsPetersson a B ∧ ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (T : Finset (GAf L n)), GlobalTheory.CoefDuty.IsBounded J → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → GlobalTheory.CoefDuty.IsClassReps J T → ∃ c : ℝ, 0 < c ∧ ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ f' ∈ NG.TypeSp a.ρ J χ, GlobalTheory.CoefDuty.classSum a β J T f f' = (c : ℂ) * B f f') (cls : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp), GlobalTheory.NJoin.Agree X P.M P.rep → ∀ i, ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) (T : Finset (GAf D.host.E D.R.nV)) (β : (P.M.loc i).wt.W →ₗ⋆[ℂ] (P.M.loc i).wt.W →ₗ[ℂ] ℂ) (c : ℝ), GlobalTheory.CoefDuty.IsInvForm (P.M.loc i).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧ (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧ GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧ (∀ x, (P.M.loc i).real x ∈ NG.TypeSp (P.M.loc i).wt.ρ J χ) ∧ ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M.loc i).wt β J T ((P.M.loc i).real x) ((P.M.loc i).real y)) : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ i, MtForm D P.M i := by
  intro hL D P X hA i
  obtain ⟨J, χ, T, β, c, hβ, hJb, hJo, hT, hc, hmem, hin⟩ := cls hL D P X hA i
  obtain ⟨B, hB, hcs⟩ := pet D.host.E D.R.nV (P.M.loc i).wt β hβ
  obtain ⟨c', hc', hcs'⟩ := hcs J χ T hJb hJo hT
  have hpos : (0 : ℝ) < c * c' := mul_pos hc hc'
  refine ⟨((c * c' : ℝ) : ℂ) • B, ?_, ?_⟩
  · intro f hf f' hf'
    obtain ⟨h1, h2, h3⟩ := hB f hf f' hf'
    refine ⟨?_, ?_, ?_⟩
    · simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
      rw [h1]
    · intro hne
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      exact mul_pos hpos (h2 hne)
    · intro h
      simp only [LinearMap.smul_apply, h3 h]
  · intro x y
    rw [hin x y, hcs' _ (hmem x) _ (hmem y)]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ i, MtForm D P.M i :=
  _root_.GlobalTheory.FormAllLevels.main_of_alt GlobalTheory.T.exists_pos_classSum_eq_mul_invariantForm _root_.GlobalTheory.T.invariant_form_bounded_congruence_alt
end GlobalTheory.FormAllLevels
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mtForm_of_realAt_agree : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ i, MtForm D P.M i := by
  atlas_forward_decl _root_.GlobalTheory.FormAllLevels.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.JoinExists
theorem main_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Nonempty (_root_.GlobalTheory.NPin.CharacterChoiceJoin P) := by
  intro h1 h2 hL D P X hA
  have key : ∀ i : D.nd.Loc, ∃ Y : RowMod D P.rep (D.nd.j i),
      ∀ (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), GlobalTheory.NJoin.IsCanon X j hj Y := by
    intro i
    have hr := D.nd.j_range i
    have hlt : D.nd.j i - 1 < D.R.m := by omega
    obtain ⟨Y, hY⟩ := _root_.GlobalTheory.T.exists_canonical_module_at_successor h1 h2 hL D P X hA ⟨D.nd.j i - 1, hlt⟩ (D.nd.j i) (by simp only; omega)
    refine ⟨Y, fun j hj => ?_⟩
    have hj' : j = ⟨D.nd.j i - 1, hlt⟩ := Fin.ext (by simp only; omega)
    subst hj'
    exact hY
  choose Y hY using key
  exact ⟨{ form := _root_.GlobalTheory.T.mtForm_of_realAt_agree hL D P X hA
           rowM := Y
           th := fun i j hj => (_root_.GlobalTheory.T.nonempty_theta_mod_of_is_canon h1 h2 hL D P X hA i j hj (Y i) (hY i j hj)).some }⟩
end GlobalTheory.JoinExists
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_join_of_agree : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Nonempty (_root_.GlobalTheory.NPin.CharacterChoiceJoin P) := by
  atlas_forward_decl _root_.GlobalTheory.JoinExists.main_alt_alt
end
end
