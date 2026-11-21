import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemOfBcPMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsometryFixFlagAnisotropicVectorOfFixFrame

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem frameAct_one {n : ℕ} (f : Fin n → (VS D).V) (b : Fin n) : frameAct f 1 b = f b := by
  simp [frameAct, Matrix.one_apply]

theorem sgnP_mem (p : PlF D) (b : Fin (D.R.rS + 1)) : TermLoc.sgnP D p b ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  refine ⟨Polynomial.X ^ 2 - 1, by monicity!, ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
  rw [pow_two, TermLoc.localSign_sq, sub_self]

set_option maxHeartbeats 1000000 in

theorem btAdm : BtAdm Zd u u' F0 what₂ := by
  intro hC γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, _⟩ := hs
  refine ⟨fun a b h => Matrix.one_apply_ne h.ne', fun a => Matrix.one_apply_eq a, fun b => ?_⟩
  intro P hgP
  rw [frameAct_one]
  haveI := P.isPrime
  set x : (VS D).V := frame (liftF F'₂) b - frame (lf D F0) b with hx
  obtain ⟨p, hpdef⟩ : ∃ p : PlF D, p = Formalism.L2.SG.Pf.LocalDenominators.plOf P.asIdeal P.isMaximal := ⟨_, rfl⟩
  have hPp : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal := by rw [hpdef]; rfl
  have hty : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) :=
    (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P hPp).1 hgP
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 ((D.s_split p).2 hty)
  have hag := (Zd.agree p).2.2.2.2.2
  obtain ⟨g', hMs⟩ : ∃ g', (Zd.M p).split = some g' := by
    cases hm : (Zd.M p).split with
    | none => rw [hm, hsg] at hag; exact hag.elim
    | some g' => exact ⟨g', rfl⟩
  have hadm := ((hloc p).1.1.2.2.2.2.2 g' hMs).2.2 b

  have hrow := hC.2.1.1 γ.lam γ.mem
  have hgP' : ∀ P' : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      P'.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P'.asIdeal :=
    fun P' hP' => (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P' hP').2 hty
  obtain ⟨-, w, hw, hw1⟩ := Formalism.L2.SG.Pf.BBTie.bt_typed_frFac Zd (Formalism.L2.SG.Pf.locEqC_holds D Zd)
    (Formalism.L2.SG.Pf.locDiffC_holds D Zd) p F0 γ.lam hrow.2.1.1.fg hrow.2.2 hrow.2.1.2.2.2 hgP' b
  have hO := (Zd.agree p).2.2.2.1
  have hsg' : TermLoc.sgnP' D p b = TermLoc.sgnP D p b := by
    show (match (D.s.atP p).split with | some _ => TermLoc.sgnP D p b | none => (-1) ^ (D.R.rS - b.val)) = _
    rw [hsg]
  set c : (D.s.atP p).Ep := TermLoc.sgnP D p b * frFac Zd.δ p b with hc
  have hdiff : locF' Zd p F'₂ b - (tLoc Zd p γ).f b = c • baseChange₂ D p x := by
    show (TermLoc.sgnP' D p b * frFac Zd.δ p b) • baseChange₂ D p (frame F'₂ b) -
      (TermLoc.sgnP D p b * frFac Zd.δ p b) • baseChange₂ D p (frame (lf D F0) b) = _
    rw [hsg', hx, map_sub, smul_sub]
    rfl
  have hinv : (TermLoc.sgnP D p b * w) * c = 1 := by
    rw [hc, mul_mul_mul_comm, TermLoc.localSign_sq, hw1, one_mul]
  have hinvO : TermLoc.sgnP D p b * w ∈ (Zd.M p).L.O := by
    rw [hO]; exact (D.s.atP p).O.mul_mem (sgnP_mem p b) (by rw [← hO]; exact hw)

  have h1 : baseChange₂ D p x ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g'.q : (D.s.atP p).Fp))
      (lattice₂ D Zd.M p Λ₂) := by
    have : baseChange₂ D p x = (TermLoc.sgnP D p b * w) • (locF' Zd p F'₂ b - (tLoc Zd p γ).f b) := by
      rw [hdiff, smul_smul, hinv, one_smul]
    rw [this]
    exact Submodule.smul_mem _ ⟨_, hinvO⟩ hadm

  have hqg := Formalism.L2.SG.Pf.Cnt.DualityBasisChange.q_gS_inv_mem Zd.agree p hMs
  have h2 : (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ₂ := by
    have key : ∀ v ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g'.q : (D.s.atP p).Fp))
        (lattice₂ D Zd.M p Λ₂), (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • v ∈ lattice₂ D Zd.M p Λ₂ := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨y, hy, rfl⟩ := hv
        rw [smul_smul]
        exact (lattice₂ D Zd.M p Λ₂).smul_mem ⟨_, hqg⟩ hy
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add a c _ _ ha hc => rw [smul_add]; exact Submodule.add_mem _ ha hc
      | smul o v _ hv =>
        have e : (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • (o • v) =
            o • ((D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • v) := by
          show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _
          rw [smul_smul, smul_smul, mul_comm]
        rw [e]; exact Submodule.smul_mem _ _ hv
    exact key _ h1
  have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    have := Formalism.L2.SG.Pf.Cnt.DualityBasisChange.gS_ne (D := D); exact_mod_cast this
  have h3 : baseChange₂ D p ((((gS D : ℕ) : D.host.E))⁻¹ • x) ∈ lattice₂ D Zd.M p Λ₂ := by
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact h2
  haveI := p.isPrime
  have h4 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p hlat _).1 h3
  obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ₂ _).1 h4
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, fun h => ht (by rw [← hPp]; exact h), ?_⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x =
      ((gS D : ℕ) : 𝓞 D.host.E) • (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • ((((gS D : ℕ) : D.host.E))⁻¹ • x)) := by
    rw [Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.oE_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) htx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u') (F0) in

def GenXiRev : Prop :=
  ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (p : PlF D),
    IsRowLat D F0 Λ → AdmWit Λ (gS D) (lf D F0) F' 1 → IsLift Λ F' →
    (locH Zd p).IsGeneric ⟨lattice₂ D Zd.M p Λ, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f, locF' Zd p F',
      (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T'⟩ →
    (locH Zd p).IsGeneric (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u'))

theorem rowLat_of_move (hC : CtxP u u' F0 what₂) (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (himg : (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) : IsRowLat D F0 Λ₂ := by
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hg : Formalism.HermitianLatticesTheory.gmap n Λ₂ = γ.lam := gmap_eq_of_image himg
  have hni : n⁻¹ ∈ Formalism.L2.SG.Pf.Cnt.StabilizerQuotient.G0 F0 := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hn.1, fun a => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) a
    · have h := hn.2.2.2.2
      simp only [FlagG.fvec, Fin.snoc_last]
      show n.symm _ = _
      rw [LinearEquiv.symm_apply_eq, h]
    · have h := hn.2.2.2.1 i
      simp only [FlagG.fvec, Fin.snoc_castSucc]
      show n.symm _ = _
      rw [LinearEquiv.symm_apply_eq, h]
  have h2 := Formalism.L2.SG.Pf.Cnt.StabilizerQuotient.rowLat_gmap ⟨n⁻¹, hni⟩ hrow
  have e : Formalism.HermitianLatticesTheory.gmap (n⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) γ.lam = Λ₂ := by
    rw [← hg, ← Formalism.L2.SG.Pf.gmap_mul_sat, inv_mul_cancel, Formalism.L2.SG.Pf.gmap_one_sat]
  rw [← e]; exact h2

variable {Zd}

theorem btGen_of (hOK : BtOK Zd u u' F0 what₂) (hGX : GenXiRev Zd u' F0) : BtGen Zd u u' F0 what₂ := by
  intro hC γ Z F'₂ φ φ' Λ₂ hs
  have hLift := btLift_holds Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hAdm := btAdm Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hG := btG_holds Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hOKv := hOK hC γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, ⟨n, hn, himg⟩⟩ := hs
  have hR := rowLat_of_move hC γ hn himg
  have hPD : PD D Λ₂ (lf D F0) u' (liftF F'₂) := ⟨hLift, ⟨1, hAdm⟩, hOKv⟩
  refine (Formalism.L2.SG.Pf.frameGenLoc_holds D Zd F0 Λ₂ (liftF F'₂) hR hPD
    (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) hG).2 fun p => ?_
  exact hGX Λ₂ (liftF F'₂) p hR hAdm hLift (hloc p).1

theorem bwdTerm'_of' (hOK : BtOK Zd u u' F0 what₂) (hGX : GenXiRev Zd u' F0) : BwdTerm' Zd u u' F0 what₂ :=
  bwdTerm'_of Zd (btLift_holds Zd) (btAdm Zd) (btG_holds Zd) hOK (btGen_of hOK hGX)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
