import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepsOnto
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopMultAndExtVInjective
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.TowerModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Laws

theorem multT_anti {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (hJ : J ⊆ J') (hχ : ∀ k ∈ J, χ k = χ' k) : MultT θ M J' χ' ≤ MultT θ M J χ := by
  unfold MultT Mult
  refine Submodule.map_mono (Submodule.span_mono fun T hT => ?_)
  exact ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k (hJ hk) g, hT.equiv, hT.cont⟩

theorem multT_withP_le {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) :
    MultT θ M (levS V β (withP L P)) (levChi V β (withP L P)) ≤ MultT θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) := by
  refine multT_anti θ M (fun k hk => ?_) (fun k hk => ?_)
  · have h1 : rTup β L (finE V k) = 1 := Subgroup.mem_bot.1 hk.2.2
    refine ⟨hk.1, hk.2.1, ?_⟩
    show rTup β L (finE V k) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · have h1 : rTup β L (finE V k) = 1 := Subgroup.mem_bot.1 hk.2.2
    unfold levChi
    rw [levFn_withP, levFn_flag1, h1, blockDiagonalExtendByOnePrimeField_one, one_mul]

variable (W : Tower D)

theorem cp_le (P : W.Lv) (j : ℕ) : W.CP P j ≤ W.CC j := multT_withP_le W.θ (W.MY j) (W.βY j) (W.datYt () j W.triv) P

theorem cxp_le (P : W.Lv) : W.CXP P ≤ W.CX := multT_withP_le W.θ W.MX W.βX (W.datXt ()) P









theorem xi_one (h : W.Pre) : W.xiH () = 1 := h.chars.xi_base

theorem Q_empty (h : W.Pre) : W.Q () = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
  have := (h.chars.Q_ram () PP).2 (Or.inl hP)
  rw [h.chars.xi_base] at this
  exact this (by intro; simp)



end Laws

theorem nonempty_tower (D : D7) (L : LevCh D Unit) (hY : ∀ j, Nonempty (DSModel (Yc D j) (parB (Ptw D) (min j D.R.m))))
    (hX : Nonempty (DSModel D.sp.X' (parB (Ptw D) D.R.m))) :
    ∃ W : Tower D, W.toLevCh = L ∧ IsInfFam W.θ ∧ IsStdChar D W.ψ (-1) ∧ ¬ W.Pre := by
  obtain ⟨MX⟩ := hX
  obtain ⟨⟨θ, hθ⟩, ψ, hψ⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  exact ⟨{ toLevCh := L, θ := θ, ψ := ψ, MY := fun j => (hY j).some, MX := MX, νY := fun _ => 0, fdY := fun _ => ∅,
           νX := 0, fdX := ∅, ωY := fun _ => 1, ωX := 1, vac := fun _ => 0, vacX := 0, vY := fun _ => 0, vX := 0,
           ItY := fun _ => 0, ItX := 0, ioY := fun _ => 0, ioX := 0 }, rfl, hθ, hψ, fun h => h.ItX.ne rfl⟩

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def levAt (L : LevCh D T) (t : T) : LevCh D Unit :=
  { L with xiH := fun _ => L.xiH t, xi := fun _ => L.xi t, Q := fun _ => L.Q t, xiR := fun _ => L.xiR t }

theorem levAt_is {L : LevCh D T} {t : T} (h : L.Is t) : (levAt L t).Is () :=
  ⟨h.mu0, h.eta, fun _ => h.xi t, fun _ _ _ => rfl, h.xi_base, fun _ => h.xi_fin t, fun _ => h.xi_triv t, fun _ => h.xi_tame t,
    h.Pg, fun _ => h.Q_pl t, fun _ => h.Q_off t, fun p hp => (h.Q_de p hp).imp fun _ hq _ => hq t, fun _ => h.Q_ram t, h.chi,
    fun _ => h.xiR t, h.βY, h.βX, h.βV, h.βW⟩

set_option maxHeartbeats 2000000 in

def ofReal (R : RealDat D A Ks) (hT : R.TopMult) (t : T) : Tower D where
  toLevCh := levAt R.toLevCh t
  θ := R.θ
  ψ := R.ψ
  MY := R.MY
  MX := R.MX
  νY := R.νY t
  fdY := R.fdY t
  νX := R.νX t
  fdX := R.fdX t
  ωY := R.ωY t
  ωX := R.ωX t
  vac := R.vac
  vacX := R.vacX
  vY := R.vY t
  vX := R.vX t
  ItY := R.ItY
  ItX := R.ItX
  ioY := R.ioY t
  ioX := R.ioX t ∘ₗ (LinearEquiv.ofEq _ _ (hT t).symm).toLinearMap

theorem isIo_ofEq {G H S Sinf Ds Dt : Type} [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds]
    [AddCommGroup Dt] [Module ℂ Dt] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {pt : Sinf → S}
    {It : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt} {C C' : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))} {Ct : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))}
    {io : C →ₗ[ℂ] Ct} (e : C' = C) (h : Lift.IsIo ν 𝓕 th pt It C Ct io) :
    Lift.IsIo ν 𝓕 th pt It C' Ct (io ∘ₗ (LinearEquiv.ofEq _ _ e).toLinearMap) := by
  subst e; exact h

set_option maxHeartbeats 2000000 in

theorem ofReal_is (R : RealDat D A Ks) (hT : R.TopMult) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) :
    (ofReal R hT A.μ0).Is :=
  { chars := levAt_is hl
    inf := hm.inf
    std := (hc.ωX A.μ0).std
    νY := hm.νY A.μ0
    νY' := hm.νY' A.μ0
    νX := hm.νX A.μ0
    ωY := hc.ωY A.μ0
    ωX := hc.ωX A.μ0
    vY := hc.vY A.μ0
    vX := hc.vX A.μ0
    ptY := hc.ptY A.μ0
    ptX := hc.ptX A.μ0
    ItY := hc.ItY A.μ0
    ItX := hc.ItX A.μ0
    ioY := hc.ioY A.μ0
    ioX := isIo_ofEq (hT A.μ0).symm (hc.ioX A.μ0) }


set_option maxHeartbeats 2000000 in

theorem ofReal_isDn (R : RealDat D A Ks) (hT : R.TopMult) (t : T) (x : (R.HX t).H) :
    (ofReal R hT t).IsDn (R.cX.toMap R.prX ((R.HX t).e x)) (R.thDn t x) :=
  ⟨(hT t).le ⟨x, rfl⟩, rfl⟩

end Real

end GlobalTheory.Core.Rk.TowerModel

end
