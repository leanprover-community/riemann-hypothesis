import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin

noncomputable section

namespace GlobalTheory.HeightCounting.Up.RowModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000




theorem overRows_allSt {p : RowP} (h : OverRows p) :
    AllSt fun K B f T w P x => p K B f T w x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ _ _ H kp _ _ w s P x =>
    s.1.elim fun c => H kp w c x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt



open Classical in

def reset {D : D7} (Rw : RowSide D) (a : ∀ w, D.naut.LP w) : RowSide D where
  locR σ w := if ∃ k : Fin 2, w ∈ placesOver D.host.E (D.host.g k) then Rw.locR σ w else a w
  satR := Rw.satR
  lab_eq k σ v := by rw [if_pos ⟨k, D.naut.plGw_over k v⟩]; exact Rw.lab_eq k σ v

theorem one_lt_norm {D : D7} (w : PlE D.host) : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w



theorem isoInf_string {D : D7} (χ : D.naut.CG 1) (d : ℕ) (τ : D.host.E →+* ℂ) (s : ℂ) (h : D.naut.infG χ τ = {s}) :
    isoInf D.nd D.naut [⟨1, χ, d⟩] τ = (Multiset.range d).map fun c : ℕ => s + ((d : ℂ) - 1 - 2 * c) / 2 := by
  simp only [isoInf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, h, Multiset.map_singleton]
  have : ∀ (n : ℕ) (g : ℂ → ℂ), (List.map (fun k : ℂ => ({g k} : Multiset ℂ)) (List.range n)).sum =
      (Multiset.range n).map fun c : ℕ => g c := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Multiset.range_succ, Multiset.map_cons, ← ih, List.range_succ]
      simp [add_comm]
  rw [this d fun k => s + (((d : ℂ) - 1) / 2 - k)]
  refine Multiset.map_congr rfl fun c _ => by ring

theorem eta_of_charSide {D : D7} {cf : CharFrame D} (C : CharSide D cf) (τ : D.what₂.Tau) :
    D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧ D.naut.infG D.naut.etaTinv (embTauBar D τ) = {(1 / 2 : ℂ)} := by
  have h : (C.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) fun _ => -(1 / 2) := by
    refine ⟨fun _ => -1, fun _ => by norm_num, fun k => ?_⟩
    rw [C.etaTinv]
    have := cf.isEta.inf k
    have e : (cf.eta⁻¹).inf k = (cf.eta.inf k)⁻¹ := rfl
    rw [e, Units.val_inv_eq_inv_val, this, ← Finset.prod_inv_distrib]
    simp
  have := C.infG _ _ h (D.eTau τ)
  refine ⟨this.1.trans (by simp), this.2.trans (by simp)⟩

theorem inf_eq_paramV {D : D7} {cf : CharFrame D} (C : CharSide D cf) (j : Fin D.R.m) (μ : D.naut.CG 1) (τ : D.what₂.Tau)
    (hμ : D.naut.infG μ (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(((D.hc τ).e j : ℚ) : ℂ)} ∧ D.naut.infG μ (embTauBar D τ) = {(((D.hc τ).e j : ℚ) : ℂ)}) :
    (hcSigma (D.hc τ)).map (· - 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
      NG.paramV D.R (D.hc τ) j (1 / 2) ∧
    (hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (embTauBar D τ) =
      (NG.paramV D.R (D.hc τ) j (1 / 2)).map fun y => -y := by
  have e := eta_of_charSide C τ
  have h1 := D.naut.infG_tw μ _ _ _ e.1
  have h2 := D.naut.infG_tw μ _ _ _ e.2
  rw [hμ.1, Multiset.map_singleton] at h1
  rw [hμ.2, Multiset.map_singleton] at h2
  rw [isoInf_string _ _ _ _ h1, isoInf_string _ _ _ _ h2]
  constructor
  · simp only [hcSigma, NG.paramV, Multiset.map_add, Multiset.map_map, Function.comp_def]
    congr 1
  · simp only [hcSigma, NG.paramV, Multiset.map_add, Multiset.map_map, Function.comp_def]
    congr 1
    · congr 1 <;> exact Multiset.map_congr rfl fun _ _ => by ring
    · have hr : Multiset.range D.R.t = (Multiset.range D.R.t).map fun c => D.R.t - 1 - c := by
        have := congrArg Finset.val (Finset.range_image_pred_top_sub D.R.t)
        rw [Finset.image_val_of_injOn (fun a ha b hb h => by
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb; omega)] at this
        exact this.symm
      conv_rhs => rw [hr]
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun c hc => ?_
      have hc' : c < D.R.t := Multiset.mem_range.1 hc
      have : ((D.R.t - 1 - c : ℕ) : ℂ) = (D.R.t : ℂ) - 1 - c := by
        rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
      simp only [Function.comp_apply, this]; ring

theorem infinitesimal_character_reference {D : D7} {cf : CharFrame D} (C : CharSide D cf) (j : Fin D.R.m) (τ : D.what₂.Tau) :
    D.naut.infG (C.e1.symm ⟨cf.mu0 j, (cf.isMu0 j).unitary⟩) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(((D.hc τ).e j : ℚ) : ℂ)} ∧
      D.naut.infG (C.e1.symm ⟨cf.mu0 j, (cf.isMu0 j).unitary⟩) (embTauBar D τ) = {(((D.hc τ).e j : ℚ) : ℂ)} := by
  have := C.infG (C.e1.symm ⟨cf.mu0 j, (cf.isMu0 j).unitary⟩) _ (by rw [Equiv.apply_symm_apply]; exact (cf.isMu0 j).inf) (D.eTau τ)
  refine ⟨this.1.trans ?_, this.2.trans ?_⟩ <;> simp [eExp]



theorem plGw_split (D : D7) (k : Fin 2) (v : D.nd.PlG k) : IsSplitPl D.host (D.naut.plGw k v) :=
  (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)).2.2.1


theorem local_lift_at_reference {D : D7} {cf : CharFrame D} (C : CharSide D cf) (Rw : RowSide D) (j : Fin D.R.m) (σ : D.what₂.FT)
    (π : D.nbc.AU (j.1 + 1)) (hs : SphericalInertData.SphInert D.nd D.naut D.nbc (j.1 + 1) π)
    (hl : ∀ w, IsSplitPl D.host w → D.nbc.locAU (j.1 + 1) π w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w)
      (spehLoc D.nd D.naut ⟨1, C.e1.symm ⟨cf.mu0 j, (cf.isMu0 j).unitary⟩, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w))
    (hi : ∀ τ, D.nbc.infW (j.1 + 1) (D.nbc.wtAU (j.1 + 1) π) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = NG.paramV D.R (D.hc τ) j (1 / 2) ∧
      D.nbc.infW (j.1 + 1) (D.nbc.wtAU (j.1 + 1) π) (embTauBar D τ) = (NG.paramV D.R (D.hc τ) j (1 / 2)).map fun y => -y) :
    LiftAt D Rw (j.1 + 1) σ π (C.e1.symm ⟨cf.mu0 j, (cf.isMu0 j).unitary⟩) where
  csd := (C.csd _).2 (by rw [Equiv.apply_symm_apply]; exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ (cf.isMu0 j).triv)
  unr w hw := ⟨(C.unr_iff _ w).2 (by
    rw [Equiv.apply_symm_apply]
    exact (cf.isMu0 j).unr w fun k hk =>
      hw (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1), (D.naut.etaTinv_def w).1⟩
  sph := hs
  loc := hl
  eta := eta_of_charSide C
  inf τ := ⟨(hi τ).1.trans (inf_eq_paramV C j _ τ (infinitesimal_character_reference C j τ)).1.symm,
    (hi τ).2.trans (inf_eq_paramV C j _ τ (infinitesimal_character_reference C j τ)).2.symm⟩

end GlobalTheory.HeightCounting.Up.RowModel

end
