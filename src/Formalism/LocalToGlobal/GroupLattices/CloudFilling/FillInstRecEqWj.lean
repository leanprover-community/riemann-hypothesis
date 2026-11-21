import Formalism.LocalToGlobal.GroupLattices.CloudFilling.CloudBound
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.ExistsPowOrbRep
import Formalism.SharpRestriction.GrowthBounds.DefsInst
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.LevelGatherings
import Formalism.LocalRingCardinality.SpanPowerMembership.GatAdd
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.RepTie
import Formalism.LocalRingCardinality.DataExtra
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

section
noncomputable section

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.FrobeniusOrbits

namespace Formalism.L2.G

theorem wG_idx (R : Ranks) (e : Fin R.m → ℚ) (b j : ℕ) (hb : b < R.m) (hj : j - 1 < R.m) (h : b = j - 1) (h1 : 1 ≤ j) :
    wG R (e ⟨b, hb⟩) (b + 1) = wG R (e ⟨j - 1, hj⟩) j := by
  subst h
  rw [Nat.sub_add_cancel h1]

theorem wRec_eq (D : D7) (u : D.what₂.Word) (g : D.R.Psi) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    ((wRec D u g j : ℤ) : ℝ) = wj D j (D.eTau.symm g) - Formalism.MainNotions.G.kaJ D j := by
  have hj' := Finset.mem_Icc.1 hj
  have hjm : j - 1 < D.R.m := by omega
  have h := (D.fm u).lam_eq D.R.m le_rfl (D.eTau.symm g)
    ⟨D.R.k + (min j D.R.m - 1) * (D.R.t + 1), blkIdx_lt D.R j⟩
  rw [dif_neg (by show ¬ D.R.k + (min j D.R.m - 1) * (D.R.t + 1) < D.R.k; omega)] at h
  have hb : (D.R.k + (min j D.R.m - 1) * (D.R.t + 1) - D.R.k) / (D.R.t + 1) = j - 1 := by
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (Nat.succ_pos _), min_eq_left hj'.2]
  have h' : ((((D.fm u).lam D.R.m (D.eTau.symm g)).w
      ⟨D.R.k + (min j D.R.m - 1) * (D.R.t + 1), blkIdx_lt D.R j⟩ : ℤ) : ℚ) =
      -wG D.R ((D.hcW u (D.eTau.symm g)).e ⟨j - 1, hjm⟩) j := by
    rw [h]
    exact congrArg Neg.neg (wG_idx D.R _ _ j _ hjm hb hj'.1)
  rw [D.hcW_e] at h'
  have h'' := congrArg (fun q : ℚ => (q : ℝ)) h'
  simp only [wG] at h''
  push_cast at h''
  unfold wRec wj Formalism.MainNotions.G.kaJ
  rw [dif_pos hjm]
  push_cast
  rw [h'']
  ring

theorem lamRec_real (D : D7) (u : D.what₂.Word) (g : D.R.Psi) (i : Fin (D.R.k - 1 + 1)) (hi : i.1 < D.R.k) :
    ((lamRec D u g i : ℤ) : ℝ) =
      (((D.hcW u (D.eTau.symm g)).u ⟨i.1, hi⟩ : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i.1 : ℝ)) := by
  have h := (D.fm u).lam_eq 0 (Nat.zero_le _) (D.eTau.symm g) ⟨i.1, by simp only [Ranks.N]; omega⟩
  rw [dif_pos hi] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [hcToWeightQ, rhoVec] at h'
  push_cast at h'
  exact h'

theorem lamRec_top {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (g : D.R.Psi) (t : D.host.TT)
    (ht : (g : D.R.GG) = D.R.tau1 t) :
    lamRec D u g 0 = L.aT t ∧ lamRec D u g (Fin.last _) = -L.bT t := by
  have hk := k_pred D.R
  have hk0 : 0 < D.R.k := by omega
  have hkR : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have tu := L.top_u (D.eTau.symm g) t hk0 (by rw [Equiv.apply_symm_apply]; exact ht)
  constructor
  · have h := lamRec_real D u g 0 (by simpa using hk0)
    apply Int.cast_injective (α := ℝ)
    rw [h]
    have e : (⟨(0 : Fin (D.R.k - 1 + 1)).1, by simpa using hk0⟩ : Fin D.R.k) = ⟨0, hk0⟩ := Fin.ext (by simp)
    rw [e, D.hcW_first u _ hk0, tu.1]
    simp
  · have h := lamRec_real D u g (Fin.last _) (by simp only [Fin.val_last]; omega)
    apply Int.cast_injective (α := ℝ)
    rw [h]
    have e : (⟨(Fin.last (D.R.k - 1)).1, by simp only [Fin.val_last]; omega⟩ : Fin D.R.k) =
        ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only [Fin.val_last])
    rw [e, D.hcW_last u _ hk0, tu.2]
    simp only [Fin.val_last]
    rw [hkR]
    push_cast
    ring

def cRec {D : D7} (L : SizeData₂ D) : ℕ := ⌊Formalism.MainNotions.G.cG L⌋₊

theorem cG_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.G.cG L := by
  unfold Formalism.MainNotions.G.cG
  linarith [L.Sc_pos]

theorem cRec_le {D : D7} (L : SizeData₂ D) : (cRec L : ℝ) ≤ Formalism.MainNotions.G.cG L := Nat.floor_le (cG_nonneg L)

theorem lt_cRec {D : D7} (L : SizeData₂ D) : 4 * L.Sc - 1 < (cRec L : ℝ) := by
  have := Nat.lt_floor_add_one (Formalism.MainNotions.G.cG L)
  unfold cRec
  unfold Formalism.MainNotions.G.cG at this ⊢
  linarith

theorem ktl_le_Del {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) :
    (D.R.k : ℝ) + D.R.t + 1 ≤ (D.s.Del : ℝ) := by
  have h := P.Del_ge.2.2.2
  have hm : (1 : ℝ) ≤ (D.R.m : ℝ) := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ hm
  have hN : (D.R.k : ℝ) + D.R.t + 1 ≤ (D.R.N D.R.m : ℝ) := by
    simp only [Ranks.N]
    push_cast
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) + 1 := by positivity
    nlinarith
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem five_le_k (R : Ranks) : (5 : ℝ) ≤ (R.k : ℝ) := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  exact_mod_cast (by omega : 5 ≤ R.k)

theorem ktl_le_Sc {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : 20 * ((D.R.k : ℝ) + D.R.t + 1) ≤ L.Sc := by
  have h1 := ktl_le_Del P
  have h2 := five_le_k D.R
  have h3 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  rw [L.Sc_eq]
  nlinarith

theorem w''_le_wj_one {D : D7} (L : SizeData₂ D) (τ : D.what₂.Tau) : L.sc.w'' D.R.n ≤ wj D 1 τ := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hle := Formalism.MainNotions.Inhab.scale_w''_le L.sc D.R.n (Formalism.MainNotions.Inhab.ranks_one_le_n D.R)
  by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
    have h1 := (L.win_top 1 le_rfl hm τ ⟨t, ht⟩ hte.symm).1
    have h2 := L.bT_ge ⟨t, ht⟩
    have h3 := Formalism.MainNotions.Inhab.scale_b'_nonneg L.sc
    linarith [hle.1]
  · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have h1 := (L.win_thick 1 le_rfl hm τ hth).1
      linarith [hle.2]
    · exact (L.win_thin 1 le_rfl hm τ ⟨(D.eTau τ).2, htop, hth⟩).1

theorem cloudBound {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (u : D.what₂.Word) : CloudBound D u (cRec L) := by
  have hk := k_pred D.R
  have hk5 := five_le_k D.R
  have hk5n : 5 ≤ D.R.k := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    omega
  have hS := ktl_le_Sc P
  have hc := lt_cRec L
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hmid : ∀ (g : D.R.Psi) (i : Fin (D.R.k - 1 + 1)), 0 < i.val → i.val < D.R.k - 1 →
      |lamRec D u g i| ≤ (cRec L : ℤ) := by
    intro g i h0 h1
    have hi : i.1 < D.R.k := by omega
    have h := lamRec_real D u g i hi
    have cl := L.cloud_u u (D.eTau.symm g) ⟨i.1, hi⟩ h0 (by show i.1 + 1 < D.R.k; omega)
    have hiR : (i.1 : ℝ) + 1 ≤ (D.R.k : ℝ) := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
    have h2 : |((lamRec D u g i : ℤ) : ℝ)| ≤ (cRec L : ℝ) := by
      rw [h, abs_le]
      constructor <;> linarith [cl.1, cl.2]
    exact_mod_cast h2
  refine ⟨fun g _ i h0 h1 => hmid g i h0 h1, fun g hg i => ?_, fun g => ?_⟩
  · have hg' : (D.eTau (D.eTau.symm g) : D.R.GG) ∉ D.host.topPlaces := by rwa [Equiv.apply_symm_apply]
    have hk0 : 0 < D.R.k := by omega
    by_cases h0 : i.val = 0
    · have hi : i.1 < D.R.k := by omega
      have h := lamRec_real D u g i hi
      have e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨0, hk0⟩ := Fin.ext h0
      rw [e, D.hcW_first u _ hk0, h0] at h
      have g1 := (L.cloud_gap (D.eTau.symm g) (by omega) hg').1
      have g2 := P.cloud_place_bound (D.eTau.symm g) (by omega) hg'
      have g3 := L.cloud_v (D.eTau.symm g) ⟨0, by omega⟩
      push_cast at g1 g2
      have h2 : |((lamRec D u g i : ℤ) : ℝ)| ≤ (cRec L : ℝ) := by
        rw [h, abs_le]
        push_cast
        constructor <;> linarith [g3.1, g3.2]
      exact_mod_cast h2
    · by_cases h1 : i.val < D.R.k - 1
      · exact hmid g i (Nat.pos_of_ne_zero h0) h1
      · have hi1 : i.val = D.R.k - 1 := by have := i.2; omega
        have hi : i.1 < D.R.k := by omega
        have h := lamRec_real D u g i hi
        have e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext hi1
        have hkR : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [e, D.hcW_last u _ hk0, P.uk_extreme (D.eTau.symm g) (by omega) hg', hi1, hkR] at h
        have g3 := L.cloud_v (D.eTau.symm g) ⟨D.R.k - 2, by omega⟩
        push_cast at h
        have h2 : |((lamRec D u g i : ℤ) : ℝ)| ≤ (cRec L : ℝ) := by
          rw [h, abs_le]
          constructor <;> linarith [g3.1, g3.2]
        exact_mod_cast h2
  · have h1 : (1 : ℕ) ∈ SizeData₂.lifts D := Finset.mem_Icc.2 ⟨le_rfl, by have := D.R.two_le_m; omega⟩
    have hw := wRec_eq D u g 1 h1
    have hw'' := w''_le_wj_one L (D.eTau.symm g)
    have hkS := P.kS_le
    have hSc := L.Sc_pos
    have hka : Formalism.MainNotions.G.kaJ D 1 = ((D.R.k : ℝ) + D.R.t + 1) / 2 := by
      unfold Formalism.MainNotions.G.kaJ
      push_cast
      ring
    have hcle := cRec_le L
    unfold Formalism.MainNotions.G.cG at hcle
    have h5 : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := by nlinarith
    have h2 : ((cRec L : ℕ) : ℝ) ≤ ((wRec D u g 1 : ℤ) : ℝ) := by
      rw [hw, hka]
      linarith
    exact_mod_cast h2

end Formalism.L2.G
end
end

section
noncomputable section

namespace Formalism.L2.G

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.G Formalism.MainNotions.Inhab

variable {D : D7}

def cutJ (D : D7) (j : ℕ) : ℕ := max 1 (min j D.R.m)

theorem cutJ_mem (D : D7) (j : ℕ) : 1 ≤ cutJ D j ∧ cutJ D j ≤ D.R.m := by
  have := D.R.two_le_m
  unfold cutJ
  omega

theorem cutJ_of_mem {j : ℕ} (hj : j ∈ SizeData₂.lifts D) : cutJ D j = j := by
  have := Finset.mem_Icc.1 hj
  unfold cutJ
  omega

open Classical in

def offRec (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) : ℝ :=
  wj D (cutJ D j) (tauOf D z) - (if z.1 = false ∧ z.2 ∈ D.host.TT then (bL L z.2 : ℝ) else 0)

theorem offRec_top (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) (hz : IsTopPl D z) :
    L.sc.b' / L.sc.x ≤ offRec L j z ∧ offRec L j z ≤ L.sc.b' / L.sc.x + L.etaSz := by
  have hz' : z.1 = false ∧ z.2 ∈ D.host.TT := hz
  have h0 : (D.eTau (tauOf D z) : D.R.GG) = D.R.tau1 z.2 := by
    rw [eTau_tauOf, ← plGG_false]
    congr 1
    exact Prod.ext hz'.1 rfl
  have h1 := L.win_top (cutJ D j) (cutJ_mem D j).1 (cutJ_mem D j).2 (tauOf D z) ⟨z.2, hz'.2⟩ h0
  have h2 : bL L z.2 = L.bT ⟨z.2, hz'.2⟩ := by unfold bL; rw [dif_pos hz'.2]
  unfold offRec
  rw [if_pos hz', h2]
  constructor <;> linarith [h1.1, h1.2]

theorem offRec_thin (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) (hz : IsThinPl D z) :
    L.sc.w'' D.R.n ≤ offRec L j z ∧ offRec L j z ≤ L.sc.w'' D.R.n + L.etaSz := by
  have hz' : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) := hz.1
  have h1 := L.win_thin (cutJ D j) (cutJ_mem D j).1 (cutJ_mem D j).2 (tauOf D z)
    (by
      rw [eTau_tauOf]
      exact ⟨Formalism.MainNotions.Inhab.plGG_mem_Psi D z, fun h => hz.1 ((plGG_top_iff D z).1 h),
        fun h => hz.2 ((plGG_thick_iff D z).1 h)⟩)
  unfold offRec
  rw [if_neg hz', sub_zero]
  exact h1

theorem offRec_thick (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) (hz : IsThickPl D z) :
    L.sc.b ≤ offRec L j z ∧ offRec L j z ≤ L.sc.b + L.etaSz + 1 := by
  have ht : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) := fun h => by
    have h1 := h.1
    rw [hz.1] at h1
    exact Bool.noConfusion h1
  have h1 := L.win_thick (cutJ D j) (cutJ_mem D j).1 (cutJ_mem D j).2 (tauOf D z)
    (by rw [eTau_tauOf]; exact (plGG_thick_iff D z).2 hz)
  unfold offRec
  rw [if_neg ht, sub_zero]
  exact h1

def instRec (L : SizeData₂ D) (K : Consts) (Ce : ℝ) : Inst D L where
  bs := bsH D.R.toFrame
  bs_orb := bsH_orb D.R.toFrame
  bs_step := bsH_step D.R.toFrame
  off := offRec L
  off_top := offRec_top L
  off_thin := offRec_thin L
  off_thick := offRec_thick L
  kapI := fun p n' TT a b => sInf (kapISet L K p n' TT a b)
  ep := fun p => ⌈Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a⌉₊

theorem instRec_fill (L : SizeData₂ D) (K : Consts) (Ce : ℝ) :
    ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × HH D), (D.eTau τ : D.R.GG) = plGG D z →
      fill (instRec L K Ce) (bL L) j z = wj D j τ := by
  intro j hj τ z h
  rw [eq_tauOf D τ z h]
  show _ + offRec L j z = _
  unfold offRec
  rw [cutJ_of_mem hj]
  ring

theorem instRec_fillG (L : SizeData₂ D) (K : Consts) (Ce : ℝ) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t : HH D) :
    fillG (instRec L K Ce) (bL L) j (false, t) = wj D j (D.eTau.symm (tau1P D.R.toFrame t)) - kaJ D j := by
  unfold fillG
  rw [instRec_fill L K Ce j hj (D.eTau.symm (tau1P D.R.toFrame t)) (false, t)
    (by rw [Equiv.apply_symm_apply, plGG_false]; rfl)]

theorem reps_instRec (L : SizeData₂ D) (K : Consts) (Ce : ℝ) {p : ℕ} (hc : IsResidueClassZero D p) :
    ((reps (instRec L K Ce) p : Finset (HH D)) : Set (HH D)) = Set.range (bsH D.R.toFrame (hP D p)) := by
  have hs : stepP D p = hP D p := by
    unfold stepP
    rw [if_neg (fun h : D.host.cls p = PrimeClass.signal => by
      have hc' : D.host.cls p = PrimeClass.inertClass := hc
      rw [hc'] at h; exact PrimeClass.noConfusion h)]
  unfold reps
  rw [hs]
  simp [instRec]

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frob_eq (D : D7) {T p : ℕ} (hg : GIdx D.host T p) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) :
    D.host.galE σ = (c0, D.R.iota (hP D p)) := by
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, inferInstance, inferInstance, σ, hσ, rfl⟩
  obtain ⟨P₂, h1, h2, σ₂, hσ₂, he⟩ := Classical.epsilon_spec hne
  have hv := @Formalism.BasicNotions.Examples₂.LevelValuationRings.frob_val _ D.host p hg.1 hg.2.2.1 P₂ h1 h2 σ₂ hσ₂
  have hh : D.R.iota (hP D p) = Formalism.BasicNotions.Examples₂.LevelValuationRings.hOf D.host p := by
    unfold hP
    rw [Formalism.HC.Frame.iota_iotaInv, ← he, hv]
  rw [hh]
  exact Formalism.BasicNotions.Examples₂.LevelValuationRings.frob_val D.host p hg.1 hg.2.2.1 P σ hσ

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

variable (D : D7) (u : D.what₂.Word) {T : ℕ} (hg : GIdx D.host T p)
    (hS : HidaSetting p (orderOf (zH D.R.toFrame (hP D p))) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zH D.R.toFrame (hP D p))) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ)

include hg in

theorem gatRec_n_frob (v : Fin (gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.nV)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (τ : D.host.E ≃ₐ[ℚ] D.host.E)
    (hτ : IsArithFrobAt ℤ τ P) :
    (gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.n' v =
      orderOf (D.host.galE τ).2 := by
  rw [frob_eq D hg P τ hτ]
  show orderOf (zPsi D.R.toFrame (D.R.iota (hP D p))) = orderOf (D.R.iota (hP D p))
  rw [← Subgroup.orderOf_coe]
  first
  | (rw [show (((zPsi D.R.toFrame (D.R.iota (hP D p))) : D.R.Psi) : D.R.GG) = MonoidHom.inr _ _ (D.R.iota (hP D p)) from rfl]
     exact orderOf_injective _ (fun a b h => congrArg Prod.snd h) _)
  | simp [zPsi, Prod.orderOf]
  | simp [zPsi, Prod.orderOf_mk]

include hg in

theorem gatRec_step_frob (v : Fin (gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.nV)
    (s : Fin ((gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.n' v))
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (τ : D.host.E ≃ₐ[ℚ] D.host.E)
    (hτ : IsArithFrobAt ℤ τ P) :
    ((D.eTau (gatRec_pos D u _ hS r L I ψ y e ⟨v, posAdd s 1⟩) : D.R.Psi) : D.R.GG) =
      ((D.eTau (gatRec_pos D u _ hS r L I ψ y e ⟨v, s⟩) : D.R.Psi) : D.R.GG) *
        D.host.galE τ * D.R.cc := by
  have hz : (((zPsi D.R.toFrame (D.R.iota (hP D p))) : D.R.Psi) : D.R.GG) = D.host.galE τ * D.R.cc := by
    rw [frob_eq D hg P τ hτ]
    refine Prod.ext ?_ ?_
    · show ((1, 1) : G0) = c0 * c0
      first
      | rfl
      | decide
      | simp [c0]
    · show D.R.iota (hP D p) = D.R.iota (hP D p) * 1
      rw [mul_one]
  rw [mul_assoc, ← hz]
  simp only [gatRec_pos, Equiv.trans_apply, Equiv.apply_symm_apply]
  first
  | exact congrArg Subtype.val (posG_step (zPsi D.R.toFrame (D.R.iota (hP D p))) v s)
  | exact congrArg Subtype.val (posG_step v s)
  | exact congrArg Subtype.val (posG_step (z := (zPsi D.R.toFrame (D.R.iota (hP D p)))) v s)

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LatticeCompatibleAt {D : D7} {L : SizeData₂ D} (X : Inst D L) {p : ℕ} (G : GAtP p)
    (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ D.what₂.Tau) (vOf : HH D → Fin G.P.nV) (Fl : Fills G) : Prop :=
  Fl.mm = D.R.m ∧ Fl.t = D.R.t ∧
  (Fl.c : ℝ) ≤ cG L ∧
  G.P.r = (if (p : ℝ) < L.sc.p0 D.R.k then rG L.sc else 1) ∧
  Set.InjOn vOf (reps X p) ∧
  (∀ (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (t : HH D),
    ((D.eTau (pos ⟨v, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau2 t →
      s ∉ Fl.TT v ∧ ∀ j ∈ SizeData₂.lifts D, (Fl.w v j s : ℝ) = fillG X (bL L) j (true, t)) ∧
  ∀ t0 ∈ reps X p,
    G.P.n' (vOf t0) = addOrderOf (hP D p) ∧
    ∀ s : Fin (G.P.n' (vOf t0)),
      ((D.eTau (pos ⟨vOf t0, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau1 (t0 + s.val • hP D p) ∧
      (s ∈ Fl.TT (vOf t0) ↔ t0 + s.val • hP D p ∈ D.host.TT) ∧
      (s ∈ Fl.TT (vOf t0) →
        Fl.a (vOf t0) s = aL L (t0 + s.val • hP D p) ∧
        Fl.b (vOf t0) s = bL L (t0 + s.val • hP D p)) ∧
      ∀ j ∈ SizeData₂.lifts D,
        (Fl.w (vOf t0) j s : ℝ) = fillG X (bL L) j (false, t0 + s.val • hP D p)

theorem latTied_iff {D : D7} {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) :
    LatTied hT X Y ↔ ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      LatticeCompatibleAt X (D.gat u w hg) (hT.gat_pos u w hg) (Y.vOf u w hg) (Y.Fl u w hg) := Iff.rfl

def rRec {D : D7} (L : SizeData₂ D) (p : ℕ) : ℕ := if (p : ℝ) < L.sc.p0 D.R.k then rG L.sc else 1

theorem tau_top_places_iff (D : D7) (t : HH D) : D.R.tau1 t ∈ D.host.topPlaces ↔ t ∈ D.host.TT := by
  rw [← Formalism.MainNotions.Inhab.plGG_false, Formalism.MainNotions.Inhab.plGG_top_iff]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem tau_coe_val (φ : Formalism.HC.Frame) (t : φ.A) : ((tau1P φ t : φ.Psi) : φ.GG) = φ.tau1 t := rfl

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem latTiedAt_rec {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (K : Consts) (Ce : ℝ) (u : D.what₂.Word)
    (hc : IsResidueClassZero D p) (hS : HidaSetting p (orderOf (zH D.R.toFrame (hP D p))) W Qq O Kf ι σ j w) (r : ℕ) (hr : r = rRec L p)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId Lc p (nOrb (zH D.R.toFrame (hP D p))) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* Oˣ)
    (y : compL Lc p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) :
    LatticeCompatibleAt (instRec L K Ce) (gatRec D u (D.R.iota (hP D p)) hS r Lc I ψ y e)
      (gatRec_pos D u (D.R.iota (hP D p)) hS r Lc I ψ y e) (vOfH D.R.toFrame (hP D p))
      (fillsRec D u (D.R.iota (hP D p)) hS r Lc I ψ y e (cRec L) (cloudBound L P u)) := by
  subst hr
  refine ⟨rfl, rfl, cRec_le L, rfl, ?_, ?_, ?_⟩
  · rw [reps_instRec L K Ce hc]
    exact vOfH_injOn _ _
  · intro v s t ht
    have ht' : ((posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩ : D.R.Psi) : D.R.GG) = D.R.tau2 t := by
      have h0 : ((D.eTau (D.eTau.symm (posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩)) : D.R.Psi) : D.R.GG) = D.R.tau2 t := ht
      rwa [Equiv.apply_symm_apply] at h0
    refine ⟨fun hs => ?_, fun jj hj => ?_⟩
    · have h1 : ((posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces := (Finset.mem_filter.1 hs).2
      rw [ht', ← Formalism.MainNotions.Inhab.plGG_true, Formalism.MainNotions.Inhab.plGG_top_iff] at h1
      exact Bool.noConfusion h1.1
    · show ((wRec D u (posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩) jj : ℤ) : ℝ) = _
      rw [wRec_eq D u _ jj hj]
      unfold fillG
      rw [instRec_fill L K Ce jj hj (D.eTau.symm (posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩)) (true, t)
        (by rw [Equiv.apply_symm_apply, ht', Formalism.MainNotions.Inhab.plGG_true])]
  · intro t0 ht0
    have ht0' : t0 ∈ Set.range (bsH D.R.toFrame (hP D p)) := by
      rw [← reps_instRec L K Ce hc]; exact ht0
    obtain ⟨x, rfl⟩ := ht0'
    refine ⟨orderOf_zH _ _, fun s => ?_⟩
    have hpos : posG (zH D.R.toFrame (hP D p)) ⟨vOfH D.R.toFrame (hP D p) (bsH D.R.toFrame (hP D p) x), s⟩ =
        tau1P D.R.toFrame (bsH D.R.toFrame (hP D p) x + s.val • hP D p) := by
      rw [posG_vOfH, bsH_idem]
    have hmem : (s ∈ (fillsRec D u (D.R.iota (hP D p)) hS (rRec L p) Lc I ψ y e (cRec L)
        (cloudBound L P u)).TT (vOfH D.R.toFrame (hP D p) (bsH D.R.toFrame (hP D p) x))) ↔
        bsH D.R.toFrame (hP D p) x + s.val • hP D p ∈ D.host.TT := by
      rw [← tau_top_places_iff]
      show s ∈ Finset.univ.filter _ ↔ _
      rw [Finset.mem_filter, hpos]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
    have ha : (fillsRec D u (D.R.iota (hP D p)) hS (rRec L p) Lc I ψ y e (cRec L)
        (cloudBound L P u)).a (vOfH D.R.toFrame (hP D p) (bsH D.R.toFrame (hP D p) x)) s =
        aL L (bsH D.R.toFrame (hP D p) x + s.val • hP D p) := by
      show (if ((posG (zH D.R.toFrame (hP D p)) _ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces then
        lamRec D u (posG (zH D.R.toFrame (hP D p)) _) 0 else 0) = _
      rw [hpos, tau_coe_val]
      unfold aL
      by_cases ht : bsH D.R.toFrame (hP D p) x + s.val • hP D p ∈ D.host.TT
      · rw [if_pos ((tau_top_places_iff D _).2 ht), dif_pos ht]
        exact (lamRec_top L u _ ⟨_, ht⟩ rfl).1
      · rw [if_neg (fun h => ht ((tau_top_places_iff D _).1 h)), dif_neg ht]
    have hb : (fillsRec D u (D.R.iota (hP D p)) hS (rRec L p) Lc I ψ y e (cRec L)
        (cloudBound L P u)).b (vOfH D.R.toFrame (hP D p) (bsH D.R.toFrame (hP D p) x)) s =
        bL L (bsH D.R.toFrame (hP D p) x + s.val • hP D p) := by
      show (if ((posG (zH D.R.toFrame (hP D p)) _ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces then
        -lamRec D u (posG (zH D.R.toFrame (hP D p)) _) (Fin.last _) else 0) = _
      rw [hpos, tau_coe_val]
      unfold bL
      by_cases ht : bsH D.R.toFrame (hP D p) x + s.val • hP D p ∈ D.host.TT
      · rw [if_pos ((tau_top_places_iff D _).2 ht), dif_pos ht, (lamRec_top L u _ ⟨_, ht⟩ rfl).2, neg_neg]
      · rw [if_neg (fun h => ht ((tau_top_places_iff D _).1 h)), dif_neg ht]
    refine ⟨?_, hmem, fun _ => ⟨ha, hb⟩, fun jj hj => ?_⟩
    · show ((D.eTau (D.eTau.symm (posG (zH D.R.toFrame (hP D p)) _)) : D.R.Psi) : D.R.GG) = _
      rw [Equiv.apply_symm_apply, hpos]
      rfl
    · show ((wRec D u (posG (zH D.R.toFrame (hP D p)) _) jj : ℤ) : ℝ) = _
      rw [hpos, wRec_eq D u _ jj hj, instRec_fillG L K Ce jj hj]

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure LocPack (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (p : ℕ) where
  W : Type
  Qq : Type
  O : Type
  Kf : Type
  [cW : CommRing W]
  [dW : IsDomain W]
  [vW : IsDiscreteValuationRing W]
  [fQ : Field Qq]
  [aW : Algebra W Qq]
  [cO : CommRing O]
  [dO : IsDomain O]
  [vO : IsDiscreteValuationRing O]
  [fK : Field Kf]
  [aO : Algebra O Kf]
  ι : Qq →+* Kf
  σ : Qq ≃+* Qq
  j : W →+* O
  w : O
  hS : HidaSetting p (orderOf (zH D.R.toFrame (hP D p))) W Qq O Kf ι σ j w
  I : LocId Lc p (nOrb (zH D.R.toFrame (hP D p))) W Qq
  ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* Oˣ

attribute [instance] LocPack.cW LocPack.dW LocPack.vW LocPack.fQ LocPack.aW LocPack.cO LocPack.dO LocPack.vO LocPack.fK
  LocPack.aO

def rSc (sc : Scale) (k p : ℕ) : ℕ := if (p : ℝ) < sc.p0 k then rG sc else 1

theorem rRec_eq {D : D7} (L : SizeData₂ D) (p : ℕ) : rRec L p = rSc L.sc D.R.k p := rfl

def epSc (R : Ranks) (sc : Scale) (Ce : ℝ) (p : ℕ) : ℕ := ⌈Ce * (R.f : ℝ) * (R.k : ℝ) ^ 2 * Real.logb p sc.a⌉₊

abbrev LocPack.gat {D : D7} {u : D.what₂.Word}
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {p : ℕ} (X : LocPack D u Lc p)
    (r e : ℕ) : GAtP p :=
  gatRec D u (D.R.iota (hP D p)) X.hS r Lc X.I X.ψ (repP Lc p) e

def LocPack.posOK {D : D7} {u : D.what₂.Word}
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {p : ℕ} [Fact p.Prime]
    (X : LocPack D u Lc p) (iK : X.Kf →+* ℂ_[p])
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) : Prop :=
  PosCompat D.host (D.R.iota (hP D p)) X.ι X.σ X.I.iw iK lam

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (X : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocPack D u (Lc u) (D.what₂.places.resChar w))
  (hd : ∀ u w h, ((X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))).d =
    Module.finrank ℂ (D.mem u).A.Mu0)

def recG : D7 :=
  { D with
    gat := fun u w h => (X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))
    gat_d := hd }

def gatTiesG : GatTies (recG D sc Ce Lc X hd) where
  gat_k := fun _ _ _ => k_pred D.R
  gat_n := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) v (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
      (hL : P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})) τ hτ =>
    haveI := hP
    haveI := hL
    gatRec_n_frob D u h (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _) _ v P τ hτ
  gat_pos := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) =>
    gatRec_pos D u _ (X u w h).hS (rSc sc D.R.k (D.what₂.places.resChar w)) (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _)
      (epSc D.R sc Ce (D.what₂.places.resChar w))
  gat_step := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) v s (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
      (hL : P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})) τ hτ =>
    haveI := hP
    haveI := hL
    gatRec_step_frob D u h (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _) _ v s P τ hτ
  gat_lam := fun _ _ _ _ _ _ => rfl

variable (L : SizeData₂ (recG D sc Ce Lc X hd)) (P : ParameterChoice' (recG D sc Ce Lc X hd) L)

def fillsG (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Fills ((recG D sc Ce Lc X hd).gat u w h) :=
  fillsRec D u _ (X u w h).hS (rSc sc D.R.k (D.what₂.places.resChar w)) (Lc u) (X u w h).I (X u w h).ψ
    (repP (Lc u) _) (epSc D.R sc Ce (D.what₂.places.resChar w)) (cRec L) ⟨(cloudBound L P u).top, (cloudBound L P u).off, (cloudBound L P u).fill⟩

def latInstG (Lv : ∀ u w h, Levels (fillsG D sc Ce Lc X hd L P u w h)) (Ch : ∀ u w h, Chain (Lv u w h))
    (Vram : ∀ u w h, Submodule ((recG D sc Ce Lc X hd).gat u w h).O ((recG D sc Ce Lc X hd).gat u w h).Fn) :
    LatInst (recG D sc Ce Lc X hd) where
  vOf := fun _ w _ => vOfH D.R.toFrame (hP D (D.what₂.places.resChar w))
  Fl := fillsG D sc Ce Lc X hd L P
  Lv := Lv
  Ch := Ch
  Vram := Vram

set_option maxHeartbeats 4000000 in

theorem latTiedG (hsc : L.sc = sc) (K : Consts) (Lv : ∀ u w h, Levels (fillsG D sc Ce Lc X hd L P u w h))
    (Ch : ∀ u w h, Chain (Lv u w h))
    (Vram : ∀ u w h, Submodule ((recG D sc Ce Lc X hd).gat u w h).O ((recG D sc Ce Lc X hd).gat u w h).Fn) :
    LatTied (gatTiesG D sc Ce Lc X hd) (instRec L K Ce) (latInstG D sc Ce Lc X hd L P Lv Ch Vram) := by
  rw [latTied_iff]
  intro (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  exact latTiedAt_rec L P K Ce u h.2.2.1 (X u w h).hS _ (by rw [rRec_eq, hsc]; rfl) (Lc u) (X u w h).I (X u w h).ψ
    (repP (Lc u) _) _


def levTieG (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Formalism.L2.Herm.GLevTie (Lc u) ((recG D sc Ce Lc X hd).gat u w h) :=
  gatRecP_lev D u _ (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ _



theorem std_of_fills {p : ℕ} (G : GAtP p) (Fl : Fills G) (v : Fin G.P.nV) (hr : 1 ≤ G.P.r) (h2r : 2 * G.P.r ≤ G.P.m + 1)
    (hm : 1 ≤ Fl.mm) :
    Formalism.MainNotions.FormalGroupSystem.Std p (G.P.n' v) G.P.m Fl.t Fl.mm Fl.c G.P.r (Fl.TT v) (Fl.a v) (Fl.b v) (G.P.lam0 v) (Fl.w v) where
  prime := (G.P.setting v).prime
  five_le := (G.P.setting v).five_le
  two_le := (G.P.setting v).two_le
  even := (G.P.setting v).even
  r_pos := hr
  two_r := h2r
  m_pos := hm
  base := Fl.base v
  dom := G.P.dom v
  w_low := fun s => ⟨le_trans (le_max_left _ _) (Fl.w_ge v s), le_trans (le_max_right _ _) (Fl.w_ge v s)⟩
  w_mono := fun s l h1 _ => Fl.w_mono v s l h1

theorem one_le_rSc (k p : ℕ) : 1 ≤ rSc sc k p := by
  unfold rSc rG
  split_ifs <;> omega

theorem two_rSc_le (k p : ℕ) (h : 2 * rG sc ≤ k) : 2 * rSc sc k p ≤ k := by
  unfold rSc
  split_ifs
  · exact h
  · unfold rG at h
    omega

theorem stdG (h2r : 2 * rG sc ≤ D.R.k) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin ((recG D sc Ce Lc X hd).gat u w h).P.nV) :
    Formalism.MainNotions.FormalGroupSystem.Std (D.what₂.places.resChar w) (((recG D sc Ce Lc X hd).gat u w h).P.n' v) ((recG D sc Ce Lc X hd).gat u w h).P.m
      (fillsG D sc Ce Lc X hd L P u w h).t (fillsG D sc Ce Lc X hd L P u w h).mm (fillsG D sc Ce Lc X hd L P u w h).c
      ((recG D sc Ce Lc X hd).gat u w h).P.r ((fillsG D sc Ce Lc X hd L P u w h).TT v) ((fillsG D sc Ce Lc X hd L P u w h).a v)
      ((fillsG D sc Ce Lc X hd L P u w h).b v) (((recG D sc Ce Lc X hd).gat u w h).P.lam0 v)
      ((fillsG D sc Ce Lc X hd L P u w h).w v) := by
  refine std_of_fills _ _ v ?_ ?_ ?_
  · exact one_le_rSc sc _ _
  · have h1 := two_rSc_le sc D.R.k (D.what₂.places.resChar w) h2r
    have h2 := D.R.m_add_three_le_k
    show 2 * rSc sc D.R.k (D.what₂.places.resChar w) ≤ D.R.k - 1 + 1
    omega
  · have := D.R.two_le_m
    show 1 ≤ D.R.m
    omega

end Formalism.L2.G
end
end
