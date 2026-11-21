import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPfLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecMeasLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrameLocX
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepRealHolds

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.Carrier.EnergyPf

open Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem intN_massDataY : (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN = IntNX X u u' ψ := rfl

end Formalism.L2.SG.Pf.Carrier.EnergyPf
end
end

section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.Pf.Carrier

namespace Formalism.L2.SG.Pf.Carrier.EnergyKM

theorem gam_eq (k r : ℕ) (κ δ : ℝ) : Formalism.FourierDecayAlt.D.GamLev k r κ δ 0 =
    (∏ a : Fin r, κ ^ (-((4 * (r - a.val) * (2 * (r - a.val) + k) : ℕ) : ℤ))) / δ ^ (r + 1) := by
  have hI : ∀ f : ℕ → ℝ, ∏ l ∈ Finset.Ioc 0 r, f l = ∏ i : Fin r, f (i.val + 1) := by
    intro f
    have hset : Finset.Ioc 0 r = Finset.Ico (0 + 1) (r + 1) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [Fin.prod_univ_eq_prod_range (fun i => f (i + 1)) r, Finset.range_eq_Ico,
      Finset.prod_Ico_add' f 0 r 1, hset]
  unfold Formalism.FourierDecayAlt.D.GamLev
  rw [Finset.prod_div_distrib, Finset.prod_const, Nat.card_Ioc, Nat.sub_zero,
    Finset.prod_Ioc_succ_top (Nat.zero_le r), hI]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one, sub_self, mul_zero, zero_mul, neg_zero, zpow_zero, mul_one]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  have ha : a.val ≤ r := a.isLt.le
  simp only [Formalism.FourierDecayAlt.C.Mlev]
  push_cast [Nat.cast_sub ha]
  congr 1
  ring

theorem level_constant_mul_gamma (r k : ℕ) (g rd : ℝ) (hg : 0 < g) (hrd : 0 < rd) :
    (2 : ℝ) ^ (r + 1) * (∏ a : Fin r, (((g / (2 * Real.pi)) ^ (2 * (r - a.val))) ^
      (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹) * Formalism.FourierDecayAlt.D.GamLev k r (Formalism.FourierDecayAlt.D.kapG g rd) (Formalism.FourierDecayAlt.D.deG g rd) 0 =
    rd ^ ((r + 1) + ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k)) * g ^ (3 * (r + 1)) := by
  rw [gam_eq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hper : ∀ a : Fin r, (((g / (2 * Real.pi)) ^ (2 * (r - a.val))) ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹ *
      Formalism.FourierDecayAlt.D.kapG g rd ^ (-((4 * (r - a.val) * (2 * (r - a.val) + k) : ℕ) : ℤ)) =
      rd ^ (4 * (r - a.val) * (2 * (r - a.val) + k)) := by
    intro a
    have hM : 2 * (r - a.val) * (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)) = 4 * (r - a.val) * (2 * (r - a.val) + k) := by
      unfold Formalism.QuantumDeterminants.Mdim
      rw [Nat.add_sub_cancel]
      ring
    rw [← pow_mul, hM, zpow_neg, zpow_natCast, ← mul_inv, ← mul_pow]
    unfold Formalism.FourierDecayAlt.D.kapG
    rw [show g / (2 * Real.pi) * (2 * Real.pi / (g * rd)) = rd⁻¹ by field_simp, inv_pow, inv_inv]
  rw [mul_div_assoc', mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun a _ => hper a),
    Finset.prod_pow_eq_pow_sum]
  unfold Formalism.FourierDecayAlt.D.deG
  rw [div_pow, div_div_eq_mul_div, pow_add]
  field_simp
  ring

theorem three_dvd (r : ℕ) : 3 ∣ (r + 1) * (8 * r ^ 2 + 10 * r + 3) := by
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, r = 3 * q ∨ r = 3 * q + 1 ∨ r = 3 * q + 2 := ⟨r / 3, by omega⟩
  · subst hq
    exact ⟨(3 * q + 1) * (24 * q ^ 2 + 10 * q + 1), by ring⟩
  · subst hq
    exact ⟨(3 * q + 2) * (2 * q + 1) * (12 * q + 7), by ring⟩
  · subst hq
    exact ⟨(q + 1) * (8 * (3 * q + 2) ^ 2 + 10 * (3 * q + 2) + 3), by ring⟩

theorem sum_closed (r k : ℕ) :
    3 * ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + k) = 4 * r * (r + 1) * (2 * r + 1) + 6 * k * r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

theorem exp_eq (r k : ℕ) (hk : 1 ≤ k) :
    (r + 1) + ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k) =
      2 * r * (r + 1) * (k - 1) + (r + 1) * (8 * r ^ 2 + 10 * r + 3) / 3 := by
  have hs : ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k) =
      ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + k) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 4 * (r - i) * (2 * (r - i) + k)) r, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hj' : r - (r - 1 - j) = j + 1 := by omega
    simp only [hj']
  have h3 := sum_closed r k
  obtain ⟨W, hW⟩ := three_dvd r
  rw [hs, hW, Nat.mul_div_cancel_left W (by norm_num : 0 < 3)]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  nlinarith [h3, hW]

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem kMatch_holds (P : Parts X u u') : EnergyPlace.KMatch P := by
  intro hg hrd hr hk hgpos hk1
  have hrdpos : 0 < Formalism.FourierDecayAlt.S6.rd D.host.E := by rw [hrd]; exact EnergyConst.rdE_pos'
  have hgpos' : (0 : ℝ) < P.S.g := by exact_mod_cast hgpos
  have hκ : 0 < Formalism.FourierDecayAlt.D.kapG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) := by
    simp only [Formalism.FourierDecayAlt.D.kapG]; positivity
  have hδ : 0 < Formalism.FourierDecayAlt.D.deG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) := by
    simp only [Formalism.FourierDecayAlt.D.deG]; positivity
  have hG : P.Gam0 ≠ 0 := by
    rw [Parts.Gam0, gam_eq]
    exact ne_of_gt (div_pos (Finset.prod_pos fun a _ => zpow_pos hκ _) (pow_pos hδ _))
  have key := level_constant_mul_gamma P.S.G.r P.S.G.k P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) hgpos' hrdpos
  rw [exp_eq _ _ hk1] at key
  rw [EnergyConst.Kexp, eq_div_iff hG]
  refine key.trans ?_
  rw [hrd, hg, hr, hk]
  rfl

end Formalism.L2.SG.Pf.Carrier.EnergyKM
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.EnergyPfLoc

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepSecX_holds : StepSecX := by
  intro D X u u' v
  obtain ⟨h, hm, hsec⟩ := Formalism.L2.SG.RealObj.InfCut.ProductExactness.SecMeasLoc_holds _ _ _ _ _ _ _ _ _ 1
    (Formalism.L2.SG.RealObj.InfCut.ProductExactness.frameLoc_X X u u' v) one_pos
  exact ⟨h, hm, fun cv hcv => hsec cv hcv⟩

theorem locRep_holds {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) :
    ∃ L, LocRep X u u' L :=
  locRep_of_sec stepSecX_holds X u u'

end Formalism.L2.SG.Pf.Carrier.EnergyPfLoc
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.Carrier.EnergyFinal

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

def PlaceNormG (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    hs2 (JvX X u u' v g) =
      ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
        (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖ ^ 2

theorem placeNorm_of_G (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hG : PlaceNormG P hr)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (hL : LocRep X u u' L) : PlaceNorm P hr L := by
  intro v cv hcv
  let c : Cinf X := fun _ => cv
  have hc : c ∈ Good X u u' := fun _ => hcv
  obtain ⟨γ, hγ⟩ := InfCut.ProductExactness.StepReal_holds D X u u' 1 one_pos c hc
  have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨γ, hγ⟩
  have hd : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf
    rw [dif_pos hex]
    exact hex.choose_spec
  have h1 : hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = L v cv := hL.2 c hc v
  have h2 := hG v ((hOf X u u' 1 c) v) cv hcv (hd v)
  exact h1.symm.trans h2

end Formalism.L2.SG.Pf.Carrier.EnergyFinal
end
end
