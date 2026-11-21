import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndDecInfAndKFinSmooth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbClosed

section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.NoPr

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.CellAmp

def Gp (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) : Prop :=
  ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε mu h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h

def AmpKF0 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

end GlobalTheory.NoPr

end
end

section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

namespace GlobalTheory.NoPr.Model

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.ThreeDimData

theorem aOf_mono (r : ℕ) {h h' : ℝ} (hh : h ≤ h') : aOf r h ≤ aOf r h' := by
  unfold aOf
  exact div_le_div_of_nonneg_right hh (by positivity)

theorem gapOK_mono {k r : ℕ} {h h' : ℝ} (hh : h ≤ h') (H : GapOK k r h) : GapOK k r h' :=
  ⟨H.1, H.2.1.trans hh, H.2.2.1.trans (aOf_mono r hh), H.2.2.2.trans (aOf_mono r hh)⟩







theorem ampKF0_iff_gapIn : AmpKF0 ↔ GlobalTheory.GapIn.AmpKF0 := Iff.rfl

open Formalism.MainNotions.S.Pv.AmpDDPf in

theorem ampKF0_holds : AmpKF0 := by
  intro k r L h μG w0 l l' hOPKF γ μR νR ν hCD b hb hab' hpm v v' hv hv' ξ ξ'
  have hSchH := Formalism.FourierDecayAlt.P.schur_hermitian
  have hNI := Formalism.FourierDecayAlt.P.norm_inverse_bound
  have hGG := Formalism.FourierDecayAlt.P.growth_group_bound
  have hRS := Formalism.MainNotions.S.Pv.AmpDDPf.right_stabilizer_invariance
  have hIn := GlobalTheory.DecInputs.decLow_and_decInf_and_kFinSmooth
  obtain ⟨hOP, hK1, hK2⟩ := hOPKF
  obtain ⟨hgap, hOK, -, hw0, hμG, -, -⟩ := hOP
  obtain ⟨hγ, hGf, hmono, hrel, hμR, hOQ, hQ⟩ := hCD
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  obtain ⟨d, hd, hSch⟩ := hSchH k r L.ε L.lam L.Hs L.σ μG L.hlam hσ hμG
  have hw0K : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w0 := Formalism.MainNotions.KFiniteLowUnitary.kFin_of_lowUnitH' hw0
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) L.σ :=
    hIn.2.2 k r L.ε L.lam L.Hs L.σ L.hlam hσ w0 hw0K
  obtain ⟨P, hP, hw⟩ := hw0
  have hnorm : ‖w0‖ = 1 := hw.1
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hw1 : ⟪w0, w0⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hfd : PI.BesselPeriodGGP.fdegH μG L.σ w0 = d :=
    Formalism.FourierDecayAlt.P.S3dx6.fdeg_of_schur hw0ne hd (hSch w0 w0 w0 w0).2
  obtain ⟨C1, Ws1, -, hC1⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v hv
  obtain ⟨C2, Ws2, -, hC2⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v' hv'
  have e1 : (1 : ℝ) - Formalism.FourierDecayAlt.ThreeDimData.aOf r h = -(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) := by ring
  have hC1' : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤
      (C1 * (Ws1.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC1 w0 hw0s g hg
  have hC2' : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤
      (C2 * (Ws2.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC2 w0 hw0s g hg
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hab : b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 := by linarith
  have hIG : Integrable (fun x : Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1))) μG := by
    have h1 := hGG k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR :=
    ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, hRS k r L γ μR hOK.1 hγ hGf hrel hmono hμR⟩
  rw [hfd]
  exact amp_core' L hμG hd hSch hNI hw1 l l' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm
    (fun t ht => hK1 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v hv)
    (fun t ht => hK2 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v' hv') hC1' hC2' ξ ξ'

end GlobalTheory.NoPr.Model

end
end
