import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroElementReduction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HJSpanLtZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselAdaptedTranslateLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryMatchingFramesAtNonconjugatePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffTypePinnedLocalGroups
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LamEqOfRed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalTypeDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelTraceAdaptedTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementPropertyStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_zero_element_reduction : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1) (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), d.Base → IsTypePlaces d.c.Pg → GlobalTheory.LocMod.PinGBy G cG → ∀ (PP : d.c.Pg) (n : GA D (d.st 0).V) (q : GL (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (GlobalTheory.LocMod.ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → (d.t 0)⁻¹ * n * d.t 0 ∈ d.lev 0 → levChi (d.st 0).V (d.st 0).β (d.st 0).L ((d.t 0)⁻¹ * n * d.t 0) = psiBes d.c.ψ (d.bes 0 D.R.rS h0).d 1 (vecB (d.bes 0 D.R.rS h0).o (d.bes 0 D.R.rS h0).ζ) n := by
  first | exact @GlobalTheory.NChainChar.levChi_eq_psiBes | exact GlobalTheory.NChainChar.levChi_eq_psiBes | (intros; apply GlobalTheory.NChainChar.levChi_eq_psiBes <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NPartConj

variable (I : Formalism.MainNotions.S.AutInst)

theorem nsmul_mL' {g k : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I} (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) :
    ((k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • v) ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv k

theorem nsmul_Lf' {k : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I} (hv : v ∈ I.Lf) :
    ((k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • v) ∈ I.Lf := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv k

theorem mL_le_Lf' (g : ℕ) : Formalism.L2.SG.HidaSetting.mL I g ≤ I.Lf :=
  Submodule.span_le.2 (by rintro _ ⟨y, hy, rfl⟩; exact nsmul_Lf' I hy)

theorem K_mL' {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I}
    (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) : I.fmat x *ᵥ v ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  have h : Formalism.L2.SG.HidaSetting.mL I g ≤
      (Formalism.L2.SG.HidaSetting.mL I g).comap (Formalism.L2.SG.Pf.unitaryCongruence.mvO I (I.fmat x)) :=
    Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      show I.fmat x *ᵥ ((g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • y) ∈ Formalism.L2.SG.HidaSetting.mL I g
      rw [Matrix.mulVec_smul]
      exact Formalism.L2.SG.Pf.unitaryCongruence.smul_mem_mL I (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hx hy))
  exact h hv

theorem K_sub_mL' {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I}
    (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) : (I.fmat x - 1) *ᵥ v ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact sub_mem (K_mL' I hx hv) hv

theorem hcn_of {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {n N N0 : Formalism.L2.SG.HidaSetting.VA I}
    (hN : I.fmat x *ᵥ N0 = N) {c : ℕ}
    (h : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (n - N0) ∈ Formalism.L2.SG.HidaSetting.mL I g) :
    (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N ∈
      Formalism.L2.SG.HidaSetting.mL I g := by
  have e : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N =
      I.fmat x *ᵥ ((c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (n - N0)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hN, smul_sub]
  rw [e]; exact K_mL' I hx h

theorem conj_sub (x m : I.Gf) (n : Formalism.L2.SG.HidaSetting.VA I) :
    (I.fmat (x⁻¹ * m * x) - 1) *ᵥ n = I.fmat x⁻¹ *ᵥ ((I.fmat m - 1) *ᵥ (I.fmat x *ᵥ n)) := by
  rw [Formalism.L2.SG.Pf.unitaryCongruence.fmat_mul, Formalism.L2.SG.Pf.unitaryCongruence.fmat_mul]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul, Matrix.one_mulVec]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul, Matrix.sub_mulVec,
    Matrix.one_mulVec]

theorem term_cong {g : ℕ} {x m : I.Gf} (hx : x ∈ I.Kset) (hm : m ∈ I.Kset)
    {f F n N : Formalism.L2.SG.HidaSetting.VA I} (hf : f ∈ I.Lf) (hn : n ∈ I.Lf) (hFx : I.fmat x *ᵥ F = F) {c : ℕ}
    (hcf : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (f - F) ∈ Formalism.L2.SG.HidaSetting.mL I g)
    (hcn : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N ∈
      Formalism.L2.SG.HidaSetting.mL I g) :
    Formalism.L2.SG.HidaSetting.ZMod' I g (((c * c : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
      (Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) -
        Formalism.L2.SG.HidaSetting.hA I F ((I.fmat m - 1) *ᵥ N))) := by
  set C : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) with hC
  have e1 : Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) =
      Formalism.L2.SG.HidaSetting.hA I (I.fmat x *ᵥ f) ((I.fmat m - 1) *ᵥ (I.fmat x *ᵥ n)) := by
    rw [conj_sub, PIW.NormChiNBi.hA_left_inv, inv_inv]
  have hsig : Formalism.L2.SG.HidaSetting.sigA I C = C := by rw [hC, map_natCast]
  have esc : ∀ u v : Formalism.L2.SG.HidaSetting.VA I, Formalism.L2.SG.HidaSetting.hA I (C • u) ((I.fmat m - 1) *ᵥ (C • v)) =
      C * C * Formalism.L2.SG.HidaSetting.hA I u ((I.fmat m - 1) *ᵥ v) := by
    intro u v
    rw [Matrix.mulVec_smul, PIW.NormChiNBi.hA_smul_left, PIW.NormChiNBi.hA_smul_right, hsig]; ring
  have hδf : C • (I.fmat x *ᵥ f) - C • F ∈ Formalism.L2.SG.HidaSetting.mL I g := by
    have e : C • (I.fmat x *ᵥ f) - C • F = I.fmat x *ᵥ (C • (f - F)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hFx, smul_sub]
    rw [e]; exact K_mL' I hx hcf
  have hA'L : C • F ∈ I.Lf := by
    have e : C • F = C • f - C • (f - F) := by rw [smul_sub]; abel
    rw [e]; exact sub_mem (nsmul_Lf' I hf) (mL_le_Lf' I g hcf)
  have hBL : (I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n)) ∈ I.Lf :=
    Formalism.L2.SG.Pf.unitaryCongruence.K_sub_mv I hm (nsmul_Lf' I (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hx hn))
  have key : ((c * c : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
      (Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) -
        Formalism.L2.SG.HidaSetting.hA I F ((I.fmat m - 1) *ᵥ N)) =
      Formalism.L2.SG.HidaSetting.hA I (C • (I.fmat x *ᵥ f) - C • F) ((I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n))) +
      Formalism.L2.SG.HidaSetting.hA I (C • F) ((I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n) - C • N)) := by
    rw [PIW.NormChiNBi.hA_sub_left, Matrix.mulVec_sub, PIW.NormChiNBi.hA_sub_right, e1, esc, esc, esc, Nat.cast_mul]
    ring
  rw [key]
  obtain ⟨s, hs, hs'⟩ := PIW.NormChiNBi.hA_mL_left I g hδf hBL
  obtain ⟨t, ht, ht'⟩ := PIW.NormChiNBi.hA_mL_right I g (K_sub_mL' I hm hcn) hA'L
  exact ⟨s + t, add_mem hs ht, by rw [hs', ht', mul_add]⟩

end GlobalTheory.NPartConj

namespace GlobalTheory.NPartConj

theorem term_each (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf)
    (hm : m ∈ X.B.I.Kset) (a : Fin D.R.rS) :
    ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  obtain ⟨c1, hc1, h1⟩ := (X.basisApprox a).2
  have hFx : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
  have hx := X.xu_K u
  obtain ⟨c2, hc2, N0, hN0, h2⟩ : ∃ c2 : ℕ, Nat.Coprime c2 X.B.g ∧ ∃ N0 : VA X.B.I,
      X.B.I.fmat (X.xu u) *ᵥ N0 = incl X.B.I (nxt X.eR (X.zR u) a) ∧
      ((c2 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (nxt X.e0 X.z0 a - N0)) ∈ mL X.B.I X.B.g := by
    unfold nxt
    split_ifs with h
    · obtain ⟨c2, hc2, h2⟩ := (X.basisApprox ⟨a.1 + 1, h⟩).1
      exact ⟨c2, hc2, _, (X.xu_fix u _).1, h2⟩
    · obtain ⟨c2, hc2, h2⟩ := X.xu_z u
      refine ⟨c2, hc2, X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u), ?_, ?_⟩
      · rw [Matrix.mulVec_mulVec, PIW.NormChiNBi.fmat_mul_inv', Matrix.one_mulVec]
      · have h3 := neg_mem h2
        rwa [← smul_neg, neg_sub] at h3
  have hcop : Nat.Coprime (c1 * c2) X.B.g := Nat.Coprime.mul hc1 hc2
  refine ⟨(c1 * c2) * (c1 * c2), Nat.Coprime.mul hcop hcop, ?_⟩
  have hcf : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (X.f0 a - incl X.B.I (X.fR a)) ∈
      mL X.B.I X.B.g := by
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact nsmul_mL' X.B.I h1
  have hcN : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (nxt X.e0 X.z0 a - N0) ∈
      mL X.B.I X.B.g := by
    rw [Nat.cast_mul, mul_smul]; exact nsmul_mL' X.B.I h2
  exact term_cong X.B.I hx hm (X.vectorsInLattice.1 a).2 (PIW.NormChiNBi.nxt_mem X a) hFx hcf
    (hcn_of X.B.I hx hN0 hcN)

theorem nsum_cong : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf), m ∈ X.B.I.Kset → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ a, (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) - hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  intro D X u m hm
  choose c hc h using term_each D X u m hm
  refine ⟨∏ a, c a, Nat.Coprime.prod_left fun a _ => hc a, ?_⟩
  rw [Finset.mul_sum]
  refine Formalism.L2.SG.Pf.unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ a)
  rw [hk]
  have e : ∀ T : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F,
      ((c a * k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T =
        (k : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((c a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T) := by
    intro T; push_cast; ring
  rw [e]
  exact Formalism.L2.SG.Pf.unitaryCongruence.Z_smul X.B.I X.B.g (natCast_mem _ k) (h a)

end GlobalTheory.NPartConj
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_multiplier_levelCharacter_sum_congr : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf), m ∈ X.B.I.Kset → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ a, (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) - hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  atlas_forward_decl GlobalTheory.NPartConj.nsum_cong
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UkPart

open Formalism.L2.SG.Pf.unitaryCongruence

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

local notation "RA" => X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F

theorem natCast_int (c : ℕ) : (c : RA) ∈ IntAf X.B.I.F X.B.I.E := natCast_mem _ c

theorem sigA_natCast (c : ℕ) : sigA X.B.I (c : RA) = c := map_natCast _ c

theorem natsmul_Lf (c : ℕ) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : (c : RA) • y ∈ X.B.I.Lf := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy c

theorem natsmul_mL (c : ℕ) {y : VA X.B.I} (hy : y ∈ mL X.B.I X.B.g) : (c : RA) • y ∈ mL X.B.I X.B.g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy c

theorem mL_le_Lf : mL X.B.I X.B.g ≤ X.B.I.Lf := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  exact natsmul_Lf X _ hy

theorem intsmul_Lf {t : RA} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    t • y ∈ X.B.I.Lf := by
  have h := X.B.I.Lf.smul_mem (⟨t, ht⟩ : IntAf X.B.I.F X.B.I.E) hy
  rwa [Subring.smul_def] at h

theorem Z_int {t : RA} (ht : ZMod' X.B.I X.B.g t) : t ∈ IntAf X.B.I.F X.B.I.E := by
  obtain ⟨s, hs, rfl⟩ := ht; exact mul_mem (natCast_int X _) hs

theorem hA_ef (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
  rw [hA_incl]
  have h := GlobalTheory.St.hform_crd_setting X (X.eX a) (X.fY b)
  rw [X.ef] at h
  have h' : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.fR b) = if a = b then 1 else 0 := by
    apply X.ιE.injective
    refine h.trans ?_; split_ifs <;> simp
  rw [h']; split_ifs <;> simp

theorem hA_fe (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if a = b then 1 else 0 := by
  rw [hA_symm X.B.I (incl X.B.I (X.eR a)), hA_ef]; split_ifs <;> simp

theorem exists_mult : ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ∀ b : Fin D.R.rS,
    (c : RA) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g ∧
    (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g := by
  choose ce hce using fun b => (X.basisApprox b).1
  choose cf hcf using fun b => (X.basisApprox b).2
  refine ⟨∏ b, ce b * cf b, Nat.Coprime.prod_left fun b _ => Nat.Coprime.mul (hce b).1 (hcf b).1, fun b => ?_⟩
  have hd : ce b * cf b ∣ ∏ b, ce b * cf b := Finset.dvd_prod_of_mem _ (Finset.mem_univ b)
  obtain ⟨k, hk⟩ := hd
  rw [hk]
  constructor
  · have : ((ce b * cf b * k : ℕ) : RA) • (X.e0 b - incl X.B.I (X.eR b)) =
        ((cf b * k : ℕ) : RA) • ((ce b : RA) • (X.e0 b - incl X.B.I (X.eR b))) := by
      rw [smul_smul]; push_cast; ring_nf
    rw [this]; exact natsmul_mL X _ (hce b).2
  · have : ((ce b * cf b * k : ℕ) : RA) • (X.f0 b - incl X.B.I (X.fR b)) =
        ((ce b * k : ℕ) : RA) • ((cf b : RA) • (X.f0 b - incl X.B.I (X.fR b))) := by
      rw [smul_smul]; push_cast; ring_nf
    rw [this]; exact natsmul_mL X _ (hcf b).2

end GlobalTheory.UkPart

namespace GlobalTheory.UkPart
open Formalism.L2.SG.Pf.unitaryCongruence
variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
local notation "RA" => X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F

theorem hA_sum_right (p : VA X.B.I) (v : Fin D.R.rS → VA X.B.I) :
    hA X.B.I p (∑ b, v b) = ∑ b, hA X.B.I p (v b) := by
  simpa only [hL_apply] using map_sum (hL X.B.I p) v Finset.univ

theorem core (u : D.what₂.Word) (m : X.B.I.Gf) (hmK : m ∈ X.B.I.Kset) (hmN : m ∈ X.NfinU u) (c : ℕ)
    (hc : ∀ b : Fin D.R.rS, (c : RA) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g ∧
      (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g)
    {p w : VA X.B.I} (hp : p ∈ X.B.I.Lf) (hw : w ∈ X.B.I.Lf)
    (ht : ∀ b, ZMod' X.B.I X.B.g (hA X.B.I (incl X.B.I (X.eR b)) ((c : RA) • w)))
    (hpe : ∀ b, ZMod' X.B.I X.B.g ((c : RA) * hA X.B.I p (incl X.B.I (X.eR b)))) :
    ZMod' X.B.I X.B.g ((c : RA) ^ 4 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w)) := by
  have hf : ∀ b, (c : RA) • incl X.B.I (X.fR b) ∈ X.B.I.Lf := fun b => by
    have e : (c : RA) • incl X.B.I (X.fR b) = (c : RA) • X.f0 b - (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) := by
      rw [smul_sub, sub_sub_cancel]
    rw [e]; exact sub_mem (natsmul_Lf X c (X.vectorsInLattice.1 b).2) (mL_le_Lf X (hc b).2)
  set W := (c : RA) • w with hWdef
  have hW : W ∈ X.B.I.Lf := natsmul_Lf X c hw
  set t : Fin D.R.rS → RA := fun b => hA X.B.I (incl X.B.I (X.eR b)) W with htdef
  set W' := W - ∑ b, t b • incl X.B.I (X.fR b) with hW'def
  have hperp : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) W' = 0 := fun a => by
    rw [hW'def, hA_sub_right, hA_sum_right]
    simp only [hA_smul_right, hA_ef, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [htdef]; exact sub_self _
  have hv := hmN.2.2 W' hperp
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun RA).1 hv
  have hlam_eq : ∀ a, hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ W') = lam a := fun a => by
    rw [← hlam, hA_sum_right]
    simp only [hA_smul_right, hA_fe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

  have hcW' : (c : RA) • W' ∈ X.B.I.Lf := by
    rw [hW'def, smul_sub, Finset.smul_sum]
    refine sub_mem (natsmul_Lf X c hW) (sum_mem fun b _ => ?_)
    rw [smul_comm]; exact intsmul_Lf X (Z_int X (ht b)) (hf b)
  have hlam_int : ∀ a, (c : RA) ^ 2 * lam a ∈ IntAf X.B.I.F X.B.I.E := fun a => by
    have h := hA_int X.B.I (hf a) (K_sub_mv X.B.I hmK hcW')
    rw [Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_natCast, hlam_eq] at h
    rw [pow_two, mul_assoc]; exact h

  have h1 : ZMod' X.B.I X.B.g ((c : RA) ^ 3 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ W')) := by
    rw [← hlam, hA_sum_right, Finset.mul_sum]
    refine Z_sum X.B.I X.B.g _ _ fun b _ => ?_
    rw [hA_smul_right]
    have e : (c : RA) ^ 3 * (lam b * hA X.B.I p (incl X.B.I (X.eR b))) =
        ((c : RA) ^ 2 * lam b) * ((c : RA) * hA X.B.I p (incl X.B.I (X.eR b))) := by ring
    rw [e]; exact Z_smul X.B.I X.B.g (hlam_int b) (hpe b)

  have h2 : ZMod' X.B.I X.B.g ((c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ∑ b, t b • incl X.B.I (X.fR b))) := by
    rw [Matrix.mulVec_sum, hA_sum_right, Finset.mul_sum]
    refine Z_sum X.B.I X.B.g _ _ fun b _ => ?_
    rw [Matrix.mulVec_smul, hA_smul_right]
    have e : (c : RA) * (t b * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (X.fR b))) =
        hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ((c : RA) • incl X.B.I (X.fR b))) * t b := by
      rw [Matrix.mulVec_smul, hA_smul_right]; ring
    rw [e]; exact Z_smul X.B.I X.B.g (hA_int X.B.I hp (K_sub_mv X.B.I hmK (hf b))) (ht b)
  have hsplit : W = W' + ∑ b, t b • incl X.B.I (X.fR b) := by rw [hW'def, sub_add_cancel]
  have e : (c : RA) ^ 4 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w) =
      (c : RA) ^ 3 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ W') +
      (c : RA) ^ 2 * ((c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ∑ b, t b • incl X.B.I (X.fR b))) := by
    have e2 : (c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w) =
        hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ W') +
        hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ∑ b, t b • incl X.B.I (X.fR b)) := by
      rw [← hA_add_right, ← Matrix.mulVec_add, ← hsplit, hWdef, Matrix.mulVec_smul, hA_smul_right]
    calc (c : RA) ^ 4 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w)
        = (c : RA) ^ 3 * ((c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w)) := by ring
      _ = _ := by rw [e2]; ring
  rw [e]
  exact Z_add X.B.I X.B.g h1 (Z_smul X.B.I X.B.g (pow_mem (natCast_int X c) 2) h2)

end GlobalTheory.UkPart

namespace GlobalTheory.UkPart
open Formalism.L2.SG.Pf.unitaryCongruence
variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
local notation "RA" => X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F

theorem conj_sub (x m : X.B.I.Gf) (v : VA X.B.I) :
    (X.B.I.fmat (x⁻¹ * m * x) - 1) *ᵥ v = X.B.I.fmat x⁻¹ *ᵥ ((X.B.I.fmat m - 1) *ᵥ (X.B.I.fmat x *ᵥ v)) := by
  rw [fmat_mul, fmat_mul]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← mul_assoc,
    fmat_inv_mul, one_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, fmat_inv_mul, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem term (u : D.what₂.Word) (m : X.B.I.Gf) (hmK : m ∈ X.B.I.Kset) (hmN : m ∈ X.NfinU u) (c : ℕ)
    (hc : ∀ b : Fin D.R.rS, (c : RA) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g ∧
      (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g) (i j : Fin D.R.k) :
    ZMod' X.B.I X.B.g ((c : RA) ^ 4 *
      hA X.B.I (X.bwd i) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ X.bw j)) := by
  have hbw : X.bw j ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 j).1
  have hbwd : X.bwd i ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 i).2
  have hfix : ∀ b, X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) :=
    fun b => (X.xu_fix u b).1
  rw [conj_sub, PIW.NormChiNBi.hA_left_inv X.B.I (X.xu u)⁻¹, inv_inv]
  refine core X u m hmK hmN c hc (K_mv X.B.I (X.xu_K u) hbwd) (K_mv X.B.I (X.xu_K u) hbw) (fun b => ?_) (fun b => ?_)
  ·
    rw [← hfix b, hA_smul_right, PIW.NormChiNBi.hA_fmat']
    have e : (c : RA) * hA X.B.I (incl X.B.I (X.eR b)) (X.bw j) =
        (c : RA) * hA X.B.I (X.e0 b) (X.bw j) - hA X.B.I ((c : RA) • (X.e0 b - incl X.B.I (X.eR b))) (X.bw j) := by
      rw [hA_smul_left, sigA_natCast, PIW.NormChiNBi.hA_sub_left]; ring
    rw [e]
    exact Z_sub X.B.I X.B.g (Z_smul X.B.I X.B.g (natCast_int X c) ((X.weightVectorsIntegral j).2.2 b).1)
      (PIW.NormChiNBi.hA_mL_left X.B.I X.B.g (hc b).1 hbw)
  ·
    rw [← hfix b, PIW.NormChiNBi.hA_fmat']
    have e : (c : RA) * hA X.B.I (X.bwd i) (incl X.B.I (X.eR b)) =
        (c : RA) * hA X.B.I (X.bwd i) (X.e0 b) - hA X.B.I (X.bwd i) ((c : RA) • (X.e0 b - incl X.B.I (X.eR b))) := by
      rw [hA_smul_right, PIW.NormChiNBi.hA_sub_right]; ring
    rw [e]
    exact Z_sub X.B.I X.B.g (Z_smul X.B.I X.B.g (natCast_int X c) ((Formalism.L2.SG.Pf.reference_frame_congruences X).2.2.1 i b))
      (PIW.NormChiNBi.hA_mL_right X.B.I X.B.g (hc b).1 hbwd)

theorem ukPart_zmod : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf),
    m ∈ X.B.I.Kset → m ∈ X.NfinU u → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) := by
  intro D X u m hmK hmN
  obtain ⟨c, hcop, hc⟩ := exists_mult X
  refine ⟨c ^ 4, Nat.Coprime.pow_left 4 hcop, ?_⟩
  rw [Finset.mul_sum]
  refine Z_sum X.B.I X.B.g _ _ fun i _ => ?_
  split_ifs with h
  · push_cast; exact term X u m hmK hmN c hc i _
  · rw [mul_zero]; exact Z_zero X.B.I X.B.g

end GlobalTheory.UkPart
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_multiplier_unipotentPart_congr_zero : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf), m ∈ X.B.I.Kset → m ∈ X.NfinU u → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) := by
  atlas_forward_decl GlobalTheory.UkPart.ukPart_zmod
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowBesChar

variable {D : D7}

theorem hA_fR_nxt_zero (X : HidaSetting D) (u : D.what₂.Word) (a : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (nxt X.eR (X.zR u) a)) = 0 := by
  rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_incl]
  have e1 : nxt X.eR (X.zR u) a = X.crd (nxt X.eX (X.zu u) a) := by
    unfold nxt; split_ifs <;> rfl
  have e2 : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.fR a) (X.crd (nxt X.eX (X.zu u) a)) = 0 := by
    apply X.ιE.injective
    rw [show X.fR a = X.crd (X.fY a) from rfl, GlobalTheory.St.hform_crd_setting, map_zero]
    unfold nxt
    split_ifs with hh
    · apply GlobalTheory.St.hT_symm_zero
      rw [X.ef, if_neg]
      intro h'
      have := congrArg Fin.val h'
      simp at this
    · exact (X.zu_orth u a).2
  rw [e1, e2, map_zero]

theorem mem_GfC_of_suppAt {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hs : SuppAt e V g) :
    g ∈ GfC V := by
  obtain ⟨-, -, v, ε, ⟨α, rfl, -, -⟩, hε⟩ := he
  show g ∈ (infHom V).ker
  rw [MonoidHom.mem_ker]
  apply Units.ext
  ext i j
  have h1 := congrArg (infPart D) (hs i j)
  rw [map_mul, hε] at h1
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show (fstA D.host.F) (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [show (fstA D.host.F) (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  rw [h0, zero_mul] at h1
  have e : (infHom V g).1 i j = infPart D (mt V g i j) := rfl
  change (infHom V g).1 i j = (1 : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).1 i j
  rw [e, Units.val_one]
  have h2 : infPart D ((mt V g - 1) i j) = infPart D (mt V g i j) - (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    rw [Matrix.sub_apply, RingHom.map_sub]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
  rw [h2] at h1
  exact sub_eq_zero.1 h1.symm

theorem smul_fact {R : Type} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R) (ε : R)
    (h : ∀ i j, M i j = ε * M i j) (v : Fin k → R) : M *ᵥ v = ε • (M *ᵥ v) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [h i j]
  ring

theorem supp_fact {A R : Type} [CommRing A] [CommRing R] {k : ℕ} (f : A →+* R) (M : Matrix (Fin k) (Fin k) A) (a : A)
    (h : ∀ i j, a * (M - 1) i j = (M - 1) i j) (v : Fin k → R) :
    (M.map f - 1) *ᵥ v = f a • ((M.map f - 1) *ᵥ v) := by
  refine smul_fact _ _ (fun i j => ?_) v
  have e1 : (M.map f - 1) i j = f ((M - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
  rw [e1, ← map_mul, h i j]

theorem exists_eps (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) {e : AE D}
    {PP : Formalism.L2.DIV.Pl D.host.E} (hi : Formalism.L2.NTheta.IsIdemAt e PP)
    (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (n : GA D (D.sp.Y 0)) (hs : SuppAt e (D.sp.Y 0) n) :
    ∃ ε : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F,
      (∀ c : ℕ, Nat.Coprime c X.B.g → ∃ t ∈ IntAf X.B.I.F X.B.I.E,
        ε = (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t) ∧
      ∀ v, (X.B.I.fmat (iotaX X h n).2 - 1) *ᵥ v = ε • ((X.B.I.fmat (iotaX X h n).2 - 1) *ᵥ v) := by
  rw [X.g_eq]
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      ∃ ε : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F,
      (∀ c : ℕ, Nat.Coprime c (D.host.g 0 * D.host.g 1) → ∃ t ∈ IntAf I.F I.E,
        ε = (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t) ∧
      ∀ v, (I.fmat (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D n)).2 - 1) *ᵥ v =
        ε • ((I.fmat (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D n)).2 - 1) *ᵥ v) := by
    intro I hI
    subst hI
    have hfin : (Formalism.L2.SG.InstExistsPf.instOf D).fmat (castGA (Eq.refl _) (Formalism.IndefR.RationalEmbedding.iota D n)).2 =
        (Lev.finE (D.sp.Y 0) n).1 := by
      have h1 := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D n)
      rw [ContinuousMulEquiv.symm_apply_apply] at h1
      rw [h1]
      rfl
    refine ⟨GlobalTheory.LevSplit.finSw D (e + cA D e), fun c hc => ?_, fun v => ?_⟩
    · have hcP : ((c : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
        intro hcm
        obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
        have h1 : ((a : 𝓞 D.host.E) * (c : 𝓞 D.host.E) + (b : 𝓞 D.host.E) * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)) = 1 := by
          have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
          push_cast at this ⊢
          exact this
        apply PP.isPrime.ne_top
        rw [Ideal.eq_top_iff_one, ← h1]
        exact PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hcm) (PP.asIdeal.mul_mem_left _ hg)
      have hc0 : ((c : ℕ) : 𝓞 D.host.E) ≠ 0 := fun h0 => hcP (h0 ▸ PP.asIdeal.zero_mem)
      have hcE : (((c : ℕ) : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) := by simp
      have hcE0 : (c : D.host.E) ≠ 0 := by rw [← hcE]; exact_mod_cast hc0
      have hint : finPart D (e * incA D (((c : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹) ∈ intAE D :=
        not_not.1 fun hn => hcP ((hi.2 _ hc0).2 hn)
      rw [hcE] at hint
      set z := e * incA D (c : D.host.E)⁻¹ with hzdef
      have hcA : ∀ y : D.host.E, cA D (incA D y) = incA D (D.sp.cm.sig y) := fun y => rfl
      have hz : incA D (c : D.host.E) * z = e := by
        rw [hzdef, mul_comm, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hcE0, RingHom.map_one, mul_one]
      have hz' : incA D (c : D.host.E) * cA D z = cA D e := by
        have : incA D (c : D.host.E) = cA D (incA D (c : D.host.E)) := by
          rw [hcA]; exact congrArg (incA D) (map_natCast _ c).symm
        rw [this, ← RingHom.map_mul, hz]
      refine ⟨GlobalTheory.LevSplit.finSw D z + GlobalTheory.LevSplit.finSw D (cA D z),
        add_mem (GlobalTheory.LevSplit.swapAE_int hint) ?_, ?_⟩
      · rw [GlobalTheory.LevSplit.finSw_cA]
        exact PIW.NormChiNBi.sigA_int _ (GlobalTheory.LevSplit.swapAE_int hint)
      · show GlobalTheory.LevSplit.finSw D (e + cA D e) =
          ((c : ℕ) : Lev.EAf D) * (GlobalTheory.LevSplit.finSw D z + GlobalTheory.LevSplit.finSw D (cA D z))
        have hcc : ((c : ℕ) : Lev.EAf D) = GlobalTheory.LevSplit.finSw D (incA D (c : D.host.E)) := by
          rw [GlobalTheory.LevSplit.finSw_incA, map_natCast]
        rw [hcc, mul_add, ← RingHom.map_mul, ← RingHom.map_mul, hz, hz', RingHom.map_add]
    · rw [hfin]
      exact supp_fact (GlobalTheory.LevSplit.finSw D) (mt (D.sp.Y 0) n) (e + cA D e) hs v
  exact key X.B.I h

open Formalism.L2.SG.Pf.unitaryCongruence in

theorem besselLevel_chi_conj_eq_finite_bessel_character (X : HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf) (ε : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (hε : ∀ c : ℕ, Nat.Coprime c X.B.g → ∃ t ∈ IntAf X.B.I.F X.B.I.E,
      ε = (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t)
    (hs : ∀ v, (X.B.I.fmat m - 1) *ᵥ v = ε • ((X.B.I.fmat m - 1) *ᵥ v))
    (hN : m ∈ X.NfinU u) (hK : (X.xu u)⁻¹ * m * X.xu u ∈ X.K2) :
    X.chi2 ((X.xu u)⁻¹ * m * X.xu u) = X.psiFinU u m := by
  have hg := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  obtain ⟨hfe, hfz, hbe, hbb⟩ := Formalism.L2.SG.Pf.reference_frame_congruences X
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hz0 : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have hbw : ∀ i, X.bw i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).1
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  set y := (X.xu u)⁻¹ * m * X.xu u with hy
  have hxK := X.xu_K u
  have hmK : m ∈ X.B.I.Kset := by
    have e : m = X.xu u * y * (X.xu u)⁻¹ := by rw [hy]; group
    rw [e]; exact K_mul _ (K_mul _ hxK hK.1) (K_inv _ hxK)
  have hsy : ∀ v, (X.B.I.fmat y - 1) *ᵥ v = ε • ((X.B.I.fmat y - 1) *ᵥ v) := by
    have e1 : ∀ v, (X.B.I.fmat y - 1) *ᵥ v =
        X.B.I.fmat (X.xu u)⁻¹ *ᵥ ((X.B.I.fmat m - 1) *ᵥ (X.B.I.fmat (X.xu u) *ᵥ v)) := by
      intro v
      rw [hy, fmat_mul, fmat_mul]
      simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.mulVec_mulVec,
        Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_assoc, fmat_inv_mul]
    intro v
    conv_lhs => rw [e1, hs, Matrix.mulVec_smul, ← e1]
  have split : ∀ (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) (f v : VA X.B.I),
      hA X.B.I f (M *ᵥ v) = hA X.B.I f v + hA X.B.I f ((M - 1) *ᵥ v) := by
    intro M f v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right]
    ring

  set T1 := ∑ a, hA X.B.I (X.f0 a) ((X.B.I.fmat y - 1) *ᵥ nxt X.e0 X.z0 a) with hT1
  set T3 := ∑ a, hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) with hT3
  set T2 := ∑ i : Fin D.R.k, (if h : i.1 + 1 < D.R.k then
        hA X.B.I (X.bwd i) ((X.B.I.fmat y - 1) *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) with hT2
  have eAy : Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd y = Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd 1 + (T1 + T2) := by
    have p1 : ∀ a, hA X.B.I (X.f0 a) (X.B.I.fmat y *ᵥ nxt X.e0 X.z0 a) =
        hA X.B.I (X.f0 a) (X.B.I.fmat 1 *ᵥ nxt X.e0 X.z0 a) + hA X.B.I (X.f0 a) ((X.B.I.fmat y - 1) *ᵥ nxt X.e0 X.z0 a) := by
      intro a; rw [fmat_one, Matrix.one_mulVec, split]
    have p2 : ∀ i : Fin D.R.k, (if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat y *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) =
        (if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat 1 *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) +
        (if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) ((X.B.I.fmat y - 1) *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) := by
      intro i
      split_ifs with h
      · rw [fmat_one, Matrix.one_mulVec, split]
      · rw [add_zero]
    unfold Afun
    rw [Finset.sum_congr rfl (fun a _ => p1 a), Finset.sum_congr rfl (fun i _ => p2 i), Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    ring
  have eC : ∑ a, hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat m *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) = T3 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [split, hA_fR_nxt_zero, zero_add]
  have hA1 : ZMod' X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd 1) :=
    Afun_Kg X.B.I X.B.g X.e0 X.f0 X.z0 X.bw X.bwd
      ⟨K_one _, fun v _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩
      he0 hf0 hz0 hbw hbwd hfe hfz hbb

  have hS : (T1 - T3) + T2 = ε * ((T1 - T3) + T2) := by
    have q1 : T1 = ε * T1 := by
      rw [hT1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      conv_lhs => rw [hsy]
      rw [hA_smul_right]
    have q3 : T3 = ε * T3 := by
      rw [hT3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      conv_lhs => rw [hs]
      rw [hA_smul_right]
    have q2 : T2 = ε * T2 := by
      rw [hT2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · conv_lhs => rw [hsy]
        rw [hA_smul_right]
      · rw [mul_zero]
    rw [mul_add, mul_sub, ← q1, ← q2, ← q3]
  obtain ⟨c1, hc1, h1⟩ := GlobalTheory.T.exists_coprime_multiplier_levelCharacter_sum_congr D X u m hmK
  obtain ⟨c2, hc2, h2⟩ := GlobalTheory.T.exists_coprime_multiplier_unipotentPart_congr_zero D X u m hmK hN
  have h1' : ZMod' X.B.I X.B.g ((c1 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * (T1 - T3)) := by
    rw [hT1, hT3, ← Finset.sum_sub_distrib]; exact h1
  obtain ⟨t, ht, hεt⟩ := hε (c1 * c2) (Nat.Coprime.mul hc1 hc2)
  have hcS : ZMod' X.B.I X.B.g (((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((T1 - T3) + T2)) := by
    have e : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((T1 - T3) + T2) =
        (c2 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((c1 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * (T1 - T3)) +
        (c1 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((c2 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T2) := by
      push_cast; ring
    rw [e]
    exact Z_add _ _ (Z_smul _ _ (natCast_mem _ c2) h1') (Z_smul _ _ (natCast_mem _ c1) h2)
  have hZS : ZMod' X.B.I X.B.g ((T1 - T3) + T2) := by
    rw [hS, hεt, mul_comm _ t, mul_assoc]
    exact Z_smul _ _ ht hcS
  have hdiff : ZMod' X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd y -
      ∑ a, hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat m *ᵥ incl X.B.I (nxt X.eR (X.zR u) a))) := by
    rw [eAy, eC]
    have e : Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd 1 + (T1 + T2) - T3 =
        Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd 1 + ((T1 - T3) + T2) := by ring
    rw [e]
    exact Z_add _ _ hA1 hZS
  show chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd y =
    psiFin X.B.I X.psiEf X.B.g X.eR X.fR (X.zR u) m
  rw [flagLevelCharacter_eq_psi_divN]
  unfold psiFin
  set C := ∑ a, hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat m *ᵥ incl X.B.I (nxt X.eR (X.zR u) a))
  have e : Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd y = C + (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd y - C) := by ring
  rw [e, divN_add, X.psiEf_add, psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg hdiff, mul_one]

theorem rowChi_conj_eq_psiBes : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), GlobalTheory.Core.Mi.IdE X → ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), IsSplitIdem D e → Formalism.L2.NTheta.IsIdemAt e PP → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ n ∈ flagN B.d, Formalism.L2.Theta.SuppAt e (D.sp.Y 0) n → ((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u)) ∈ rowJ X h → rowChi X h (((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u))) = psiBes ψ B.d 1 (vecB B.o B.ζ) n := by
  intro D X h u ψ A B _hE PP e hsp hid hg n hn hsupp hJ
  have hGf : n ∈ GfC (D.sp.Y 0) := mem_GfC_of_suppAt hsp hsupp
  have h1 : (iotaX X h n).1 = 1 := (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h n).2 hGf
  have hix : iotaX X h ((iotaX X h).symm (1, X.xu u)) = (1, X.xu u) :=
    ContinuousMulEquiv.apply_symm_apply _ _
  have hι : iotaX X h (((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u))) =
      (1, (X.xu u)⁻¹ * (iotaX X h n).2 * X.xu u) := by
    rw [map_mul, map_mul, map_inv, hix]
    ext
    · simp [h1]
    · rfl
  have hK : (X.xu u)⁻¹ * (iotaX X h n).2 * X.xu u ∈ X.K2 := by
    have h2 := hJ
    unfold rowJ at h2
    rw [Set.mem_preimage, hι] at h2
    exact h2.2
  obtain ⟨ε, hε, hs⟩ := exists_eps X h hid hg n hsupp
  have hN : (iotaX X h n).2 ∈ X.NfinU u := ((B.tieN n).1 hn).2
  have hc := besselLevel_chi_conj_eq_finite_bessel_character X u _ ε hε hs hN hK
  have hψ := B.tieψ n hn
  rw [h1, Formalism.L2.S.Pv.TauS.psiInfU_one, one_mul] at hψ
  rw [rowChi, hι]
  dsimp only
  rw [hc, ← hψ, star_star]

end GlobalTheory.RowBesChar
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_support_split_places : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), GlobalTheory.Core.Mi.IdE X → ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), IsSplitIdem D e → Formalism.L2.NTheta.IsIdemAt e PP → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ n ∈ flagN B.d, Formalism.L2.Theta.SuppAt e (D.sp.Y 0) n → ((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u)) ∈ rowJ X h → rowChi X h (((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u))) = psiBes ψ B.d 1 (vecB B.o B.ζ) n := by
  first | exact @GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes | exact GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes | (intros; apply GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.PrinFrame

section Alg

open Matrix

variable {A : Type} [CommRing A] {n : ℕ}

theorem conj_single_mem (S : Subring A) (p : S) (hp : p * p = p) (γ : GL (Fin n) A)
    (h : ∀ i j, i ≠ j → ∀ a b, (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S) (i j a b : Fin n) :
    (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S := by
  by_cases hij : i = j
  · subst hij
    by_cases hl : ∃ l, l ≠ i
    · obtain ⟨l, hl⟩ := hl
      have hp' : (p : A) * p = p := congrArg Subtype.val hp
      have e1 : ∑ c, γ.1 l c * (γ⁻¹).1 c l = 1 := by
        have := congrFun (congrFun γ.mul_inv l) l
        rwa [Matrix.mul_apply, Matrix.one_apply_eq] at this
      have e2 : (p : A) * ((γ⁻¹).1 a i * γ.1 i b) =
          ∑ c, ((p : A) * ((γ⁻¹).1 a i * γ.1 l c)) * ((p : A) * ((γ⁻¹).1 c l * γ.1 i b)) := by
        rw [← mul_one ((p : A) * _), ← e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        linear_combination (-((γ⁻¹).1 a i * γ.1 i b * γ.1 l c * (γ⁻¹).1 c l)) * hp'
      rw [e2]
      exact S.sum_mem fun c _ => S.mul_mem (h i l hl.symm a c) (h l i hl c b)
    · push Not at hl
      have e1 : (γ⁻¹).1 i i * γ.1 i i = 1 := by
        have := congrFun (congrFun γ.inv_mul i) i
        rwa [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i (fun c _ hc => absurd (hl c) hc)
          (fun hc => absurd (Finset.mem_univ i) hc)] at this
      rw [hl a, hl b, e1, mul_one]
      exact p.2
  · exact h i j hij a b

theorem red_conj_eq_one (S : Subring A) {k : Type} [CommRing k] (ρ : S →+* k) (p : S) (hρ : ρ p = 1) (γ : GL (Fin n) A)
    (h : ∀ i j a b, (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S) (y y₀ : Matrix (Fin n) (Fin n) S)
    (hy : y₀.map S.subtype = γ.1 * y.map S.subtype * (γ⁻¹).1) (h1 : y.map ρ = 1) : y₀.map ρ = 1 := by
  have e0 : ∀ {B : Type} [CommRing B] (f : S →+* B) (z : Matrix (Fin n) (Fin n) S), (z - 1).map f = z.map f - 1 := by
    intro B _ f z
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]
  have e1 : (y₀ - 1).map S.subtype = γ.1 * (y - 1).map S.subtype * (γ⁻¹).1 := by
    rw [e0, e0, hy, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv]
  have e2 : ∀ b a, ρ ((y - 1) b a) = 0 := fun b a => by
    have := congrFun (congrFun (e0 ρ y) b) a
    rwa [h1, sub_self] at this
  rw [← sub_eq_zero, ← e0]
  ext j i
  have e3 : p * (y₀ - 1) j i = ∑ a, ∑ b, (⟨_, h i j a b⟩ : S) * (y - 1) b a := by
    apply Subtype.ext
    have := congrFun (congrFun e1 j) i
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Subring.subtype_apply] at this
    rw [Subring.coe_mul, this]
    simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have e4 := congrArg ρ e3
  rw [map_mul, hρ, one_mul] at e4
  simp only [map_sum, map_mul, e2, mul_zero, Finset.sum_const_zero] at e4
  exact e4

theorem transv_entry (S : Subring A) (p : S) (β β₀ : GL (Fin n) A) (i j : Fin n) (z : Matrix (Fin n) (Fin n) S)
    (h : (p : A) • (β.1 * z.map S.subtype * (β⁻¹).1) =
      (p : A) • (β₀.1 * (Matrix.transvection i j (1 : S)).map S.subtype * (β₀⁻¹).1)) (a b : Fin n) :
    (p : A) * (((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b) ∈ S := by
  have h2 := congrArg (fun M => (β⁻¹).1 * M * β.1) h
  have e0 : (Matrix.transvection i j (1 : S)).map S.subtype = 1 + Matrix.single i j (1 : A) := by
    rw [Matrix.transvection, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single,
      map_one]
  have e1 : (β⁻¹).1 * (β.1 * z.map S.subtype * (β⁻¹).1) * β.1 = z.map S.subtype := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have e2 : (β⁻¹).1 * (β₀.1 * (1 + Matrix.single i j (1 : A)) * (β₀⁻¹).1) * β.1 =
      1 + ((β₀⁻¹ * β)⁻¹).1 * Matrix.single i j (1 : A) * (β₀⁻¹ * β).1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Units.inv_mul, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_smul, Matrix.smul_mul] at h2
  rw [e0, e1, e2] at h2
  have h3 := congrFun (congrFun h2 a) b
  have e3 : (((β₀⁻¹ * β)⁻¹).1 * Matrix.single i j (1 : A) * (β₀⁻¹ * β).1) a b =
      ((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b := by
    generalize ((β₀⁻¹ * β)⁻¹).1 = M
    generalize (β₀⁻¹ * β).1 = N
    simp [Matrix.mul_apply, Matrix.single, ite_and]
  simp only [Matrix.smul_apply, Matrix.add_apply, e3, smul_eq_mul, Matrix.map_apply, Subring.subtype_apply, mul_add] at h3
  rw [← sub_eq_iff_eq_add'] at h3
  rw [← h3]
  refine S.sub_mem (S.mul_mem p.2 (z a b).2) (S.mul_mem p.2 ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

end Alg

end GlobalTheory.PrinFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrinFrame

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem redFn_eq_one_of_le (V : HSp D) (β β₀ : GL (Fin V.rank) (Lev.EAf D))
    (h₀ : Formalism.L2.DIV.IsFrame β₀ (Formalism.L2.Herm.crdLat V V.L0))
    (hle : ∀ κ ∈ GfC V, finE V κ ∈ Formalism.L2.DIV.St β₀ → finE V κ ∈ Formalism.L2.DIV.St β)
    (P : Formalism.L2.DIV.Pl D.host.E) (hP : ¬ Formalism.IndefR.Lev.IsConjPl P P) (x : GL (Fin V.rank) (Lev.EAf D))
    (hx : x ∈ Formalism.L2.DIV.St β) (hx₀ : x ∈ Formalism.L2.DIV.St β₀) (h1 : redFn β P x = 1) : redFn β₀ P x = 1 := by
  obtain ⟨β₁, h₁⟩ := GlobalTheory.StdFrames.exists_base V
  obtain ⟨c, hc⟩ := GlobalTheory.StdFrames.isSD_one h₁
  have hB : IsBaseFrame V β₀ (Formalism.L2.Herm.crdLat V V.L0) (1 ^ c) := ⟨h₀, hc.2⟩
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt hP
  obtain ⟨p, hp, hpp, hres⟩ := GlobalTheory.ParahoricLift.exists_idem_int he
  have hoff : ∀ i j, i ≠ j → ∀ a b, (p : Lev.EAf D) * (((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j hij
    have hu' : p * (Matrix.transvection i j (1 : Formalism.L2.Herm.intAf D.host.F D.host.E)).det = p := by
      rw [Matrix.det_transvection_of_ne i j hij, mul_one]
    have hmm := GlobalTheory.ParahoricLift.conj_inv_part β₀ p p _ hu' hpp
    rw [hp] at hmm
    obtain ⟨κ, hs, hκ⟩ := GlobalTheory.ParahoricLift.split_lift_fin V he.1 _ _ hmm
    have hPI : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
    obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    have hsf := GlobalTheory.LevSplit.supp_fin V (f := e + cA D e) hs
    rw [← hp] at hκ
    have hf : GlobalTheory.LevSplit.finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
      rw [RingHom.map_add, GlobalTheory.LevSplit.finSw_cA, hp]
    have hSt : finE V κ ∈ Formalism.L2.DIV.St β₀ :=
      GlobalTheory.ParahoricLift.mem_St_of_part D.sp.cm.sig V.gram _ β₀ hB.1 (GlobalTheory.ParahoricLift.hatL_selfDual hB) p p hpp
        (GlobalTheory.LevSplit.sigR_int p.2) _ hu' (finE V κ) (GlobalTheory.LevSplit.finE_mem_UA V κ) _ hf hsf hκ
    obtain ⟨z, hz⟩ := hle κ ((T3 P e _ hPI).2.2.1 κ hs) hSt
    rw [← hz] at hκ
    exact transv_entry _ p β β₀ i j z.1 hκ
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y₀, hy₀⟩ := hx₀
  rw [redFn_frGL] at h1
  rw [← hy₀, redFn_frGL]
  have e1 : intGL D.host.F D.host.E V.rank y₀ = (β₀⁻¹ * β) * intGL D.host.F D.host.E V.rank y * (β₀⁻¹ * β)⁻¹ := by
    have e2 : β₀ * intGL D.host.F D.host.E V.rank y₀ * β₀⁻¹ = β * intGL D.host.F D.host.E V.rank y * β⁻¹ := hy₀
    rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq] at e2
    rw [e2]
    group
  exact Units.ext (red_conj_eq_one _ (resS D.host.F P) p hres (β₀⁻¹ * β) (conj_single_mem _ p hpp _ hoff) y.1 y₀.1
    (congrArg Units.val e1) (congrArg Units.val h1))

theorem kset_iff_finE (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) : (iotaX X h κ).2 ∈ X.B.I.Kset ↔ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset ↔ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
    intro I hI
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx := GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) (Formalism.IndefR.RationalEmbedding.iota D κ).2
    generalize Lev.finE (D.sp.Y 0) κ = y at e2 ⊢
    subst e2
    exact hx
  exact key X.B.I h

theorem edgeSum_symEdge_one {k : Type} [CommRing k] {n : ℕ} (ρ l : ℕ) : edgeSum (symEdge ρ l) (1 : GL (Fin n) k) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · refine Matrix.one_apply_ne ?_
    rintro rfl
    unfold symEdge at h
    omega
  · rfl

theorem rowChi_eq_one : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), GlobalTheory.Core.Mi.IdE X → ∀ (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St β) ↔ ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset)) → ∀ κ ∈ rowJ X h, (∀ PP ∈ Pg, redFn β PP (finE (D.sp.Y 0) κ) = 1) → rowChi X h κ = 1 := by
  intro D X h _ Pg hPg hIdem β hβ κ hκ hred
  have hnc := GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces Pg hPg hIdem
  have hψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    haveI := PP.isPrime
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun e => hψ (by rw [e]; rfl)⟩
  choose ψ0 hψ0 using hψ
  obtain ⟨β₀, h₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin X h Pg hPg hnc ψ0 fun PP _ => hψ0 PP
  have hle : ∀ κ ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β₀ → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β :=
    fun κ h1 h2 => ((hβ κ).2 ⟨(GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h κ).2 h1, (kset_iff_finE X h β₀ h₀ κ).2 h2⟩).2
  have hS₀ := ((hK κ).1.1 hκ.2).1
  have hS := hle κ ((GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h κ).1 hκ.1) hS₀
  refine ((hK κ).2 hκ.2).trans (Finset.prod_eq_one fun PP hPP => ?_)
  rw [redFn_eq_one_of_le (D.sp.Y 0) β β₀ h₀ hle PP (hnc PP hPP PP hPP) _ hS hS₀ (hred PP hPP), edgeSum_symEdge_one,
    AddChar.map_zero_eq_one]

end GlobalTheory.PrinFrame

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_level_reduction_criterion : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), GlobalTheory.Core.Mi.IdE X → ∀ (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St β) ↔ ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset)) → ∀ κ ∈ rowJ X h, (∀ PP ∈ Pg, redFn β PP (finE (D.sp.Y 0) κ) = 1) → rowChi X h κ = 1 := by
  first | exact @GlobalTheory.PrinFrame.rowChi_eq_one | exact GlobalTheory.PrinFrame.rowChi_eq_one | (intros; apply GlobalTheory.PrinFrame.rowChi_eq_one <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChrMatch

variable {D : D7}

theorem suppAt_conj (e : AE D) (V : HSp D) (a n : GA D V) (hn : Formalism.L2.Theta.SuppAt e V n) :
    Formalism.L2.Theta.SuppAt e V (a * n * a⁻¹) := by
  have h1 : Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 =
      Formalism.L2.Theta.mt V a * (Formalism.L2.Theta.mt V n - 1) * Formalism.L2.Theta.mt V a⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have h2 : (e + cA D e) • (Formalism.L2.Theta.mt V n - 1) = Formalism.L2.Theta.mt V n - 1 := by
    ext i j; exact hn i j
  intro i j
  have h3 : (e + cA D e) • (Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1) = Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 := by
    rw [h1, ← Matrix.smul_mul, ← Matrix.mul_smul, h2]
  exact congrFun (congrFun h3 i) j

theorem levChi_mul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ levS V β L) (hk' : k' ∈ levS V β L) : levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have := (levChar D.sp.cm V.gram β L).map_mul ⟨finE V k, hk.2⟩ ⟨finE V k', hk'.2⟩
  unfold levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg Units.val this

theorem levChi_of_red_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0)
    (hQ : L.Q = ∅) {k : GA D V} (hk : ∀ PP ∈ L.Pg, redFn β PP (finE V k) = 1) : levChi V β L k = 1 := by
  have h1 : rTup β L (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [hk PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, hs, hQ]
  simp

theorem rowChi_conj_of_mem (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1)
    (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : GlobalTheory.Core.Mi.IdE S.X) (hB : d.Base)
    (hTP : IsTypePlaces d.c.Pg) (hPG : GlobalTheory.LocMod.PinGBy G cG) (hLev : LevX (F₀ u) d h0)
    (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)) (hBl : B.lev = d.B 0 D.R.rS h0) (hAd : B.Adapted (S.tr u).wt)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = d.t 0)
    (hs : s = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * d.bot.β)) ↔
      ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset))
    (hmem : ∀ k ∈ levS (D.sp.Y 0) d.bot.β d.bot.L, s * k * s⁻¹ ∈ rowJ S.X S.inst) :
    ∀ k ∈ levS (D.sp.Y 0) d.bot.β d.bot.L, rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hemb : ∀ b, embA B.d B.o b = (embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b : GA D (d.st 0).V) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (d.st 0).V) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (d.bes 0 D.R.rS h0).d : Subgroup (GA D (d.st 0).V)) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  have hps : psiBes d.c.ψ B.d 1 (vecB B.o B.ζ) =
      (psiBes d.c.ψ (d.bes 0 D.R.rS h0).d 1 (vecB (d.bes 0 D.R.rS h0).o (d.bes 0 D.R.rS h0).ζ) : GA D (d.st 0).V → ℂ) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => psiBes d.c.ψ L.d 1 (vecB L.o L.ζ)) hBl)
  refine GlobalTheory.T.level_group_property_closed_mul D u d τ G cG h0 hB hTP hPG
    (fun k : GA D (D.sp.Y 0) => rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k) ?_ ?_ ?_ ?_
  · intro (k : GA D (D.sp.Y 0)) hk (k' : GA D (D.sp.Y 0)) hk' q q'
    show rowChi S.X S.inst (s * (k * k') * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L (k * k')
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    have q₁ : rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k := q
    have q₂ : rowChi S.X S.inst (s * k' * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k' := q'
    rw [levChi_mul (D.sp.Y 0) d.bot.β d.bot.L hk hk', ← q₁, ← q₂, e, rowChi, rowChi, rowChi, map_mul, Prod.snd_mul,
      S.Y.hK.2.2.2.1 _ (hmem k hk).2 _ (hmem k' hk').2, star_mul']
  · intro PP (n : GA D (D.sp.Y 0)) q hn hq hl hk
    have h2 := GlobalTheory.T.level_zero_element_reduction D u d τ G cG h0 hB hTP hPG PP n q hq hl hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
      rw [hs]; group
    have hj := hmem (t⁻¹ * n * t) (by rw [ht]; exact hk)
    rw [e] at hj
    have h1 := GlobalTheory.T.flag_support_split_places D S.X S.inst u d.c.ψ _ B hE PP.1 (G PP).q.e (G PP).q.split (G PP).idem (hTP.1 PP.1 PP.2) _
      (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn') (suppAt_conj _ _ _ _ hl.1) hj
    subst ht
    show rowChi S.X S.inst (s * ((show GA D (D.sp.Y 0) from d.t 0)⁻¹ * n * (show GA D (D.sp.Y 0) from d.t 0)) * s⁻¹) = _
    refine (congrArg _ e).trans (h1.trans (Eq.trans ?_ h2.symm))
    rw [GlobalTheory.CharLaws.psiBes_conj]
    exact congrFun hps n
  · intro b hb hk
    have h1 := (GlobalTheory.T.bessel_adapted_translate_level D u F₀ S d h0 hE hB hLev B hBl hAd a₀ hH0 b hb).2 hk
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    rw [hemb b] at e
    subst ht
    exact (congrArg _ e).trans h1
  · intro (k : GA D (D.sp.Y 0)) hk hr1
    obtain ⟨hr, ξ, hL⟩ := (hB.st 0 hm).lev
    have hLb : d.bot.L = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) := hL
    show rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k
    rw [GlobalTheory.T.row_level_reduction_criterion D S.X S.inst hE d.c.Pg hTP hB.com.split _ hSt _ (hmem k hk) (fun PP hPP => by
      rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.redFn_conj]; exact hr1 PP hPP), hLb]
    exact (levChi_of_red_one _ _ _ rfl rfl hr1).symm


end GlobalTheory.ChrMatch

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroChar

theorem map_conj_local {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) {β : GL (Fin (c.V 0).rank) (Lev.EAf D)} {b : GA D (c.V 0)}
    {π' : Lev.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a) {n : GA D (c.V 0)}
    {q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k}
    (hloc : (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) n q)
    (σ : Fin (c.V 0).rank → XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) (hσ : Function.Bijective σ)
    (hM : MovedTo (ofSplit G.q) (c.V 0) b β
      (((G.FY 0 (G.s + 1) (Nat.zero_add _)).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val).submatrix id σ)) :
    ((β⁻¹ * finE (c.V 0) (b⁻¹ * n * b) * β).val).map π' =
      ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val * q.val *
        ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val).submatrix σ σ := by
  set F := G.FY 0 (G.s + 1) (Nat.zero_add _) with hF
  set B := (G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _) with hB
  set p := ofSplit G.q with hp
  have hβ := GlobalTheory.LocMod.StepVec.map_eq_of_movedTo p F (π' := π') hπ B.val σ hM
  have hfin : ∀ g : GA D (c.V 0), (finE (c.V 0) g).val.map π' = (mt (c.V 0) g).map p.π := by
    intro g
    rw [GlobalTheory.LevSplit.finE_val]
    ext i j
    exact hπ _
  have hBB : (B⁻¹).val * B.val = 1 := Units.inv_mul B
  have hmt : ∀ g h : GA D (c.V 0), (mt (c.V 0) (g * h)).map p.π = (mt (c.V 0) g).map p.π * (mt (c.V 0) h).map p.π :=
    fun g h => Matrix.map_mul
  have ht1 : (mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π = 1 := by
    rw [← hmt, mul_inv_cancel]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  set W := (mt (c.V 0) b⁻¹).map p.π * F.β * B.val with hW
  set W' := (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π with hW'
  have hWW : W' * W = 1 := by
    rw [hW, hW']
    calc (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π * ((mt (c.V 0) b⁻¹).map p.π * F.β * B.val)
        = (B⁻¹).val * (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * B.val := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ht1, Matrix.mul_one, F.γβ, Matrix.mul_one, hBB]
  have hβ' : β.val.map π' = W.submatrix id σ := by
    rw [hβ]; rfl
  have hinv : (β⁻¹).val.map π' = W'.submatrix σ id := by
    refine Matrix.left_inv_eq_left_inv (A := β.val.map π') ?_ ?_
    · rw [← Matrix.map_mul, Units.inv_mul]; exact Matrix.map_one _ (map_zero _) (map_one _)
    · rw [hβ', ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hWW]
      exact Matrix.submatrix_one_equiv (Equiv.ofBijective σ hσ)
  have hn : (mt (c.V 0) n).map p.π = F.β * q.val * F.γ := hloc.2
  rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hinv, hfin, hβ', hmt, hmt, hn]
  have hs : ∀ (X : Matrix (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) (Fin (c.V 0).rank) G.k)
      (Mid : Matrix (Fin (c.V 0).rank) (Fin (c.V 0).rank) G.k)
      (Z : Matrix (Fin (c.V 0).rank) (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k),
      X.submatrix σ id * Mid * Z.submatrix id σ = (X * Mid * Z).submatrix σ σ := fun X Mid Z => Matrix.ext fun i j => rfl
  rw [hs]
  congr 1
  rw [hW, hW']
  calc (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π *
        ((mt (c.V 0) b⁻¹).map p.π * (F.β * q.val * F.γ) * (mt (c.V 0) b).map p.π) *
        ((mt (c.V 0) b⁻¹).map p.π * F.β * B.val)
      = (B⁻¹).val * (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * q.val *
        (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * B.val := by
        simp only [Matrix.mul_assoc]
    _ = (B⁻¹).val * q.val * B.val := by simp only [ht1, Matrix.mul_one, F.γβ]

set_option maxHeartbeats 1000000 in

theorem psi_red_at {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Pl D.host.E) (b : GA D (c.V 0))
    (β : GL (Fin (c.V 0).rank) (Lev.EAf D)) (hL : GlobalTheory.LevZero.LocAt G PP b β) (hr : D.R.r ≤ (c.V 0).rank) (n : GA D (c.V 0))
    (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k) (p : ℕ) (hq : q ∈ GlobalTheory.RootEx.N G.k _ (G.s + 1) p)
    (hloc : (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) n q) (hS : finE (c.V 0) (b⁻¹ * n * b) ∈ St β)
    (hblk : redFn β PP (finE (c.V 0) (b⁻¹ * n * b)) ∈ blockTri (blk2 D.R.r)) (z : 𝓞 D.host.E)
    (hz : Ideal.Quotient.mk PP.asIdeal z = edgeSum (GlobalTheory.chainEdge D.R.k) (upperLeftBlock hr (redFn β PP (finE (c.V 0) (b⁻¹ * n * b))))) :
    (G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (ofSplit G.q).pr (z : D.host.E)) : ℂ) = (G.S.ψ (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D G.k G.q PP hL.idem
  obtain ⟨e, he, hM⟩ := hL.frame (G.s + 1) (Nat.zero_add _)
  have hσ : Function.Bijective (fun i => stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm i)) :=
    (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _))).bijective
  have hmat := map_conj_local G hπ hloc _ hσ hM
  obtain ⟨y, hy⟩ := hS
  have hI : β⁻¹ * finE (c.V 0) (b⁻¹ * n * b) * β = intGL _ _ _ y := by
    rw [← hy]
    simp [frGL, MulAut.conj_apply]
    group
  rw [hI] at hmat
  rw [← hy, redFn_frGL] at hz hblk
  unfold edgeSum at hz
  rw [upper_block_val_submatrix hr hblk] at hz
  have hrk : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hN := (GlobalTheory.RootEx.Radical.mem_N_iff q).1 hq
  have hsum : (∑ i : Fin D.R.r, ∑ j : Fin D.R.r, if GlobalTheory.chainEdge D.R.k i j then
      ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val * q.val *
        ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val)
        (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr i)))
        (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr j))) else 0) =
      (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q :=
    GlobalTheory.NChainChar.edge_sum_typeFrame D.R.k D.R.t G.s (c.V 0).rank D.R.r p hr hrk e he G.S.ϖ q hN
  set w : Formalism.L2.Herm.intAf D.host.F D.host.E := ∑ i : Fin D.R.r, ∑ j : Fin D.R.r,
    if GlobalTheory.chainEdge D.R.k i j then y.val (Fin.castLE hr i) (Fin.castLE hr j) else 0 with hw
  have hres : resS D.host.F PP w = Ideal.Quotient.mk PP.asIdeal z := by
    rw [hz, hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · exact map_zero _
  have hker := (hred.ker (w - Formalism.L2.DIV.oToS D.host.F D.host.E z)).1 (by
    rw [map_sub, hres, Formalism.L2.DIV.resS_oToS, sub_self])
  have hpw : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) w = (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q := by
    rw [← hsum, hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · have := congrFun (congrFun hmat (Fin.castLE hr i)) (Fin.castLE hr j)
      exact this
    · exact map_zero _
  have hpz : π' ((Formalism.L2.DIV.oToS D.host.F D.host.E z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
      (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
  have hv : ValuativeRel.valuation G.k ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) < 1 := by
    have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (w - Formalism.L2.DIV.oToS D.host.F D.host.E z) =
        -((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) := by
      rw [map_sub, hpw]
      rw [show (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
        π' ((Formalism.L2.DIV.oToS D.host.F D.host.E z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) from rfl, hpz]
      ring
    rw [h1, Valuation.map_neg] at hker
    exact hker
  have hone : G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q)) = 1 := by
    refine (G.S.cond _).2 ?_ _ le_rfl
    have h5 := (G.S.unif _).1 hv
    have h6 : ValuativeRel.valuation G.k (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (G.S.ϖ : G.k)) = ValuativeRel.valuation G.k ((1 : G.kˣ) : G.k) := by
      rw [Units.inv_mul, Units.val_one]
    rw [← h6, map_mul, map_mul]
    exact mul_le_mul_right h5 _
  have e2 : ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (ofSplit G.q).pr (z : D.host.E) =
      ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) +
        GlobalTheory.RootEx.simpleSum q := by
    have : ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (G.S.ϖ : G.k) = 1 := by rw [Units.inv_mul]
    linear_combination (GlobalTheory.RootEx.simpleSum q) * this
  rw [e2, AddChar.map_add_eq_mul, hone, one_mul]

theorem levChi_eq_psiBes : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = psiBes c.ψ (c.bes 0 D.R.rS h0).d 1 (vecB (c.bes 0 D.R.rS h0).o (c.bes 0 D.R.rS h0).ζ) n := by
  intro D c v cm st b G h0 hB PP n q hq hloc hlev
  obtain ⟨hr, ξ, hL⟩ := hB.mem.lev
  have hL' : st.L = Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B := hL
  have hl := hlev.2
  rw [hL'] at hl
  change finE (c.V 0) (b⁻¹ * n * b) ∈ lev _ _ _ _ at hl
  rw [mem_lev, mem_parLev] at hl
  have hP : (fun PP : cm.Pg => upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) (b⁻¹ * n * b)))) ∈ cm.P.H := hl.2
  have hchi : levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = ((cm.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) := by
    rw [hL']
    unfold levChi levFn
    rw [extendOne_of_mem _ hl.2]
    have e1 : (Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B).s = 0 := rfl
    have e2 : (Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B).Q = ∅ := rfl
    simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
    rfl
  rw [hchi]
  choose x hx using (hB.grp _).1 hP
  rw [hB.chr ⟨_, hP⟩ x hx, Units.coe_prod, Finset.prod_eq_single PP]
  · obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := PP.1.asIdeal)
      (edgeSum (GlobalTheory.chainEdge D.R.k) (upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) (b⁻¹ * n * b)))))
    rw [GlobalTheory.LevZero.lam_eq_of_red (G PP) PP.1 (hB.loc PP).idem (x PP) _ (hx PP) z hz]
    rw [psi_red_at (G PP) PP.1 b st.β (hB.loc PP) hr n q _ hq hloc hl.1.2.1 (blockTri_blkOf_le _ _ (hl.1.2.2.1 PP.1 PP.2)) z hz]
    rw [GlobalTheory.LocBesChar.psiBes_isLoc D (G PP).k (ofSplit (G PP).q) c.ψ (G PP).S.ψ (G PP).char D.R.rS
      (c.B 0 D.R.rS h0) ((G PP).sc 0) _ ((G PP).s + 1) ((G PP).FX 0 (by omega)) ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _))
      ((G PP).bes 0 D.R.rS h0 ((G PP).s + 1) (Nat.zero_add _)) n q hq hloc]
  · intro PP' _ hne
    obtain ⟨e, he⟩ := hB.com.split
    have h1 := GlobalTheory.NChainChar.redFn_conj_eq_one he PP.2 (hB.loc PP).idem hloc.1 b hl.1.2.1 PP'.2
      (fun h => hne (Subtype.ext h).symm)
    have h2 : Ideal.Quotient.mk PP'.1.asIdeal (0 : 𝓞 D.host.E) = edgeSum (GlobalTheory.chainEdge D.R.k)
        (upperLeftBlock hr (redFn st.β PP'.1 (finE (c.V 0) (b⁻¹ * n * b)))) := by
      rw [h1, map_zero]
      unfold upperLeftBlock
      rw [blockDiagonalExtendByOnePrimeField_one]
      symm
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · rw [Units.val_one, Matrix.one_apply_ne]
        intro e; rw [e] at hij; exact absurd hij.1 (by omega)
      · rfl
    rw [GlobalTheory.LevZero.lam_eq_of_red (G PP') PP'.1 (hB.loc PP').idem (x PP') _ (hx PP') 0 h2]
    simp [GlobalTheory.LocMod.Place.pr]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.LevZeroChar
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexZeroLevelCharacter_eq_besselCharacter : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = psiBes c.ψ (c.bes 0 D.R.rS h0).d 1 (vecB (c.bes 0 D.R.rS h0).o (c.bes 0 D.R.rS h0).ζ) n := by
  atlas_forward_decl GlobalTheory.LevZeroChar.levChi_eq_psiBes
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZeroChr

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

set_option maxHeartbeats 1000000 in

theorem rowChi_conj_of_mem (W : RealPack ex) (hW : PkHyp W) (u : D.what₂.Word) (f : FamCh W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hPl : Placed f B) (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀)
    (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : β = (pk W).βY 0)
    (Lz : Formalism.L2.DIV.LevDat D.host.E ℂ (D.sp.Y 0).rank) (hLz : Lz = GlobalTheory.LevZero.datZero W)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (hmem : ∀ k ∈ levS (D.sp.Y 0) β Lz, s * k * s⁻¹ ∈ rowJ W.S.X W.Q.instEq) :
    ∀ k ∈ levS (D.sp.Y 0) β Lz, rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) β Lz k := by
  obtain ⟨kk, i1, i2, i3, i4, ι, v, o, n, G, pl, hcis, hvis, htie, hshape, hpin, hread, hbot⟩ := hPl
  have hBot := GlobalTheory.T.bessel_local_type_data W hW u f B kk ι v o n G pl ⟨hcis, hvis, htie, hshape, hpin, hread, hbot⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hBl := hbot.lev h0
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  have hTP : GlobalTheory.Core.Mi.IsTypePlaces (GlobalTheory.BaseChain.com W).Pg := hBot.typ
  have hemb : ∀ b, embA B.d B.o b = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o b : GA D (f.c.V 0)) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (f.c.V 0)) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (f.c.bes 0 D.R.rS h0).d : Subgroup (GA D (f.c.V 0))) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  have hps : psiBes W.Q.Rl.ψ B.d 1 (vecB B.o B.ζ) =
      (psiBes f.c.ψ (f.c.bes 0 D.R.rS h0).d 1 (vecB (f.c.bes 0 D.R.rS h0).o (f.c.bes 0 D.R.rS h0).ζ) : GA D (f.c.V 0) → ℂ) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => psiBes W.Q.Rl.ψ L.d 1 (vecB L.o L.ζ)) hBl)
  have hred : ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (k : GA D (D.sp.Y 0)),
      redFn (finE (D.sp.Y 0) s * β) PP (finE (D.sp.Y 0) (s * k * s⁻¹)) = redFn β PP (finE (D.sp.Y 0) k) := fun PP k => by
    rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.redFn_conj]
  subst hβ hLz
  refine GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents (c := f.c) (GlobalTheory.BaseChain.com W) (GlobalTheory.LevZero.stZero W) (f.g.b 0) (fun PP => G (pl.symm PP)) h0 hBot
    (fun k : GA D (D.sp.Y 0) => rowChi W.S.X W.Q.instEq (s * k * s⁻¹) =
      levChi (D.sp.Y 0) ((pk W).βY 0) (GlobalTheory.LevZero.datZero W) k) ?_ ?_ ?_ ?_
  · intro (k : GA D (D.sp.Y 0)) hk (k' : GA D (D.sp.Y 0)) hk' q q'
    show rowChi W.S.X W.Q.instEq (s * (k * k') * s⁻¹) = levChi (D.sp.Y 0) ((pk W).βY 0) (GlobalTheory.LevZero.datZero W) (k * k')
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    have q₁ : rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) ((pk W).βY 0) (GlobalTheory.LevZero.datZero W) k := q
    have q₂ : rowChi W.S.X W.Q.instEq (s * k' * s⁻¹) = levChi (D.sp.Y 0) ((pk W).βY 0) (GlobalTheory.LevZero.datZero W) k' := q'
    rw [GlobalTheory.ChrMatch.levChi_mul (D.sp.Y 0) ((pk W).βY 0) (GlobalTheory.LevZero.datZero W) hk hk', ← q₁, ← q₂, e, rowChi, rowChi, rowChi,
      map_mul, Prod.snd_mul, W.S.Y.hK.2.2.2.1 _ (hmem k hk).2 _ (hmem k' hk').2, star_mul']
  · intro PP (n : GA D (D.sp.Y 0)) q hn hq hl hk
    have h2 := GlobalTheory.T.indexZeroLevelCharacter_eq_besselCharacter (c := f.c) (GlobalTheory.BaseChain.com W) (GlobalTheory.LevZero.stZero W) (f.g.b 0) (fun PP => G (pl.symm PP)) h0 hBot
      PP n q hq hl hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      rw [hs]; group
    have hj := hmem (t⁻¹ * n * t) (by rw [ht]; exact hk)
    rw [e] at hj
    have h1 := GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes D W.S.X W.Q.instEq u W.Q.Rl.ψ _ B hE PP.1 (G (pl.symm PP)).q.e
      (G (pl.symm PP)).q.split (hBot.loc PP).idem (hTP.1 PP.1 PP.2) _
      (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn') (GlobalTheory.ChrMatch.suppAt_conj _ _ _ _ hl.1) hj
    subst ht
    show rowChi W.S.X W.Q.instEq
      (s * ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * n * (show GA D (D.sp.Y 0) from f.g.b 0)) * s⁻¹) = _
    refine (congrArg _ e).trans (h1.trans (Eq.trans ?_ h2.symm))
    rw [GlobalTheory.CharLaws.psiBes_conj]
    exact congrFun hps n
  · intro (b : GA D (D.sp.X 0)) hb hk
    have hk' : (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ rJ W := by
      rw [hemb b]; exact hk
    have h1 := (GlobalTheory.T.level_trace_adapted_translate W hW u f B hbot.trace hbot.adapted a₀ hH0 b hb).2 hk'
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    subst ht
    have h3 := (congrArg (rowChi W.S.X W.Q.instEq) e).trans h1
    rw [hemb b] at h3
    exact h3
  · intro (k : GA D (D.sp.Y 0)) hk hr1
    show rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) ((pk W).βY 0) (GlobalTheory.LevZero.datZero W) k
    rw [GlobalTheory.PrinFrame.rowChi_eq_one D W.S.X W.Q.instEq hE (GlobalTheory.BaseChain.com W).Pg hTP hBot.com.split _ hSt _ (hmem k hk)
      (fun PP hPP => (hred PP k).trans (hr1 PP hPP))]
    exact (GlobalTheory.ChrMatch.levChi_of_red_one _ _ _ rfl rfl hr1).symm

set_option maxHeartbeats 1000000 in

theorem row_character_eq_extension : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → GlobalTheory.LevZero.StabAt f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (GlobalTheory.LevZero.frAt f B a₀ a) → Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (GlobalTheory.LevZero.frAt f B a₀ a) (GlobalTheory.LevZero.datZero W) (finE (D.sp.Y 0) κ) ∈ (GlobalTheory.LevZero.datZero W).P.H → κ ∈ rowJ W.S.X W.Q.instEq → rowChi W.S.X W.Q.instEq κ = ((Formalism.L2.DIV.ext1 (GlobalTheory.LevZero.datZero W).P.H (GlobalTheory.LevZero.datZero W).P.chi (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (GlobalTheory.LevZero.frAt f B a₀ a) (GlobalTheory.LevZero.datZero W) (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hPl a₀ hH0 a ha hac hSt κ hκ hκS hP _
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by
    have := GlobalTheory.Chain.StepVac.rank_Yc (D := D) (j := 0) (Nat.zero_le _)
    exact le_of_eq (this.trans (by simp))
  have hM := GlobalTheory.T.central_adapted_element_property W hW u f B hPl a₀ hH0 a ha hac hSt
  obtain ⟨β, hβ⟩ : ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), β = (pk W).βY 0 := ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ Lz : Formalism.L2.DIV.LevDat D.host.E ℂ (D.sp.Y 0).rank, Lz = GlobalTheory.LevZero.datZero W := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = tOf f B a₀ a := ⟨_, rfl⟩
  have hfr : GlobalTheory.LevZero.frAt f B a₀ a = finE (D.sp.Y 0) s * β := by rw [hs, hβ]; rfl
  have hSt' : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset) := by
    rw [← hfr]; exact hSt
  have key := rowChi_conj_of_mem W hW u f B hPl a₀ hH0 a hac _ s rfl hs β hβ Lz hLz hSt'
  have hM' : ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β) →
      rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ) ∈ Lz.P.H → κ ∈ rowJ W.S.X W.Q.instEq := by
    rw [← hfr, hLz]; exact fun κ h1 h2 h3 => (hM κ h1 h2).2 h3
  have hκS' : finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β) := by rw [← hfr]; exact hκS
  have hP' : rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ) ∈ Lz.P.H := by rw [← hfr, hLz]; exact hP
  suffices hgoal : rowChi W.S.X W.Q.instEq κ =
      ((ext1 Lz.P.H Lz.P.chi (rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) by
    rw [← hfr, hLz] at hgoal; exact hgoal
  have e1 : Lz.s = 0 := by rw [hLz]; rfl
  have e2 : Lz.Q = ∅ := by rw [hLz]; rfl
  have e3 : (D.sp.Y 0).rank ≤ Lz.r := by rw [hLz]; exact hn
  clear hκS hP hM hSt hfr hs hβ hLz
  have hfin : ∀ s k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) → s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := fun s k hk => by
    rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq] at hk ⊢
    rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  have hmem : ∀ k ∈ levS (D.sp.Y 0) β Lz, s * k * s⁻¹ ∈ rowJ W.S.X W.Q.instEq := by
    intro k hk
    obtain ⟨hf, hl⟩ := hk
    change finE (D.sp.Y 0) k ∈ lev _ _ _ _ at hl
    rw [mem_lev, mem_parLev] at hl
    have hs' : finE (D.sp.Y 0) (s * k * s⁻¹) ∈ St (finE (D.sp.Y 0) s * β) := by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hl.1.2.1
    refine hM' _ (hfin s k hf) hs' ?_
    rw [hfe, GlobalTheory.FrameConj.rTup_conj]
    exact hl.2
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  rw [hfe, GlobalTheory.FrameConj.rTup_conj] at hP' ⊢
  have hk₀ : k₀ ∈ levS (D.sp.Y 0) β Lz := by
    refine ⟨?_, ?_⟩
    · have := hfin s⁻¹ _ hκ
      rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
    · show finE (D.sp.Y 0) k₀ ∈ lev _ _ _ _
      rw [mem_lev, mem_parLev]
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS'
      exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hκS', fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ e3 _,
        fun PP hPP => absurd (e2 ▸ hPP) (Finset.notMem_empty _)⟩, hP'⟩
  refine (key hmem k₀ hk₀).trans ?_
  unfold levChi levFn
  simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]

end GlobalTheory.LevZeroChr

end
end
