import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCoset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphismCovolumeEqLatticeMass
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.CharacterFixedPoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActFrame
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowEqIffMovedLatticeInnerDataEq

section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (t₀ t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), t₀.relevant → t₀.G ≠ 0 → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → t.relevant ∧ t.G = t₀.G ∧ Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm ∧ nmlOf Y u u' t = nmlOf Y u u' t₀ ∧ ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → (Y.tO u u').s0 t₀ t = 1 ∧ (Y.tO u u').scal t₀ t) := by
  first | exact @GlobalTheory.HL.CosetConst.coset_const | exact GlobalTheory.HL.CosetConst.coset_const | (intros; apply GlobalTheory.HL.CosetConst.coset_const <;> assumption)
end

section
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.CosetOrbital

open Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FormTranspose

theorem sum_norm_sq_basis_indep {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {ι : Type} [Fintype ι] (T : Wq →L[ℂ] Wp) (b e : OrthonormalBasis ι ℂ Wq) :
    ∑ i, ‖T (b i)‖ ^ 2 = ∑ i, ‖T (e i)‖ ^ 2 := by
  haveI := FiniteDimensional.complete ℂ Wq
  haveI := FiniteDimensional.complete ℂ Wp
  set c := stdOrthonormalBasis ℂ Wp
  have key : ∀ f : OrthonormalBasis ι ℂ Wq,
      ∑ i, ‖T (f i)‖ ^ 2 = ∑ k, ‖ContinuousLinearMap.adjoint T (c k)‖ ^ 2 := by
    intro f
    have h1 : ∀ i, ‖T (f i)‖ ^ 2 = ∑ k, ‖⟪ContinuousLinearMap.adjoint T (c k), f i⟫_ℂ‖ ^ 2 := by
      intro i
      rw [← c.sum_sq_norm_inner_right (T (f i))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ContinuousLinearMap.adjoint_inner_left]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact f.sum_sq_norm_inner_left _
  rw [key b, key e]

theorem norm_hsEmb_unitary {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (c : ℂ) (hc : ‖c‖ = 1) (A : Wp ≃ₗᵢ[ℂ] Wp) (B : Wq ≃ₗᵢ[ℂ] Wq) (O : Wq →L[ℂ] Wp) :
    ‖Formalism.L2.SG.PackageTie.hsEmb (c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
      (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq))))‖ =
      ‖Formalism.L2.SG.PackageTie.hsEmb O‖ := by
  have hsq : ∀ T : Wq →L[ℂ] Wp, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ ^ 2 =
      ∑ i, ‖T (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
    intro T
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Formalism.L2.SG.PackageTie.hsEmb]
  have h2 : ‖Formalism.L2.SG.PackageTie.hsEmb (c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
      (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq))))‖ ^ 2 =
      ‖Formalism.L2.SG.PackageTie.hsEmb O‖ ^ 2 := by
    rw [hsq, hsq]
    have e1 : ∀ i, ‖(c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
        (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq)))) (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 =
        ‖O (((stdOrthonormalBasis ℂ Wq).map B.symm) i)‖ ^ 2 := by
      intro i
      simp [norm_smul, hc]
    simp_rw [e1]
    exact sum_norm_sq_basis_indep O _ _
  have h0 : 0 ≤ ‖Formalism.L2.SG.PackageTie.hsEmb O‖ := norm_nonneg _
  have h0' := norm_nonneg (Formalism.L2.SG.PackageTie.hsEmb (c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
      (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq)))))
  nlinarith [sq_nonneg (‖Formalism.L2.SG.PackageTie.hsEmb O‖ - ‖Formalism.L2.SG.PackageTie.hsEmb (c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
      (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq))))‖)]

variable {D : D7} (X : HidaSetting D)

theorem psi_inv (u : D.what₂.Word) {n : X.B.I.Ginf} (hn : n ∈ X.NinfU u) :
    X.psiInfU u n⁻¹ = (X.psiInfU u n)⁻¹ := by
  have hC := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  have hne : ∀ s, X.psiInfU u s ≠ 0 := by
    intro s h0; have := psiInfU_norm X u s; rw [h0, norm_zero] at this; exact zero_ne_one this
  have h1 : X.psiInfU u 1 = 1 := by
    have e := (hC.2.1 1 hC.1 1 hC.1).2
    rw [one_mul] at e
    have e2 : X.psiInfU u 1 * (X.psiInfU u 1 - 1) = 0 := by rw [mul_sub, ← e]; ring
    rcases mul_eq_zero.1 e2 with h | h
    · exact absurd h (hne 1)
    · exact sub_eq_zero.1 h
  have e := (hC.2.1 n hn n⁻¹ (hC.2.2 n hn)).2
  rw [mul_inv_cancel, h1] at e
  exact eq_inv_of_mul_eq_one_right e.symm

end GlobalTheory.CosetOrbital

namespace GlobalTheory.CosetOrbital
open Formalism.L2.SG.Pf.FormTranspose

theorem wu_move {D : D7} (X : HidaSetting D) (v : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.NinfU v) (h : X.B.I.Ginf)
    (hh : h ∈ X.SinfU v) (x : X.B.I.Ginf) :
    X.Wu v ((s⁻¹ * h) * x) = (X.psiInfU v s⁻¹ * X.psiInfU v h) •
      (Formalism.L2.SG.RealObj.InfCut.piIso X v h hh) (X.Wu v x) := by
  have hNS : ∀ {s : X.B.I.Ginf}, s ∈ X.NinfU v → s ∈ X.SinfU v := fun hs p => (hs p).1
  have hsi : s⁻¹ ∈ X.NinfU v := ninf_inv X v hs
  rw [mul_assoc, (X.Wu_spec v).1 s⁻¹ (hNS hsi) (h * x), (X.piU_rep v).2.2.2.1 s⁻¹ hsi,
    ContinuousLinearMap.one_apply, (X.Wu_spec v).1 h hh x, Formalism.L2.SG.RealObj.InfCut.piIso_apply, smul_smul]
  rfl

end GlobalTheory.CosetOrbital

namespace GlobalTheory.CosetOrbital

open Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FormTranspose Set

variable {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)

theorem pinned_form (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq)
    (t : TauC Y u u') (hrel : t.relevant) (w : Point D.host.E (D.R.rS + 1))
    (hreal : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ)
    (g : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (g' : X.B.I.Ginf) (hg' : g' ∈ X.SinfU u')
    (hdec : t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' w * g'⁻¹) :
    ∃ μR : Measure X.B.I.Ginf, Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧
      (MeasurableSet (FundOf t) ∧ ∀ y ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ FundOf t) ∧
      OOt t = (μR (FundOf t)).toReal •
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         OO ((νq (Formalism.L2.SG.RealObj.gamW X u u' w)).map (fun x => g * x)) Set.univ (X.Wu u) (X.Wu u') t.pt.1) := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  set γw := Formalism.L2.SG.RealObj.gamW X u u' w with hγw
  have hγwP : Formalism.L2.SG.RealObj.IsPtRep X u u' w γw := by
    simp only [hγw, Formalism.L2.SG.RealObj.gamW, dif_pos hreal]; exact hreal.choose_spec
  obtain ⟨μw, hμwH, hμwQ, hμwS⟩ := hP.2 w hreal
  set cj : X.B.I.Ginf → X.B.I.Ginf := fun y => g * y * g⁻¹ with hcj
  have hcjm : Measurable cj := (measurable_const_mul g).mul_const g⁻¹
  set μR := μw.map cj with hμR
  set ν := (νq γw).map (fun x => g * x) with hν
  have hRset : ∀ z, cj z ∈ Rset t ↔ z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := by
    intro z
    have e2 : t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 = g' * (γw⁻¹ * z * γw) * g'⁻¹ := by
      rw [show t.pt.1 = g * γw * g'⁻¹ from hdec]; group
    show (g * z * g⁻¹ ∈ X.NinfU u ∧ t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 ∈ X.NinfU u') ↔
      (z ∈ X.NinfU u ∧ γw⁻¹ * z * γw ∈ X.NinfU u')
    rw [e2, sinf_conj_iff X u hg, sinf_conj_iff X u' hg']
  have hHaar : IsHaarOnSet X.B.I (Rset t) μR := by
    obtain ⟨h1, h2, h3, h4⟩ := hμwH
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : SigmaFinite μw := h1
      exact ((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)).sigmaFinite_map
    · intro h0
      apply h2
      have := congrArg (fun m : Measure X.B.I.Ginf => m univ) h0
      simp only [hμR, Measure.map_apply hcjm MeasurableSet.univ, preimage_univ, Measure.coe_zero,
        Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    · have hcje : ⇑((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)) = cj := rfl
      rw [hμR, ← hcje, MeasurableEquiv.map_apply]
      refine measure_mono_null (fun z hz => ?_) h3
      intro hzS; exact hz ((hRset z).2 hzS)
    · intro r hr
      set z := g⁻¹ * r * g with hz
      have hcz : cj z = r := by simp only [hcj, hz]; group
      have hzS : z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := (hRset z).1 (hcz ▸ hr)
      have hcomp : (fun y => r * y) ∘ cj = cj ∘ (fun y => z * y) := by
        funext y; simp only [Function.comp, hcj, hz]; group
      rw [hμR, Measure.map_map (measurable_const_mul r) hcjm, hcomp,
        ← Measure.map_map hcjm (measurable_const_mul z), h4 z hzS]
  have hmulm : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_mul
  have hQ' : IsQuotMeasS X.B.I μR ν := by
    intro f hf
    have hσ : SigmaFinite μw := hμwH.1
    have hσR : SigmaFinite μR := hHaar.1
    have hF : Measurable fun x => ∫⁻ s, f (s * x) ∂μR := (hf.comp hmulm).lintegral_prod_left'
    rw [hν, lintegral_map hF (measurable_const_mul g)]
    have e1 : ∀ x0, ∫⁻ s, f (s * (g * x0)) ∂μR = ∫⁻ z, (fun y => f (g * y)) (z * x0) ∂μw := by
      intro x0
      rw [hμR, lintegral_map (f := fun s => f (s * (g * x0))) (hf.comp (measurable_mul_const _)) hcjm]
      refine lintegral_congr fun z => ?_
      simp only [hcj]
      congr 1
      group
    simp only [e1]
    rw [← hμwQ (fun y => f (g * y)) (hf.comp (measurable_const_mul g))]
    exact (lintegral_mul_left_eq_self f g).symm
  have hFE : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u' t
  have hFO : IsSFund X.B.I (ROinf t) (FundOf t) := by
    unfold FundOf; rw [dif_pos hFE]; exact hFE.choose_spec
  set Γ0 := ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin with hΓ0
  have hKu : ∀ r ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * r ∈ FundOf t := by
    intro r _
    obtain ⟨s0, hs0, hs0F⟩ := hFO.2.1 r
    refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
    have h2 : (s0 * s'⁻¹) * (s' * r) ∈ FundOf t := by simpa [mul_assoc] using hs0F
    have := hFO.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
    exact (mul_inv_eq_one.1 this).symm
  have hFA := Formalism.L2.SG.Pf.formAllC_holds D X Y u u' t μR ν (FundOf t)
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u' t hrel) hHaar hQ' hFO.1 hKu
  exact ⟨μR, ⟨γw, g, g', μw, hγwP, hg, hg', hdec, hμwH, hμwS, rfl⟩, ⟨hFO.1, hKu⟩, hFA⟩

end GlobalTheory.CosetOrbital

namespace GlobalTheory.CosetOrbital

open Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FormTranspose

theorem conj_inv_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) : conj (z⁻¹) = z := by
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have h1 : conj z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_right h1

theorem coset_orbital_form : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ t₀ : TauC Y u u', t₀.relevant → t₀.G ≠ 0 → ∀ w, w = Formalism.L2.SG.PairVal.ptOf t₀.toTerm → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧ ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u); OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w))‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (xn xm : X.B.I.GA), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → RatLink X xn n → RatLink X xm m → ∃ (μR : Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧ (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ K) ∧ OOt t = (((μR K).toReal : ℂ) * ((X.psiInfU u xn.1)⁻¹ * X.psiInfU u' xm.1)) • T := by
  intro D X Y u u' hSt ν hν t₀ hrel₀ hG₀ w hw
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  have hRD := Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of X Y u u'
    (Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := Formalism.L2.SG.Pf.RowForm.realDecompC_gamW X Y u u' hRD t₀ hrel₀ hG₀
  subst hw
  set O := OO (ν (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm))) Set.univ (X.Wu u) (X.Wu u')
    (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm)) with hO
  set A := Formalism.L2.SG.RealObj.InfCut.piIso X u g hg with hA
  set B := Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg' with hB
  set c0 := X.psiInfU u g * conj (X.psiInfU u' g') with hc0
  have hc0n : ‖c0‖ = 1 := by
    rw [hc0, norm_mul, Complex.norm_conj, psiInfU_norm, psiInfU_norm, one_mul]
  refine ⟨hpt, c0 • ((A.toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u).comp
    (O.comp (B.symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'))), norm_hsEmb_unitary c0 hc0n A B O, ?_⟩
  rintro t n m xn xm ⟨hn, hm, hlin⟩ hxn hxm
  obtain ⟨hrel, -, hptt, -⟩ := GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset D X Y u u' hSt t₀ t n m hrel₀ hG₀ ⟨hn, hm, hlin⟩
  have hL := GlobalTheory.RatIsomPoint.ratLink_points D X
  have hxnN : xn.1 ∈ X.NinfU u := ((hL.2.2 u xn n hxn).1).1 hn
  have hxmN : xm.1 ∈ X.NinfU u' := ((hL.2.2 u' xm m hxm).1).1 hm
  have hlink : RatLink X (xn⁻¹ * t₀.pt * xm) t.lin := by
    rw [hlin]
    have h1 := (hL.2.1 _ _ _ _ hxn t₀.rep.2.1).2.1
    exact (hL.2.1 _ _ _ _ (hL.2.1 _ _ _ _ h1 t₀.rep.2.1).1 hxm).1
  have hpt_eq : t.pt = xn⁻¹ * t₀.pt * xm := (hL.1 t.lin t.rep.2.2.1).unique t.rep.2.1 hlink
  have hpt1 : t.pt.1 = xn.1⁻¹ * t₀.pt.1 * xm.1 := by rw [hpt_eq]; rfl
  have hNS : ∀ (v : D.what₂.Word) {s : X.B.I.Ginf}, s ∈ X.NinfU v → s ∈ X.SinfU v := fun v s hs => fun p => (hs p).1
  have hgt : xn.1⁻¹ * g ∈ X.SinfU u :=
    (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)).mul_mem (hNS u (ninf_inv X u hxnN)) hg
  have hgt' : xm.1⁻¹ * g' ∈ X.SinfU u' :=
    (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u')).mul_mem (hNS u' (ninf_inv X u' hxmN)) hg'
  have hdect : t.pt.1 = (xn.1⁻¹ * g) * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm) *
      (xm.1⁻¹ * g')⁻¹ := by
    rw [hpt1, hdec]; group
  obtain ⟨μR, hPin, hK, hFA⟩ := pinned_form X Y u u' ν hν t hrel _ hpt _ hgt _ hgt' hdect
  refine ⟨μR, FundOf t, hPin, hK, ?_⟩

  have hmove := Formalism.L2.SG.Pf.RowForm.ClassFrameNormal.oo_map_mulLeft
    (ν (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm))) (X.Wu u) (X.Wu u')
    (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm)) (xn.1⁻¹ * g) (xm.1⁻¹ * g')
    (X.psiInfU u xn.1⁻¹ * X.psiInfU u g) (X.psiInfU u' xm.1⁻¹ * X.psiInfU u' g') A B
    (wu_move X u xn.1 hxnN g hg) (wu_move X u' xm.1 hxmN g' hg')
  rw [hFA, hdect, hmove]
  rw [psi_inv X u hxnN, psi_inv X u' hxmN, map_mul, conj_inv_of_norm_one _ (psiInfU_norm X u' xm.1),
    ← Complex.coe_smul, smul_smul, smul_smul, hc0]
  congr 1
  ring

end GlobalTheory.CosetOrbital
end
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_integrals_terms_one_doubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ t₀ : TauC Y u u', t₀.relevant → t₀.G ≠ 0 → ∀ w, w = Formalism.L2.SG.PairVal.ptOf t₀.toTerm → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧ ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u); OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w))‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (xn xm : X.B.I.GA), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → RatLink X xn n → RatLink X xm m → ∃ (μR : Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧ (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ K) ∧ OOt t = (((μR K).toReal : ℂ) * ((X.psiInfU u xn.1)⁻¹ * X.psiInfU u' xm.1)) • T := by
  atlas_forward_decl GlobalTheory.CosetOrbital.coset_orbital_form
end

section
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdmWitChar

open Formalism.L2.SG.Pf.unitaryCongruence Matrix
open scoped TensorProduct

private theorem coprime_absNorm_of_isCoprime_span {K : Type} [Field K] [NumberField K] (J : Ideal (𝓞 K)) (g : ℕ)
    (hJ : J ⊔ Ideal.span {((g : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm J) g := by
  have h1mem : (1 : 𝓞 K) ∈ J ⊔ Ideal.span {((g : ℕ) : 𝓞 K)} := by rw [hJ]; exact Submodule.mem_top
  obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 h1mem
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  apply Nat.coprime_of_dvd
  intro p hp hpc hpg
  obtain ⟨k, rfl⟩ := hpg
  by_cases hJb : J = ⊥
  · have hj0 : j = 0 := (Submodule.mem_bot _).1 (hJb ▸ hj)
    have h1 : ((p * k : ℕ) : 𝓞 K) * r = 1 := by rw [← hjy, hj0, zero_add, mul_comm]
    have h2 := congrArg (Algebra.norm ℤ) h1
    rw [map_mul, map_one, ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap] at h2
    have hd : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
    have h3 : ((p : ℤ)) ∣ 1 := by
      rw [← h2]
      apply Dvd.dvd.mul_right
      apply Dvd.dvd.pow _ hd.ne'
      push_cast
      exact dvd_mul_right _ _
    have h4 := Int.eq_one_of_dvd_one (by positivity) h3
    norm_cast at h4
    exact hp.one_lt.ne' h4
  · haveI : Finite (𝓞 K ⧸ J) := J.finiteQuotientOfFreeOfNeBot hJb
    haveI : Fintype (𝓞 K ⧸ J) := Fintype.ofFinite _
    haveI := Fact.mk hp
    have hcard : p ∣ Fintype.card (𝓞 K ⧸ J) := by
      rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
      exact hpc
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hcard
    have hpx : ((p : ℕ) : 𝓞 K ⧸ J) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hunit : ((p : ℕ) : 𝓞 K ⧸ J) * Ideal.Quotient.mk J ((k : 𝓞 K) * r) = 1 := by
      rw [← map_natCast (Ideal.Quotient.mk J), ← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
      have : ((p : ℕ) : 𝓞 K) * ((k : 𝓞 K) * r) - 1 = -j := by
        rw [← hjy]; push_cast; ring
      rw [this]
      exact J.neg_mem hj
    have hx0 : x = 0 := by
      calc x = (((p : ℕ) : 𝓞 K ⧸ J) * Ideal.Quotient.mk J ((k : 𝓞 K) * r)) * x := by rw [hunit, one_mul]
        _ = Ideal.Quotient.mk J ((k : 𝓞 K) * r) * (((p : ℕ) : 𝓞 K ⧸ J) * x) := by ring
        _ = 0 := by rw [hpx, mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx

private theorem hidaSetting_modGAt {D : D7} (X : HidaSetting D) : Formalism.L2.SG.NormCut.ModGAt X := by
  intro g1 Λ hΛ v hv
  have hgg : X.B.g = gS D := X.g_eq
  have hg0 : ((gS D : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    have : (gS D) ≠ 0 := hgg ▸ Formalism.L2.SG.Pf.modulus_g_ne_zero X
    exact_mod_cast this
  let J : Ideal (𝓞 D.host.E) :=
    Submodule.comap (LinearMap.toSpanSingleton (𝓞 D.host.E) (VS D).V v) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ)
  have hJ : J ⊔ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hgM : ((gS D : ℕ) : 𝓞 D.host.E) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hMb : M ≠ ⊥ := fun h => hg0 (by rw [h] at hgM; exact (Submodule.mem_bot _).1 hgM)
    obtain ⟨s, hs, hsv⟩ := hv ⟨M, hM.isPrime, hMb⟩ hgM
    exact hs (hle (Ideal.mem_sup_left (show s ∈ J from hsv)))
  have hcop : Nat.Coprime (Ideal.absNorm J) (gS D) := coprime_absNorm_of_isCoprime_span J (gS D) hJ
  have hcJ : ((Ideal.absNorm J : ℕ) : 𝓞 D.host.E) ∈ J := Ideal.absNorm_mem J
  have hcv : ((Ideal.absNorm J : ℕ) : 𝓞 D.host.E) • v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := hcJ
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hcv
  obtain ⟨w, hw, hwv⟩ := hcv
  have hlin : ∀ (n : ℕ) (y : (VS D).V), X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (((n : 𝓞 D.host.E)) • y)) =
      (n : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y)) := by
    intro n y
    have h1 : ((n : 𝓞 D.host.E)) • y = ((n : D.host.E)) • y := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [h1, Formalism.L2.SG.NormCut.crd_smul' X, map_natCast, Formalism.L2.SG.NormCut.incl_smul' X, map_natCast,
      Matrix.mulVec_smul]
  refine ⟨Ideal.absNorm J, hgg ▸ hcop, ?_⟩
  rw [← hlin, ← hwv, hlin]
  exact Submodule.subset_span ⟨_, (hΛ w).1 hw, by rw [hgg]⟩

private theorem psiEf_divN_eq {D : D7} (X : HidaSetting D) (y : X.B.I.E) :
    X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y)) =
      (Formalism.L2.SG.PairVal.psiInf (gS D) (X.ιE y))⁻¹ := by
  have hg : X.B.g = gS D := X.g_eq
  have hdiv : Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y) := by
    unfold Formalism.L2.SG.HidaSetting.divN
    simp [Formalism.UG.inclE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hdiv]
  have h1 := X.psiEf_rat (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y)
  have h2 := Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g y
  have h3 : Formalism.L2.SG.HidaSetting.psiEinf X.B.I (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y) =
      Formalism.L2.SG.PairVal.psiInf X.B.g (X.ιE y) := by
    rw [← h2]
    unfold Formalism.L2.SG.HidaSetting.psiEinf
    refine Finset.prod_congr rfl (fun v _ => ?_)
    congr 1
    have hφ : X.B.I.φ v (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹)) = ((X.B.g : ℂ))⁻¹ := by
      rw [map_inv₀, map_natCast, map_inv₀, map_natCast]
    rw [map_mul, hφ]
    simp [star_mul', div_eq_mul_inv]
    ring
  rw [h3] at h1
  rw [← hg]
  exact eq_inv_of_mul_eq_one_left h1

private theorem chiN_eq_of_fmat_mulVec_snoc {D : D7} (X : HidaSetting D) (κ : X.B.I.Gf)
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (key : ∀ c, X.B.I.fmat κ *ᵥ Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c -
        ∑ a, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a c : 𝓞 D.host.E) : D.host.E)) •
          Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a ∈ mL X.B.I X.B.g) :
    chiN X κ = X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (X.ιE.symm (∑ a : Fin D.R.rS, ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E))))) := by
  have hg : X.B.g ≠ 0 := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  obtain ⟨hfe, hfz, -, -⟩ := Formalism.L2.SG.Pf.reference_frame_congruences X
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hint : ∀ x : 𝓞 D.host.E,
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (x : D.host.E)) ∈ IntAf X.B.I.F X.B.I.E :=
    fun x => Formalism.L2.SG.NormCut.inclE_int X x
  have hZ : ZMod' X.B.I X.B.g ((∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a)) -
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
        (X.ιE.symm (∑ a : Fin D.R.rS, ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E))) - 0) := by
    rw [sub_zero, map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Z_sum X.B.I X.B.g _ _ (fun a _ => ?_)
    have hnxt : nxt X.e0 X.z0 a = Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a.succ := by
      unfold nxt
      split_ifs with h
      · have hs : (a.succ : Fin (D.R.rS + 1)) = Fin.castSucc ⟨a.1 + 1, h⟩ :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc])
        rw [hs, Fin.snoc_castSucc]
      · have hs : (a.succ : Fin (D.R.rS + 1)) = Fin.last _ :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
        rw [hs, Fin.snoc_last]
    rw [hnxt]
    have hw : ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a.succ -
        ∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) •
          Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c)) :=
      mL_Qs X.B.I X.B.g (hf0 a) (key a.succ)
    rw [hA_sub_right] at hw
    have hsum : hA X.B.I (X.f0 a) (∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) •
          Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) =
        ∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
          hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) := by
      rw [← hL_apply, map_sum]
      simp [hL_apply]
    rw [hsum] at hw
    have hrest : ZMod' X.B.I X.B.g ((∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
          hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c)) -
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E))) := by
      have he : (∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
          hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c)) -
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E)) =
          ∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
            (hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) - if c = a.castSucc then 1 else 0) := by
        simp [mul_sub, Finset.sum_sub_distrib]
      rw [he]
      refine Z_sum X.B.I X.B.g _ _ (fun c _ => Z_smul X.B.I X.B.g (hint _) ?_)
      refine Fin.lastCases ?_ (fun b => ?_) c
      · have hne : (Fin.last D.R.rS) ≠ a.castSucc := (Fin.castSucc_lt_last a).ne'
        simpa [hne] using hfz a
      · by_cases hb : b = a
        · subst hb
          have h1 := (X.gramIntegral b b).2.2
          simp only at h1
          have h2 := Z_sig X.B.I X.B.g h1
          simpa [hA_symm X.B.I (X.e0 b) (X.f0 b), map_sub, map_one] using h2
        · have hne : b.castSucc ≠ a.castSucc := fun h => hb (Fin.castSucc_injective _ h)
          simpa [hne] using hfe a b (Ne.symm hb)
    have := Z_add X.B.I X.B.g hw hrest
    convert this using 1
    ring
  have hmul := psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg hZ
  unfold chiN
  rw [hmul, psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg (Z_zero X.B.I X.B.g), mul_one]

theorem chiN_kOf_eq_inv_psiInf_sgUp : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (t : TauC Y u u') (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)), AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ → chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  intro D X Y u u' hS t ξ hξ
  have hK := Formalism.L2.SG.NormCut.termK_car (Y.cs u) (Y.cs u') t.mem t.mem' t.rep
  have hRL : Formalism.L2.SG.TermOp.RatLink X t.pt t.lin := t.rep.2.1
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hM : Formalism.L2.SG.NormCut.ModGAt X := hidaSetting_modGAt X
  have hξm : ∀ c, ModG (VS D) t.lam (gS D) (t.lin (frame (lf D (X.Fu u')) c) - frameAct (frame (lf D (X.Fu u))) ξ c) := by
    intro c
    have h3 := hξ.2.2 c
    have h4 := Formalism.L2.SG.NormCut.frame_mapLF hiso (lf D (X.Fu u')) c
    unfold GTerm.frame at h3
    exact h4 ▸ h3
  have key := Formalism.L2.SG.NormCut.key_gen (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') hM t.mem t.pt t.lin hRL ξ hξm hK
  rw [chiN_eq_of_fmat_mulVec_snoc X _ ξ key, psiEf_divN_eq, RingEquiv.apply_symm_apply]
  congr 2
  rw [GlobalTheory.RatIsomPoint.sgUp_eq]
  simp [Matrix.map_apply]

end GlobalTheory.AdmWitChar
end
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_unipotentPart_of_admissibilityWitness : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (t : TauC Y u u') (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)), AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ → chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  atlas_forward_decl GlobalTheory.AdmWitChar.chiN_kOf_eq_inv_psiInf_sgUp
end

section
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpTerm

theorem gval_of_movesTo {D : D7} {T T' : D.host.E} {F00 F : LFlag (VS D) D.R.rS T}
    {F'0 F' : LFlag (VS D) D.R.rS T'} {ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (h : MovesTo F00 F'0 F F' ρ U U') : Gval F F' = Gval F00 F'0 := by
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := h
  have hZ : ZhatL F F' = U.conjTranspose * ZhatL F00 F'0 * U' := by
    ext a b
    have e1 : ZhatL F F' a b = (VS D).hT (ρ (frame F a)) (ρ (frame F' b)) := by
      rw [hρ]; rfl
    have hz : ∀ c d, ZhatL F00 F'0 c d = (VS D).hT (frame F00 c) (frame F'0 d) := fun _ _ => rfl
    rw [e1, hF a, hF' b]
    simp only [Matrix.mul_apply, hz, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Matrix.conjTranspose_apply, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
    simp only [RingHom.id_apply]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))
    ring
  have hD : ∀ l, Dl F.fl F'.fl l = Dl F00.fl F'0.fl l := by
    intro l
    have := Formalism.L2.SG.Pf.leadMinor_uni U.conjTranspose (ZhatL F00 F'0) U'
      (fun a c hac => by simp [Matrix.conjTranspose_apply, (hU c a).1 hac])
      (fun a => by simp [Matrix.conjTranspose_apply, (hU a a).2 rfl])
      (fun d b hbd => (hU' d b).1 hbd) (fun b => (hU' b b).2 rfl) l
    rw [← hZ] at this
    exact this
  simp only [Gval, Gflag, hD]

theorem G_eq_gval {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (t : TauC Y u u') :
    t.G = Gval (lf D (X.Fu u)) t.frame :=
  Formalism.L2.SG.TermDef.Gt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _) ⟨t.frame, t.rep.2.2.2.2⟩

theorem lam_eq_of_row {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} {t t₀ : TauC Y u u'}
    (h : (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀) : t.lam = t₀.lam ∧ t.lam' = t₀.lam' :=
  ⟨congrArg (fun r => r.1.1) h, congrArg (fun r => r.2.1.1) h⟩

theorem exists_admissibleWitness_rowTerm {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (t : TauC Y u u') :
    ∃ ξ, AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ :=
  t.rep.2.2.2.2.2.1

end GlobalTheory.AmpTerm

namespace GlobalTheory.AmpTerm

open Formalism.L2.SG.PairVal in

theorem amp_eq_mass_phase : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → Formalism.L2.SG.PairVal.ptOf t₀.toTerm = w → ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w)‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = ((((((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat (ρ * n) t.lam) : ℝ) : ℂ) * G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat (ρ * n) t.lam)) • T := by
  intro D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c ν hν t₀ ρ U U' hmv hrel hpt
  have hG0 : t₀.G ≠ 0 := by
    rw [G_eq_gval]; exact fun h => hG ((gval_of_movesTo hmv).symm.trans h)
  obtain ⟨-, T0, hT0, hform⟩ := GlobalTheory.T.orbital_integrals_terms_one_doubleCoset D X Y u u' hS ν hν t₀ hrel hG0 w hpt.symm
  have hpU : psiInf (gS D) (sgUp U) ≠ 0 := by
    intro h; have := norm_psiInf (gS D) (sgUp U); rw [h, norm_zero] at this; exact zero_ne_one this
  have hpU' : psiInf (gS D) (sgUp U') ≠ 0 := by
    intro h; have := norm_psiInf (gS D) (sgUp U'); rw [h, norm_zero] at this; exact zero_ne_one this
  refine ⟨(((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
      psiInf (gS D) (sgUp U) * (psiInf (gS D) (sgUp U'))⁻¹) • T0, ?_, ?_⟩
  · rw [map_smul, norm_smul, hT0]
    unfold Jw
    rw [map_smul, norm_smul, norm_mul, norm_mul, norm_inv, norm_psiInf, norm_psiInf]
    simp
  · rintro t n m hrow ⟨hn, hm, hlin⟩
    obtain ⟨hlam, hlam'⟩ := lam_eq_of_row hrow
    have hL := GlobalTheory.RatIsomPoint.ratLink_points D X
    obtain ⟨xn, hxn, -⟩ := hL.1 n hn.1
    obtain ⟨xm, hxm, -⟩ := hL.1 m hm.1
    obtain ⟨μR, K, hpin, hK, hOO⟩ := hform t n m xn xm ⟨hn, hm, hlin⟩ hxn hxm
    obtain ⟨-, -, -, -, -, hgrp⟩ :=
      GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
    obtain ⟨A, A', hA, hA', hnA, hmA', hmv'⟩ := hgrp t n m ⟨hn, hm, hlin⟩
    have hcos := GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset D X Y u u' hS t₀ t n m hrel hG0 ⟨hn, hm, hlin⟩
    have hvol := GlobalTheory.T.automorphismCovolume_eq_latticeMass D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t (ρ * n) (U * A) (U' * A')
      hmv' hcos.1 μR hpin K hK
    obtain ⟨ξ, hξ⟩ := exists_admissibleWitness_rowTerm t
    have hchi := GlobalTheory.T.levelCharacter_unipotentPart_of_admissibilityWitness D X Y u u' hS t ξ hξ
    have hterm := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t (ρ * n) (U * A) (U' * A')
      hmv').2 ξ hξ
    have hdat := (GlobalTheory.T.termRow_eq_iff_movedLatticeInnerData_eq D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv t n m hlam hlam'
      ⟨hn, hm, hlin⟩).1 hrow
    rw [hdat] at hterm
    have hpn := (hL.2.2 u xn n hxn).2 hn A hnA
    have hpm := (hL.2.2 u' xm m hxm).2 hm A' hmA'
    have hU := hmv.2.1
    have hU' := hmv.2.2.1
    unfold ampN
    rw [hchi, hOO, hpn, hpm, hvol, hterm, Formalism.L2.SG.Pf.sgUp_mul hU hA, Formalism.L2.SG.Pf.sgUp_mul hU' hA',
      Formalism.L2.SG.Pf.psiInf_add, Formalism.L2.SG.Pf.psiInf_add, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp

end GlobalTheory.AmpTerm
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTerm_amplitude_eq_mass_mul_phase : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → Formalism.L2.SG.PairVal.ptOf t₀.toTerm = w → ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w)‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = ((((((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat (ρ * n) t.lam) : ℝ) : ℂ) * G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat (ρ * n) t.lam)) • T := by
  atlas_forward_decl GlobalTheory.AmpTerm.amp_eq_mass_phase
end
