import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefTraceCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCSecMove
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLine
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopAct
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NotCdomRaiseOfLt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnReal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGauge
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntMulOfCpt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolCut
import Formalism.HermitianCurvature.StatementNF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolPhaseRel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnAnn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTSS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddDone

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_gauge_move : GTRMove := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk μ0 h0 e0 he0
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
  have hTT : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    intro ζ hζ
    rw [hT, hT']
    exact hζ
  set c1 : Fin P.r → ℂ := fun _ => 1 with hc1def
  have hc1 : c1 ∈ OmX P.r := fun _ => one_ne_zero

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' :=
    ⟨Bs.k_pos, hz, hz', Bs.T_pos, Bs.T'_pos, h0, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩

  have hφ : ∀ ρ : M.Ty P, (NF.QR P.k P.r Bs.z Bs.z').indicator (fun q => e0 ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := by
    intro ρ
    refine ⟨?_, ?_, ?_⟩
    · have hc : ContDiffOn ℝ ∞ (fun q : (Fin P.r → ℂ) × ℂ => e0 ρ q.2) (NF.QR P.k P.r Bs.z Bs.z') := by
        refine (he0.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_
        show P.TT < Complex.normSq q.2
        have := hq.2
        rw [hT, hT'] at this
        exact this
      exact hc.congr fun q hq => Set.indicator_of_mem hq _
    · intro q hq
      rw [Set.indicator_of_mem hq]
      have hq2 : P.TT < Complex.normSq q.2 := by
        have := hq.2
        rw [hT, hT'] at this
        exact this
      exact (he0.2 q.2 hq2).1 ρ
    · intro q hq
      exact Set.indicator_of_notMem hq _
  choose Φr hΦr hrad using fun ρ => Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' hRB _ (hφ ρ)
  obtain ⟨e, he_def⟩ : ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp),
      e = fun ρ ζ => (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) := ⟨_, rfl⟩

  have hdom : ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      (c1, NF.muZ P.k P.r Bs.μsec ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩
  have hdom0 : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → (c1, NF.muZ P.k P.r μ0 ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' h0 (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩
  have hdec : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∃ h ∈ UWset P.k P.r Bs.z, ∃ h' ∈ UWset P.k P.r Bs.z',
      NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' := by
    intro ζ hζ
    obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos h0
      (hdom ζ hζ).2.1 (hdom ζ hζ).2.2
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec (hTT ζ hζ)] at he
    exact ⟨h, hh, h', hh', he⟩

  have hrad0 : ∀ ρ ζ, P.TT < Complex.normSq ζ → (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r μ0 ζ) = e0 ρ ζ := by
    intro ρ ζ hζ
    have hq : (c1, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc1, hTT ζ hζ⟩
    have h1 := congrFun (hrad ρ) (c1, ζ)
    unfold NF.radR at h1
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq] at h1
    exact h1

  have htr : ∀ ρ ζ, P.TT < Complex.normSq ζ → ∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z',
      NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' →
      e ρ ζ = (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h')) := by
    intro ρ ζ hζ h hh h' hh' hd
    rw [he_def]
    show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) = _
    rw [hd, ← hrad0 ρ ζ hζ]
    exact (hΦr ρ).2.2 (c1, NF.muZ P.k P.r μ0 ζ) (hdom0 ζ hζ) h hh h' hh'

  have hsmooth : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ} := by
    intro ρ
    rw [he_def]
    have hmZ : ContDiffOn ℝ ∞ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) {ζ : ℂ | P.TT < Complex.normSq ζ} :=
      contDiffOn_const.prodMk ((Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).mono fun ζ hζ => hTT ζ hζ)
    have hopen : IsOpen {ζ : ℂ | P.TT < Complex.normSq ζ} :=
      isOpen_lt continuous_const Complex.continuous_normSq
    refine contDiffOn_of_locally_contDiffOn fun ζ₀ hζ₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := (hΦr ρ).2.1 _ (hdom ζ₀ hζ₀)
    refine ⟨{ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U,
      hmZ.continuousOn.isOpen_inter_preimage hopen hU, ⟨hζ₀, hx₀U⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun ζ : ℂ => F (c1, NF.muZ P.k P.r Bs.μsec ζ))
        ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩
          ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U)) :=
      hF.comp (hmZ.mono fun ζ hζ => hζ.1) fun ζ hζ => hζ.2.2
    exact hc.congr fun ζ hζ => hΦF _ hζ.2.2 (hdom ζ hζ.1).2.1

  have hrep := Bs.π_rep
  have hrep' := Bs.π'_rep
  have pmi : ∀ h ∈ UWset P.k P.r Bs.z, (Bs.π h).comp (Bs.π h⁻¹) = 1 := by
    intro h hh
    rw [← hrep.2 h hh h⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh), Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, hrep.1]
  have pim' : ∀ h' ∈ UWset P.k P.r Bs.z', (Bs.π' h'⁻¹).comp (Bs.π' h') = 1 := by
    intro h' hh'
    rw [← hrep'.2 h'⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh') h' hh', Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh', hrep'.1]

  have hframe : IsFrameB P Bs e := by
    refine ⟨hsmooth, fun ζ hζ => ⟨?_, ?_, ?_⟩⟩
    · intro ρ p hp
      rw [he_def]
      show (Bs.π p.1).comp (((Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' p.2)) =
        (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)
      rw [← (hΦr ρ).2.2 (c1, NF.muZ P.k P.r Bs.μsec ζ) (hdom ζ hζ) p.1 hp.1 p.2 hp.2.1]
      show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (p.1 * NF.muZ P.k P.r Bs.μsec ζ * p.2) = _
      rw [hp.2.2]
    · intro ρ ρ'
      obtain ⟨h, hh, h', hh', hd⟩ := hdec ζ hζ
      rw [htr ρ ζ hζ h hh h' hh' hd, htr ρ' ζ hζ h hh h' hh' hd, sm_inner_conj Bs hh hh']
      exact (he0.2 ζ hζ).2.1 ρ ρ'
    · intro X hX
      obtain ⟨h, hh, h', hh', hd⟩ := hdec ζ hζ
      have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
      have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
      set X0 := (Bs.π h⁻¹).comp (X.comp (Bs.π' h'⁻¹)) with hX0def
      have e1 : ∀ Y : B.Mat P.k P.r, h⁻¹ * (h * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul]
      have e2 : ∀ Y : B.Mat P.k P.r, h' * (h'⁻¹ * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.one_mul]
      have hX0 : X0 ∈ NF.Fib P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' ζ := by
        intro p hp
        have hp1 := hp.1
        have hp2 := hp.2.1
        have hp3 := hp.2.2
        have ht1 : h * p.1 * h⁻¹ ∈ UWset P.k P.r Bs.z :=
          Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hh hp1) hhi
        have ht2 : h'⁻¹ * p.2 * h' ∈ UWset P.k P.r Bs.z' :=
          Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hhi' hp2) hh'
        have e3 : ∀ Y : B.Mat P.k P.r, p.1 * (NF.muZ P.k P.r μ0 ζ * (p.2 * Y)) = NF.muZ P.k P.r μ0 ζ * Y := by
          intro Y
          conv_rhs => rw [← hp3]
          simp only [Matrix.mul_assoc]
        have ht : (h * p.1 * h⁻¹, h'⁻¹ * p.2 * h') ∈ NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ := by
          refine ⟨ht1, ht2, ?_⟩
          show h * p.1 * h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * (h'⁻¹ * p.2 * h') = NF.muZ P.k P.r Bs.μsec ζ
          rw [hd]
          simp only [Matrix.mul_assoc, e1, e2, e3]
        have hXt := hX _ ht
        have hA : (Bs.π p.1).comp (Bs.π h⁻¹) = (Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹)) := by
          rw [← hrep.2 _ hp1 _ hhi, ← hrep.2 _ hhi _ ht1]
          congr 1
          simp only [Matrix.mul_assoc, e1]
        have hB : (Bs.π' h'⁻¹).comp (Bs.π' p.2) = (Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹) := by
          rw [← hrep'.2 _ hhi' _ hp2, ← hrep'.2 _ ht2 _ hhi']
          congr 1
          simp only [Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
        calc (Bs.π p.1).comp (X0.comp (Bs.π' p.2))
            = ((Bs.π p.1).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' p.2))) := by
              simp only [hX0def, ContinuousLinearMap.comp_assoc]
          _ = ((Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹))).comp
                (X.comp ((Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹))) := by rw [hA, hB]
          _ = (Bs.π h⁻¹).comp (((Bs.π (h * p.1 * h⁻¹)).comp (X.comp (Bs.π' (h'⁻¹ * p.2 * h')))).comp
                (Bs.π' h'⁻¹)) := by simp only [ContinuousLinearMap.comp_assoc]
          _ = X0 := by rw [hXt]
      have hXX : X = (Bs.π h).comp (X0.comp (Bs.π' h')) := by
        have : (Bs.π h).comp (X0.comp (Bs.π' h')) =
            ((Bs.π h).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' h'))) := by
          simp only [hX0def, ContinuousLinearMap.comp_assoc]
        rw [this, pmi h hh, pim' h' hh']
        ext v
        rfl
      have hc : ∀ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) = inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) := by
        intro ρ
        rw [htr ρ ζ hζ h hh h' hh' hd]
        conv_lhs => rw [hXX]
        exact sm_inner_conj Bs hh hh' _ _
      have hsp0 := (he0.2 ζ hζ).2.2 X0 hX0
      have hrhs : ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ =
          ∑ ρ, inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) • (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h')) :=
        Finset.sum_congr rfl fun ρ _ => by rw [hc ρ, htr ρ ζ hζ h hh h' hh' hd]
      rw [hrhs]
      conv_lhs => rw [hXX, hsp0]
      ext v
      simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, map_sum, map_smul]
  refine ⟨e, hframe, fun Φ => ?_⟩
  funext ρ
  unfold trR
  congr 1
  funext q
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  obtain ⟨h, hh, h', hh', hd⟩ := hdec q.1.2 hζ
  unfold rawR
  congr 1
  rw [htr ρ q.1.2 hζ h hh h' hh' hd, hd]
  have hq : (q.1.1, NF.muZ P.k P.r μ0 q.1.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' h0 (q := (q.1.1, q.1.2)) ⟨q.2.1, hTT q.1.2 hζ⟩
  rw [Φ.2.2.2 _ hq h hh h' hh']
  exact sm_inner_conj Bs hh hh' _ _

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

private theorem hsVec_finset_sum_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} [Fintype ι]
    (c : ι → ℂ) (A : ι → Wq →L[ℂ] Wp) : B.hsVec (∑ i, c i • A i) = ∑ i, c i • B.hsVec (A i) := by
  ext j
  simp [B.hsVec]

private theorem hsVec_injective_apply {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A C : Wq →L[ℂ] Wp)
    (h : B.hsVec A = B.hsVec C) : A = C := by
  have h' : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = C (stdOrthonormalBasis ℂ Wq i) := fun i => by
    have := congrArg (fun v => v i) h
    simpa [B.hsVec] using this
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using h' i)

private theorem toSm_smul_hermitian_curvature (P : M.Par) (c : ℂ) (u : MA.Qp P.r P.TT → ℂ) :
    MA.toSm P (c • u) = c • MA.toSm P u := by
  unfold MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · rw [dif_pos hu, dif_pos (Subalgebra.smul_mem _ hu c)]
    rfl
  · rw [dif_neg hu]
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, smul_zero, dif_pos (Subalgebra.zero_mem _)]
      rfl
    · rw [smul_zero, dif_neg]
      intro hm
      apply hu
      have := Subalgebra.smul_mem _ hm c⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem radial_constant_of_point_and_line (hPt : GTKPt) (hLine : GTKLine) : GTRConst := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d h
  obtain ⟨Qr, hQ⟩ := hPt Wp Wq P Bs X d h
  obtain ⟨e1, he1F, -⟩ := gauge_kappa_of_point_line hPt hLine Wp Wq P Bs X d h
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [h.1.2.2.2.1, h.1.2.2.2.2.1]
    rfl
  set ζ0 : ℂ := ((|P.TT| + 1 : ℝ) : ℂ) with hζ0def
  have hζ0 : P.TT < Complex.normSq ζ0 := by
    rw [hζ0def, Complex.normSq_ofReal]
    nlinarith [le_abs_self P.TT, abs_nonneg P.TT]
  have hFib : ∀ ζ, P.TT < Complex.normSq ζ →
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro ζ hζ
    unfold NF.Fib
    rw [h.2.2.1.2 ζ ζ0 (hTT ▸ hζ) (hTT ▸ hζ0)]
  choose E hEmem hEQ hEnorm hEuniq using fun ρ => hLine Wp Wq P Bs X d h Qr hQ ζ0 hζ0 ρ
  have hEQ' : ∀ ρ σ, E ρ ∘SL Qr σ = if ρ = σ then E ρ else 0 := by
    intro ρ σ
    calc E ρ ∘SL Qr σ = (E ρ ∘SL Qr ρ) ∘SL Qr σ := by rw [hEQ ρ]
      _ = E ρ ∘SL (Qr ρ ∘SL Qr σ) := ContinuousLinearMap.comp_assoc _ _ _
      _ = _ := by
        rw [hQ.1 ρ σ]
        split_ifs <;> simp [hEQ ρ]
  have hinQ : ∀ ρ σ (C : Wq →L[ℂ] Wp), inner ℂ (B.hsVec (E ρ)) (B.hsVec (C ∘SL Qr σ)) =
      if ρ = σ then inner ℂ (B.hsVec (E ρ)) (B.hsVec C) else 0 := by
    intro ρ σ C
    rw [GTK.hs_comp_right _ _ _ (hQ.2.2.1 σ), hEQ' ρ σ]
    split_ifs
    · rfl
    · rw [GTK.hs_expand]
      simp
  have horth : ∀ ρ σ, inner ℂ (B.hsVec (E ρ)) (B.hsVec (E σ)) = if ρ = σ then 1 else 0 := by
    intro ρ σ
    have hh := hinQ ρ σ (E σ)
    rw [hEQ σ] at hh
    rw [hh]
    split_ifs with hρσ
    · subst hρσ
      exact hEnorm ρ
    · rfl
  have hv : Orthonormal ℂ (fun σ => B.hsVec (E σ)) := orthonormal_iff_ite.mpr horth
  have hw : Orthonormal ℂ (fun σ => B.hsVec (e1 σ ζ0)) := orthonormal_iff_ite.mpr (he1F.2 ζ0 hζ0).2.1
  have hspan1 : ∀ Y ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0,
      B.hsVec Y ∈ Submodule.span ℂ (Set.range (fun σ => B.hsVec (e1 σ ζ0))) := by
    intro Y hY
    rw [(he1F.2 ζ0 hζ0).2.2 Y hY, hsVec_finset_sum_smul]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hle : Submodule.span ℂ (Set.range (fun σ => B.hsVec (E σ))) ≤
      Submodule.span ℂ (Set.range (fun σ => B.hsVec (e1 σ ζ0))) := by
    rw [Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    exact hspan1 _ (hEmem σ)
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [finrank_span_eq_card hv.linearIndependent, finrank_span_eq_card hw.linearIndependent])
  have hexp : ∀ Y ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0,
      Y = ∑ σ, inner ℂ (B.hsVec (E σ)) (B.hsVec Y) • E σ := by
    intro Y hY
    have hm : B.hsVec Y ∈ Submodule.span ℂ (Set.range (fun σ => B.hsVec (E σ))) := heq ▸ hspan1 Y hY
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
    have hcoef : ∀ σ, inner ℂ (B.hsVec (E σ)) (B.hsVec Y) = c σ := by
      intro σ
      rw [← hc]
      exact hv.inner_right_fintype c σ
    apply hsVec_injective_apply
    rw [hsVec_finset_sum_smul]
    simp only [hcoef]
    exact hc.symm
  refine ⟨fun ρ _ => E ρ, ⟨fun ρ => contDiffOn_const, fun ζ hζ =>
    ⟨fun ρ => (hFib ζ hζ).symm ▸ hEmem ρ, horth, fun Y hY => hexp Y (hFib ζ hζ ▸ hY)⟩⟩, ?_, fun ρ ζ ζ' => rfl⟩
  intro f Φ
  funext ρ
  unfold trR MA.actA
  simp only [MA.kap, AlgHom.comp_apply, Matrix.diagonalAlgHom_apply, Matrix.diagonal_apply]
  have hR : rawR P Bs.μsec (fun ρ _ => E ρ) (↑((d.κ f).1 Φ)) ρ =
      f ρ • rawR P Bs.μsec (fun ρ _ => E ρ) (↑Φ) ρ := by
    funext q
    simp only [rawR, Pi.smul_apply, smul_eq_mul]
    rw [hQ.2.2.2 f Φ q, GTK.hs_comp_sum]
    simp only [hinQ, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  symm
  refine (Finset.sum_eq_single ρ ?_ ?_).trans ?_
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    rfl
  · intro hρ
    exact absurd (Finset.mem_univ ρ) hρ
  · rw [if_pos rfl, hR, toSm_smul_hermitian_curvature]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem radial_gauge_constant_holds : GTRConst := GTK.radial_constant_of_point_and_line gauge_kappa_pointwise_holds gauge_kappa_line_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.Qx8

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frameG_exists {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ g : Mx k r, g ∈ UH (Hpk k r) ∧
      (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
      g *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) = z := by
  set s : ℝ := Real.sqrt (Tz k r z) with hs
  have hss : (s : ℂ) * (s : ℂ) = ((Tz k r z : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hs, Real.mul_self_sqrt hT.le]
  set a : Fin (2 * r + k + 1) → ℂ := (s : ℂ) • bvec (wI k r (Fin.last k)) with ha
  have haW : inWb k r a := by
    intro i hi
    rw [ha, Pi.smul_apply, inWb_bvec_wI _ i hi, smul_zero]
  have haa : herm (Hpk k r) a a = ((-(Tz k r z) : ℝ) : ℂ) := by
    rw [ha, herm_smul_left', herm_smul_right', herm_wI, if_pos rfl, if_pos rfl]
    have : star (s : ℂ) = s := Complex.conj_ofReal s
    rw [this]
    push_cast
    linear_combination -hss
  have hzz : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := by
    rw [TwoByOneBlock.herm_self_eq]; push_cast; rfl
  obtain ⟨g, hgU, hga, hfix⟩ := TwoByOneBlock.trans (Hpk k r) hpk_herm a z (-(Tz k r z)) (by linarith [hT]) haa hzz
  have horth : ∀ (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → ∀ c : Fin r,
      herm (Hpk k r) (bvec (eI k r c)) w = 0 ∧ herm (Hpk k r) (bvec (esI k r c)) w = 0 := by
    intro w hw c
    rw [inWb_iff] at hw
    rw [herm_bvec_left, hpk_e, dot_bvec, herm_bvec_left, hpk_es, dot_bvec, Pi.star_apply, Pi.star_apply, (hw c).1,
      (hw c).2]
    simp
  exact ⟨g, hgU, fun c => ⟨hfix _ (horth a haW c).1 (horth z hz c).1, hfix _ (horth a haW c).2 (horth z hz c).2⟩, hga⟩

end Formalism.FourierDecayAlt.P.Qx8

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GTRIntPf

theorem u_step (P : M.Par) (hOK : P.OK) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ P.k - 1) : P.u (i + 1) + 1 ≤ P.u i := by
  have hg := hOK.gap i (Finset.mem_Icc.2 ⟨h1, h2⟩)
  unfold M.Par.lo M.Par.hi at hg
  have e1 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
  have e2 := min_le_left (P.u i) (P.u' i)
  linarith

theorem u_mono (P : M.Par) (hOK : P.OK) (a : ℕ) (ha : 1 ≤ a) :
    ∀ d : ℕ, a + d ≤ P.k → P.u (a + d) + d ≤ P.u a := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := u_step P hOK (a + d) (by omega) (by omega)
    rw [show a + (d + 1) = a + d + 1 by omega]
    push_cast
    linarith

theorem u_int (P : M.Par) (hOK : P.OK) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ P.k) : ∃ n : ℤ, P.u i - P.u 1 = n :=
  hOK.int_u i (Finset.mem_Icc.2 ⟨hi, hik⟩)

theorem sum_int {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, ∃ n : ℤ, f i = n) :
    ∃ n : ℤ, ∑ i ∈ s, f i = n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨n, hn⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨m, hm⟩ := h a (Finset.mem_insert_self a s)
    exact ⟨m + n, by rw [Finset.sum_insert ha, hm, hn]; push_cast; ring⟩

theorem sdec (P : M.Par) (hOK : P.OK) :
    SDec (fun j : Fin P.k => ((P.u ((j : ℕ) + 1) : ℝ) : ℂ) - (P.k : ℂ) / 2 + 1 / 2) := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  obtain ⟨na, hna⟩ := u_int P hOK ((a : ℕ) + 1) (by omega) (by have := a.isLt; omega)
  obtain ⟨nb, hnb⟩ := u_int P hOK ((b : ℕ) + 1) (by omega) (by have := b.isLt; omega)
  have hm := u_mono P hOK ((a : ℕ) + 1) (by omega) ((b : ℕ) - a) (by have := b.isLt; omega)
  rw [show (a : ℕ) + 1 + ((b : ℕ) - a) = (b : ℕ) + 1 by omega] at hm
  have hba : (1 : ℝ) ≤ (((b : ℕ) - (a : ℕ) : ℕ) : ℝ) := by
    have : 1 ≤ (b : ℕ) - (a : ℕ) := by omega
    exact_mod_cast this
  have hdiff : P.u ((a : ℕ) + 1) - P.u ((b : ℕ) + 1) = ((na - nb : ℤ) : ℝ) := by
    push_cast; linarith
  have hge : (1 : ℤ) ≤ na - nb := by
    have : (1 : ℝ) ≤ ((na - nb : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨(na - nb - 1).toNat, ?_⟩
  have hN : (((na - nb - 1).toNat : ℕ) : ℤ) = na - nb - 1 := Int.toNat_of_nonneg (by omega)
  have hNR : (((na - nb - 1).toNat : ℕ) : ℝ) = ((na - nb : ℤ) : ℝ) - 1 := by
    have := congrArg (fun x : ℤ => (x : ℝ)) hN
    push_cast at this ⊢
    linarith
  have hNC : (((na - nb - 1).toNat : ℕ) : ℂ) = (((((na - nb - 1).toNat : ℕ) : ℝ)) : ℂ) := by push_cast; rfl
  rw [hNC, hNR, ← hdiff]
  push_cast
  ring

theorem first_weight_half_integral {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (P : M.Par) (z : Fin (2 * P.r + P.k + 1) → ℂ) (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp))
    (hOK : P.OK) (hk : 2 ≤ P.k) (hz : inWb P.k P.r z) (hT : 0 < Tz P.k P.r z) (hty : IsType P.k P.r z π P.u) :
    ∃ n : ℤ, P.u 1 = n + ((P.k : ℝ) - 1) / 2 := by
  obtain ⟨hnt, hrep, hcont, -, -, hcap⟩ := hty
  have hR : IsRepW P.k P.r z π := ⟨hrep, hcont⟩
  obtain ⟨g, hgU, hgfix, hgz⟩ := Qx8.frameG_exists hz hT
  set Bs := QrCap.fr P.k P.r g with hBs
  have hB : IsFrameOf P.k P.r [z] Bs := QrCap.fr_frame hgU hgfix _ hgz
  set E := EB π Bs with hE
  have hFG := frame_general_linear Wp P.k P.r P.k z π Bs hR hB
  have hgl : GlRel E := hFG.1
  set m : Fin P.k → ℂ := fun j => ((P.u ((j : ℕ) + 1) : ℝ) : ℂ) - (P.k : ℂ) / 2 + 1 / 2 with hm
  have hq : ∀ (w : ℂ) (v : Wp), qdet E w v = cpol m w • v := by
    intro w v
    rw [← hFG.2 w v, hcap Bs hB w v, ProductIntervalFrames.prod_Icc_one]
    congr 1
    unfold cpol
    apply Finset.prod_congr rfl
    intro j _
    simp only [hm]
    ring
  have htop : CapSp E m = ⊤ := by
    rw [eq_top_iff]
    intro v _
    exact mem_CapSp.2 (hq · v)
  have hne : CapSp E m ≠ ⊥ := by
    rw [htop]
    exact top_ne_bot
  have hstabT : Stab E (⊤ : Submodule ℂ Wp) := fun _ _ _ _ => Submodule.mem_top
  obtain ⟨ν, v, -, hv0, hHW, -⟩ := exists_singular_maximal_vector Wp P.k E hgl ⊤ hstabT top_ne_bot
  have hsd := sdec P hOK
  have hν := (capelli_singular Wp P.k E m hgl hne).2 hsd ν v (by rw [htop]; exact Submodule.mem_top) hv0 hHW
  set c0 : Fin P.k := ⟨0, by omega⟩ with hc0
  have hν0 : ν c0 = m c0 := by rw [hν c0]; simp [hc0]

  set θ : Fin P.k → ℝ := fun c => if c = c0 then 2 * Real.pi else 0 with hθ
  have hDg : QrCap.Dg θ = QrCap.Dg (0 : Fin P.k → ℝ) := by
    unfold QrCap.Dg
    congr 1
    funext c
    simp only [hθ, Pi.zero_apply]
    split_ifs
    · push_cast
      rw [show (2 * (Real.pi : ℂ)) * Complex.I = 2 * Real.pi * Complex.I by ring, Complex.exp_two_pi_mul_I]
      simp
    · rfl
  have hblk : PI.UpqRep.blockW P.k P.r (QrCap.Dg θ) = 1 := by
    rw [hDg, ← QrCap.diag_exp_blockW]
    have : QrCap.dθ P.k P.r (0 : Fin P.k → ℝ) = 0 := by
      funext i
      unfold QrCap.dθ
      split_ifs <;> simp
    rw [this, NormedSpace.exp_zero]
    exact Matrix.diagonal_one
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det _).2 (WeylGroupFacts.isUnit_of_uh hgU)
  have hπ1 : π (NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • unitB (Hpk P.k P.r) Bs c c)) = 1 := by
    rw [QrCap.torus hgU θ, hblk, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)]
    exact hrep.1
  have hop := QrCap.op_torus hR hB θ
  rw [hπ1] at hop
  set A : Wp →L[ℂ] Wp := ∑ c, ((θ c : ℂ) * Complex.I) • ecOp π (unitB (Hpk P.k P.r) Bs c c) with hA
  have hAv : A v = ((2 * Real.pi : ℂ) * Complex.I * ν c0) • v := by
    rw [hA, ContinuousLinearMap.sum_apply, Finset.sum_eq_single c0]
    · rw [ContinuousLinearMap.smul_apply]
      have h1 : ecOp π (unitB (Hpk P.k P.r) Bs c0 c0) v = ν c0 • v := hHW.1 c0
      rw [h1, smul_smul]
      simp [hθ]
    · intro b _ hb
      simp [hθ, hb]
    · intro h; exact absurd (Finset.mem_univ c0) h
  have hexp := QrCap.exp_eig A _ v hAv
  rw [← hop] at hexp
  have h1 : Complex.exp ((2 * Real.pi : ℂ) * Complex.I * ν c0) = 1 := by
    by_contra hne1
    have : (1 - Complex.exp ((2 * Real.pi : ℂ) * Complex.I * ν c0)) • v = 0 := by
      rw [sub_smul, one_smul]
      have := hexp
      simp only [ContinuousLinearMap.one_apply] at this
      rw [← this, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact hne1 (sub_eq_zero.1 h).symm
    · exact hv0 h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  have hνn : ν c0 = n := by
    have hpi : (2 * Real.pi : ℂ) * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    rw [hn]; ring
  refine ⟨n, ?_⟩
  have hre := congrArg Complex.re (hν0.symm.trans hνn)
  simp only [hm, hc0] at hre
  simp at hre
  linarith

end GTRIntPf

open GTRIntPf in
theorem radial_gauge_integrality_holds : GTRInt := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hpl hk ρ
  obtain ⟨hOK, hz, hz', hTz, hTz', hty, hty'⟩ := hpl
  have hT : 0 < Tz P.k P.r z := by rw [hTz]; exact hOK.T_pos
  obtain ⟨N0, hN0⟩ := first_weight_half_integral P z π hOK hk hz hT hty

  have hU : ∃ n : ℤ, ∑ i ∈ Finset.Icc 1 P.k, ((P.u i - P.u 1) + (P.u' i - P.u 1)) = n := by
    apply sum_int
    intro i hi
    obtain ⟨a, ha⟩ := hOK.int_u i hi
    obtain ⟨b, hb⟩ := hOK.int_u' i hi
    exact ⟨a + b, by rw [ha, hb]; push_cast; ring⟩
  have hRh : ∃ n : ℤ, ∑ i ∈ Finset.Icc 1 (P.k - 1), (M.rho P ρ i - P.u 1 - 1 / 2) = n := by
    apply sum_int
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
    unfold M.rho
    rw [dif_pos ⟨hi1, hi2⟩]
    unfold M.Par.lo
    obtain ⟨a, ha⟩ := hOK.int_u (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    obtain ⟨b, hb⟩ := hOK.int_u' (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    rcases max_choice (P.u (i + 1)) (P.u' (i + 1)) with h | h
    · exact ⟨a + ((ρ ⟨i - 1, by omega⟩ : Fin _) : ℕ), by rw [h]; push_cast; linarith⟩
    · exact ⟨b + ((ρ ⟨i - 1, by omega⟩ : Fin _) : ℕ), by rw [h]; push_cast; linarith⟩
  obtain ⟨nU, hnU⟩ := hU
  obtain ⟨nR, hnR⟩ := hRh
  have hcU : ∑ i ∈ Finset.Icc 1 P.k, ((P.u i - P.u 1) + (P.u' i - P.u 1)) = uSum P - 2 * P.k * P.u 1 := by
    unfold uSum
    rw [Finset.sum_congr rfl (fun i _ => show (P.u i - P.u 1) + (P.u' i - P.u 1) = (P.u i + P.u' i) - 2 * P.u 1 by ring),
      Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    rw [show P.k + 1 - 1 = P.k by omega]
    ring
  have hcR : ∑ i ∈ Finset.Icc 1 (P.k - 1), (M.rho P ρ i - P.u 1 - 1 / 2) =
      rhoSum P ρ - ((P.k : ℝ) - 1) * (P.u 1 + 1 / 2) := by
    unfold rhoSum
    rw [Finset.sum_congr rfl (fun i _ => show M.rho P ρ i - P.u 1 - 1 / 2 = M.rho P ρ i - (P.u 1 + 1 / 2) by ring),
      Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    rw [show P.k - 1 + 1 - 1 = P.k - 1 by omega, Nat.cast_sub (by omega)]
    push_cast
    ring

  obtain ⟨t, ht⟩ : ∃ t : ℕ, (P.k : ℝ) * ((P.k : ℝ) - 1) = 2 * t := by
    obtain ⟨t, ht⟩ := Nat.even_mul_pred_self P.k
    refine ⟨t, ?_⟩
    have : ((P.k * (P.k - 1) : ℕ) : ℝ) = ((t + t : ℕ) : ℝ) := by rw [ht]
    push_cast [Nat.cast_sub (show 1 ≤ P.k by omega)] at this
    linarith
  refine ⟨nU - nR + (P.k + 1) * N0 + t, ?_⟩
  have e1 : uSum P = nU + 2 * P.k * P.u 1 := by linarith
  have e2 : rhoSum P ρ = nR + ((P.k : ℝ) - 1) * (P.u 1 + 1 / 2) := by linarith
  rw [e1, e2, hN0]
  push_cast
  linear_combination ht / 2

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTRT

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section vals

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec
  ext i
  simp

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

theorem vl_add (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    SSC.vl P Bs e (Φ + Ψ) ρ q = SSC.vl P Bs e Φ ρ q + SSC.vl P Bs e Ψ ρ q := by
  unfold SSC.vl
  rw [SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]
  unfold rawR
  simp only [Submodule.coe_add, Pi.add_apply, hsVec_add, inner_add_right, mul_add]

theorem vl_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    SSC.vl P Bs e (c • Φ) ρ q = c * SSC.vl P Bs e Φ ρ q := by
  unfold SSC.vl
  rw [SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]
  unfold rawR
  simp only [Submodule.coe_smul, Pi.smul_apply, hsVec_smul, inner_smul_right]
  ring

end vals

theorem dzQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have h0 : MA.eulerQ (TT := P.TT) M.vz (1 : MA.SmQ P.r P.TT) = 0 := by
    have h := Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vz 1 1
    rw [mul_one, one_mul, mul_one] at h
    have h2 : MA.eulerQ (TT := P.TT) M.vz (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vz 1 =
        MA.eulerQ (TT := P.TT) M.vz 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  unfold dzQ MA.DAlg.dzP MA.DAlg.mkP
  have h0' : (MA.DQ P).ev M.vz 1 = 0 := h0
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0
  rw [h0', map_zero]

theorem dzbQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzbQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have h0 : MA.eulerQ (TT := P.TT) M.vzb (1 : MA.SmQ P.r P.TT) = 0 := by
    have h := Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vzb 1 1
    rw [mul_one, one_mul, mul_one] at h
    have h2 : MA.eulerQ (TT := P.TT) M.vzb (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vzb 1 =
        MA.eulerQ (TT := P.TT) M.vzb 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  unfold dzbQ MA.DAlg.dzbP MA.DAlg.mkP
  have h0' : (MA.DQ P).ev M.vzb 1 = 0 := h0
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0
  rw [h0', map_zero]

theorem theta_fst {V : Type} [AddCommGroup V] [Module ℂ V] (P : M.Par) (d : Q.NFData P (Q.Pr V)) (Φ : V) :
    (ThetaNF P d).1 Φ = d.L.ζ.1 (d.L.nab.1 Φ) + d.L.ζb.1 (d.L.nabs.1 Φ) +
      (d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Φ +
      d.L.TT • d.L.GGi.1 ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Φ) := by
  unfold ThetaNF
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTRT

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

theorem radial_gauge_transition_holds : GTRTrans := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hC ρ m hm ζ hζ
  classical
  have hpl := hyp.1
  have hk2 := hyp.2.1
  have hTT : 0 ≤ P.TT := (mul_pos hpl.1.T_pos hpl.1.T'_pos).le
  have hLTT : d.L.TT = ((P.TT : ℝ) : ℂ) := by
    rw [hyp.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2, hpl.2.2.2.1, hpl.2.2.2.2.1]
    rfl
  obtain ⟨Φ0, hΦ0, -⟩ := SSTr.exists_tr P Bs hpl hk2 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  set Ψ0 := (d.κ (dTy P ρ)).1 Φ0 with hΨ0
  have t0 : trR P Bs e Ψ0 ρ = 1 := by
    rw [hΨ0, hk (dTy P ρ) Φ0, hΦ0, actA_kap]
    simp [dTy]
  let q0 : MA.Qp P.r P.TT := ⟨((fun _ => (1 : ℂ)), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have v0 : SSC.vl P Bs e Ψ0 ρ q0 = 1 := by
    unfold SSC.vl
    rw [t0]
    rfl
  have t1 : trR P Bs e (d.L.nab.1 Ψ0) ρ = fnZ P (A ρ) := by
    rw [(hC Ψ0 ρ).1, t0, GTRT.dzQ_one P hTT, mul_one, zero_add]
  have t2 : trR P Bs e (d.L.nabs.1 Ψ0) ρ = fnZ P (B ρ) := by
    rw [(hC Ψ0 ρ).2, t0, GTRT.dzbQ_one P hTT, mul_one, neg_zero, zero_add]
  have v1 : SSC.vl P Bs e (d.L.nab.1 Ψ0) ρ q0 = A ρ ζ := by
    unfold SSC.vl
    rw [t1, fnZ_val P (hAB ρ).1]
  have v2 : SSC.vl P Bs e (d.L.nabs.1 Ψ0) ρ q0 = B ρ ζ := by
    unfold SSC.vl
    rw [t2, fnZ_val P (hAB ρ).2]

  have vm : SSC.vl P Bs e ((ThetaNF P d).1 Ψ0) ρ q0 = m := by
    unfold SSC.vl
    rw [hm Ψ0, t0, GTRT.dzQ_one P hTT, GTRT.dzbQ_one P hTT, mul_zero, mul_zero, sub_zero, zero_add]
    show m * 1 = m
    ring
  have v3 : SSC.vl P Bs e ((d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Ψ0) ρ q0 = ((rhoSum P ρ : ℝ) : ℂ) := by
    rw [SSC.vl_kap P Bs d e hk, v0, mul_one]
  have v4 : SSC.vl P Bs e ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Ψ0) ρ q0 =
      ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ) := by
    rw [SSC.vl_kap P Bs d e hk, v0, mul_one]
  clear_value Ψ0

  have hfn := fun Ψ => SSC.vl_fn P Bs X d hyp e Ψ ρ q0
  rw [GTRT.theta_fst, GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_add P Bs hpl hk2 e he,
    GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_smul P Bs hpl hk2 e he, (hfn _).1, (hfn _).2.1, (hfn _).2.2,
    v3, v4, v1, v2, hLTT] at vm
  have hq : q0.1.2 = ζ := rfl
  rw [hq] at vm
  have hG : (Complex.normSq ζ : ℂ) - (P.TT : ℂ) ≠ 0 := by
    have : P.TT < Complex.normSq ζ := hζ
    intro h0
    have h1 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have : Complex.normSq ζ - P.TT = 0 := by exact_mod_cast h1
    linarith
  rw [← vm]
  push_cast
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem modA_eq_fun (P : M.Par) (ρ : M.Ty P) :
    modA P ρ = fun w => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹ := by
  funext w
  have h : (w * star w : ℂ) = (Complex.normSq w : ℂ) := Complex.mul_conj w
  rw [h]
  simp only [modA, div_eq_mul_inv]

theorem dZb_modA (P : M.Par) (ρ : M.Ty P) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    NF.dZb (modA P ρ) ζ = -(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2 := by
  have hns : (ζ * star ζ : ℂ) = (Complex.normSq ζ : ℂ) := Complex.mul_conj ζ
  have hlt : P.TT < Complex.normSq ζ := hζ
  have hN0 : ζ * star ζ - (P.TT : ℂ) ≠ 0 := by
    rw [hns, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hlt.ne')
  have hS := (hasFDerivAt_id (𝕜 := ℝ) ζ).star
  have hN := ((hasFDerivAt_id (𝕜 := ℝ) ζ).mul hS).sub_const (P.TT : ℂ)
  have hI := ((hasDerivAt_inv hN0).hasFDerivAt.restrictScalars ℝ).comp ζ hN
  have hF := ((hasFDerivAt_const (𝕜 := ℝ) (M.aC P ρ : ℂ) ζ).mul hS).mul hI
  have hF' : HasFDerivAt (fun w : ℂ => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹) _ ζ := hF
  rw [modA_eq_fun]
  simp only [NF.dZb]
  rw [hF'.fderiv]
  rw [← hns]
  simp [Complex.star_def]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem re_dZb_modA (P : M.Par) (ρ : M.Ty P) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    (NF.dZb (modA P ρ) ζ).re = -(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 := by
  rw [dZb_modA P ρ hζ]
  have h : (-(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2) =
      ((-(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.ofReal_re]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvTr

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem dZb_sub {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w) :
    NF.dZb (fun x => f x - g x) w = NF.dZb f w - NF.dZb g w := by
  simp only [NF.dZb]
  rw [show (fun x => f x - g x) = f - g from rfl, (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem dzQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have hev : (MA.DQ P).ev M.vz 1 = 0 := by
    apply Subtype.ext
    funext q
    show MA.coordE M.vz q.1 * MA.wirt M.vz (MA.ext ((1 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = 0
    have hloc : MA.ext (1 : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] fun _ => (1 : ℂ) := by
      filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx
      simp [MA.ext, hx]
    simp [MA.wirt, hloc.fderiv_eq]
  simp only [dzQ, MA.DAlg.dzP, MA.DAlg.mkP]
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0
  rw [hev, map_zero]

theorem dzbQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzbQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have hev : (MA.DQ P).ev M.vzb 1 = 0 := by
    apply Subtype.ext
    funext q
    show MA.coordE M.vzb q.1 * MA.wirt M.vzb (MA.ext ((1 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = 0
    have hloc : MA.ext (1 : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] fun _ => (1 : ℂ) := by
      filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx
      simp [MA.ext, hx]
    simp [MA.wirt, hloc.fderiv_eq]
  simp only [dzbQ, MA.DAlg.dzbP, MA.DAlg.mkP]
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0
  rw [hev, map_zero]

theorem actA_ggiA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.ggiA P (MA.DQ P)) g ρ = mulQ P ((MA.DQ P).ggiP P.TT) (g ρ) := by
  simp only [MA.actA, MA.ggiA, MA.sc, mulQ, Matrix.scalar_apply]
  refine (Finset.sum_eq_single ρ ?_ ?_).trans ?_
  · intro b _ hb
    simp [Matrix.diagonal, Ne.symm hb]
    rfl
  · intro h
    exact absurd (Finset.mem_univ ρ) h
  · simp [Matrix.diagonal]
    rfl

theorem curvTr_core
    (hmod : ∀ (P : M.Par) (ρ : M.Ty P) (ζ : ℂ), ζ ∈ Ann P →
      NF.dZb (modA P ρ) ζ = -(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2) :
    GTCCurvTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hK A B hAB hC hBA hcurv ρ ζ hζ
  have hTT : 0 ≤ P.TT := tt_nonneg_of_hyp hyp
  have hev : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q :=
    fun Φ σ q => SSTr.trR_apply P Bs hyp.1 hyp.2.1 e he Φ σ q
  have tsub : ∀ (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e (Φ - Ψ) σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q -
          ((trR P Bs e Ψ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
    intro Φ Ψ σ q
    rw [hev, hev, hev, Submodule.coe_sub, sub_eq_add_neg, ← neg_one_smul ℂ (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      VLem.rawR_add, VLem.rawR_smul]
    simp [sub_eq_add_neg]
  have tsmul : ∀ (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e (c • Φ) σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        c * ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
    intro c Φ σ q
    rw [hev, hev, Submodule.coe_smul, VLem.rawR_smul]
    rfl
  obtain ⟨Φ₀, hΦ₀, -⟩ := SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  have hAs := (hAB ρ).1
  have hBs := (hAB ρ).2
  have hΨ : trR P Bs e ((d.κ (dTy P ρ)).1 Φ₀) ρ = 1 := by
    rw [hK, actA_kap, hΦ₀]
    simp [dTy]
  have hN : trR P Bs e (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀)) ρ = fnZ P (A ρ) := by
    rw [(hC _ ρ).1, hΨ, dzQ_one P hTT, zero_add, mul_one]
  have hS : trR P Bs e (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀)) ρ = fnZ P (B ρ) := by
    rw [(hC _ ρ).2, hΨ, dzbQ_one P hTT, neg_zero, zero_add, mul_one]
  have hSN : trR P Bs e (d.L.nabs.1 (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀))) ρ =
      -dzbQ P (fnZ P (A ρ)) + fnZ P (B ρ) * fnZ P (A ρ) := by
    rw [(hC _ ρ).2, hN]
  have hNS : trR P Bs e (d.L.nab.1 (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀))) ρ =
      dzQ P (fnZ P (B ρ)) + fnZ P (A ρ) * fnZ P (B ρ) := by
    rw [(hC _ ρ).1, hS]
  have hG : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      trR P Bs e (d.L.GGi.1 Φ) ρ = mulQ P ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ ρ) := by
    intro Φ
    rw [((GT.gauge_function_holds Wp Wq P Bs X d hyp e) Φ).2.2.2.2.2, actA_ggiA]
  have hc' : d.L.nabs.1 (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀)) - d.L.nab.1 (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀)) =
      ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) • d.L.GGi.1 (d.L.GGi.1 ((d.κ (dTy P ρ)).1 Φ₀)) :=
    congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 Φ₀) (hcurv ρ)
  have hζQ : (((fun _ => (1 : ℂ)), ζ) : MA.E P.r) ∈ MA.Qset P.r P.TT := ⟨fun _ => one_ne_zero, hζ⟩
  have key := congrArg (fun Φ => ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) ⟨_, hζQ⟩) hc'
  rw [tsub, tsmul, hSN, hNS, hG, hG, hΨ] at key
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg, Pi.add_apply, Pi.mul_apply, Pi.neg_apply,
    mulQ_ggiP, Subalgebra.coe_one, Pi.one_apply, dzbQ_apply P hTT, dzQ_apply P hTT,
    fnZ_val P hAs, fnZ_val P hBs] at key
  have hz1 := wirt_fnZ_zb P hAs ⟨_, hζQ⟩
  have hz2 := wirtinger_derivative_fibre_function P hBs ⟨_, hζQ⟩
  dsimp only at hz1 hz2
  rw [hz1, hz2] at key
  have hAd : DifferentiableAt ℝ (A ρ) ζ := (hAs.contDiffAt ((ann_open P).mem_nhds hζ)).differentiableAt (by simp)
  have hmd : DifferentiableAt ℝ (modA P ρ) ζ :=
    ((modA_smooth P ρ hTT).contDiffAt ((ann_open P).mem_nhds hζ)).differentiableAt (by simp)
  have hBeq : B ρ =ᶠ[nhds ζ] fun w => star (A ρ w) := by
    filter_upwards [(ann_open P).mem_nhds hζ] with w hw
    exact hBA ρ w hw
  have hdZB : NF.dZ (B ρ) ζ = star (NF.dZb (A ρ) ζ) := by
    rw [Formalism.FourierDecayAlt.P5.HerB.dZ_eq, hBeq.fderiv_eq, ← Formalism.FourierDecayAlt.P5.HerB.dZ_eq]
    exact Formalism.FourierDecayAlt.P5.HerB.dZ_conj hAd
  change -NF.dZb (A ρ) ζ + B ρ ζ * A ρ ζ - (NF.dZ (B ρ) ζ + A ρ ζ * B ρ ζ) =
    ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ *
      (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * 1)) at key
  rw [hdZB] at key
  have h2 : -NF.dZb (A ρ) ζ + B ρ ζ * A ρ ζ - (star (NF.dZb (A ρ) ζ) + A ρ ζ * B ρ ζ) =
      -(NF.dZb (A ρ) ζ + star (NF.dZb (A ρ) ζ)) := by ring
  have h4 : ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ *
      (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * 1)) =
      ((2 * M.aC P ρ * P.TT * ((Complex.normSq ζ - P.TT)⁻¹ * (Complex.normSq ζ - P.TT)⁻¹) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, h4] at key
  have h3 := congrArg Complex.re key
  rw [Complex.neg_re, Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re] at h3
  have hx : 0 < Complex.normSq ζ - P.TT := sub_pos.mpr hζ
  rw [dZb_sub hmd hAd, Complex.sub_re, re_dZb_modA P ρ hζ]
  have hw : (NF.dZb (A ρ) ζ).re = -(M.aC P ρ * P.TT) * ((Complex.normSq ζ - P.TT)⁻¹ * (Complex.normSq ζ - P.TT)⁻¹) := by
    linarith
  rw [hw]
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvTr

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem curvature_trace_holds : GTCCurvTr := CurvTr.curvTr_core (fun P ρ ζ hζ => dZb_modA P ρ hζ)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem reference_annulus_holds : GTCRefAn := by
  intro TT α c hTT hα hre R hR hR2
  have hpt : ∀ θ : ℝ, TT < Complex.normSq (circleMap 0 R θ) := by
    intro θ
    have h1 : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    rw [Complex.normSq_eq_norm_sq, h1]
    exact hR2
  have hcα : Continuous (fun θ : ℝ => α (circleMap 0 R θ)) :=
    hα.continuousOn.comp_continuous (continuous_circleMap 0 R) hpt
  have hd : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I := by
    funext θ
    exact deriv_circleMap 0 R θ
  have hF : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) := by
    have h2 : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ) := by
      rw [hd]
      exact (continuous_circleMap 0 R).mul continuous_const
    exact h2.smul hcα
  have key : ∀ θ : ℝ, Complex.imCLM (deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) = c := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul, Complex.imCLM_apply]
    rw [← hre (circleMap 0 R θ) (hpt θ)]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  unfold circleIntegral
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hF.intervalIntegrable _ _)]
  simp only [key]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Complex MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph

def AnnT (TT : ℝ) : Set ℂ := {ζ : ℂ | TT < Complex.normSq ζ}

theorem isOpen_annT (TT : ℝ) : IsOpen (AnnT TT) := isOpen_lt continuous_const Complex.continuous_normSq

theorem circleMap_mem_annT {TT R : ℝ} (hR : TT < R ^ 2) (θ : ℝ) : circleMap 0 R θ ∈ AnnT TT := by
  show TT < Complex.normSq (circleMap 0 R θ)
  rw [Complex.normSq_eq_norm_sq, norm_circleMap_zero, sq_abs]
  exact hR

theorem re_conj_fderiv {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT))
    (h1 : ∀ ζ ∈ AnnT TT, ‖u ζ‖ = 1) {ζ : ℂ} (hζ : ζ ∈ AnnT TT) (h : ℂ) :
    (star (u ζ) * fderiv ℝ u ζ h).re = 0 := by
  have hopen := isOpen_annT TT
  have hd : DifferentiableAt ℝ u ζ := (hu.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hζ)
  have hP := hd.hasFDerivAt.star.mul hd.hasFDerivAt
  have hconst : (fun w => star (u w) * u w) =ᶠ[nhds ζ] fun _ => (1 : ℂ) := by
    filter_upwards [hopen.mem_nhds hζ] with w hw
    have hn := h1 w hw
    rw [mul_comm]
    have e : u w * star (u w) = (Complex.normSq (u w) : ℂ) := Complex.mul_conj _
    rw [e, Complex.normSq_eq_norm_sq, hn]
    simp
  have hz := hP.fderiv.symm.trans (hconst.fderiv_eq.trans (hasFDerivAt_const (𝕜 := ℝ) (1 : ℂ) ζ).fderiv)
  have hv := congrArg (fun L => (L h).re) hz
  simp [Complex.mul_re, Complex.star_def] at hv
  simp [Complex.mul_re, Complex.star_def]
  linarith

theorem im_conj_dZ_mul {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT))
    (h1 : ∀ ζ ∈ AnnT TT, ‖u ζ‖ = 1) {ζ : ℂ} (hζ : ζ ∈ AnnT TT) (h : ℂ) :
    (star (u ζ) * NF.dZ u ζ * h).im = (star (u ζ) * fderiv ℝ u ζ h).im / 2 := by
  have hr1 := re_conj_fderiv hu h1 hζ 1
  have hrI := re_conj_fderiv hu h1 hζ Complex.I
  have hh : h = h.re • (1 : ℂ) + h.im • Complex.I := by
    apply Complex.ext <;> simp
  have hlin : fderiv ℝ u ζ h = h.re • fderiv ℝ u ζ 1 + h.im • fderiv ℝ u ζ Complex.I := by
    conv_lhs => rw [hh]
    rw [map_add, map_smul, map_smul]
  rw [hlin]
  simp only [NF.dZ]
  simp [Complex.mul_re, Complex.mul_im, Complex.star_def] at hr1 hrI ⊢
  linear_combination (h.im / 2) * hr1 - (h.re / 2) * hrI

theorem winding {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT))
    (h1 : ∀ ζ ∈ AnnT TT, ‖u ζ‖ = 1) {R : ℝ} (hR : TT < R ^ 2) :
    ∃ n : ℤ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      star (u (circleMap 0 R θ)) * fderiv ℝ u (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)).im =
        2 * Real.pi * n := by
  have hopen := isOpen_annT TT
  have hmem : ∀ θ, circleMap 0 R θ ∈ AnnT TT := circleMap_mem_annT hR
  have hdiff : ∀ ζ ∈ AnnT TT, DifferentiableAt ℝ u ζ := fun ζ hζ =>
    (hu.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hζ)
  have hv : ∀ θ, HasDerivAt (fun t => u (circleMap 0 R t))
      (fderiv ℝ u (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)) θ := by
    intro θ
    exact (hdiff _ (hmem θ)).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 R θ)
  set g : ℝ → ℂ := fun θ => star (u (circleMap 0 R θ)) *
    fderiv ℝ u (circleMap 0 R θ) (circleMap 0 R θ * Complex.I) with hgdef
  have hgcont : Continuous g := by
    have hf := hu.continuousOn_fderiv_of_isOpen hopen (by simp)
    have hc : Continuous (circleMap 0 R) := continuous_circleMap 0 R
    have h2 : Continuous fun θ => fderiv ℝ u (circleMap 0 R θ) := hf.comp_continuous hc hmem
    have h3 : Continuous fun θ => u (circleMap 0 R θ) := hu.continuousOn.comp_continuous hc hmem
    exact (continuous_star.comp h3).mul (h2.clm_apply (hc.mul continuous_const))
  set G : ℝ → ℂ := fun t => ∫ θ in (0 : ℝ)..t, g θ with hGdef
  have hG : ∀ t, HasDerivAt G (g t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hgcont.intervalIntegrable _ _)
      (hgcont.stronglyMeasurableAtFilter _ _) hgcont.continuousAt
  have hnorm : ∀ t, u (circleMap 0 R t) * star (u (circleMap 0 R t)) = 1 := by
    intro t
    have hn := h1 _ (hmem t)
    have e : u (circleMap 0 R t) * star (u (circleMap 0 R t)) = (Complex.normSq (u (circleMap 0 R t)) : ℂ) :=
      Complex.mul_conj _
    rw [e, Complex.normSq_eq_norm_sq, hn]
    simp
  have hF : ∀ t, HasDerivAt (fun t => u (circleMap 0 R t) * Complex.exp (-G t)) 0 t := by
    intro t
    have h4 := (hv t).mul ((hG t).neg.cexp)
    have h0 : fderiv ℝ u (circleMap 0 R t) (circleMap 0 R t * Complex.I) * Complex.exp (-G t) +
        u (circleMap 0 R t) * (Complex.exp (-G t) * -g t) = 0 := by
      rw [hgdef]
      beta_reduce
      linear_combination -(Complex.exp (-G t) * fderiv ℝ u (circleMap 0 R t) (circleMap 0 R t * Complex.I)) * hnorm t
    exact h4.congr_deriv h0
  have hconst := is_const_of_deriv_eq_zero (fun t => (hF t).differentiableAt) (fun t => (hF t).deriv)
    (2 * Real.pi) 0
  have hv2 : circleMap 0 R (2 * Real.pi) = circleMap 0 R 0 := by
    simpa using periodic_circleMap 0 R 0
  have hv0 : u (circleMap 0 R 0) ≠ 0 := by
    intro h0
    have hn := h1 _ (hmem 0)
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have hE : Complex.exp (-G (2 * Real.pi)) = 1 := by
    have h5 : u (circleMap 0 R 0) * Complex.exp (-G (2 * Real.pi)) = u (circleMap 0 R 0) * 1 := by
      have h6 := hconst
      simp only [hG0, neg_zero, Complex.exp_zero, mul_one] at h6
      rw [hv2] at h6
      rw [mul_one]
      exact h6
    exact mul_left_cancel₀ hv0 h5
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hE
  refine ⟨-n, ?_⟩
  have h7 : G (2 * Real.pi) = -(n * (2 * Real.pi * Complex.I)) := by
    rw [← hn]
    ring
  show (G (2 * Real.pi)).im = 2 * Real.pi * ((-n : ℤ) : ℝ)
  rw [h7]
  simp
  ring

theorem continuousOn_dZ {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT)) :
    ContinuousOn (NF.dZ u) (AnnT TT) := by
  have hf := hu.continuousOn_fderiv_of_isOpen (isOpen_annT TT) (by simp)
  have e : NF.dZ u = fun ζ => (1 / 2 : ℂ) * (fderiv ℝ u ζ 1 - Complex.I * fderiv ℝ u ζ Complex.I) := rfl
  rw [e]
  exact continuousOn_const.mul ((hf.clm_apply continuousOn_const).sub
    (continuousOn_const.mul (hf.clm_apply continuousOn_const)))

theorem hol_unit {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT))
    (h1 : ∀ ζ ∈ AnnT TT, ‖u ζ‖ = 1) {R : ℝ} (hR : TT < R ^ 2) :
    ∃ n : ℤ, (circleIntegral (fun w => star (u w) * NF.dZ u w) 0 R).im = Real.pi * n := by
  have hopen := isOpen_annT TT
  have hmem : ∀ θ, circleMap 0 R θ ∈ AnnT TT := circleMap_mem_annT hR
  obtain ⟨n, hn⟩ := winding hu h1 hR
  refine ⟨n, ?_⟩
  have hf := hu.continuousOn_fderiv_of_isOpen hopen (by simp)
  have hc : Continuous (circleMap 0 R) := continuous_circleMap 0 R
  have h2 : Continuous fun θ => fderiv ℝ u (circleMap 0 R θ) := hf.comp_continuous hc hmem
  have h3 : Continuous fun θ => u (circleMap 0 R θ) := hu.continuousOn.comp_continuous hc hmem
  have hdz : Continuous fun θ => NF.dZ u (circleMap 0 R θ) := (continuousOn_dZ hu).comp_continuous hc hmem
  set f1 : ℝ → ℂ := fun θ => deriv (circleMap 0 R) θ •
    (star (u (circleMap 0 R θ)) * NF.dZ u (circleMap 0 R θ)) with hf1def
  set f2 : ℝ → ℂ := fun θ => star (u (circleMap 0 R θ)) *
    fderiv ℝ u (circleMap 0 R θ) (circleMap 0 R θ * Complex.I) with hf2def
  have hf1 : Continuous f1 := by
    rw [hf1def]
    simp only [deriv_circleMap, smul_eq_mul]
    exact (hc.mul continuous_const).mul ((continuous_star.comp h3).mul hdz)
  have hf2 : Continuous f2 := (continuous_star.comp h3).mul (h2.clm_apply (hc.mul continuous_const))
  have hpt : ∀ θ, (f1 θ).im = (f2 θ).im / 2 := by
    intro θ
    rw [hf1def, hf2def]
    simp only [deriv_circleMap, smul_eq_mul]
    rw [show circleMap 0 R θ * Complex.I * (star (u (circleMap 0 R θ)) * NF.dZ u (circleMap 0 R θ)) =
      star (u (circleMap 0 R θ)) * NF.dZ u (circleMap 0 R θ) * (circleMap 0 R θ * Complex.I) by ring]
    exact im_conj_dZ_mul hu h1 (hmem θ) _
  have hI1 : (circleIntegral (fun w => star (u w) * NF.dZ u w) 0 R).im =
      ∫ θ in (0 : ℝ)..2 * Real.pi, (f1 θ).im := by
    rw [circleIntegral]
    exact (intervalIntegral.intervalIntegral_im (hf1.intervalIntegrable _ _)).symm
  have hI2 : ∫ θ in (0 : ℝ)..2 * Real.pi, (f2 θ).im = (∫ θ in (0 : ℝ)..2 * Real.pi, f2 θ).im :=
    intervalIntegral.intervalIntegral_im (hf2.intervalIntegrable _ _)
  rw [hI1]
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, hI2]
  have hn' : (∫ θ in (0 : ℝ)..2 * Real.pi, f2 θ).im = 2 * Real.pi * n := hn
  rw [hn']
  ring

theorem curv_alg (u0 p q s11 sii : ℂ) (hn : u0 * star u0 = 1) (ha : (star u0 * p).re = 0)
    (hb : (star u0 * q).re = 0) (h11 : (star p * p + star u0 * s11).re = 0)
    (hII : (star q * q + star u0 * sii).re = 0) :
    ((star p + Complex.I * star q) * (p - Complex.I * q) + star u0 * (s11 + sii)).re = 0 := by
  have hn' := congrArg Complex.re hn
  simp [Complex.mul_re, Complex.mul_im, Complex.star_def] at hn' ha hb h11 hII ⊢
  linear_combination h11 + hII - 2 * (-u0.re * q.im + u0.im * q.re) * ha
    - 2 * (u0.re * p.im - u0.im * p.re) * hb + 2 * (q.re * p.im - q.im * p.re) * hn'

theorem hasFDerivAt_star {u : ℂ → ℂ} {ζ : ℂ} (hd : DifferentiableAt ℝ u ζ) :
    HasFDerivAt (fun w => star (u w)) (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ u ζ)) ζ := by
  refine hd.hasFDerivAt.star.congr_fderiv ?_
  exact ContinuousLinearMap.ext fun v => rfl

theorem curv_unit {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT))
    (h1 : ∀ ζ ∈ AnnT TT, ‖u ζ‖ = 1) {ζ : ℂ} (hζ : ζ ∈ AnnT TT) :
    (NF.dZb (fun w => star (u w) * NF.dZ u w) ζ).re = 0 := by
  have hs := isOpen_annT TT
  have hn : AnnT TT ∈ nhds ζ := hs.mem_nhds hζ
  have hud : ∀ w ∈ AnnT TT, DifferentiableAt ℝ u w := fun w hw =>
    (hu.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hw)
  have hd2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ u) (AnnT TT) :=
    hu.fderiv_of_isOpen hs (by simp)
  have hDd : DifferentiableAt ℝ (fderiv ℝ u) ζ := (hd2.differentiableOn (by simp)).differentiableAt hn
  set S := fderiv ℝ (fderiv ℝ u) ζ with hS
  have hDv : ∀ v : ℂ, HasFDerivAt (fun w => fderiv ℝ u w v) (S.flip v) ζ := by
    intro v
    have := hDd.hasFDerivAt.clm_apply (hasFDerivAt_const v ζ)
    simpa using this
  have hsym : S 1 Complex.I = S Complex.I 1 :=
    ((hu.contDiffAt hn).isSymmSndFDerivAt (by (try simp); exact (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.2 le_top))) 1 Complex.I

  have h2 : ∀ k : ℂ, (star (fderiv ℝ u ζ k) * fderiv ℝ u ζ k + star (u ζ) * S k k).re = 0 := by
    intro k
    have hφ : HasFDerivAt (fun w => star (u w) * fderiv ℝ u w k)
        (star (u ζ) • S.flip k + fderiv ℝ u ζ k • Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ u ζ)) ζ :=
      (hasFDerivAt_star (hud ζ hζ)).mul (hDv k)
    have hre := Complex.reCLM.hasFDerivAt.comp ζ hφ
    have h0 : HasFDerivAt (Complex.reCLM ∘ fun w => star (u w) * fderiv ℝ u w k) (0 : ℂ →L[ℝ] ℝ) ζ := by
      apply (hasFDerivAt_const (0 : ℝ) ζ).congr_of_eventuallyEq
      filter_upwards [hn] with w hw
      simp only [Function.comp_apply, Complex.reCLM_apply]
      exact re_conj_fderiv hu h1 hw k
    have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L k) (hre.unique h0)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
      Complex.reCLM_apply, ContinuousLinearMap.zero_apply, smul_eq_mul] at he
    rw [← he, Complex.star_def]
    congr 1
    ring

  have ht : HasFDerivAt (fun w => NF.dZ u w)
      ((1 / 2 : ℂ) • (S.flip 1 - Complex.I • S.flip Complex.I)) ζ := by
    have := ((hDv 1).sub ((hDv Complex.I).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
    unfold NF.dZ
    exact this
  have hF : HasFDerivAt (fun w => star (u w) * NF.dZ u w) _ ζ := (hasFDerivAt_star (hud ζ hζ)).mul ht
  have hnorm : u ζ * star (u ζ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1 ζ hζ]; simp
  have key : NF.dZb (fun w => star (u w) * NF.dZ u w) ζ = (1 / 4 : ℂ) *
      ((star (fderiv ℝ u ζ 1) + Complex.I * star (fderiv ℝ u ζ Complex.I)) *
        (fderiv ℝ u ζ 1 - Complex.I * fderiv ℝ u ζ Complex.I) + star (u ζ) * (S 1 1 + S Complex.I Complex.I)) := by
    unfold NF.dZb
    rw [hF.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul]
    unfold NF.dZ
    simp only [Complex.star_def, hsym]
    ring_nf
    rw [Complex.I_sq]
    ring
  have := curv_alg (u ζ) (fderiv ℝ u ζ 1) (fderiv ℝ u ζ Complex.I) (S 1 1) (S Complex.I Complex.I) hnorm
    (re_conj_fderiv hu h1 hζ 1) (re_conj_fderiv hu h1 hζ Complex.I) (h2 1) (h2 Complex.I)
  rw [key, Complex.mul_re, this]
  simp

end Ph

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem connection_uniqueness_holds : GTCConnUniq := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he A B A' B' hAB hAB' hC hC' ρ ζ hζ
  obtain ⟨Φ, hΦ, -⟩ := SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  have h1 := (hC Φ ρ).1
  have h2 := (hC' Φ ρ).1
  rw [hΦ] at h1 h2
  simp only [mul_one] at h1 h2
  have h3 : fnZ P (A ρ) = fnZ P (A' ρ) := by
    have := h1.symm.trans h2
    exact add_left_cancel this
  rw [fnZ_eq_mk P (hAB ρ).1, fnZ_eq_mk P (hAB' ρ).1] at h3
  have hq : ((fun _ => (1 : ℂ), ζ) : (Fin P.r → ℂ) × ℂ) ∈ MA.Qset P.r P.TT :=
    ⟨fun _ => one_ne_zero, hζ⟩
  have := congrFun (congrArg Subtype.val h3) ⟨_, hq⟩
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem phase_holomorphy_holds : GTCPhHol := by
  intro TT u hu h1 R _ hR
  exact Ph.hol_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hR

theorem phase_curvature_holds : GTCPhCurv := by
  intro TT u hu h1 ζ hζ
  exact Ph.curv_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hζ

theorem connection_phase_holds : GTCConnPhase := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e A B u hAB hu hC
  exact connF_phase P (tt_nonneg_of_hyp hyp) Bs d e A B u hAB hC hu

theorem gTCHol_of_ref (hRef : GTCRef) : GTCHol :=
  gTCHol_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_holomorphy_holds

theorem gTCCurv_of_ref (hRef : GTCRef) : GTCCurv :=
  gTCCurv_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_curvature_holds

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

def GTConnOfLeaves : Prop := GTCLocal → GTCReal → GTCCurv → GTCHol → GTCAnnulus → GTConn

theorem gTConn_of_leaves : GTConnOfLeaves := fun hL hR hC hH hA =>
  gTConn_of_cut hL (gTCPhase_of_cut hR hC hH hA torus_parameter) gauge_transform_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTCRefTrace_of_rotK (h : GTRRotK) : GTCRefTrace :=
  gTCRefTrace_of_cutK radial_gauge_move radial_gauge_constant_holds top_normal_form_of_curvature top_action_on_gauge_holds h radial_gauge_integrality_holds radial_gauge_transition_holds gauge_reality_holds

theorem gTCRef_of_rotK (h : GTRRotK) : GTCRef :=
  gTCRef_of_cut gauge_reality_holds curvature_identity_holds curvature_trace_holds (gTCRefTrace_of_rotK h) reference_annulus_holds

theorem gTConn_of_rotK (h : GTRRotK) : GTConn :=
  gTConn_of_leaves gauge_locality_holds gauge_reality_holds (gTCCurv_of_ref (gTCRef_of_rotK h)) (gTCHol_of_ref (gTCRef_of_rotK h)) annulus_condition_holds

theorem genTransfer_of_rotK (h : GTRRotK) : GenTransfer :=
  genTransfer_of_cut GT.gauge_function_holds gauge_kappa_holds (gTConn_of_rotK h) second_shift_gauge_holds

theorem gCore_of_rotK (h : GTRRotK) : GCore := gCore_of_genTransfer (genTransfer_of_rotK h)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_rotK (hJ : JfSmoothDS) (hR : Gauge.GC.GTRRotK) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_ssnRep hJ (Gauge.GC.genTransfer_of_rotK hR) h

end Formalism.FourierDecayAlt.P.CutMP
end
