import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.UnfoldingVolume
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.IwasawaCovolume
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.MassRatioBoundPower
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemV
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGen
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeVolRatio
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GaugeVolumeBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPf

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
  Formalism.MainNotions.LeviCoordinates
open scoped ENNReal Pointwise

namespace Formalism.L2.S.S7.ZsCovSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem muA_FD (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (ys : Finset I.Gf)
    (hys : Formalism.MainNotions.FundamentalDomainUnfolding.ClassReps I ys) (Dy : I.Gf → Set I.Ginf)
    (hD : ∀ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.IsFundInf I y (Formalism.MainNotions.FundamentalDomainUnfolding.muInf I) (Dy y)) :
    I.muA μf (UnfoldingVolume.FD I ys Dy) = μf I.Kset * ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf I (Dy y) := by
  rw [UnfoldingVolume.FD, measure_biUnion_finset]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [UnfoldingVolume.muA_eq, Measure.prod_prod, UnfoldingVolume.Ky_measure, mul_comm]
  · intro y hy y' hy' hne
    refine Set.disjoint_left.2 fun p hp hp' => hne ?_
    have hk : y⁻¹ * p.2 ∈ I.Kset := hp.2
    have hk' : y'⁻¹ * p.2 ∈ I.Kset := hp'.2
    refine hys.2 y hy y' hy' ⟨1, rrg_one_mem I, (y⁻¹ * p.2) * (y'⁻¹ * p.2)⁻¹,
      UnfoldingVolume.kmul I hk (UnfoldingVolume.kinv I hk'), ?_⟩
    show y' = 1 * y * ((y⁻¹ * p.2) * (y'⁻¹ * p.2)⁻¹)
    group
  · intro y hy
    exact (hD y hy).1.prod (UnfoldingVolume.Ky_meas I y)

theorem FD_meas (I : AutInst) (ys : Finset I.Gf) (Dy : I.Gf → Set I.Ginf)
    (hD : ∀ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.IsFundInf I y (Formalism.MainNotions.FundamentalDomainUnfolding.muInf I) (Dy y)) :
    MeasurableSet (UnfoldingVolume.FD I ys Dy) :=
  Finset.measurableSet_biUnion ys fun y hy => (hD y hy).1.prod (UnfoldingVolume.Ky_meas I y)

theorem blockEquiv {n P Q : ℕ} (ε : Fin n → Bool) (hP : (Finset.univ.filter fun i => ε i = true).card = P)
    (hn : P + Q = n) :
    ∃ e : Fin P ⊕ Fin Q ≃ Fin n, (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false := by
  have hT : Fintype.card {i // ε i = true} = P := by rw [Fintype.card_subtype]; exact hP
  have hF : Fintype.card {i // ¬ ε i = true} = Q := by
    rw [Fintype.card_subtype_compl, hT, Fintype.card_fin]; omega
  let eT : Fin P ≃ {i // ε i = true} := (Fintype.equivFinOfCardEq hT).symm
  let eF : Fin Q ≃ {i // ¬ ε i = true} := (Fintype.equivFinOfCardEq hF).symm
  refine ⟨(Equiv.sumCongr eT eF).trans (Equiv.sumCompl fun i => ε i = true), fun i => ?_, fun j => ?_⟩
  · simpa using (eT i).2
  · simpa using (eF j).2

theorem volgU_eq_Icc (n : ℕ) :
    IwasawaCovolume.volgU n = ∏ i ∈ Finset.Icc 1 n, (2 * Real.pi) ^ i / ((i - 1).factorial : ℝ) := by
  induction n with
  | zero => simp [IwasawaCovolume.volgU]
  | succ k ih =>
    rw [IwasawaCovolume.volgU, Finset.prod_range_succ, ← IwasawaCovolume.volgU, ih, Finset.prod_Icc_succ_top (by omega)]
    simp

end Formalism.L2.S.S7.ZsCovSum
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
  Formalism.MainNotions.LeviCoordinates
open scoped ENNReal Pointwise

namespace Formalism.L2.S.S7.ZsCovTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : Formalism.IndefR.Eqv.UI.Frames D V)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem isFund_image (hc0 : ∀ v, D.s.cdScale V.rank (fr.ε v) ≠ 0)
    (μf : Measure (Formalism.IndefR.Eqv.UI.instV fr).Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    {s : Set (Formalism.IndefR.Eqv.UI.instV fr).GA} (hsm : MeasurableSet s)
    (hs : IsFundamentalDomain (rr_GF (Formalism.IndefR.Eqv.UI.instV fr)) s ((Formalism.IndefR.Eqv.UI.instV fr).muA μf)) :
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig V.gram) (Formalism.IndefR.Eqv.UI.brg fr '' s)
      (ZsCovMeas.muV fr μf) := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := Formalism.IndefR.Eqv.ga_facts D V
  have hH := ZsCovMeas.isHaar_muV fr hc0 μf
  have hGF : (Formalism.IndefR.Eqv.UI.brg fr) '' (Formalism.IndefR.Eqv.UI.instV fr).GFset =
      Formalism.L2.SG.AdBridge.ratHA (Formalism.IndefR.Eqv.UI.instV fr) :=
    (Formalism.L2.SG.Closed.adelic_isomorphism_statement (Formalism.IndefR.Eqv.UI.instV fr)).2.1 (Formalism.IndefR.Eqv.UI.brg fr)
      (Formalism.IndefR.Eqv.UI.brg_isBridge fr)
  have hto : ∀ γ : rr_GF (Formalism.IndefR.Eqv.UI.instV fr),
      Formalism.IndefR.Eqv.UI.brg fr (γ : (Formalism.IndefR.Eqv.UI.instV fr).GA) ∈ HFinIn (AF D.host.F) D.sp.cm.sig V.gram := by
    intro γ
    have : Formalism.IndefR.Eqv.UI.brg fr (γ : (Formalism.IndefR.Eqv.UI.instV fr).GA) ∈
        Formalism.L2.SG.AdBridge.ratHA (Formalism.IndefR.Eqv.UI.instV fr) := hGF ▸ ⟨γ, γ.2, rfl⟩
    exact this
  have hfrom : ∀ g : HFinIn (AF D.host.F) D.sp.cm.sig V.gram, ∃ γ : rr_GF (Formalism.IndefR.Eqv.UI.instV fr),
      Formalism.IndefR.Eqv.UI.brg fr (γ : (Formalism.IndefR.Eqv.UI.instV fr).GA) = (g.1 : GA D V) := by
    intro g
    have h : (g.1 : GA D V) ∈ Formalism.L2.SG.AdBridge.ratHA (Formalism.IndefR.Eqv.UI.instV fr) := g.2
    rw [← hGF] at h
    obtain ⟨γ, hγ, hγg⟩ := h
    exact ⟨⟨γ, hγ⟩, hγg⟩
  have hsm1 : ∀ (γ : rr_GF (Formalism.IndefR.Eqv.UI.instV fr)) (y : (Formalism.IndefR.Eqv.UI.instV fr).GA),
      Formalism.IndefR.Eqv.UI.brg fr (γ • y) =
        (⟨Formalism.IndefR.Eqv.UI.brg fr γ, hto γ⟩ : HFinIn (AF D.host.F) D.sp.cm.sig V.gram) • Formalism.IndefR.Eqv.UI.brg fr y := by
    intro γ y
    show Formalism.IndefR.Eqv.UI.brg fr ((γ : (Formalism.IndefR.Eqv.UI.instV fr).GA) * y) = _
    rw [map_mul]
    rfl
  have hsmul : ∀ (γ : rr_GF (Formalism.IndefR.Eqv.UI.instV fr)) (t : Set (Formalism.IndefR.Eqv.UI.instV fr).GA),
      Formalism.IndefR.Eqv.UI.brg fr '' (γ • t) =
        (⟨Formalism.IndefR.Eqv.UI.brg fr γ, hto γ⟩ : HFinIn (AF D.host.F) D.sp.cm.sig V.gram) •
          (Formalism.IndefR.Eqv.UI.brg fr '' t) := by
    intro γ t
    ext z
    simp only [Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨Formalism.IndefR.Eqv.UI.brg fr y, ⟨y, hy, rfl⟩, (hsm1 γ y).symm⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨γ • y, ⟨y, hy, rfl⟩, hsm1 γ y⟩
  have hmuV : ∀ t, ZsCovMeas.muV fr μf (Formalism.IndefR.Eqv.UI.brg fr '' t) =
      ZsCovMeas.cdProd fr * (Formalism.IndefR.Eqv.UI.instV fr).muA μf t := by
    intro t
    rw [ZsCovMeas.muV, Measure.smul_apply, smul_eq_mul]
    congr 1
    refine ((Formalism.IndefR.Eqv.UI.brg fr).toHomeomorph.toMeasurableEquiv.map_apply _).trans ?_
    exact congrArg _ (Set.preimage_image_eq _ (Formalism.IndefR.Eqv.UI.brg fr).injective)
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  · exact ((Formalism.IndefR.Eqv.UI.brg fr).toHomeomorph.measurableEmbedding.measurableSet_image.2 hsm).nullMeasurableSet
  · have hc := hs.ae_covers
    have h2 : ∀ᵐ z ∂(((Formalism.IndefR.Eqv.UI.instV fr).muA μf).map (Formalism.IndefR.Eqv.UI.brg fr)),
        ∃ g : HFinIn (AF D.host.F) D.sp.cm.sig V.gram, g • z ∈ Formalism.IndefR.Eqv.UI.brg fr '' s := by
      refine ((Formalism.IndefR.Eqv.UI.brg fr).toHomeomorph.measurableEmbedding.ae_map_iff).2 ?_
      filter_upwards [hc] with x hx
      obtain ⟨γ, hγ⟩ := hx
      exact ⟨⟨Formalism.IndefR.Eqv.UI.brg fr γ, hto γ⟩, γ • x, hγ, hsm1 γ x⟩
    exact Measure.ae_smul_measure h2 _
  · intro g hg
    obtain ⟨γ, hγ⟩ := hfrom g
    have hγ1 : γ ≠ 1 := by
      intro h1
      apply hg
      apply Subtype.ext
      rw [← hγ, h1]
      first | rfl | (simp; rfl)
    have hd : (Formalism.IndefR.Eqv.UI.instV fr).muA μf (γ • s ∩ (1 : rr_GF (Formalism.IndefR.Eqv.UI.instV fr)) • s) = 0 :=
      hs.aedisjoint hγ1
    rw [one_smul] at hd
    have hg' : g = ⟨Formalism.IndefR.Eqv.UI.brg fr γ, hto γ⟩ := Subtype.ext hγ.symm
    rw [hg', ← hsmul]
    show ZsCovMeas.muV fr μf (Formalism.IndefR.Eqv.UI.brg fr '' (γ • s) ∩ Formalism.IndefR.Eqv.UI.brg fr '' s) = 0
    rw [← Set.image_inter (Formalism.IndefR.Eqv.UI.brg fr).injective, hmuV, hd, mul_zero]
  · intro g
    exact (measurePreserving_mul_left (ZsCovMeas.muV fr μf) (g.1 : GA D V)).quasiMeasurePreserving

theorem covolSum_of_tie (X : Formalism.MainNotions.BridgeLemma.CData) (hX : X.I = Formalism.IndefR.Eqv.UI.instV fr)
    (hΛ : fr.Λ = Formalism.IndefR.Eqv.UI.Lv D V) {P Q : ℕ} (hV : V.SigOK) (hs : ∀ τ, V.sig τ = (P, Q))
    (hε : ∀ v, (Finset.univ.filter fun i => fr.ε v i = true).card = P)
    (hT : VolTie D) (hI : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep D) (hC : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D V.rank)
    (hcd : cdScaleTie D) (hCG : ∀ v, Formalism.MainNotions.S.Gauge.CdGauge D V.rank (fr.ε v))
    (hVU : Formalism.MainNotions.S.Gauge.VolUn V.rank) :
    Formalism.MainNotions.FundamentalDomainUnfolding.CovolSum X (IwasawaCovolume.covolR X) := by
  have key : ∀ (ys : Finset (Formalism.IndefR.Eqv.UI.instV fr).Gf)
      (Dy : (Formalism.IndefR.Eqv.UI.instV fr).Gf → Set (Formalism.IndefR.Eqv.UI.instV fr).Ginf),
      Formalism.MainNotions.FundamentalDomainUnfolding.ClassReps (Formalism.IndefR.Eqv.UI.instV fr) ys →
      (∀ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.IsFundInf (Formalism.IndefR.Eqv.UI.instV fr) y
        (Formalism.MainNotions.FundamentalDomainUnfolding.muInf (Formalism.IndefR.Eqv.UI.instV fr)) (Dy y)) →
      ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf (Formalism.IndefR.Eqv.UI.instV fr) (Dy y) =
        ENNReal.ofReal ((Formalism.IndefR.Eqv.UI.instV fr).gaugeU *
          (IwasawaCovolume.volgU V.rank ^ Fintype.card (InfinitePlace D.host.F) * massI D V.rank)) := by
    intro ys Dy hys hD
    obtain ⟨g1, g2, g3⟩ := Formalism.IndefR.Eqv.gf_facts fr
    obtain ⟨k1, k2, k3, k4, k5⟩ := Formalism.IndefR.Eqv.ga_facts D V
    set ν : Measure (Formalism.IndefR.Eqv.UI.instV fr).Gf := Measure.haar with hν
    have hKc : IsCompact (Formalism.IndefR.Eqv.UI.instV fr).Kset := PI.WAU.Cpt.isCompact_Kset (Formalism.IndefR.Eqv.UI.instV fr)
    have hKo : IsOpen (Formalism.IndefR.Eqv.UI.instV fr).Kset := PI.WAU.kset_open (Formalism.IndefR.Eqv.UI.instV fr)
    have hk0 : ν (Formalism.IndefR.Eqv.UI.instV fr).Kset ≠ 0 := (hKo.measure_pos ν ⟨1, UnfoldingVolume.kone (Formalism.IndefR.Eqv.UI.instV fr)⟩).ne'
    have hkt : ν (Formalism.IndefR.Eqv.UI.instV fr).Kset ≠ ⊤ := hKc.measure_lt_top.ne
    set μf : Measure (Formalism.IndefR.Eqv.UI.instV fr).Gf := (ν (Formalism.IndefR.Eqv.UI.instV fr).Kset)⁻¹ • ν with hμfdef
    have hμf : μf.IsHaarMeasure :=
      Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr hkt) (ENNReal.inv_ne_top.mpr hk0)
    have hK1 : μf (Formalism.IndefR.Eqv.UI.instV fr).Kset = 1 := by
      rw [hμfdef, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hk0 hkt]

    have hg : ∀ v, (D.s.cdScale V.rank (fr.ε v) : ℝ) * Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) *
        IwasawaCovolume.volgU V.rank = 1 := by
      intro v
      have h := hCG v
      unfold Formalism.MainNotions.S.Gauge.CdGauge at h
      rw [hVU, ← ZsCovSum.volgU_eq_Icc] at h
      exact h
    have hc0 : ∀ v, D.s.cdScale V.rank (fr.ε v) ≠ 0 := by
      intro v h0
      have h := hg v
      rw [h0] at h
      simp at h
    have hw := IwasawaCovolume.volgU_pos V.rank
    have hgpos : ∀ v, 0 < Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) := by
      intro v
      have h : ((D.s.cdScale V.rank (fr.ε v) : ℝ) * IwasawaCovolume.volgU V.rank) * Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) = 1 := by
        rw [← hg v]; ring
      exact pos_of_mul_pos_right (h ▸ one_pos) (mul_nonneg (D.s.cdScale V.rank (fr.ε v)).2 hw.le)

    have hn : P + Q = V.rank := by
      have := Formalism.BasicNotions.sig_sum V hV D.host.φ₀
      rw [hs] at this
      exact this
    choose e h1 h2 using fun v => ZsCovSum.blockEquiv (fr.ε v) (hε v) hn

    have hvol := ZsCovMeas.isVolMeas_muV fr hcd hΛ e h1 h2 hc0 μf hK1
    have hFD := UnfoldingVolume.fd_isFund (Formalism.IndefR.Eqv.UI.instV fr) μf ys hys Dy hD
    have hF := isFund_image fr hc0 μf (ZsCovSum.FD_meas (Formalism.IndefR.Eqv.UI.instV fr) ys Dy hD) hFD
    have htie : ZsCovMeas.muV fr μf (Formalism.IndefR.Eqv.UI.brg fr '' UnfoldingVolume.FD (Formalism.IndefR.Eqv.UI.instV fr) ys Dy) =
        ENNReal.ofReal (D.vol V) := ((hT V P Q hV hs).2 _ hvol).2 _ hF
    have hvm := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.vol_eq_mass_of_indep D V.rank hT hI hC V P Q hV hs rfl
    have hmu : ZsCovMeas.muV fr μf (Formalism.IndefR.Eqv.UI.brg fr '' UnfoldingVolume.FD (Formalism.IndefR.Eqv.UI.instV fr) ys Dy) =
        ZsCovMeas.cdProd fr * ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf (Formalism.IndefR.Eqv.UI.instV fr) (Dy y) := by
      rw [ZsCovMeas.muV, Measure.smul_apply, smul_eq_mul]
      congr 1
      refine ((Formalism.IndefR.Eqv.UI.brg fr).toHomeomorph.toMeasurableEquiv.map_apply _).trans ?_
      refine (congrArg _ (Set.preimage_image_eq _ (Formalism.IndefR.Eqv.UI.brg fr).injective)).trans ?_
      rw [ZsCovSum.muA_FD (Formalism.IndefR.Eqv.UI.instV fr) μf ys hys Dy hD, hK1, one_mul]
    rw [hmu, hvm] at htie

    have hm0 : 0 ≤ massI D V.rank := hvm ▸ (D.vol_pos V).le
    have hG : (Formalism.IndefR.Eqv.UI.instV fr).gaugeU * IwasawaCovolume.volgU V.rank ^ Fintype.card (InfinitePlace D.host.F) =
        ∏ v : InfinitePlace D.host.F, (Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) * IwasawaCovolume.volgU V.rank) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      rfl
    have hG0 : ∀ v : InfinitePlace D.host.F, 0 ≤ Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) * IwasawaCovolume.volgU V.rank :=
      fun v => (mul_pos (hgpos v) hw).le
    have hone : ZsCovMeas.cdProd fr * ENNReal.ofReal
        (∏ v : InfinitePlace D.host.F, (Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) * IwasawaCovolume.volgU V.rank)) = 1 := by
      rw [ENNReal.ofReal_prod_of_nonneg fun v _ => hG0 v, ZsCovMeas.cdProd, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _), ← mul_assoc, hg v,
        ENNReal.ofReal_one]
    calc ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf (Formalism.IndefR.Eqv.UI.instV fr) (Dy y)
        = (ZsCovMeas.cdProd fr * ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf (Formalism.IndefR.Eqv.UI.instV fr) (Dy y)) *
            ENNReal.ofReal (∏ v : InfinitePlace D.host.F,
              (Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) * IwasawaCovolume.volgU V.rank)) := by
          rw [mul_comm (ZsCovMeas.cdProd fr), mul_assoc, hone, mul_one]
      _ = ENNReal.ofReal (massI D V.rank) * ENNReal.ofReal ((Formalism.IndefR.Eqv.UI.instV fr).gaugeU *
            IwasawaCovolume.volgU V.rank ^ Fintype.card (InfinitePlace D.host.F)) := by
          rw [htie, hG]
      _ = ENNReal.ofReal ((Formalism.IndefR.Eqv.UI.instV fr).gaugeU * (IwasawaCovolume.volgU V.rank ^ Fintype.card (InfinitePlace D.host.F) *
            massI D V.rank)) := by
          rw [← ENNReal.ofReal_mul hm0]
          congr 1
          ring
  have gen : ∀ J : AutInst, J = Formalism.IndefR.Eqv.UI.instV fr → ∀ (ys : Finset J.Gf) (Dy : J.Gf → Set J.Ginf),
      Formalism.MainNotions.FundamentalDomainUnfolding.ClassReps J ys → (∀ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.IsFundInf J y (Formalism.MainNotions.FundamentalDomainUnfolding.muInf J) (Dy y)) →
      ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf J (Dy y) ≤ ENNReal.ofReal (J.gaugeU * (IwasawaCovolume.volgU J.n ^
        Fintype.card (InfinitePlace J.F) * Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm J.E J.n) (Formalism.MainNotions.StandardLattice.stdLat J.E J.n))) := by
    rintro J rfl ys Dy hys hD
    exact (key ys Dy hys hD).le
  unfold Formalism.MainNotions.FundamentalDomainUnfolding.CovolSum IwasawaCovolume.covolR
  exact gen X.I hX

end Formalism.L2.S.S7.ZsCovTie
end
end

section
noncomputable section

namespace Formalism.L2.S.S7.ZsCovR

open NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.IwasawaCovolume

theorem volgU_le (N : ℕ) : volgU N ≤ 7 ^ (N * N) := by
  unfold volgU
  calc ∏ i ∈ Finset.range N, (2 * Real.pi) ^ (i + 1) / ((i.factorial : ℕ) : ℝ)
      ≤ ∏ _i ∈ Finset.range N, (7 : ℝ) ^ N := by
        refine Finset.prod_le_prod (fun i _ => by positivity) fun i hi => ?_
        have hi' : i + 1 ≤ N := Finset.mem_range.1 hi
        have hf : (1 : ℝ) ≤ ((i.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero i)
        have h2pi : 2 * Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
        calc (2 * Real.pi) ^ (i + 1) / ((i.factorial : ℕ) : ℝ) ≤ (2 * Real.pi) ^ (i + 1) :=
              div_le_self (by positivity) hf
          _ ≤ 7 ^ (i + 1) := pow_le_pow_left₀ (by positivity) h2pi _
          _ ≤ 7 ^ N := pow_le_pow_right₀ (by norm_num) hi'
    _ = (7 : ℝ) ^ (N * N) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]

theorem mass_chain (hMR : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.MassRatioStd) (E : Type) [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (n : ℕ) (hn : 2 ≤ n) :
    Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) =
      Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E 2) (Formalism.MainNotions.StandardLattice.stdLat E 2) *
        ∏ M ∈ Finset.Icc 3 n, Formalism.HermitianLatticesTheory.massRatioRightSide E M := by
  induction n, hn using Nat.le_induction with
  | base => rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty, mul_one]
  | succ n hn ih =>
    have h3 : 3 ≤ n + 1 := by omega
    have hr := hMR E hE (n + 1) h3
    replace hr : Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E (n + 1)) (Formalism.MainNotions.StandardLattice.stdLat E (n + 1)) /
        Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) = Formalism.HermitianLatticesTheory.massRatioRightSide E (n + 1) := hr
    have hpos := Formalism.MainNotions.MassRatioBoundPower.massRatio_pos (K := E) h3
    have hne : Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) ≠ 0 := by
      intro h0; rw [h0, div_zero] at hr; exact hpos.ne' hr.symm
    rw [div_eq_iff hne] at hr
    rw [hr, ih, Finset.prod_Icc_succ_top (by omega)]
    ring

theorem mass_nonneg (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) :
    0 ≤ Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) := by
  unfold Formalism.HermitianLatticesTheory.mass
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => by positivity
  · exact le_rfl

theorem fDeg_E (I : AutInst) : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces I.E
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank I.E
  rw [IsTotallyComplex.nrRealPlaces_eq_zero] at h1 h2
  rw [Formalism.MainNotions.BridgeLevelGen.finrank_E] at h2
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem card_F (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have : IsTotallyReal I.F := I.cm.totReal
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [IsTotallyReal.nrComplexPlaces_eq_zero] at h2
  simpa [AutInst.f] using h2

theorem two_vInv_E (I : AutInst) : 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd := by
  unfold Formalism.HermitianLatticesTheory.vInv AutInst.rd
  rw [fDeg_E]; ring

def CasimirBaseCount : ℕ := 27 + Formalism.MainNotions.MassRatioBoundPower.cZ

theorem covolR_nonneg (X : CData) : 0 ≤ covolR X :=
  mul_nonneg (pow_nonneg (volgU_pos _).le _) (mass_nonneg _ _)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem covolR_le (hMR : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.MassRatioStd) (X : CData) {n₀ : ℕ} {A : ℝ}
    (hX : X.HypB n₀ A) (hn2 : 2 ≤ X.I.n) :
    covolR X ≤ cn_Y X ^ ((CasimirBaseCount : ℝ) * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) := by
  unfold covolR
  rw [card_F]
  obtain ⟨hset, -, -⟩ := hX
  have hb : (2 : ℝ) ≤ X.b := hset.2.2.1
  have hg : 1 ≤ X.g := hset.2.2.2.2.2.2.2.1
  have hf1 : 1 ≤ X.I.f := Formalism.MainNotions.BridgeVolRatio.one_le_f X.I
  have hrd : 1 ≤ X.I.rd := Formalism.MainNotions.BridgeVolRatio.one_le_rd X.I
  have hE : Formalism.HermitianLatticesTheory.IsCMUnram X.I.E := X.I.cm.cmUnram
  have hd : Module.finrank ℚ X.I.E ≤ 2 * Formalism.HermitianLatticesTheory.fDeg X.I.E := by
    rw [Formalism.MainNotions.BridgeLevelGen.finrank_E, fDeg_E]
  have hchain := mass_chain hMR X.I.E hE X.I.n hn2
  have hvI := two_vInv_E X.I
  have hfD := fDeg_E X.I
  set n := X.I.n with hndef
  set f := X.I.f with hfdef
  set Y := cn_Y X with hY
  have hYdef : Y = (n : ℝ) * f * X.I.rd * (X.g : ℝ) * X.b := rfl
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hf1' : (1 : ℝ) ≤ f := by exact_mod_cast hf1
  have hg1 : (1 : ℝ) ≤ X.g := by exact_mod_cast hg
  have hb1 : (1 : ℝ) ≤ X.b := by linarith
  have hnf : (1 : ℝ) ≤ (n : ℝ) * f := one_le_mul_of_one_le_of_one_le hn1 hf1'
  have hnfr : (1 : ℝ) ≤ (n : ℝ) * f * X.I.rd := one_le_mul_of_one_le_of_one_le hnf hrd
  have hnfrg : (1 : ℝ) ≤ (n : ℝ) * f * X.I.rd * X.g := one_le_mul_of_one_le_of_one_le hnfr hg1
  have hY1' : (n : ℝ) * f * X.I.rd * X.g ≤ Y := by
    rw [hYdef]; exact le_mul_of_one_le_right (by linarith) hb1
  have hY2 : 2 ≤ Y := by rw [hYdef]; nlinarith
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hrdY : X.I.rd ≤ Y := by
    calc X.I.rd ≤ (n : ℝ) * f * X.I.rd := le_mul_of_one_le_left (by linarith) hnf
      _ ≤ (n : ℝ) * f * X.I.rd * X.g := le_mul_of_one_le_right (by linarith) hg1
      _ ≤ Y := hY1'
  have hnY : (n : ℝ) ≤ Y := by
    calc (n : ℝ) ≤ (n : ℝ) * f := le_mul_of_one_le_right (by linarith) hf1'
      _ ≤ (n : ℝ) * f * X.I.rd := le_mul_of_one_le_right (by linarith) hrd
      _ ≤ (n : ℝ) * f * X.I.rd * X.g := le_mul_of_one_le_right (by linarith) hg1
      _ ≤ Y := hY1'
  have hfY : (f : ℝ) ≤ Y := by
    calc (f : ℝ) ≤ (n : ℝ) * f := le_mul_of_one_le_left (by linarith) hn1
      _ ≤ (n : ℝ) * f * X.I.rd := le_mul_of_one_le_right (by linarith) hrd
      _ ≤ (n : ℝ) * f * X.I.rd * X.g := le_mul_of_one_le_right (by linarith) hg1
      _ ≤ Y := hY1'

  have hv : 2 * Formalism.HermitianLatticesTheory.vInv X.I.E ≤ Y := by rw [hvI]; exact hrdY
  have hfDY : (Formalism.HermitianLatticesTheory.fDeg X.I.E : ℝ) ≤ Y := by rw [hfD]; exact hfY
  have hprod := Formalism.MainNotions.MassRatioBoundPower.prod_massRatio_le (K := X.I.E) hd n hY2 hnY hv
  rw [hfD] at hprod
  have hmass2 := Formalism.MainNotions.BridgeLemV.mass_two_le_pow hE hY2 hv hfDY
  rw [hfD] at hmass2
  have h8 : (8 : ℝ) ≤ Y ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hY2 3
    norm_num at this
    linarith
  have hvol : volgU n ^ f ≤ Y ^ (3 * (n * n) * f) := by
    calc volgU n ^ f ≤ ((7 : ℝ) ^ (n * n)) ^ f := pow_le_pow_left₀ (volgU_pos n).le (volgU_le n) f
      _ ≤ ((Y ^ 3) ^ (n * n)) ^ f := by
          gcongr
          linarith
      _ = Y ^ (3 * (n * n) * f) := by rw [← pow_mul, ← pow_mul]; ring_nf

  have hpn : 0 ≤ ∏ M ∈ Finset.Icc 3 n, Formalism.HermitianLatticesTheory.massRatioRightSide X.I.E M :=
    Finset.prod_nonneg fun M hM => Formalism.MainNotions.MassRatioBoundPower.mass_ratio_rhs_nonneg (Finset.mem_Icc.1 hM).1
  have hmn : Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm X.I.E n) (Formalism.MainNotions.StandardLattice.stdLat X.I.E n) ≤
      Y ^ (22 * f) * Y ^ ((2 * n + Formalism.MainNotions.MassRatioBoundPower.cZ) * n * f) := by
    rw [hchain]
    exact mul_le_mul hmass2 hprod hpn (by positivity)
  have hexp : 3 * (n * n) * f + (22 * f + (2 * n + Formalism.MainNotions.MassRatioBoundPower.cZ) * n * f) ≤ CasimirBaseCount * n ^ 2 * f := by
    have e1 : 3 * (n * n) * f + (22 * f + (2 * n + Formalism.MainNotions.MassRatioBoundPower.cZ) * n * f) =
        5 * (n * n * f) + 22 * f + Formalism.MainNotions.MassRatioBoundPower.cZ * (n * f) := by ring
    have e2 : CasimirBaseCount * n ^ 2 * f = 27 * (n * n * f) + Formalism.MainNotions.MassRatioBoundPower.cZ * (n * n * f) := by
      unfold CasimirBaseCount; ring
    have h1 : f ≤ n * n * f := Nat.le_mul_of_pos_left f (Nat.mul_pos (by omega) (by omega))
    have h2 : n * f ≤ n * n * f := Nat.mul_le_mul_right f (Nat.le_mul_of_pos_left n (by omega))
    have h3 := Nat.mul_le_mul_left Formalism.MainNotions.MassRatioBoundPower.cZ h2
    rw [e1, e2]
    linarith
  calc volgU n ^ f * Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm X.I.E n) (Formalism.MainNotions.StandardLattice.stdLat X.I.E n)
      ≤ Y ^ (3 * (n * n) * f) * (Y ^ (22 * f) * Y ^ ((2 * n + Formalism.MainNotions.MassRatioBoundPower.cZ) * n * f)) :=
        mul_le_mul hvol hmn (mass_nonneg _ _) (by positivity)
    _ = Y ^ (3 * (n * n) * f + (22 * f + (2 * n + Formalism.MainNotions.MassRatioBoundPower.cZ) * n * f)) := by
        rw [← pow_add, ← pow_add]
    _ ≤ Y ^ (CasimirBaseCount * n ^ 2 * f) := pow_le_pow_right₀ hY1 hexp
    _ = Y ^ ((CasimirBaseCount : ℝ) * (n : ℝ) ^ 2 * (f : ℝ)) := by
        rw [← Real.rpow_natCast]
        congr 1
        push_cast
        ring

end Formalism.L2.S.S7.ZsCovR

end
end

section
noncomputable section

open MeasureTheory Set Topology Formalism.MainNotions.S Formalism.MainNotions.FundamentalDomainUnfolding

namespace Formalism.L2.S.S7.FundamentalDomainSubgroups

variable (I : AutInst)

def kSub : Subgroup I.Gf := (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

def gamSub (y : I.Gf) : Subgroup I.GA where
  carrier := GamY I y
  one_mem' := ⟨(Formalism.MainNotions.LeviCoordinates.rr_GF I).one_mem, by
    show y⁻¹ * 1 * y ∈ I.Kset
    rw [mul_one, inv_mul_cancel]
    exact (kSub I).one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Formalism.MainNotions.LeviCoordinates.rr_GF I).mul_mem ha hb, ?_⟩
    have e : y⁻¹ * (a * b).2 * y = (y⁻¹ * a.2 * y) * (y⁻¹ * b.2 * y) := by
      rw [Prod.snd_mul]; group
    rw [e]
    exact (kSub I).mul_mem ha' hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Formalism.MainNotions.LeviCoordinates.rr_GF I).inv_mem ha, ?_⟩
    have e : y⁻¹ * a⁻¹.2 * y = (y⁻¹ * a.2 * y)⁻¹ := by
      rw [Prod.snd_inv]; group
    rw [e]
    exact (kSub I).inv_mem ha'

def gamInf (y : I.Gf) : Subgroup I.Ginf := (gamSub I y).map (MonoidHom.fst I.Ginf I.Gf)

theorem eq_one_of_fst (γ : I.GA) (hγ : γ ∈ I.GFset) (h1 : γ.1 = 1) : γ = 1 := by
  obtain ⟨M, -, hv, hf⟩ := hγ
  obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace I.F) := inferInstance
  have hP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hP' : (I.P v)⁻¹ * I.P v = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have h := hv v
  have hu : uMat (γ.1 v) = 1 := by rw [h1]; rfl
  rw [hu] at h
  have hMφ : (M : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
    calc (M : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)
        = I.P v * ((I.P v)⁻¹ * (M : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) * (I.P v)⁻¹ := by
          simp only [Matrix.mul_assoc, hP, Matrix.mul_one]
          rw [← Matrix.mul_assoc, hP, Matrix.one_mul]
      _ = 1 := by rw [← h, Matrix.mul_one, hP]
  have hM : (M : Matrix (Fin I.n) (Fin I.n) I.E) = 1 := by
    ext i j
    have := congrFun (congrFun hMφ i) j
    rw [Matrix.map_apply] at this
    apply (I.φ v).injective
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have hf1 : I.fmat γ.2 = 1 := by
    rw [hf, hM, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Prod.ext h1 ?_
  apply Subtype.ext
  apply Units.ext
  exact hf1

theorem gamInf_discrete (y : I.Gf) : DiscreteTopology (gamInf I y) := by
  haveI : T2Space I.Gf := Formalism.L2.SG.Pf.finite_adeles_group_t2 I
  haveI hD : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF I) := Formalism.L2.SG.Pf.gf_discrete I
  have hS : IsClosed ((Formalism.MainNotions.LeviCoordinates.rr_GF I : Subgroup I.GA) : Set I.GA) := Subgroup.isClosed_of_discrete
  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : I.Ginf)
  set Cf : Set I.Gf := (fun k => y * k * y⁻¹) '' I.Kset with hCfdef
  have hK : IsCompact Cf := (PI.WAU.maximal_compact_isCompact I).image (by fun_prop)
  have hC : IsCompact (C ×ˢ Cf) := hCc.prod hK
  set Fs : Set I.GA := ((Formalism.MainNotions.LeviCoordinates.rr_GF I : Subgroup I.GA) : Set I.GA) ∩ C ×ˢ Cf with hFsdef
  have hDs : DiscreteTopology Fs := DiscreteTopology.of_subset hD inter_subset_left
  have hFin : Fs.Finite := IsCompact.finite (hC.inter_left hS)
    (by first | exact ⟨hDs⟩ | exact hDs | exact isDiscrete_iff_discreteTopology.2 hDs)
  set T : Set I.Ginf := ((fun γ : I.GA => γ.1) '' Fs) \ {1} with hTdef
  have hT : IsClosed T := ((hFin.image _).subset diff_subset).isClosed
  rw [discreteTopology_iff_isOpen_singleton_one]
  refine isOpen_induced_iff.2 ⟨interior C \ T, isOpen_interior.sdiff hT, ?_⟩
  ext ⟨h, hh⟩
  simp only [mem_preimage, mem_diff, mem_singleton_iff]
  constructor
  · rintro ⟨hint, hnT⟩
    obtain ⟨γ, ⟨hγF, hγK⟩, rfl⟩ := Subgroup.mem_map.1 hh
    apply Subtype.ext
    by_contra hne
    apply hnT
    have hFs : γ ∈ Fs := ⟨hγF, interior_subset hint, ⟨y⁻¹ * γ.2 * y, hγK, (by group)⟩⟩
    exact ⟨⟨γ, hFs, rfl⟩, hne⟩
  · intro h1
    have e : h = 1 := congrArg Subtype.val h1
    subst e
    exact ⟨mem_interior_iff_mem_nhds.2 hC1, fun hT1 => hT1.2 rfl⟩

theorem FundInfExists_holds : FundInfExists := by
  intro I y
  haveI := gamInf_discrete I y
  obtain ⟨F, hFm, hcov, huniq⟩ := Formalism.L2.SG.Pf.exists_strictFund (gamInf I y)
  refine ⟨F, hFm, fun z => ?_, fun γ hγ hne => ?_⟩
  · obtain ⟨s, hs, hsz⟩ := hcov z
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hs
    exact ⟨γ, hγ, hsz⟩
  · have e : (fun z => γ.1 * z) '' F ∩ F = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨x, hx, rfl⟩ hw
      have h1 := huniq x hx γ.1 (Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩) hw
      exact hne (eq_one_of_fst I γ hγ.1 h1)
    rw [e, measure_empty]

end Formalism.L2.S.S7.FundamentalDomainSubgroups
end
end

section
namespace Formalism.L2.S.S7.UnfoldingBorel

theorem UnfoldVol_of_borel (hB : Formalism.L2.SG.LitS.BorelClassFinite) : Formalism.MainNotions.FundamentalDomainUnfolding.UnfoldVol :=
  Formalism.L2.S.S7.UnfoldingVolume.UnfoldVol_holds hB Formalism.L2.S.S7.FundamentalDomainSubgroups.FundInfExists_holds

end Formalism.L2.S.S7.UnfoldingBorel
end

section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.StandardLattice

namespace Formalism.L2.S.S7.CovolumeGaugeFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem covolume_gauge_of_frames (hB : Formalism.L2.SG.LitS.BorelClassFinite)
    (hGD : ∀ (n : ℕ) (ε : Fin n → Bool), Gauge.GaugeDens ε) (hMR : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.MassRatioStd)
    (hVU : ∀ n, Gauge.VolUn n) :
    ∀ (X : CData) (n₀ : ℕ) (A C cb : ℝ), 8 ≤ n₀ → X.HypC n₀ A C cb →
      (∃ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (P Q : ℕ),
        X.I = Formalism.IndefR.Eqv.UI.instV fr ∧ fr.Λ = Formalism.IndefR.Eqv.UI.Lv D V ∧
        (∀ v, (Finset.univ.filter fun i => fr.ε v i = true).card = P) ∧ V.SigOK ∧ (∀ τ, V.sig τ = (P, Q)) ∧
        VolTie D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D V.rank ∧ cdScaleTie D) →
      Formalism.MainNotions.BridgeVolRatio.GaugeVolumeBoundVar X (ZsCovR.CasimirBaseCount : ℝ) := by
  intro X n₀ A C cb hn hX hT
  obtain ⟨D, V, fr, P, Q, hXI, hΛ, hε, hV, hs, hTie, hI, hC, hcd⟩ := hT
  exact Formalism.MainNotions.FundamentalDomainUnfolding.gauge_volume_bound_of_parts (Formalism.L2.S.S7.UnfoldingBorel.UnfoldVol_of_borel hB) hGD X hX.1
    (ZsCovR.covolR_nonneg X)
    (ZsCovTie.covolSum_of_tie fr X hXI hΛ hV hs hε hTie hI hC hcd
      (fun v => Formalism.MainNotions.S.Gauge.complex_gauge_normalization D hcd _ _) (hVU _))
    (ZsCovR.covolR_le hMR X hX.1 (by have := hX.1.1.1; omega))

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem volRatio_of_tiesFr (hB : Formalism.L2.SG.LitS.BorelClassFinite)
    (hGD : ∀ (n : ℕ) (ε : Fin n → Bool), Gauge.GaugeDens ε) (hMR : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.MassRatioStd)
    (hVU : ∀ n, Gauge.VolUn n) :
    ∃ Cv : ℝ, 1 ≤ Cv ∧ ∀ (X : CData) (n₀ : ℕ) (A C cb : ℝ), 8 ≤ n₀ → X.HypC n₀ A C cb → 1 ≤ X.qq →
      (∃ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (P Q : ℕ),
        X.I = Formalism.IndefR.Eqv.UI.instV fr ∧ fr.Λ = Formalism.IndefR.Eqv.UI.Lv D V ∧
        (∀ v, (Finset.univ.filter fun i => fr.ε v i = true).card = P) ∧ V.SigOK ∧ (∀ τ, V.sig τ = (P, Q)) ∧
        VolTie D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D V.rank ∧ cdScaleTie D) →
      Formalism.MainNotions.BridgeDeepQ.VolRatio X Cv :=
  ⟨(ZsCovR.CasimirBaseCount : ℝ) + 2, by have : (0 : ℝ) ≤ ZsCovR.CasimirBaseCount := Nat.cast_nonneg _; linarith,
    fun X n₀ A C cb hn hX _ hT => Formalism.MainNotions.BridgeVolRatio.vol_ratio_of_gauge_volume hGD X (le_trans (by norm_num) hn) hX.1
      (covolume_gauge_of_frames hB hGD hMR hVU X n₀ A C cb hn hX hT)⟩

end Formalism.L2.S.S7.CovolumeGaugeFrames
end
end
