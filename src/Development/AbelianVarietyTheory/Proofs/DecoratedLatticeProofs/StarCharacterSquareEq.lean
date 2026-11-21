import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroElementReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSupportSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselAdaptedTranslateLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffTypePinnedLocalGroups
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws

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
