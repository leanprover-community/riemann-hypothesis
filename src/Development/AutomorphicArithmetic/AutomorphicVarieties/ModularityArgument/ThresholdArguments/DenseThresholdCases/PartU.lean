import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.IrrComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.TypePlain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2IsoL
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2IsoQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Sph
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Unr
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LNotMemBasePrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtOfForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsUnramifiedAtTotallyRealOfInertiaLeRestrictionR
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsDescentToLevelGroupOfUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConjInertiaDiagonalOfIsTypeWD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CLocConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuWrap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatFrobT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.HasHTOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.PlainTorOfPs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicTensorInductionOfLocalPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
open private ex_emb from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HodgeTateWeightsOfLocalGlobal
namespace UpperTheory.V.Z.Ord.AtLOrdinary
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem plainTor_of_ps [CharZero k] {n : ℕ} (σ : SmIrr (GL (Fin n) k)) (ω : Fin n → kˣ →* ℂˣ) (hs : ∀ i, IsSmoothChar (ω i))
    (hd : ∀ i j, i ≠ j → ∃ y : Uo k, ω i y ≠ ω j y) (e : σ.ρ.Equiv (PS ω)) :
    GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  have hμ : ∀ i, IsSmoothChar (ω i * absPow k (((n : ℂ) - 1) / 2)) := fun i => (hs i).mul (isSmoothChar_absPow _)
  have hsup := hasSupport_of_isSubquotient_prinSeries k n _ hμ ⟨_, σ.ρ, σ.smooth, σ.irred⟩
    (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective)
  refine ⟨_, hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), fun y hy => ?_, fun y hy z hz e' => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e'
    by_cases hij : i = j
    · subst hij
      have h1 : absPow k ((1 : ℝ) : ℂ) = 1 := by
        have := mul_left_cancel (a := ω i * absPow k (((n : ℂ) - 1) / 2)) (b := 1) (c := absPow k 1) (by simpa using e')
        simpa using this.symm
      exact one_ne_zero (absPow_ofReal_eq_one.1 h1)
    · obtain ⟨y, hy⟩ := hd i j hij
      have h1 := DFunLike.congr_fun e' (y : kˣ)
      simp only [MonoidHom.mul_apply, isUnram_absPow k 1 (y : kˣ) y.2, isUnram_absPow k (((n : ℂ) - 1) / 2) (y : kˣ) y.2, mul_one] at h1
      exact hy h1
end UpperTheory.V.Z.Ord.AtLOrdinary
open UpperTheory.V.Z.Ord.AtLOrdinary in
theorem UpperTheory.V.Z.Ord.at_l_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → AtLOf := by
  intro _ l _ L Ω _ _ _ _ _ ι n A w h r HT τ lam hHT hLG hw ω hs hd ⟨e⟩ rc hrc _ O _ _ _ Bw hj
  haveI : CharZero (w.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective
  have hP := plainTor_of_ps τ ω hs hd e
  have hG : Win.Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc n τ hP
  obtain ⟨h1, h2⟩ := hHT hP A h O Bw hj
  refine ⟨h1, fun t LL' τ' hτ => ?_, fun s => ?_⟩
  · obtain ⟨j, rfl⟩ := ex_emb h Bw hj t LL' τ' hτ
    have e : HT (j.1.comp (algebraMap L _)) =
        Finset.univ.val.map fun i => htW lam i (j.1.comp (algebraMap L _)) := by
      refine Multiset.map_injective (f := fun k : ℤ => (k : ℂ)) Int.cast_injective ?_
      rw [hw j]
      simp only [infOfWeight, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      simp only [htW, lowW, Function.comp_apply, DomWeight.dual]
      push_cast
      ring
    have h3 := h2 _ LL' τ' hτ
    rw [e] at h3
    exact h3
  · rw [((hLG A h rc hrc).2 O Bw hj hG).2]
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.P
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G L Ω →* GL (Fin n) (Qbar l)} {w : Plc L} {τ : SmIrr (GLw n w)} {A : ValuationSubring Ω}
  {HT : (L →+* Qbar l) → Multiset ℤ}
theorem ordinary_at_l_of_local_global_hodge_tate_weights (N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (h : IsPlaceOver A w) (lam : Wt L l n) (_ : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∃ τ, HtGT r HT w τ)
    (k : HtGT r HT w τ) (hL : LocGlobT ι r w τ)
    (hw : ∀ j : W.Emb l w, (HT (j.1.comp (algebraMap L _))).map (fun k : ℤ => (k : ℂ)) =
      (infOfWeight (lam (j.1.comp (algebraMap L _))).dual).map fun z => ((n : ℂ) - 1) / 2 - z) :
    Ord.AtLT ι h (r.comp (Dec (F := L) A).subtype) lam τ := _root_.UpperTheory.V.Z.Ord.at_l_of_literal_automorphy_n N l L Ω ι n A w h r HT τ lam k hL hw
end UpperTheory.V.Z.Desc.P
end
end
end

section
noncomputable abbrev UpperTheory.V.Af.Hypotheses'.exists_reciprocity_dense := @UpperTheory.V.Z.Win.exists_rec_alt_alt_alt
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z.Desc.P in
theorem UpperTheory.V.Z.Desc.P.partX_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∃ Y : (hset Q τ₀).PartAltAlt ι lam ξ, (Y.Y = YOf Q ι τ₀ e ξ σ ∧ _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam Y.r ∧ (∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ) ∧ (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → _root_.UpperTheory.V.Z.Win.LocGlobT ι (Y.r.comp V.pr) w τ)) ∧ (Af.IsIrr (Y.r.comp V.pr) →
      ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (Y.r.comp V.pr) π ∧
        (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧
        ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), π.IsLocComp w τ →
          IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) := by
  intro PH l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam d e ξ hb σ hσ hY
  have P := PH.toClassicalTheorems
  have hAx := _root_.UpperTheory.V.Hi.axU_s P.litN l L Ω s n hn V Q c m τ₀
  have hund : ∀ {A : ValuationSubring Ω} {w : Plc L}, IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 (Lp L))) :=
    fun hA y => hA (algebraMap (𝓞 (Lp L)) (𝓞 L) y)
  have hwv : ∀ v, (s.w v).under (𝓞 (Lp L)) = v := fun v =>
    HeightOneSpectrum.ext (Ideal.ext fun y => (hund (s.hw v) y).symm.trans (s.hA v y))
  have hl : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := fun w => by
    rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
    rfl
  have hsp : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∈ V.S' → IsSplitAt w := fun w hw =>
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ hw) w rfl
  have hspS : ∀ v ∈ s.S, IsSplitAt (s.w v) := fun v hv => hsp _ (by rw [hwv]; exact V.sub hv)
  have hspQ : ∀ q, IsSplitAt (Q.wq q) := fun q => hsp _ (by rw [Q.range]; exact Or.inr ⟨q, rfl⟩)
  have hin : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → w.under (𝓞 (Lp L)) ∈ V.S' := fun w hw =>
    V.sub (Or.inl ((hl w).1 hw))
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hunr := partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY
  have hwt := partUR2Wt l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY
  have hex : ∀ w : Plc L, IsSplitAt w → ∃ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧
        (IsUnramU σ w → Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w n)) := fun w hw => by
    obtain ⟨τ, -, h1, h2⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ, hσ⟩ w hw
    refine ⟨τ, h1, fun h => ?_⟩
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (h2.1 h)
    exact ⟨v, h0, fun u hu => by simpa using hv ⟨u, hu⟩⟩
  choose loc hloc hfix using hex
  obtain ⟨R, HT, hRc, hRs, hRu, hW, hLH, hpair, hcusp⟩ :=
    _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH PH L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ
  obtain ⟨ρ, hρc, rfl, hform⟩ := UpperTheory.exists_descent_to_level_group_of_unramified l L Ω s n V c R hRc fun w hw A hA =>
    hRu w (mt (hin w) hw) (hunr w hw) A hA
  have hLG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ := fun w hw τ hτ => (hLH w hw τ hτ).1
  have hHG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Desc.P.HtGT (ρ.comp V.pr) HT w τ := fun w hw τ hτ => (hLH w hw τ hτ).2
  have hall : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∃ τ, _root_.UpperTheory.V.Z.Desc.P.HtGT (ρ.comp V.pr) HT w τ :=
    fun w hw => ⟨_, hHG w (hsp w (hin w hw)) _ (hloc _ (hsp w (hin w hw)))⟩
  have hsat : ∀ w : (hset Q τ₀).Wp, ∃ a : ℕ → ℂ, a 0 = 1 ∧
      (∀ j, ∀ v ∈ fixd (loc w.1 w.2.2).ρ (KO (w.1.adicCompletion L) (Fin n)), sphOp (loc w.1 w.2.2).ρ j v = a j • v) ∧
      ∀ (B : ValuationSubring Ω) (g : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) g →
        (ρ (V.pr g⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = heckePol n (normV w.1) a := fun w => by
    obtain ⟨b, hb'⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results P L n w.1 _).1 (hfix w.1 w.2.2 (hunr _ w.2.1))
    obtain ⟨-, a, h0, h1, h2⟩ := satT L n w.1 _ b hb'
    have hw := mt (hin w.1) w.2.1
    refine ⟨a, h0, h1, fun B g hB hg => ?_⟩
    rw [← h2]
    exact (_root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P L Ω l ι n _ hRc w.1 hw _ b hb'
      (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (hLG w.1 w.2.2 _ (hloc _ _)) hw) B hB).2 g hg
  choose a ha0 ha1 ha2 using hsat
  refine ⟨{ Y := YOf Q ι τ₀ e ξ σ
            le := inf_le_left
            ne := hY
            σl := fun v => loc (s.w v.1) (hspS _ (Or.inl v.2))
            isoL := fun v => partUR2IsoL l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ v _ (hloc _ _)
            σq := fun q => loc (Q.wq q) (hspQ q)
            isoQ := fun q => partUR2IsoQ l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hAx q _ (hloc _ _)
            a := a
            a_zero := ha0
            sph := fun w j => partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hAx w.1 w.2.1 w.2.2 _ (hloc _ _) j _
              (ha1 w j)
            r := ρ
            cont := hρc
            ss := fun M hM => ?_
            frob := ha2
            atL := fun v => _root_.UpperTheory.V.Z.Desc.P.ordinary_at_l_of_local_global_hodge_tate_weights P.litN (s.hw v.1) lam hall (hHG _ (hspS _ (Or.inl v.2)) _ (hloc _ _))
              (hLG _ (hspS _ (Or.inl v.2)) _ (hloc _ _)) fun j => hW _ _ (hwt ⟨v, j⟩)
            atQ := fun q => _root_.UpperTheory.V.Z.Desc.P.lgAwayT (hLG _ (hspQ q) _ (hloc _ _)) (hAx.Q_away q) },
    ⟨rfl, ⟨?_, fun t ht u => ?_, fun hi => ?_, ?_⟩, fun v => hloc _ _, hLG⟩, fun hi => ?_⟩
  · obtain ⟨M', h1, h2⟩ := hRs M fun g => hM (V.pr g)
    refine ⟨M', fun g => ?_, h2⟩
    obtain ⟨g, rfl⟩ := hpr g
    exact h1 g
  · obtain ⟨P', hP'⟩ := hpair s.c s.hc
    exact ⟨P', hform P' hP'⟩
  · have hS : ∀ u : s.St, (u : Plc (Lp L)) ∈ s.S := fun u => Or.inr (Or.inl u.2)
    obtain ⟨rc, hrc⟩ : ∃ rc : IrrGL ((s.w u).adicCompletion L) → WD (s.hw u), _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc := P.exists_reciprocity_dense (s.hw u)
    have hT := _root_.UpperTheory.V.Hi.partUR2Type_alt l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY _ (hτ t ht)
      (fun u => loc (s.w u) (hspS _ (hS u))) (fun u => hloc _ _) u rc hrc
    have hu : ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal := fun h => s.St_l u u.2 (by simpa only [hwv] using (hl _).1 h)
    obtain ⟨g, hg⟩ := UpperTheory.exists_conj_inertia_diagonal_of_isTypeWD l L Ω ι n _ _ (s.hw u) hu (ρ.comp V.pr)
      (fun i => W.pushCh (algebraMap c.O (Qbar l)) ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))) _
      (_root_.UpperTheory.V.Z.Desc.P.woTypeT (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (hLG _ (hspS _ (hS u)) _ (hloc _ _)) hu _ (s.hw u) rc hrc)
        (fun i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp V.pr)) hT) hT
    refine ⟨g, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hx⟩
  · obtain ⟨π, h1, h2, h3, h4, -⟩ := hcusp ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M hM hI => hi.2.2 M hM fun g => by
      obtain ⟨g, rfl⟩ := hpr g
      exact hI g⟩
    exact ⟨π, h1, h2, h3, fun v j => h4 _ _ (hwt ⟨v, j⟩)⟩
  · exact ⟨σ, hσ, hLG, hwt, hunr, fun w hw => ⟨_, hloc w hw⟩, loc _ (hspS _ (Or.inr (Or.inr rfl))), hloc _ _,
      partUR2V0 l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY _ (hloc _ _)⟩
  · obtain ⟨π, h1, h2, h3, -, h5, h6⟩ := hcusp hi
    exact ⟨π, h1, h2, h3, h5, h6⟩
theorem UpperTheory.V.Z.Desc.P.partU_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∃ Y : (hset Q τ₀).PartAltAlt ι lam ξ, Y.Y = YOf Q ι τ₀ e ξ σ ∧ _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam Y.r ∧ (∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → _root_.UpperTheory.V.Z.Win.LocGlobT ι (Y.r.comp V.pr) w τ :=
  fun PH l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam d e ξ hb σ hσ hY =>
    (_root_.UpperTheory.V.Z.Desc.P.partX_alt PH l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ hb σ hσ hY).imp fun _ h => h.1
end
end
