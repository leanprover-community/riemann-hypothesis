import Formalism.WachLatticeTwists.RealDisplaySplitting.GaloisTheoremWithGenerator
import Formalism.WachLatticeTwists.RealDisplaySplitting.Statement
import Formalism.WachLatticeTwists.RealDisplaySplitting.StatementB
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.SplitF
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveReal
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveRealSecond
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveRealLift
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TopAll
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.IdempotentRankOneAtPoint

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2 Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

set_option maxHeartbeats 8000000 in
theorem realization_basic_form : StatRealF := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum hF cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz HcG F Vo VS Io IS ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD _ _ Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y _ _ _ _ HfW Hf₂
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA Zc clsV H₁ _ _ _ _ Hf₁ gR
    τH DatH bH wH mH hrows hseq hcls hclsV hliftR hH0 hJC hJR
  have hk : ∀ w, Function.Injective (kRow (Dat w) _ (uD w) (huD w)) :=
    fun w => kRowInj O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w)
  have hcycw : ∀ w, IsCycOn ℓ (decs Ek Aw w) (ε.comp (decs Ek Aw w).subtype) :=
    fun w g n ζ h => hcyc g.1 n ζ h
  have hnu : ¬ IsUnit (ℓ : O) := fun h => (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hO.p_mem)) h
  have hKO : ∀ c : Fin (t + 1), c ≠ 0 → Nonempty (blockRestrictedRepresentationType bl ρk c ≃ₗ[O] KO O) :=
    fun c hc => blk_ko bl ρk c (hcard1 c hc)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := hFix
  have key : ∀ w, w ∈ what₂ →
      ∃ (pr : LinearMap.range (kRow (Dat w) _ (uD w) (huD w)) →ₗ[O] H1 (Dat w).ρTl' →ₗ[O] KO O)
      (pair : H1 (Dat w).ρT →ₗ[FractionRing O] H1 (Dat w).ρT' →ₗ[FractionRing O] FractionRing O),
      BKIn (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (qK (Dat w) _ (hk w)) (Dat w).j' pr pair (HfW w) (Hf₂ w)
        ((((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w))) (Fs w) ∧
      InRowRhoNoBK (blockRestrictedRepresentationType bl ρk 0) r χ E (decs Ek Aw w) ε ρ₁ inc π γ
        (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (clsRow (Dat w) (vD w)) pr (Fs w) (Im w) := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hRows w hw
    exact rowRhoReal ℓ O (VT w) (VT' w) Ek Ω (Aw w) a1 R' Tc (blockRestrictedRepresentationType bl ρk 0) r χ E ε T₁ T₂ ρ₁ ρ₂ inc π γ
      (Dat w) (uD w) (huD w) (vD w) (HfW w) (Hf₂ w) (Fs w) (Im w) hO hFr hA (hcycw w) a3 a4 f8 a5 a6 a7 a9
      (f10 w hw) (hk w)
  choose! pr pair hpp using key
  let HcR : ∀ (c : Fin (t + 1)) (w : ℕ),
      Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))) := fun c =>
    Fin.cases (motive := fun c => ∀ w : ℕ,
        Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))))
      (fun w => LinearMap.range (kRow (Dat w) _ (uD w) (huD w)))
      (fun c' w => lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c'.succ) r χ) (decs Ek Aw w))) c
  have hFix' : InRhoFix (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz (HcG 0)
      (HcR 0) (F 0) Io ε ρ₁ ρ₂ inc π γ lam (fun w => clsRow (Dat w) (vD w)) pr Fs Im :=
    ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, fun w hw => (hpp w hw).2, f11⟩
  have hBK' : ∀ w ∈ what₂, BKIn (HcR 0 w) (qK (Dat w) _ (hk w)) (Dat w).j' (pr w) (pair w) (HfW w) (Hf₂ w)
      (F 0 w) (Fs w) := by
    intro w hw
    rw [(hRows w hw).2.2.2.2.2.2.2.1]
    exact (hpp w hw).1
  have hC' : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ m : blockRestrictedRepresentationType bl ρk c, e₁ • m = 0) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c, E • m = 0) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) ∧
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ (decs Ek Aw w))) ≤ H0) ∧
      (∀ w ∈ what₂, RowIn ℓ (blockRestrictedRepresentationType bl ρk c) r χ E (decs Ek Aw w) (HcR c w) (F c w) (uT w) (wT w) (sT w) (mT w)
        ((c : ℕ) - 1) (dT w) (UT w) (locDeg (pl w))) ∧
      InChiFix (blockRestrictedRepresentationType bl ρk c) r χ E colIdx (decs Ek Aw) what₂ qs
        (Sha ((c : ℕ) - 1)) (HcG c) (HcR c) (F c) Io IS I γQ ζ ζO nQ := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = Fin.succ c' := ⟨c.pred hc0, (Fin.succ_pred _ _).symm⟩
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hC _ hc
    refine ⟨g1, g2, g3, g4, fun w hw => ?_, g6⟩
    obtain ⟨a1, a2, -⟩ := hRows w hw
    obtain ⟨b1, b2, b3⟩ := g5 w hw
    exact rowChiReal ℓ O hinjO Ek Ω (Aw w) a1 (pl w) a2 R' Tc (blockRestrictedRepresentationType bl ρk c'.succ) r χ E ε
      ((c'.succ : ℕ) - 1) (hcycw w) (hKO _ hc0) b2 (F _ w) (fun _ => b1) (fun h => absurd h (by omega))
      (uT w) (wT w) (sT w) (mT w) (dT w) (UT w) b3
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := hOne
  have hc1 : c1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [c1] at this
  have hOne' : (∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt r χ g • m = m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, e₁ • m = 0) ∧
     (∀ m : blockRestrictedRepresentationType bl ρk c1, E • m = δO • m) ∧
     (∀ l, ∀ g ∈ I (colIdx l), u l (g : Ω ≃ₐ[Ek] Ω) = 0) ∧ (∀ l, ∃ g ∈ decs Ek Aw (colIdx l), u l g = 1) ∧
     (∀ l, unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) (decs Ek Aw (colIdx l))) (I (colIdx l)) ≤
       F c1 (colIdx l)) ∧
     (∀ w ∈ what₂, RowIn ℓ (blockRestrictedRepresentationType bl ρk c1) r χ E (decs Ek Aw w) (HcR c1 w) (F c1 w) (uT w) (wT w) (sT w) (mT w)
       0 (dT w) (UT w) (locDeg (pl w))) ∧
     InChiFix (blockRestrictedRepresentationType bl ρk c1) r χ E colIdx (decs Ek Aw) what₂ qs (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞))
       (HcG c1) (HcR c1) (F c1) Io IS I γQ ζ ζO nQ := by
    refine ⟨o1, o2, o3, o4, o5, o6, fun w hw => ?_, ?_⟩
    · obtain ⟨a1, a2, -⟩ := hRows w hw
      exact rowChiReal ℓ O hinjO Ek Ω (Aw w) a1 (pl w) a2 R' Tc (blockRestrictedRepresentationType bl ρk c1) r χ E ε 0 (hcycw w)
        (hKO _ hc1) (fun g _ m => by simpa using o1 g m) (F c1 w) (fun h => absurd h (lt_irrefl 0))
        (fun _ => (o7 w hw).1) (uT w) (wT w) (sT w) (mT w) (dT w) (UT w) (o7 w hw).2
    · obtain ⟨i1, i2, i3, i4⟩ := o8
      exact ⟨i1, i2, i3, i4, vhEInChi Ek Ω Av hAv ℓ O hreal R' Tc (blockRestrictedRepresentationType bl ρk c1) (hKO _ hc1) r χ o1
        (decs Ek Aw) (what₂ ∪ qs ∪ univ.image colIdx) (HcG c1) (F c1) Vo VS Io IS o9 o10⟩
  exact split_all_second_form ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ ι colIdx hinj
    (decs Ek Aw) j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs
    (fun w => locDeg (pl w)) s (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞)) H0
    Sha uT wT sT mT dT UT hEsum hF L tens v₁ κ V iL qV Ff κz HcG HcR F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam (fun w => H1 (Dat w).ρTl') (fun w => clsRow (Dat w) (vD w)) pr Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y
    (fun w => H1 (Dat w).ρT) (fun w => H1 (Dat w).ρT') (fun w => qK (Dat w) _ (hk w)) (fun w => (Dat w).j')
    pair HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hnu hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4 hFix' hBK' hC' hOne' hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA Zc clsV H₁ Hf₁ gR
    τH DatH bH wH mH hrows hseq hcls hclsV hliftR hH0 hJC hJR

end Formalism.RepresentationBoundsCohomology.SF
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2 Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

set_option maxHeartbeats 8000000 in
theorem realization_second_form : StatReal2F := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum hF cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS ε T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hπD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR
  have hrow : ∀ w ∈ cols, conj w ∈ what₂ := fun w hw => hrows ▸ Finset.mem_image_of_mem conj hw
  obtain ⟨f1, f2, f3, f4, f6, f7, f8, f9, f11⟩ := hFix
  have hres : ∀ (c : Fin (t + 1)) (w : ℕ), lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ≤
      (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))).comap
        (resH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)) :=
    fun c w => resLC O _ _ (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)
  have hFix' : InRhoFixReal (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz
      (lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ)) (F 0) Io ε ρ₁ ρ₂ inc π γ lam Dat uD huD vD Fs Im := by
    refine ⟨f1, f2, f3, f4, fun w hw => ?_, f6, f7, f8, f9, fun w hw => ?_, f11⟩
    · rw [kRowRange O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w) (hRows w hw).2.2.2.1.openT]
      exact hres 0 w
    · exact inRowReal_of ℓ r χ E (decs Ek Aw w) ρ₁ inc π (Dat w) (vD w) (hπD w) (heD w) (Fs w) (Hf₁ w) hO hA hinc
        (hur.comp continuous_subtype_val) (hRows w hw).2.2.2.2.2.2.2.2.2
  have hRows' : ∀ w ∈ what₂, (Aw w).valuation (ℓ : Ω) < 1 ∧ IsPlaceOver (Aw w) (pl w) ∧
      (∀ g : decs Ek Aw w, (Dat w).ε g = ε g) ∧ RealLat (Dat w) ∧
      (∀ (g : decs Ek Aw w) t, vD w (ρ₂ g t) = (Dat w).ρTl' g (vD w t)) ∧
      (∀ t m, γ t m = pairKO (Dat w).bT (Dat w).T (uD w m) (vD w t)) ∧
      (∀ a, a ∈ HfW w ↔ ∀ b ∈ Hf₂ w, cupFG (Dat w) a b = 0) ∧
      F 0 w = (((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w)) ∧
      Fs w = ((Hf₂ w).restrictScalars O).comap (Dat w).j' := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := hRows w hw
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
  refine realization_basic_form ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz (fun c => lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)) F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix' hRows' ?_ ?_ hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA (fun w => zcRow (Dat w) (vD w))
    (fun w => clsRowV (Dat w) (wD w)) (fun w => H1 (resRep ρ₁ (decs Ek Aw w))) Hf₁ gR
    τH DatH bH wH mH hrows hseq ?_ ?_ (fun w hw => ⟨rfl, hliftR w hw⟩) hH0 hJC hJR
  · intro c hc
    obtain ⟨g1, g2, g3, g4, g5, ⟨i1, i3, i4⟩, i5⟩ := hC c hc
    exact ⟨g1, g2, g3, g4, g5, i1, fun w _ => hres c w, i3, i4, i5⟩
  · obtain ⟨o1, o2, o3, o4, o5, o6, o7, ⟨i1, i3, i4⟩, o10⟩ := hOne
    refine ⟨o1, o2, o3, o4, o5, o6, o7, ⟨i1, fun w _ => hres c1 w, i3, i4⟩, ?_, o10⟩
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, rfl, hc⟩
  · intro w hw
    exact classMapReal O (VT (conj w)) (VT' (conj w)) _ (Dat (conj w)) T₂ (resRep ρ₂ (decs Ek Aw (conj w)))
      (vD (conj w)) (hRows' _ (hrow w hw)).2.2.2.2.1 (Fs (conj w))
  · intro w hw a ha
    exact clsVReal O (VT (conj w)) (VT' (conj w)) _ (Dat (conj w)) T₂ V₂ (resRep ρV (decs Ek Aw (conj w))) iV
      (vD (conj w)) (wD (conj w)) (hwD w hw).1 (hwD w hw).2 a ha

end Formalism.RepresentationBoundsCohomology.SF
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2 Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

set_option maxHeartbeats 8000000 in
theorem realization_weight_form : StatRealWAF := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum hF cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS ε T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := hOne
  exact realization_second_form ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu
    (fun l => srcNO2 ℓ O _ _ _ _ _ _ (hLe l)) (fun l => srcNO2 ℓ O _ _ _ _ _ _ (hLE l)) hrat0 hb1 hb3 hb4
    hFix hRows
    (fun c hc => ⟨(hC c hc).1, (hC c hc).2.1, (hC c hc).2.2.1, (hC c hc).2.2.2.1,
      fun w hw => ⟨((hC c hc).2.2.2.2.1 w hw).1, ((hC c hc).2.2.2.2.1 w hw).2.1,
        row_tb_of_w ℓ _ r χ E _ _ _ _ _ _ _ _ _ ((hC c hc).2.2.2.2.1 w hw).2.2⟩, (hC c hc).2.2.2.2.2⟩)
    ⟨o1, o2, o3, o4, o5, o6, fun w hw => ⟨(o7 w hw).1, row_tb_of_w ℓ _ r χ E _ _ _ _ _ _ _ _ _ (o7 w hw).2⟩, o8⟩
    hrest conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD (fun w hw => srcNO2 ℓ O _ _ _ _ _ _ (hliftR w hw))
    (fun w hw => ⟨(hH0 w hw).1, h0WJ ℓ _ _ _ _ (hH0 w hw).2⟩) hJC hJR

end Formalism.RepresentationBoundsCohomology.SF
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2 Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

set_option maxHeartbeats 8000000 in
theorem realization_all_first_form : StatRealAll1F := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum hF cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz HcG F Vo VS Io IS ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y _ _ _ _ HfW Hf₂
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
  have hk : ∀ w, Function.Injective (kRow (Dat w) _ (uD w) (huD w)) :=
    fun w => kRowInj O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w)
  have hcycw : ∀ w, IsCycOn ℓ (decs Ek Aw w) (ε.comp (decs Ek Aw w).subtype) :=
    fun w g n ζ h => hcyc g.1 n ζ h
  have hnu : ¬ IsUnit (ℓ : O) := fun h => (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hO.p_mem)) h
  have hKO : ∀ c : Fin (t + 1), c ≠ 0 → Nonempty (blockRestrictedRepresentationType bl ρk c ≃ₗ[O] KO O) :=
    fun c hc => blk_ko bl ρk c (hcard1 c hc)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := hFix
  have key : ∀ w, w ∈ what₂ →
      ∃ (pr : LinearMap.range (kRow (Dat w) _ (uD w) (huD w)) →ₗ[O] H1 (Dat w).ρTl' →ₗ[O] KO O)
      (pair : H1 (Dat w).ρT →ₗ[FractionRing O] H1 (Dat w).ρT' →ₗ[FractionRing O] FractionRing O),
      BKIn (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (qK (Dat w) _ (hk w)) (Dat w).j' pr pair (HfW w) (Hf₂ w)
        ((((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w))) (Fs w) ∧
      InRowRhoNoBK (blockRestrictedRepresentationType bl ρk 0) r χ E (decs Ek Aw w) ε ρ₁ inc π γ
        (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (clsRow (Dat w) (vD w)) pr (Fs w) (Im w) := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hRows w hw
    exact rowRhoReal ℓ O (VT w) (VT' w) Ek Ω (Aw w) a1 R' Tc (blockRestrictedRepresentationType bl ρk 0) r χ E ε T₁ T₂ ρ₁ ρ₂ inc π γ
      (Dat w) (uD w) (huD w) (vD w) (HfW w) (Hf₂ w) (Fs w) (Im w) hO hFr hA (hcycw w) a3 a4 f8 a5 a6 a7 a9
      (f10 w hw) (hk w)
  choose! pr pair hpp using key
  let HcR : ∀ (c : Fin (t + 1)) (w : ℕ),
      Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))) := fun c =>
    Fin.cases (motive := fun c => ∀ w : ℕ,
        Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))))
      (fun w => LinearMap.range (kRow (Dat w) _ (uD w) (huD w)))
      (fun c' w => lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c'.succ) r χ) (decs Ek Aw w))) c
  have hFix' : InRhoFix (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz (HcG 0)
      (HcR 0) (F 0) Io ε ρ₁ ρ₂ inc π γ lam (fun w => clsRow (Dat w) (vD w)) pr Fs Im :=
    ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, fun w hw => (hpp w hw).2, f11⟩
  have hBK' : ∀ w ∈ what₂, BKIn (HcR 0 w) (qK (Dat w) _ (hk w)) (Dat w).j' (pr w) (pair w) (HfW w) (Hf₂ w)
      (F 0 w) (Fs w) := by
    intro w hw
    rw [(hRows w hw).2.2.2.2.2.2.2.1]
    exact (hpp w hw).1
  have hC' : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ m : blockRestrictedRepresentationType bl ρk c, e₁ • m = 0) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c, E • m = 0) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) ∧
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ (decs Ek Aw w))) ≤ H0) ∧
      (∀ w ∈ what₂, RowIn ℓ (blockRestrictedRepresentationType bl ρk c) r χ E (decs Ek Aw w) (HcR c w) (F c w) (uT w) (wT w) (sT w) (mT w)
        ((c : ℕ) - 1) (dT w) (UT w) (locDeg (pl w))) ∧
      InChiFix (blockRestrictedRepresentationType bl ρk c) r χ E colIdx (decs Ek Aw) what₂ qs
        (Sha ((c : ℕ) - 1)) (HcG c) (HcR c) (F c) Io IS I γQ ζ ζO nQ := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = Fin.succ c' := ⟨c.pred hc0, (Fin.succ_pred _ _).symm⟩
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hC _ hc
    refine ⟨g1, g2, g3, g4, fun w hw => ?_, g6⟩
    obtain ⟨a1, a2, -⟩ := hRows w hw
    obtain ⟨b1, b2, b3⟩ := g5 w hw
    exact rowChiReal ℓ O hinjO Ek Ω (Aw w) a1 (pl w) a2 R' Tc (blockRestrictedRepresentationType bl ρk c'.succ) r χ E ε
      ((c'.succ : ℕ) - 1) (hcycw w) (hKO _ hc0) b2 (F _ w) (fun _ => b1) (fun h => absurd h (by omega))
      (uT w) (wT w) (sT w) (mT w) (dT w) (UT w) b3
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := hOne
  have hc1 : c1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [c1] at this
  have hOne' : (∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt r χ g • m = m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, e₁ • m = 0) ∧
     (∀ m : blockRestrictedRepresentationType bl ρk c1, E • m = δO • m) ∧
     (∀ l, ∀ g ∈ I (colIdx l), u l (g : Ω ≃ₐ[Ek] Ω) = 0) ∧ (∀ l, ∃ g ∈ decs Ek Aw (colIdx l), u l g = 1) ∧
     (∀ l, unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) (decs Ek Aw (colIdx l))) (I (colIdx l)) ≤
       F c1 (colIdx l)) ∧
     (∀ w ∈ what₂, RowIn ℓ (blockRestrictedRepresentationType bl ρk c1) r χ E (decs Ek Aw w) (HcR c1 w) (F c1 w) (uT w) (wT w) (sT w) (mT w)
       0 (dT w) (UT w) (locDeg (pl w))) ∧
     InChiFix (blockRestrictedRepresentationType bl ρk c1) r χ E colIdx (decs Ek Aw) what₂ qs (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞))
       (HcG c1) (HcR c1) (F c1) Io IS I γQ ζ ζO nQ := by
    refine ⟨o1, o2, o3, o4, o5, o6, fun w hw => ?_, ?_⟩
    · obtain ⟨a1, a2, -⟩ := hRows w hw
      exact rowChiReal ℓ O hinjO Ek Ω (Aw w) a1 (pl w) a2 R' Tc (blockRestrictedRepresentationType bl ρk c1) r χ E ε 0 (hcycw w)
        (hKO _ hc1) (fun g _ m => by simpa using o1 g m) (F c1 w) (fun h => absurd h (lt_irrefl 0))
        (fun _ => (o7 w hw).1) (uT w) (wT w) (sT w) (mT w) (dT w) (UT w) (o7 w hw).2
    · obtain ⟨i1, i2, i3, i4⟩ := o8
      exact ⟨i1, i2, i3, i4, vhEInChi Ek Ω Av hAv ℓ O hreal R' Tc (blockRestrictedRepresentationType bl ρk c1) (hKO _ hc1) r χ o1
        (decs Ek Aw) (what₂ ∪ qs ∪ univ.image colIdx) (HcG c1) (F c1) Vo VS Io IS o9 o10⟩
  exact realization_all_forms_holds ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ ι colIdx hinj
    (decs Ek Aw) j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs
    (fun w => locDeg (pl w)) s (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞)) H0
    Sha uT wT sT mT dT UT hEsum hF L tens v₁ κ V iL qV Ff κz HcG HcR F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam (fun w => H1 (Dat w).ρTl') (fun w => clsRow (Dat w) (vD w)) pr Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y
    (fun w => H1 (Dat w).ρT) (fun w => H1 (Dat w).ρT') (fun w => qK (Dat w) _ (hk w)) (fun w => (Dat w).j')
    pair HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hnu hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4 hFix' hBK' hC' hOne' hrest

set_option maxHeartbeats 8000000 in
theorem realization_all_second_form : StatRealAll2F := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum hF cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS ε T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hπD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
  obtain ⟨f1, f2, f3, f4, f6, f7, f8, f9, f11⟩ := hFix
  have hres : ∀ (c : Fin (t + 1)) (w : ℕ), lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ≤
      (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))).comap
        (resH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)) :=
    fun c w => resLC O _ _ (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)
  have hFix' : InRhoFixReal (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz
      (lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ)) (F 0) Io ε ρ₁ ρ₂ inc π γ lam Dat uD huD vD Fs Im := by
    refine ⟨f1, f2, f3, f4, fun w hw => ?_, f6, f7, f8, f9, fun w hw => ?_, f11⟩
    · rw [kRowRange O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w) (hRows w hw).2.2.2.1.openT]
      exact hres 0 w
    · exact inRowReal_of ℓ r χ E (decs Ek Aw w) ρ₁ inc π (Dat w) (vD w) (hπD w) (heD w) (Fs w) (Hf₁ w) hO hA hinc
        (hur.comp continuous_subtype_val) (hRows w hw).2.2.2.2.2.2.2.2.2
  have hRows' : ∀ w ∈ what₂, (Aw w).valuation (ℓ : Ω) < 1 ∧ IsPlaceOver (Aw w) (pl w) ∧
      (∀ g : decs Ek Aw w, (Dat w).ε g = ε g) ∧ RealLat (Dat w) ∧
      (∀ (g : decs Ek Aw w) t, vD w (ρ₂ g t) = (Dat w).ρTl' g (vD w t)) ∧
      (∀ t m, γ t m = pairKO (Dat w).bT (Dat w).T (uD w m) (vD w t)) ∧
      (∀ a, a ∈ HfW w ↔ ∀ b ∈ Hf₂ w, cupFG (Dat w) a b = 0) ∧
      F 0 w = (((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w)) ∧
      Fs w = ((Hf₂ w).restrictScalars O).comap (Dat w).j' := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := hRows w hw
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
  refine realization_all_first_form ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz (fun c => lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)) F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix' hRows' ?_ ?_ hrest
  · intro c hc
    obtain ⟨g1, g2, g3, g4, g5, ⟨i1, i3, i4⟩, i5⟩ := hC c hc
    exact ⟨g1, g2, g3, g4, g5, i1, fun w _ => hres c w, i3, i4, i5⟩
  · obtain ⟨o1, o2, o3, o4, o5, o6, o7, ⟨i1, i3, i4⟩, o10⟩ := hOne
    refine ⟨o1, o2, o3, o4, o5, o6, o7, ⟨i1, fun w _ => hres c1 w, i3, i4⟩, ?_, o10⟩
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, rfl, hc⟩

set_option maxHeartbeats 8000000 in
theorem realization_all_weight_form : StatRealAllWAF := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum hF cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS ε T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := hOne
  exact realization_all_second_form ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu
    (fun l => srcNO2 ℓ O _ _ _ _ _ _ (hLe l)) (fun l => srcNO2 ℓ O _ _ _ _ _ _ (hLE l)) hrat0 hb1 hb3 hb4
    hFix hRows
    (fun c hc => ⟨(hC c hc).1, (hC c hc).2.1, (hC c hc).2.2.1, (hC c hc).2.2.2.1,
      fun w hw => ⟨((hC c hc).2.2.2.2.1 w hw).1, ((hC c hc).2.2.2.2.1 w hw).2.1,
        row_tb_of_w ℓ _ r χ E _ _ _ _ _ _ _ _ _ ((hC c hc).2.2.2.2.1 w hw).2.2⟩, (hC c hc).2.2.2.2.2⟩)
    ⟨o1, o2, o3, o4, o5, o6, fun w hw => ⟨(o7 w hw).1, row_tb_of_w ℓ _ r χ E _ _ _ _ _ _ _ _ _ (o7 w hw).2⟩, o8⟩
    hrest

end Formalism.RepresentationBoundsCohomology.SF
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2 Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

set_option maxHeartbeats 8000000 in
theorem realDisplay2_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (rr : ℕ → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδ : δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i))
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hrr : ∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m)
    (hba : ∀ c : Fin (t + 1), c ≠ 0 → ∀ g (m : blockRestrictedRepresentationType bl ρk c),
      uElt r χ g • m = ((((ε g) ^ ((c : ℕ) - 1))⁻¹ : Oˣ) : O) • m)
    (hl : lhs = vcc T Z (p π')) :
    RealDisplay2 ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC0,
    hOne0⟩ := hR
  obtain ⟨p1, p2, p3, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR
  exact realization_second_form ℓ O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e'
    hEE hee π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE
    (fun x' hx' => by
      obtain ⟨δx, q1, q2, q3, q4⟩ := hpts x'
      exact ⟨δx, q1, q2, q3, q4, (hrat0 x' hx').1, (hrat0 x' hx').2⟩)
    hE0 hτ0 hne hFix hRows
    (fun c hc2 => ⟨(hC0 c hc2).1, (hC0 c hc2).2.1, (hC0 c hc2).2.2.2, (hC c hc2).1,
      fun w hw => ⟨((hC c hc2).2.1 w hw).1,
        fun g _ m => hba c (by rintro rfl; simp at hc2) g m, ((hC c hc2).2.1 w hw).2⟩, (hC c hc2).2.2⟩)
    ⟨p1, p2, p3, hOne⟩
    hrest conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR

set_option maxHeartbeats 8000000 in
theorem realDisplayWA_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (rr : ℕ → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδ : δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i))
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hrr : ∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m)
    (hba : ∀ c : Fin (t + 1), c ≠ 0 → ∀ g (m : blockRestrictedRepresentationType bl ρk c),
      uElt r χ g • m = ((((ε g) ^ ((c : ℕ) - 1))⁻¹ : Oˣ) : O) • m)
    (hl : lhs = vcc T Z (p π')) :
    RealDisplayWA ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC0,
    hOne0⟩ := hR
  obtain ⟨p1, p2, p3, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR
  exact realization_weight_form ℓ O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e'
    hEE hee π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE
    (fun x' hx' => by
      obtain ⟨δx, q1, q2, q3, q4⟩ := hpts x'
      exact ⟨δx, q1, q2, q3, q4, (hrat0 x' hx').1, (hrat0 x' hx').2⟩)
    hE0 hτ0 hne hFix hRows
    (fun c hc2 => ⟨(hC0 c hc2).1, (hC0 c hc2).2.1, (hC0 c hc2).2.2.2, (hC c hc2).1,
      fun w hw => ⟨((hC c hc2).2.1 w hw).1,
        fun g _ m => hba c (by rintro rfl; simp at hc2) g m, ((hC c hc2).2.1 w hw).2⟩, (hC c hc2).2.2⟩)
    ⟨p1, p2, p3, hOne⟩
    hrest conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR

set_option maxHeartbeats 8000000 in
theorem realDisplayAll2_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (rr : ℕ → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδ : δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i))
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hrr : ∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m)
    (hba : ∀ c : Fin (t + 1), c ≠ 0 → ∀ g (m : blockRestrictedRepresentationType bl ρk c),
      uElt r χ g • m = ((((ε g) ^ ((c : ℕ) - 1))⁻¹ : Oˣ) : O) • m)
    (hl : lhs = vcc T Z (p π')) :
    RealDisplayAll2 ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC0,
    hOne0⟩ := hR
  obtain ⟨p1, p2, p3, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne hrest
  exact realization_all_second_form ℓ O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e'
    hEE hee π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE
    (fun x' hx' => by
      obtain ⟨δx, q1, q2, q3, q4⟩ := hpts x'
      exact ⟨δx, q1, q2, q3, q4, (hrat0 x' hx').1, (hrat0 x' hx').2⟩)
    hE0 hτ0 hne hFix hRows
    (fun c hc2 => ⟨(hC0 c hc2).1, (hC0 c hc2).2.1, (hC0 c hc2).2.2.2, (hC c hc2).1,
      fun w hw => ⟨((hC c hc2).2.1 w hw).1,
        fun g _ m => hba c (by rintro rfl; simp at hc2) g m, ((hC c hc2).2.1 w hw).2⟩, (hC c hc2).2.2⟩)
    ⟨p1, p2, p3, hOne⟩
    hrest

set_option maxHeartbeats 8000000 in
theorem realDisplayAllWA_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (rr : ℕ → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδ : δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i))
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hrr : ∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m)
    (hba : ∀ c : Fin (t + 1), c ≠ 0 → ∀ g (m : blockRestrictedRepresentationType bl ρk c),
      uElt r χ g • m = ((((ε g) ^ ((c : ℕ) - 1))⁻¹ : Oˣ) : O) • m)
    (hl : lhs = vcc T Z (p π')) :
    RealDisplayAllWA ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC0,
    hOne0⟩ := hR
  obtain ⟨p1, p2, p3, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne hrest
  exact realization_all_weight_form ℓ O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e'
    hEE hee π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE
    (fun x' hx' => by
      obtain ⟨δx, q1, q2, q3, q4⟩ := hpts x'
      exact ⟨δx, q1, q2, q3, q4, (hrat0 x' hx').1, (hrat0 x' hx').2⟩)
    hE0 hτ0 hne hFix hRows
    (fun c hc2 => ⟨(hC0 c hc2).1, (hC0 c hc2).2.1, (hC0 c hc2).2.2.2, (hC c hc2).1,
      fun w hw => ⟨((hC c hc2).2.1 w hw).1,
        fun g _ m => hba c (by rintro rfl; simp at hc2) g m, ((hC c hc2).2.1 w hw).2⟩, (hC c hc2).2.2⟩)
    ⟨p1, p2, p3, hOne⟩
    hrest

end Formalism.RepresentationBoundsCohomology.SF
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.ringDataObjects

set_option maxHeartbeats 4000000 in
theorem galois_theorem_primitive_data : GaloisTheoremPrimitiveData := by
  intro ℓ _ O _ _ _ _ X _ T d _ _ Ek Ω _ _ _ _ _ r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  obtain ⟨eB, e₁, s, hAB, hall⟩ := chain_from_primitive_data O X T d (Ω ≃ₐ[Ek] Ω) r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  refine ⟨eB, e₁, s, hAB, ?_⟩
  intro O' _ _ _ _ _ _ e he hspl
  obtain ⟨D, hD, ⟨i1, i2, i3, i4, i5, hT, hFree⟩, hv⟩ := hall O' e he hspl
  obtain ⟨hP, hA, -, -, -⟩ := hyp
  obtain ⟨hI, ⟨m, jj, a, hja, hs⟩, hsep⟩ := hAB
  obtain ⟨b1, b2, b3, b4⟩ := bridge O X T d (Ω ≃ₐ[Ek] Ω) r π eB hI.1 hI.2.2.1 m jj a hja (ϖ ^ L)
  rw [← hs] at b1 b2 b3 b4
  obtain ⟨cP, -, cI, -, -⟩ := stageC O O' e he X T d (Ω ≃ₐ[Ek] Ω) r π t bl χ₁ ε hP hA eB e₁ hI g₀ s b1 b2 b3 b4
    hsep hspl
  obtain ⟨hd1, hd2⟩ := deltaBc O O' e he
  have hT' := hT
  obtain ⟨-, -, -, -, hee, -, -, -, hsurj, -, hcard1, -, -, -, -, -, -, hOne0⟩ := hT'
  obtain ⟨-, -, p3, -⟩ := hOne0
  refine ⟨D, hD, hd2 ℓ, (hd1 X d (Ω ≃ₐ[Ek] Ω) t bl T r π χ₁ ε g₀ eB e₁ s D hD).2,
    surjection_of_rank_one_idempotent O' D.R' _ (D.ρk 0).toRingHom D.e₁ (hsurj 0) hee (idempotent_rank_one_at_point cI hD),
    scalar_action_on_block O' D.R' _ D.E D.δO p3 (blk_scalar D _ (hcard1 _ (by
      intro h
      have := congrArg Fin.val h
      simp at this))), i1, i2, i3, i4, i5, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ Z
  have hδO := deltaO_eq hD
  have hrr := rr_act hD
  have hba := blk_act cP hD
  exact ⟨realDisplay2_of ℓ O' X D.X' Z D.p d D.R' D.T' Ek Ω D.r D.χ D.E D.e₁ D.δ t ht bl D.ρk D.δO
      (bcChar O' ε) g₀ _ (bcT O' T) D.T' D.q D.b D.π' D.ρπ D.sE D.tE D.rr (bcChar O' χ₁ g₀) hT (hFree Z) rfl hδO
      hrr hba (hv Z).symm,
    realDisplayWA_of ℓ O' X D.X' Z D.p d D.R' D.T' Ek Ω D.r D.χ D.E D.e₁ D.δ t ht bl D.ρk D.δO
      (bcChar O' ε) g₀ _ (bcT O' T) D.T' D.q D.b D.π' D.ρπ D.sE D.tE D.rr (bcChar O' χ₁ g₀) hT (hFree Z) rfl hδO
      hrr hba (hv Z).symm,
    realDisplayAll2_of ℓ O' X D.X' Z D.p d D.R' D.T' Ek Ω D.r D.χ D.E D.e₁ D.δ t ht bl D.ρk D.δO
      (bcChar O' ε) g₀ _ (bcT O' T) D.T' D.q D.b D.π' D.ρπ D.sE D.tE D.rr (bcChar O' χ₁ g₀) hT (hFree Z) rfl hδO
      hrr hba (hv Z).symm,
    realDisplayAllWA_of ℓ O' X D.X' Z D.p d D.R' D.T' Ek Ω D.r D.χ D.E D.e₁ D.δ t ht bl D.ρk D.δO
      (bcChar O' ε) g₀ _ (bcT O' T) D.T' D.q D.b D.π' D.ρπ D.sE D.tE D.rr (bcChar O' χ₁ g₀) hT (hFree Z) rfl hδO
      hrr hba (hv Z).symm⟩


end Formalism.RepresentationBoundsCohomology.SF
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.FIN Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.ringDataObjects

theorem gen : StatGen := by
  intro ℓ hℓ O _ _ _ G _ ε g₀ s₀ y ⟨hu, h0, hs1, hs2, hx⟩
  have key : ∀ n : ℕ, n ≠ 0 → (ε g₀) ^ n ≠ 1 := by
    intro n hn h1
    have h := powSubOneO O ℓ hℓ hu s₀ hs1 hs2 ((ε g₀ : Oˣ) : O) y hx n hn
    have h2 : ((ε g₀ : Oˣ) : O) ^ n - 1 = 0 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one, sub_self]
    rw [h2, IsDiscreteValuationRing.addVal_zero] at h
    have h3 : IsDiscreteValuationRing.addVal O (ℓ : O) ≠ ⊤ := by
      intro h4
      exact h0 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h4)
    exact (WithTop.mul_ne_top h3 (ENat.natCast_ne_top _)) h.symm
  refine ⟨?_, ?_⟩
  · have aux : ∀ i j : ℕ, i ≤ j → (ε g₀) ^ i = (ε g₀) ^ j → i = j := by
      intro i j hij h
      by_contra hne
      refine key (j - i) (by omega) ?_
      have : (ε g₀) ^ j = (ε g₀) ^ i * (ε g₀) ^ (j - i) := by rw [← pow_add]; congr 1; omega
      rw [this] at h
      exact (mul_eq_left.1 h.symm)
    intro i j h
    rcases le_total i j with hij | hij
    · exact aux i j hij h
    · exact (aux j i hij h.symm).symm
  · intro O' _ _
    have h := congrArg (algebraMap O O') hx
    simpa [bcChar] using h



end Formalism.RepresentationBoundsCohomology.SF
end
end
