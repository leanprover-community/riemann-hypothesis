import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapSecondPlace
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveReal
import Formalism.WachLatticeTwists.RealClassMaps.StatClassMapReal
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.RowChiReal

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG toH1Cocycles traceH1 transportCocycles)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem kRowRange : StatKRowRange := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ G _ _ D M _ _ ρM u hu hopen
  have hdisc : DiscreteTopology (VT ⧸ D.T) :=
    QuotientAddGroup.discreteTopology (N := D.T.toAddSubgroup) hopen
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      refine ⟨transportCocycles (MulEquiv.refl G) u ρM D.ρA hu ⟨c.1, c.2.2⟩, ?_, rfl⟩
      have h1 : IsLocallyConstant c.1 := (IsLocallyConstant.iff_continuous _).2 c.2.1
      exact h1.comp u.symm
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : IsLocallyConstant (c : G → M) := hc
    have h3 : (fun g : G => u ((c : G → M) g)) ∈ Z1 D.ρA := by
      refine ⟨(hc'.comp u).continuous, fun a b => ?_⟩
      beta_reduce
      rw [c.2, map_add, hu]
    refine ⟨Submodule.Quotient.mk ⟨_, h3⟩, ?_⟩
    refine congrArg (Submodule.mkQ _) (Subtype.ext (funext fun g => ?_))
    change u.symm (u ((c : G → M) g)) = _
    rw [LinearEquiv.symm_apply_apply]

theorem resLC : StatResLC := by
  intro O G M _ _ _ _ _ ρ Dw
  rintro _ ⟨c, hc, rfl⟩
  have hc' : IsLocallyConstant (c : G → M) := hc
  refine ⟨restrictCocycles1 ρ Dw c, ?_, rfl⟩
  exact hc'.comp_continuous continuous_subtype_val

section
variable {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']

theorem clsRow_of_mem (D : LatData O Γ VT VT') {T₂ : Type} [AddCommGroup T₂] [Module O T₂] (v : T₂ ≃ₗ[O] D.T')
    (f : Γ → T₂) (h : (fun g => v (f g)) ∈ Z1 D.ρTl') : clsRow D v f = Submodule.Quotient.mk ⟨_, h⟩ :=
  dif_pos h

theorem clsRowV_of_mem (D : LatData O Γ VT VT') {V₂ : Type} [AddCommGroup V₂] [Module O V₂] (w : V₂ ≃ₗ[O] VT')
    (f : Γ → V₂) (h : (fun g => w (f g)) ∈ Z1 D.ρT') : clsRowV D w f = Submodule.Quotient.mk ⟨_, h⟩ :=
  dif_pos h

end

theorem classMapReal : StatClassMapReal := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ G _ _ D T₂ _ _ ρ₂ v hv Fs
  refine ⟨fun a ha b hb => ?_, fun c a ha => ?_, fun a ha => ?_, fun x _ => ?_⟩
  · have hab : a + b ∈ zcRow D v := add_mem ha hb
    rw [clsRow_of_mem D v _ hab, clsRow_of_mem D v _ ha, clsRow_of_mem D v _ hb, ← Submodule.Quotient.mk_add]
    exact congrArg _ (Subtype.ext (funext fun g => map_add v _ _))
  · have hca : c • a ∈ zcRow D v := Submodule.smul_mem _ c ha
    rw [clsRow_of_mem D v _ hca, clsRow_of_mem D v _ ha, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun g => map_smul v _ _))
  · rw [clsRow_of_mem D v _ ha, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h
      refine ⟨v.symm m, funext fun g => ?_⟩
      have h1 : v (a g) = D.ρTl' g m - m := hm g
      apply v.injective
      change v (ρ₂ g (v.symm m) - v.symm m) = v (a g)
      rw [map_sub, hv, LinearEquiv.apply_symm_apply, h1]
    · rintro ⟨m, hm⟩
      refine (mem_coboundaries1 _ _).2 ⟨v m, fun g => ?_⟩
      change v (a g) = _
      rw [← hm]
      change v (ρ₂ g m - m) = _
      rw [map_sub, hv]
  · induction x using Submodule.Quotient.induction_on with
    | _ c =>
      have h : (fun g => v (v.symm (c.1 g))) ∈ Z1 D.ρTl' := by
        simpa using c.2
      refine ⟨fun g => v.symm (c.1 g), h, ?_⟩
      rw [clsRow_of_mem D v _ h]
      exact congrArg _ (Subtype.ext (funext fun g => (v.apply_symm_apply _).symm))

theorem clsVReal : StatClsVReal := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ G _ _ D T₂ V₂ _ _ _ _ ρV iV v w hw hwe a ha
  have ha' : (fun g => v (a g)) ∈ Z1 D.ρTl' := ha
  have h : (fun g => w (iV (a g))) ∈ Z1 D.ρT' := by
    refine ⟨?_, fun g k => ?_⟩
    · simp only [hw]
      exact continuous_subtype_val.comp ha'.1
    · simp only [hw]
      have := congrArg Subtype.val (ha'.2 g k)
      exact this
  rw [clsRow_of_mem D v _ ha, clsRowV_of_mem D w _ h]
  refine ⟨?_, fun h0 => ?_⟩
  · exact congrArg _ (Subtype.ext (funext fun g => (hw (a g)).symm))
  · rw [Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h0
    refine ⟨w.symm m, funext fun g => ?_⟩
    have h1 : w (iV (a g)) = D.ρT' g m - m := hm g
    apply w.injective
    change w (ρV g (w.symm m) - w.symm m) = _
    rw [map_sub, hwe, LinearEquiv.apply_symm_apply, h1]

end Formalism.RepresentationBoundsCohomology.FIN
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem ko_tors (O : Type) [CommRing O] [IsDomain O] (z : KO O) : ∃ c : O, c ≠ 0 ∧ c • z = 0 := by
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine Submodule.mem_one.2 ⟨a, ?_⟩
  rw [Algebra.smul_def, mul_comm]
  exact hq.symm

theorem psiCont : StatPsiCont := by
  intro p O _ _ _ _ _ _ _ A _ _ _ _ _ Y hO hA ψ
  have hfg : IsFGTop O Y := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective (Y.subtype.restrictScalars O) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : O × Y => q.1 • (q.2 : A))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : O, a ≠ 0 ∧ ∀ y : Y, a • ψ y = 0 := by
    obtain ⟨s, hs⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Y => ko_tors O (ψ y)
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span O (s : Set Y) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hx
      rw [hc, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, smul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have hopen := hfg.isOpen_mulSub hO ha
  refine continuous_of_continuousAt_zero ψ.toAddMonoidHom ?_
  intro U hU
  have hU0 : (0 : KO O) ∈ U := by
    have := mem_of_mem_nhds hU
    simpa using this
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hopen.mem_nhds (zero_mem _)) ?_
  rintro _ ⟨z, rfl⟩
  show ψ (a • z) ∈ U
  rw [map_smul, hka]
  exact hU0

theorem inRowReal_of (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw]
    {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    [TopologicalSpace T₁] [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁]
    (ρ₁ : Representation O G T₁) (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂)
    (D : LatData O Dw VT VT') (v : T₂ ≃ₗ[O] D.T') (hc : Continuous fun t => v (π t))
    (he : ∀ g t, v (π (resRep ρ₁ Dw g t)) = D.ρTl' g (v (π t)))
    (Fs : Submodule O (H1 D.ρTl')) (Hf₁ : Submodule O (H1 (resRep ρ₁ Dw)))
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hinc : Continuous inc)
    (hur : Continuous fun g : Dw => uElt r χ (g : G)) (hIm : Hf₁.map (gRow D _ π v hc he) ≤ Fs) :
    InRowReal r χ E Dw ρ₁ inc π D v Fs (Hf₁.map (gRow D _ π v hc he)) := by
  refine ⟨fun a => Continuous a, fun a ha => ?_, fun a ha => ?_, fun ψ f hf => ?_, fun a ha => hc.comp ha, ?_, hIm⟩
  · refine Continuous.subtype_mk (f := fun q : Dw × Dw =>
      inc (a q.1) * (uElt r χ (q.1 : G) * ((uElt r χ (q.2 : G) - 1) * E))) ?_ _
    exact (hinc.comp (ha.comp continuous_fst)).mul ((hur.comp continuous_fst).mul
      (((hur.comp continuous_snd).sub continuous_const).mul continuous_const))
  · exact ((hinc.comp ha).mul (hur.mul continuous_const)).neg
  · exact (psiCont p O A (Ymod r χ E) hO hA ψ).comp hf
  · rintro _ ⟨y, _, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      have h : (fun g => v (π (c.1 g))) ∈ Z1 D.ρTl' :=
        (cocycles1MapOfEquivariant (resRep ρ₁ Dw) D.ρTl' (v.toLinearMap ∘ₗ π) hc he c).2
      refine ⟨c.1, c.2.2, c.2.1, ?_⟩
      rw [clsRow_of_mem D v _ h]
      rfl

end Formalism.RepresentationBoundsCohomology.FIN
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

set_option maxHeartbeats 8000000 in
theorem theorem_n_five_real_second : RealClassMapSecondPlace := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum cols eO cB vδ N h0 c1
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
  refine theorem_n_five_real ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum
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

end Formalism.RepresentationBoundsCohomology.FIN
end
end
