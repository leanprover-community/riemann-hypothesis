import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotientProdIrrUc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldPointLiftsGenericFibre
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic UpperTheory.V

namespace UpperTheory.V.Z.Win.Birth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem good_of_isCuspFormR (a : ℕ) (ψ : AddChar (Ad F) ℂ) (φ : TR.Sm F a) (h : TR.IsCuspForm φ) :
    Good ψ (a - 1) φ.1 := by
  have hcont : Continuous φ.1 := GlobalTheory.SlTwoCusp.continuous_of_isOpen_stab F a φ h.1.level
  refine ⟨hcont, fun γ _ g => h.1.left γ g, ?_, ?_⟩
  · intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex a k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast a k) (0 : UnipotentBlockColumnIndex a k k → Ad F) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hra g
    have hra' : r < a := by omega
    have hper := per_blk (E := F) (r := r) (m := a - 1) hcont (fun c g => h.1.left _ g) g
    have hper2 : Per (ratN F a r) (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) :=
      ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
        simp only [map_add]
        exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
    have key := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratN F a r) (ratV F _) (isCoLat_ratV F (BlockIx a r))
      (isCoLat_ratV F _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
    rw [← key]
    have hfun : (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) = fun x => φ.1 (unip x * g) :=
      funext fun x => by rw [← blkU_comp_equiv]; rfl
    rw [hfun] at hper2 ⊢
    letI : MeasurableSpace (BlockIx a r → Ad F) := borel _
    haveI : BorelSpace (BlockIx a r → Ad F) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice _ (ratN F a r) (isCoLat_ratV F (BlockIx a r))
    obtain ⟨-, -, -, hint⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average _ _ (isCoLat_ratV F (BlockIx a r)) μ 𝓕 hμ hF _ hper2
    have hc := h.2 r hr hra' μ 𝓕 hμ hF g
    rw [hint, h1] at hc
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc
    exact hc

private theorem exists_split_locR (a : ℕ) (w : HeightOneSpectrum (𝓞 F)) (g : GA F a) :
    ∃ (h : GA F a) (gw : GL (Fin a) (w.adicCompletion F)),
      g = h * finGL F a (locGL F a w gw) ∧
        ∀ u : GL (Fin a) (w.adicCompletion F),
          h * finGL F a (locGL F a w u) = finGL F a (locGL F a w u) * h := by
  obtain ⟨gw, hgw⟩ : ∃ gw, gw = GeneralLinearGroup.map (pLoc F w) (GeneralLinearGroup.map (pFin F) g) := ⟨_, rfl⟩
  refine ⟨g * (finGL F a (locGL F a w gw))⁻¹, gw, by rw [inv_mul_cancel_right], fun u => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc F w)
      (GeneralLinearGroup.map (pFin F) (g * (finGL F a (locGL F a w gw))⁻¹)) = 1 := by
    rw [map_mul, map_inv, pFin_finGL, map_mul, map_inv, pLoc_locGL, hgw, mul_inv_cancel]
  generalize g * (finGL F a (locGL F a w gw))⁻¹ = k at hk ⊢
  obtain ⟨y, z, rfl, hz⟩ : ∃ y z, k = TR.infGL F a y * finGL F a z ∧ GeneralLinearGroup.map (pLoc F w) z = 1 :=
    ⟨_, _, (TR.infGL_mul_finGL k).symm, hk⟩
  rw [mul_assoc, ← map_mul, LocUniq.comm_locGL w hz u, map_mul, ← mul_assoc, TR.infGL_comm, mul_assoc]

private theorem locTri_adelicR (a : ℕ) (w : HeightOneSpectrum (𝓞 F)) (u : GL (Fin a) (w.adicCompletion F))
    (hlow : ∀ i j : Fin a, j < i → u.val i j = 0) (hdiag : ∀ j : Fin a, u.val j j = 1) :
    (∀ i j : Fin a, j < i → (finGL F a (locGL F a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL F a (locGL F a w u)).val j j = 1) ∧
      ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL F a (locGL F a w u)).val p.1 p.2 =
        sFin F (sLoc F w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  have hoff : ∀ i j : Fin a, i ≠ j → (finGL F a (locGL F a w u)).val i j = sFin F (sLoc F w (u.val i j)) := by
    intro i j h
    rw [finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    rw [hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]
  · intro j
    exact cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ p.2 := by
      intro h; rw [h] at hp'; omega
    exact hoff p.1 p.2 hne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem isGeneric_of_isLocCompR (a : ℕ) (P : TR.CuspSub F a) (w : HeightOneSpectrum (𝓞 F))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion F))) (hσ : P.IsLocComp w σ) : GlobalTheory.LocGL.IsGeneric σ.ρ := by
  obtain ⟨f, hf0, hf⟩ := hσ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar F
  have hg : ∀ v, Good ψ (a - 1) (f v).1.1 := fun v => good_of_isCuspFormR a ψ (f v).1 (P.cusp _ (f v).2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  have hv1 : (f v₀).1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := exists_split_locR a w g₀
  have hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x =
      whit ψ (a - 1) (f v).1.1 (x * finGL F a (locGL F a w u)) := fun u v x => by
    rw [hf u v]
    exact whit_rt _ _ _ _
  let l : σ.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) (f v).1.1 h
      map_add' := fun v v' => by
        rw [map_add f]
        exact congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => by
        rw [map_smul f]
        exact congrFun (whit_smul (a - 1) c (f v).1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) (f v).1.1 h := fun _ => rfl
  have hne : l (σ.ρ gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion F) (Fin a)) v,
      l (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion F)).val p.1 p.2) : ℂ) * l v := by
    intro u v
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 u.2
    obtain ⟨t1, t2, t3⟩ := locTri_adelicR a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic F a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3]
    rfl
  refine ⟨locPsi hψ w, ?_, fun h1 => ?_, ?_⟩
  · refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af F => ((0, x) : InfiniteAdeleRing F × Af F)).comp
      (CuspSub.continuous_sLoc w)
  · obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  · refine Submodule.Quotient.nontrivial_iff.2 fun htop => hne ?_
    have hle : GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion F) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤
        LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw, smul_eq_mul]
      exact sub_eq_zero.2 rfl
    exact hle (htop ▸ Submodule.mem_top)

end UpperTheory.V.Z.Win.Birth
end
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.RoadU GlobalTheory.LocLanglands UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private UpperTheory.V.Af.RealLocalComponent.isotypic from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
open private satLocFree from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree

namespace UpperTheory.V.Z.Win.Birth

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ofChar_ne_nu (θ : kˣ →* ℂˣ) (hθ : IsSmoothChar θ) : IrrGL.ofChar θ hθ ≠ (IrrGL.ofChar θ hθ).nu 1 := by
  intro e
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
  have h1 : absPow k 1 = 1 := mul_left_cancel (a := θ) (by rw [mul_one]; exact e.symm)
  have h2 : absPow k ((1 : ℝ) : ℂ) = 1 := by simpa using h1
  exact one_ne_zero (absPow_ofReal_eq_one.1 h2)

private theorem carrier_of_len {D : Segment k} (h : D.len = 1) : D.carrier = {D.first} := by
  ext x
  rw [Segment.mem_carrier, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain rfl : n = 0 := by omega
    simp
  · rintro rfl
    exact ⟨0, by omega, by simp⟩

private theorem linked_of_len {D D' : Segment k} (h : D.len = 1) (h' : D'.len = 1) (θ : kˣ →* ℂˣ) (hθ : IsSmoothChar θ)
    (e' : D'.first = IrrGL.ofChar θ hθ) (e : D.first = D'.first.nu 1) : D.Linked D' := by
  have hne : D.first ≠ D'.first := by
    rw [e, e']
    exact fun h => ofChar_ne_nu θ hθ h.symm
  rw [Segment.Linked, carrier_of_len h, carrier_of_len h']
  refine ⟨⟨Segment.ofChar θ hθ 2 (by norm_num), ?_⟩, ?_, ?_⟩
  · have hf : (Segment.ofChar θ hθ 2 (by norm_num)).first = D'.first := e'.symm
    have hl : (Segment.ofChar θ hθ 2 (by norm_num)).len = 2 := rfl
    ext x
    simp only [Segment.mem_carrier, Set.mem_union, Set.mem_singleton_iff]
    rw [hl, hf]
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
      · right
        simp
      · left
        simpa using e.symm
    · rintro (rfl | rfl)
      · exact ⟨1, by omega, by simpa using e.symm⟩
      · exact ⟨0, by omega, by simp⟩
  · simpa using hne
  · simpa using hne.symm

end Local

theorem plainTor_of_sph {E : Type} [Field E] [NumberField E] {N : ℕ} (hN : 1 ≤ N) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (hg : IsGeneric σ.ρ) : PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, ϖ, hs, -, -, -⟩ := GlobalTheory.SatSupp.hasSupport_of_hasSatGL E N hN w σ B hB
  obtain ⟨α, -, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  obtain ⟨h, Δ, y, hd, hun, hL, ⟨φ⟩⟩ := GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds _ N σ.V σ.ρ σ.smooth σ.irred hg
  have hsub : IsSubquotient σ.ρ (prodIrr y hd) :=
    IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective
  have hsp := GlobalTheory.LocLanglands.SphFac.isSpherical_factor _ h N y hd σ.V σ.ρ hsub hα.2.1
  have h1 : ∀ i, (y i).1 = 1 := fun i => GlobalTheory.TempSat.deg_eq_one_of_isLSeg (hL i) (hsp i)
  have hlen : ∀ i, (Δ i).len = 1 := fun i => by
    have h2 := (hL i).deg_eq
    rw [h1 i, Segment.deg] at h2
    exact Nat.eq_one_of_mul_eq_one_right h2
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds GlobalTheory.geometricLemmaFiltration_holds
  have hs2 : HasSupport σ.ρ (∑ i, (Δ i).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hL i).hasSupport) σ.irred hsub
  have he : ∑ i, (Δ i).ms = chars ξ hξ :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hs2
      (hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm)
  refine ⟨chars ξ hξ, hs, fun z hz => ?_, fun a ha b hb e => ?_⟩
  · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rfl
  · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hb
    rw [← he] at ha hb
    obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 ha
    obtain ⟨i', -, hi'⟩ := Multiset.mem_sum.1 hb
    have ea : a = (Δ i).first := by
      have := Segment.mem_ms.1 hi
      rwa [carrier_of_len (hlen i)] at this
    have eb : b = (Δ i').first := by
      have := Segment.mem_ms.1 hi'
      rwa [carrier_of_len (hlen i')] at this
    subst ea
    by_cases hii : i = i'
    · subst hii
      rw [← eb] at e
      subst hj
      exact ofChar_ne_nu _ _ e
    · exact hun i i' hii (linked_of_len (hlen i) (hlen i') (ξ j) (hξ j) (eb ▸ hj.symm) (eb ▸ e))

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem plainAtR_of_hasSat {n : ℕ} (hn : 1 ≤ n) (π : TR.CuspSub F n) (v : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ)
    (hB : π.HasSat v B) : PlainAtR π v := fun σ hσ =>
  plainTor_of_sph hn v σ B (((satLocFree F n v σ).2 _ π.finPart (UpperTheory.V.Af.RealLocalComponent.isotypic π v σ hσ) B).1 hB)
    (isGeneric_of_isLocCompR n π v σ hσ)

end UpperTheory.V.Z.Win.Birth
end
end

section
open NumberField IsDedekindDomain GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.LocLanglands Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private expo_intR sys_twist from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR

namespace UpperTheory.V.Z.Win.Birth

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem plainTor_tw {x : IrrGL k} (h : GlobalTheory.RoadU.PlainTor x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GlobalTheory.RoadU.PlainTor (x.tw χ hχ) := by
  obtain ⟨s, hs, h1, hu⟩ := h
  refine ⟨s.map (·.tw χ hχ), (hs.tw χ hχ).of_equiv (x.twEquiv χ hχ), ?_, ?_⟩
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    exact h1 y' hy'
  · intro y hy z hz e
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.tw_nu] at e
    have hinv : IsSmoothChar χ⁻¹ := hχ.inv
    have e2 := congrArg (·.tw χ⁻¹ hinv) e
    simp only [IrrGL.tw_tw, mul_inv_cancel, IrrGL.tw_one] at e2
    exact hu y' hy' z' hz' e2

end Local

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

private theorem plainAtR_twist {π : TR.CuspSub F n} {v : HeightOneSpectrum (𝓞 F)} (h : PlainAtR π v) (χ : HChar F) :
    PlainAtR (π.twist χ) v := by
  intro σ hσ
  have e : (π.twist χ).twist χ⁻¹ = π := by
    rw [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one]
  have h1 := hσ.twist χ⁻¹
  rw [e] at h1
  have h2 := h _ h1
  have hsm := GlobalTheory.HeckeComp.smooth_loc χ⁻¹ v
  have hsm' := GlobalTheory.HeckeComp.smooth_loc χ v
  have h3 : IrrGL.of (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).ρ
      (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).smooth
      (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).irred =
      (IrrGL.of σ.ρ σ.smooth σ.irred).tw (χ⁻¹.loc v) hsm :=
    (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ hsm).symm
  rw [h3] at h2
  have h4 := plainTor_tw h2 (χ.loc v) hsm'
  rw [IrrGL.tw_tw] at h4
  have e3 : χ⁻¹.loc v * χ.loc v = 1 := MonoidHom.ext fun x => by
    change (χ.loc v x)⁻¹ * χ.loc v x = 1
    simp
  have key : ∀ (c : (v.adicCompletion F)ˣ →* ℂˣ) (hc : IsSmoothChar c), c = 1 →
      (IrrGL.of σ.ρ σ.smooth σ.irred).tw c hc = IrrGL.of σ.ρ σ.smooth σ.irred := by
    rintro _ hc rfl
    exact IrrGL.tw_one _ _
  rwa [key _ _ e3] at h4

end UpperTheory.V.Z.Win.Birth

theorem UpperTheory.V.Z.Win.Birth.prTw :
    UpperTheory.V.Z.Win.Birth.PrTw := by
  rintro F Ω _ _ _ _ _ _ l _ ι r κ ⟨-, art, χ, a, ha, hχ, hL⟩ ⟨π, hr, hA, hP⟩
  refine ⟨π.twist χ, hr.twist (expo_intR hχ), sys_twist hA ha hL fun w B hB hu => hB.twist hu, fun v => ?_⟩
  rcases hP v with h | ⟨B, hB⟩
  · exact Or.inl (plainAtR_twist h χ)
  · by_cases hu : χ.UnrAt v
    · exact Or.inr ⟨_, hB.twist hu⟩
    · exact Or.inl (plainAtR_twist (plainAtR_of_hasSat (by norm_num) π v B hB) χ)
end
