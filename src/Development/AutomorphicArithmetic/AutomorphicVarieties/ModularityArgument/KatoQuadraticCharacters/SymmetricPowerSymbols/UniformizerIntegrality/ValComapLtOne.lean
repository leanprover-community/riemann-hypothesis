import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.ChB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFi

section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

private theorem unif_lc {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {f : G → A} (hf : IsLocallyConstant f) : ∀ᶠ h in nhds (1 : G), ∀ g : G, f (g * h) = f g := by
  choose V hVo hV1 hVm using fun g : G => exists_open_nhds_one_mul_subset
    (show {y : G | f (g * y) = f g} ∈ nhds (1 : G) from
      ((hf.isOpen_fiber (f g)).preimage (continuous_const_mul g)).mem_nhds (by simp))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun g : G => (fun x => g⁻¹ * x) ⁻¹' V g)
    (fun g => (hVo g).preimage (continuous_const_mul g⁻¹))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using hV1 x⟩)
  filter_upwards [(Filter.biInter_finset_mem t).2 (fun g _ => (hVo g).mem_nhds (hV1 g))] with h hh x
  obtain ⟨g, hg, hx⟩ : ∃ g ∈ t, g⁻¹ * x ∈ V g := by
    simpa using ht (Set.mem_univ x)
  have h1 : f (g * (g⁻¹ * x * h)) = f g := hVm g (Set.mul_mem_mul hx (Set.mem_iInter₂.1 hh g hg))
  have h2 : f (g * (g⁻¹ * x * 1)) = f g := hVm g (Set.mul_mem_mul hx (hV1 g))
  simp only [mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at h1 h2
  rw [h1, h2]

theorem UpperTheory.V.Z.Kato.Sym.PT.lcGeo :
    UpperTheory.V.Z.Kato.Sym.PT.LcGeo := by
  classical
  intro F K E _ _ _ _ _ _ _ _ A η hη
  have l : IsLocallyConstant (fun g : E ≃ₐ[K] E => η (AlgEquiv.restrictScalarsHom F g)) :=
    hη.comp_continuous
      (f := fun g : E ≃ₐ[K] E => (⟨AlgEquiv.restrictScalarsHom F g, TopSpec.res_mem_geo g⟩ : geo F K E))
      ((TopSpec.continuous_res (F := F) (K := K) (Ω := E)).subtype_mk _)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff K E _).1 (unif_lc l)
  let b := Module.finBasis K L
  refine ⟨Finset.univ.image fun i => (b i : E), fun g hg g' hg' hB => ?_⟩
  obtain ⟨g, rfl⟩ := TopSpec.exists_res hg
  obtain ⟨g', rfl⟩ := TopSpec.exists_res hg'
  have hlin : g.toLinearMap.comp L.val.toLinearMap = g'.toLinearMap.comp L.val.toLinearMap :=
    b.ext fun i => hB _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hmem : g⁻¹ * g' ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hz' : g z = g' z := LinearMap.congr_fun hlin ⟨z, hz⟩
    rw [AlgEquiv.mul_apply, ← hz']
    exact g.symm_apply_apply z
  have h := hsub hmem g
  simp only [mul_inv_cancel_left] at h
  exact h.symm
end

section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

private theorem val_lt_one_iff {K : Type} [Field K] (B : ValuationSubring K) (x : K) :
    B.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ B := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < B.valuation x := by
      rw [zero_lt_iff]
      exact (Valuation.ne_zero_iff _).2 hx
    rw [← one_lt_inv₀ h0, ← map_inv₀, ← not_le, B.valuation_le_one_iff]
    simp [hx]

private theorem val_comap_lt_one {K L : Type} [Field K] [Field L] (B : ValuationSubring L) (e : K →+* L) (x : K)
    (h : B.valuation (e x) < 1) : (B.comap e).valuation x < 1 := by
  rw [val_lt_one_iff] at h ⊢
  rcases h with h | h
  · exact Or.inl ((map_eq_zero e).1 h)
  · right
    rw [ValuationSubring.mem_comap, map_inv₀]
    exact h

theorem UpperTheory.V.Z.Kato.Sym.PT.ptIs :
    UpperTheory.V.Z.Kato.Sym.PT.PtIs := by
  intro Ω _ _ _ ε X l n M hl hM hd u v hu hv huF hvF e he η hη
  obtain ⟨hau, hku⟩ := chB Ω ε X l n M hl hM hd u hu.1 huF e he
  obtain ⟨hav, hkv⟩ := chB Ω ε X l n M hl hM hd v hv.1 hvF e he
  obtain ⟨c1, c2, c3, -, -⟩ := cjB Ω ε X M e he
  obtain ⟨hcob, hlc, hun⟩ := hη
  have hD : ∀ g, InD X g → FixF X M g ∧ cj X M e g ∈ geo (topF X M) (topL X M) (topBar X M) :=
    fun g hg => c3 g fun f _ => hg f
  refine ⟨hu, hv, hau, hav, fun g h hg hh => ?_, ?_, ?_⟩
  · show ka X (l ^ n) (e (topRoot X M (l ^ n) u)) g * ka X (l ^ n) (e (topRoot X M (l ^ n) v)) h =
      η (cj X M e h) - η (cj X M e (g * h)) + η (cj X M e g)
    rw [hku g (hD g hg).1, hkv h (hD h hh).1, (c2 g h (hD g hg).1 (hD h hh).1).2.2.1]
    exact hcob _ (hD g hg).2 _ (hD h hh).2
  · classical
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
    haveI : IsGalois (topL X M) (topBar X M) := inferInstance
    obtain ⟨B, hB⟩ := lcGeo (topF X M) (topL X M) (topBar X M) _ η hlc
    refine ⟨B.image e, fun h h' hh hh' hb => ?_⟩
    refine hB _ (hD h hh).2 _ (hD h' hh').2 fun b hbB => e.injective ?_
    rw [c1 h (hD h hh).1, c1 h' (hD h' hh').1]
    exact hb _ (Finset.mem_image_of_mem _ hbB)
  · intro B h hB hh hin
    refine hun (B.comap (e : topBar X M →+* Kb X)) _ (fun f hf => ?_) (fun z hz => ?_) (hD h hh).2
    · rw [ValuationSubring.mem_comap]
      show e _ ∈ B
      rw [he f]
      rcases hf with hf | ⟨c, hc⟩
      · rw [hf]; exact hB.2
      · rw [← hc]; exact hB.1 c
    · apply val_comap_lt_one
      rw [ValuationSubring.valuation_le_one_iff] at hz
      show B.valuation (e _) < 1
      rw [map_sub, c1 h (hD h hh).1]
      exact hin _ ((ValuationSubring.valuation_le_one_iff _ _).2 hz)
end
