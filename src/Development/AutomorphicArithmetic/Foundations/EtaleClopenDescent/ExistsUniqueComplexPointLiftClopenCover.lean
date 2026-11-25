module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.existsUnique_complexPoint_lift_clopen_cover :
    ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (M : Type) (W : M → Y.Opens), (∀ i j, i ≠ j → W i ⊓ W j = ⊥) → iSup W = ⊤ → ∀ y : CxPts s' (RingHom.id ℂ), ∃! m : M, ∃! y' : CxPts ((W m).ι ≫ s') (RingHom.id ℂ), y'.1 ≫ (W m).ι = y.1 := by
  intro Y s' M W hd hc y
  obtain ⟨m, hm⟩ := CxPts.exists_mem_ptsIn hc y
  have hr : Set.range y.1 ⊆ Set.range (W m).ι := by
    rw [Scheme.Opens.range_ι, Set.range_subset_iff]
    exact fun x => hm (show x ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  refine ⟨m, ?_, ?_⟩
  · refine ⟨⟨IsOpenImmersion.lift (W m).ι y.1 hr, ?_⟩, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    · rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact y.2
    · exact fun z hz => Subtype.ext (IsOpenImmersion.lift_uniq _ _ hr z.1 hz)
  · rintro m' ⟨z, hz, -⟩
    by_contra hne
    let x : (Sp ℂ : Scheme.{0}) := IsLocalRing.closedPoint ℂ
    have hz' : z.1 ≫ (W m').ι = y.1 := hz
    have hm' : y.1 x ∈ W m' := by
      rw [← hz', Scheme.Hom.comp_apply]
      exact (z.1 x).2
    have hmem : y.1 x ∈ W m' ⊓ W m := ⟨hm', CxPts.mem_ptsIn.mp hm⟩
    rw [hd m' m hne] at hmem
    exact hmem
