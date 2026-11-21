import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem comap_irreducible {G H L : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (π : UnitaryRep G H) (ρ : UnitaryRep G L) (T : H →L[ℂ] L) (hT : ∀ v, ‖T v‖ = ‖v‖)
    (hTπ : ∀ g v, T (π g v) = ρ g (T v)) (V : Submodule ℂ L)
    (hle : ∀ x ∈ V, ∃ v, T v = x) (hcl : IsClosed (V : Set L)) (hinv : ρ.IsInvariant V)
    (hne : V ≠ ⊥) (hirr : ∀ V' ≤ V, IsClosed (V' : Set L) → ρ.IsInvariant V' → V' = ⊥ ∨ V' = V) :
    ∃ (_ : CompleteSpace (V.comap T.toLinearMap)) (hV : π.IsInvariant (V.comap T.toLinearMap)),
      (π.restrict (V.comap T.toLinearMap) hV).IsIrreducible := by
  have hc : IsClosed ((V.comap T.toLinearMap : Submodule ℂ H) : Set H) :=
    IsClosed.preimage T.continuous hcl
  have hI : π.IsInvariant (V.comap T.toLinearMap) := by
    intro g v hv
    show T (π g v) ∈ V
    rw [hTπ]
    exact hinv g _ hv
  have hcs : CompleteSpace (V.comap T.toLinearMap) := hc.completeSpace_coe
  refine ⟨hcs, hI, ?_, fun U hU hUi => ?_⟩
  · rw [Submodule.nontrivial_iff_ne_bot]
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨v, rfl⟩ := hle x hx
    have hv : v ∈ V.comap T.toLinearMap := hx
    rw [h0, Submodule.mem_bot] at hv
    rw [hv, map_zero]
    exact Submodule.zero_mem _
  · let J : (V.comap T.toLinearMap) →ₗᵢ[ℂ] L :=
      { toLinearMap := T.toLinearMap ∘ₗ (V.comap T.toLinearMap).subtype
        norm_map' := fun v => hT v.1 }
    have hinj := Submodule.map_injective_of_injective (f := J.toLinearMap) J.injective
    have htop : (⊤ : Submodule ℂ (V.comap T.toLinearMap)).map J.toLinearMap = V := by
      refine le_antisymm ?_ fun x hx => ?_
      · rintro _ ⟨v, -, rfl⟩
        exact v.2
      · obtain ⟨v, rfl⟩ := hle x hx
        exact ⟨⟨v, hx⟩, trivial, rfl⟩
    have hclU : IsClosed ((U.map J.toLinearMap : Submodule ℂ L) : Set L) :=
      J.isometry.isClosedEmbedding.isClosedMap _ hU
    have hinvU : ρ.IsInvariant (U.map J.toLinearMap) := by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨_, hUi g v hv, hTπ g v.1⟩
    refine (hirr (U.map J.toLinearMap) ((Submodule.map_mono le_top).trans htop.le) hclU hinvU).imp
      (fun h0 => hinj (h0.trans (Submodule.map_bot _).symm)) fun h0 => hinj (h0.trans htop.symm)

theorem UpperTheory.ConvolutionTheory.Dp.sumT :
    UpperTheory.ConvolutionTheory.Dp.SumT := by
  intro K _ _ n μ _ V hV
  exact comap_irreducible (cuspRepT μ) (rightRegularRep (rationalGLOne K n) μ) (toLp μ) (norm_toLp μ)
    (toLp_cuspRepT μ) V (fun x hx => ⟨⟨x, hV.le hx⟩, rfl⟩) hV.closed hV.inv hV.ne_bot hV.irred
end

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.formsIrr :
    UpperTheory.ConvolutionTheory.Dp.FormsIrr := by
  intro K _ _ n μ _ V hV
  obtain ⟨hcs, hI, hirr⟩ := sumT K n μ V hV
  have hc : IsClosed ((V.comap (toLp μ).toLinearMap : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ)) :=
    hV.closed.preimage (toLp μ).continuous
  have e : formsIn μ V = summandCuspForms (V.comap (toLp μ).toLinearMap) := by
    rw [formsIn, clsL, Submodule.comap_comp, summandCuspForms]
  have hne := summandCuspForms_ne_bot μ _ hI hirr
  have hcl := topologicalClosure_map_summandCuspForms hc hI hirr hne
  have h1 := summandCuspForms_stable_ρ hc hI
  have h2 := summandCuspForms_stable_σ hI
  have h3 := summandCuspForms_stable_τ hI
  have h4 := fun W hW a b c d => eq_summandCuspForms (W := W) hc hI hirr hW a b c d
  rw [← e] at hne hcl h1 h2 h3 h4
  refine ⟨⟨h1, h2, h3⟩, hne, fun W hW hs => ?_, ?_⟩
  · exact (em (W = ⊥)).imp_right fun h0 => h4 W hW hs.ρ hs.σ hs.τ h0
  · refine le_antisymm (Submodule.topologicalClosure_minimal _ ?_ hV.closed) fun v hv => ?_
    · exact Submodule.map_le_iff_le_comap.2 inf_le_right
    · obtain ⟨u, rfl⟩ : ∃ u : CuspL2 μ, toLp μ u = v := ⟨(⟨v, hV.le hv⟩ : cuspidalL2 μ), rfl⟩
      have hu : u ∈ closure (((formsIn μ V).map (cuspVecL μ) : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ)) := by
        rw [← Submodule.topologicalClosure_coe, hcl]
        exact hv
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      refine map_mem_closure (toLp μ).continuous hu fun x hx => ?_
      obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hx
      exact Submodule.mem_map_of_mem (f := clsL μ) hφ
end
