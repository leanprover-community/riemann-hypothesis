import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.formsClosure :
    UpperTheory.ConvolutionTheory.Dp.FormsClosure := by
  intro K _ _ n μ _ U hU hs
  have hsup := sup_orthRel_centralCuspForms μ U hU hs.ρ hs.τ
  have hin : ∀ a b : cuspForms K n, inner ℂ (clsL μ a) (clsL μ b) = inner ℂ (cuspToL2 μ a) (cuspToL2 μ b) :=
    fun _ _ => rfl
  apply le_antisymm
  · rintro φ ⟨hφc, hφV⟩
    have hφc' := hφc
    rw [← hsup] at hφc'
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hφc'
    have huV : clsL μ u ∈ (U.map (clsL μ)).topologicalClosure :=
      Submodule.le_topologicalClosure _ ⟨u, hu, rfl⟩
    have hcV : clsL μ c ∈ (U.map (clsL μ)).topologicalClosure := by
      have h : clsL μ (u + c) ∈ (U.map (clsL μ)).topologicalClosure := hφV
      rw [map_add] at h
      simpa using Submodule.sub_mem _ h huV
    have hle : U.map (clsL μ) ≤ (ℂ ∙ clsL μ c)ᗮ := by
      rintro _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, hin]
      exact hc.2 v hv
    have h2 := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _) hcV
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hin, inner_self_eq_zero] at h2
    have h0 : c = 0 :=
      injOn_cuspToL2 μ (hc.1 : _) (fun _ _ => rfl) (h2.trans (map_zero (cuspToL2 μ)).symm)
    rw [h0, add_zero]
    exact hu
  · intro φ hφ
    exact ⟨hU hφ, Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩⟩
end

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

set_option maxHeartbeats 1600000 in
theorem UpperTheory.ConvolutionTheory.Dp.closureSummand :
    UpperTheory.ConvolutionTheory.Dp.ClosureSummand := by
  intro K _ _ n μ _ U hU hs h0 hirr
  have hcl : IsClosed (cuspidalL2 μ : Set (LL μ)) := (completeSpace_coe_iff_isComplete.1 (inferInstanceAs (CompleteSpace (CuspL2 μ)))).isClosed
  have hle : (U.map (clsL μ)).topologicalClosure ≤ cuspidalL2 μ :=
    Submodule.topologicalClosure_minimal _ (by rintro _ ⟨φ, -, rfl⟩; exact toLp_mem μ _) hcl
  have hI := isInvariant_topologicalClosure_map μ hU hs.ρ hs.σ hs.τ
  have hmap : ∀ y ∈ (U.map (cuspVecL μ)).topologicalClosure, toLp μ y ∈ (U.map (clsL μ)).topologicalClosure := fun y hy =>
    Submodule.topologicalClosure_minimal (U.map (cuspVecL μ))
      (t := (U.map (clsL μ)).topologicalClosure.comap (toLp μ).toLinearMap)
      (by rintro _ ⟨φ, hφ, rfl⟩; exact Submodule.le_topologicalClosure (U.map (clsL μ)) ⟨φ, hφ, rfl⟩)
      ((Submodule.isClosed_topologicalClosure _).preimage (toLp μ).continuous) hy
  refine ⟨hle, Submodule.isClosed_topologicalClosure _, fun g v hv => ?_, fun e => h0 ?_, fun V' hV' hc hi => ?_⟩
  · refine mem_of_mem_topologicalClosure (Submodule.isClosed_topologicalClosure _) (rightRegularRep (rationalGLOne K n) μ g) ?_ hv
    rintro _ ⟨φ, hφ, rfl⟩
    exact hmap _ (hI g _ (Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩))
  · refine eq_bot_iff.2 fun φ hφ => eq_zero_of_cuspVecL_eq_zero (μ := μ) (hU hφ) (toLp_injective μ ?_)
    have h1 : clsL μ φ ∈ (U.map (clsL μ)).topologicalClosure := Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩
    rw [e, Submodule.mem_bot] at h1
    exact h1.trans (map_zero (toLp μ)).symm
  · refine or_iff_not_imp_left.2 fun hne => le_antisymm hV' ?_
    set W := V'.comap (toLp μ).toLinearMap with hW
    have hWc : IsClosed (W : Set (CuspL2 μ)) := hc.preimage (toLp μ).continuous
    have hWi : (cuspRepT μ).IsInvariant W := fun g v hv => hi g _ hv
    have hW0 : W ≠ ⊥ := by
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact (Submodule.ne_bot_iff _).2 ⟨(⟨v, hle (hV' hv)⟩ : cuspidalL2 μ), hv, fun e => hv0 (congrArg Subtype.val e)⟩
    obtain ⟨φ, hφ, hφ0, hφW⟩ := exists_cuspForm_mem_of_ne_bot μ hWc hWi hW0
    have h1 : summandCuspForms W ≤ U := fun ψ hψ => by
      rw [← formsClosure K n μ U hU hs]
      exact ⟨hψ.1, hV' hψ.2⟩
    rcases hirr _ h1 ⟨summandCuspForms_stable_ρ hWc hWi, summandCuspForms_stable_σ hWi, summandCuspForms_stable_τ hWi⟩ with e | e
    · have h2 : φ ∈ summandCuspForms W := mem_summandCuspForms.2 ⟨hφ, hφW⟩
      rw [e, Submodule.mem_bot] at h2
      exact (hφ0 h2).elim
    · have hmin : U.map (clsL μ) ≤ V' := by
        rintro _ ⟨ψ, hψ, rfl⟩
        have h3 : ψ ∈ summandCuspForms W := e.ge hψ
        exact (mem_summandCuspForms.1 h3).2
      exact fun v hv => closure_minimal (show ((U.map (clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) ⊆ V' from hmin) hc hv
end

section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.exSummand :
    UpperTheory.ConvolutionTheory.Dp.ExSummand := by
  intro E _ _ _ n μ _ π V
  constructor
  · intro h
    refine ⟨h.carrier_eq ▸ inf_le_left, ?_⟩
    rw [h.carrier_eq, (formsIrr E n μ V h.summand).2.2.2]
  · rintro ⟨hc, rfl⟩
    obtain ⟨hne, hirr⟩ := (Cm.stab_carrier π).isIrreducible_iff.1 (Cm.isIrreducible_toModule π)
    exact ⟨closureSummand E n μ _ hc (Cm.stab_carrier π) hne hirr, (formsClosure E n μ _ hc (Cm.stab_carrier π)).symm⟩
end
