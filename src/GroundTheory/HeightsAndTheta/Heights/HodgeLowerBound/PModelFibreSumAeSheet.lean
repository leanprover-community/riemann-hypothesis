import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ModelProjObjects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeF

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ModelFibreSumAe.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : HermLine ι) (c : ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (E : Set M.Xc) (v : M.Xc → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsSmoothHerm L → IsPtsNull P e N →
    (∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' E) = 0) →
    (∀ z ∈ mcPts P, z ∉ N → M.proj z ∉ E → g z = v (M.proj z)) →
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (fun (_ : Fin e) z => c * Real.log (L.h z)) g y w =
      ∑ᶠ x ∈ modelQ M Ψ ⁻¹' {y} \ modelBad M Ψ E,
        v x * pushDens M.atlas (fun (_ : Fin e) => modelPot M L c) (modelQ M Ψ) x

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace ModelFibreSumAlmostEverywhere

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem lift_mem (x : M.Xc) : modelLift M x x ∈ mcPts P :=
  ((modelLift_spec M x).1 x (mem_modelU M x)).1

theorem proj_lift (x : M.Xc) : M.proj (modelLift M x x) = x :=
  ((modelLift_spec M x).1 x (mem_modelU M x)).2

theorem lift_compat {x z : M.Xc} (hz : z ∈ modelU M x) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ modelLift M z z = fun p => c p.1 * modelLift M x z p := by
  have h1 := (modelLift_spec M x).1 z hz
  obtain ⟨c, hc, h⟩ := (M.fibre _ h1.1 _ (lift_mem M z)).mp (h1.2.trans (proj_lift M z).symm)
  exact ⟨c, hc, h⟩

theorem proj_eq_of_segre {x : M.Xc} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (μ : ℂ) (hμ : μ ≠ 0)
    (h : segre z = μ • segre (modelLift M x x)) : M.proj z = x := by
  obtain ⟨c, hc, hzc⟩ := sameOrbit_of_segre (lift_mem M x).1 μ hμ h
  have := (M.fibre _ (lift_mem M x) _ hz).mpr ⟨c, hc, hzc⟩
  rw [← this, proj_lift]

theorem modelQ_eq_local {x z : M.Xc} (hz : z ∈ modelU M x) :
    modelQ M Ψ z = fun i => Ψ (segre (modelLift M x z)) i.succ / Ψ (segre (modelLift M x z)) 0 := by
  obtain ⟨c, hc, hzc⟩ := lift_compat M hz
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext i
  simp only [modelQ, hzc, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem analyticAt_lift_chart (x : M.Xc) (j : Fin M.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x) :
    AnalyticAt ℂ (fun v => modelLift M x ((M.atlas.chart j).symm v)) u :=
  analyticAt_pi_iff.mpr fun p => (modelLift_spec M x).2 p j u hu

theorem analyticAt_segre_lift (x : M.Xc) (j : Fin M.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x) :
    AnalyticAt ℂ (fun v => Ψ (segre (modelLift M x ((M.atlas.chart j).symm v)))) u := by
  classical
  have hl := analyticAt_lift_chart M x j hu
  have hs : AnalyticAt ℂ (fun v => segre (modelLift M x ((M.atlas.chart j).symm v))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs

theorem analyticAt_modelQ (x : M.Xc) (j : Fin M.atlas.n) (hj : x ∈ (M.atlas.chart j).source)
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) :
    AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) := by
  set u := M.atlas.chart j x
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  have hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x :=
    ⟨(M.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact mem_modelU M x⟩
  have hH := analyticAt_segre_lift M Ψ x j hu
  have hH0 : AnalyticAt ℂ (fun v => Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre (modelLift M x ((M.atlas.chart j).symm u))) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun v => fun i : Fin e =>
      Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) i.succ /
        Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x)).mem_nhds hu,
    hH0.continuousAt.eventually_ne hne] with v hv hv0
  exact (modelQ_eq_local M Ψ hv.2).symm

theorem psi_zero_ne_of_not_mem_bad {E : Set M.Xc} {x : M.Xc} (hx : x ∉ modelBad M Ψ E) :
    Ψ (segre (modelLift M x x)) 0 ≠ 0 :=
  fun h => hx (Or.inr (Or.inl h))

theorem notMem_of_notMem_bad {E : Set M.Xc} {x : M.Xc} (hx : x ∉ modelBad M Ψ E) : x ∉ E :=
  fun h => hx (Or.inl h)

def modelW (x : M.Xc) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)

theorem modelW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : M.Xc}
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) : modelW M Ψ x ∈ fibre P Ψ (modelQ M Ψ x) := by
  classical
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (modelLift M x x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (modelLift M x x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * modelLift M x x p, mcPts_smul hPh c hc (lift_mem M x), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [modelW, h0]
    · simp only [modelW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, modelQ]
      rw [div_eq_inv_mul]

theorem modelW_injOn : Set.InjOn (modelW M Ψ) {x | Ψ (segre (modelLift M x x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  have h := congrArg (fun v => Ψ (segre (modelLift M x x)) 0 • v) hw
  simp only [modelW, smul_smul, mul_inv_cancel₀ (show Ψ (segre (modelLift M x x)) 0 ≠ 0 from hx),
    one_smul] at h
  have := proj_eq_of_segre M (lift_mem M x)
    (Ψ (segre (modelLift M x x)) 0 * (Ψ (segre (modelLift M x' x')) 0)⁻¹)
    (by simp [show Ψ (segre (modelLift M x x)) 0 ≠ 0 from hx,
      show Ψ (segre (modelLift M x' x')) 0 ≠ 0 from hx']) h
  rw [proj_lift] at this
  exact this

theorem mem_fibre_data {y : Fin e → ℂ} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hΨz : Ψ (segre z) = Fin.cons 1 y) :
    Ψ (segre (modelLift M (M.proj z) (M.proj z))) 0 ≠ 0 ∧ modelQ M Ψ (M.proj z) = y ∧
      modelW M Ψ (M.proj z) = segre z := by
  obtain ⟨c, hc, hxc⟩ := (M.fibre _ hz _ (lift_mem M (M.proj z))).mp (proj_lift M _).symm
  have hseg : segre (modelLift M (M.proj z) (M.proj z)) = (∏ k, c k) • segre z := by
    rw [hxc]; exact segre_smul c z
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hΨx : Ψ (segre (modelLift M (M.proj z) (M.proj z))) = (∏ k, c k) • Fin.cons 1 y := by
    rw [hseg, map_smul, hΨz]
  have h0 : Ψ (segre (modelLift M (M.proj z) (M.proj z))) 0 = ∏ k, c k := by simp [hΨx]
  refine ⟨by rw [h0]; exact hpc, ?_, ?_⟩
  · funext i
    simp only [modelQ, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    field_simp
  · rw [modelW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]

theorem image_bad_null {E : Set M.Xc}
    (hE : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' E) = 0) :
    volume (modelQ M Ψ '' (modelBad M Ψ E ∩ {x | Ψ (segre (modelLift M x x)) 0 ≠ 0})) = 0 := by
  set A := M.atlas
  set G : Set M.Xc := {x | Ψ (segre (modelLift M x x)) 0 ≠ 0}
  set D : Fin A.n → Set (Fin e → ℂ) := fun j => {u | u ∈ (A.chart j).target ∧
    (A.chart j).symm u ∈ G ∧ ¬ (AnalyticAt ℂ (modelQ M Ψ ∘ (A.chart j).symm) u ∧
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}
  have han : ∀ j, ∀ u ∈ (A.chart j).target, (A.chart j).symm u ∈ G →
      AnalyticAt ℂ (modelQ M Ψ ∘ (A.chart j).symm) u := by
    intro j u hu hG
    have := analyticAt_modelQ M Ψ _ j ((A.chart j).map_target hu) hG
    rwa [(A.chart j).right_inv hu] at this
  have hsub : modelQ M Ψ '' (modelBad M Ψ E ∩ G) ⊆
      (⋃ j, (modelQ M Ψ ∘ (A.chart j).symm) ''
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (E ∩ G))) ∪
      ⋃ j, (modelQ M Ψ ∘ (A.chart j).symm) '' D j := by
    rintro _ ⟨x, ⟨hxb, hxG⟩, rfl⟩
    rcases hxb with hxE | hxc
    · obtain ⟨j, hj⟩ := A.cover x
      refine Or.inl (Set.mem_iUnion.mpr ⟨j, A.chart j x, ⟨(A.chart j).map_source hj, ?_⟩, ?_⟩)
      · rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact ⟨hxE, hxG⟩
      · simp [(A.chart j).left_inv hj]
    · rcases hxc with h0 | ⟨j, hj, hbad⟩
      · exact absurd h0 hxG
      · refine Or.inr (Set.mem_iUnion.mpr ⟨j, A.chart j x, ⟨(A.chart j).map_source hj, ?_, hbad⟩, ?_⟩)
        · show (A.chart j).symm (A.chart j x) ∈ G
          rw [(A.chart j).left_inv hj]; exact hxG
        · simp [(A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun j => ?_)
    (measure_iUnion_null fun j => ?_))
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
        (hE j))
    intro u hu
    exact ((han j u hu.1 hu.2.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u).restrictScalars ℝ) ?_ ?_
    · intro u hu
      exact ((han j u hu.1 hu.2.1).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro u hu
      have h0 : LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
        by_contra h
        exact hu.2.2 ⟨han j u hu.1 hu.2.1, h⟩
      have := abs_det_restrictScalars (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u)
      rw [h0, norm_zero, zero_pow two_ne_zero, abs_eq_zero] at this
      exact this

end ModelFibreSumAlmostEverywhere

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace ModelFibreSumAlmostEverywhere

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))


theorem exists_sheet (L : HermLine ι) (r : ℝ) (E : Set M.Xc) (hP : IsArithVar P (e + 1))
    (hL : IsSmoothHerm L) (x : M.Xc) (hx : x ∉ modelBad M Ψ E) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ, IsSheet P Ψ (modelQ M Ψ x) (modelW M Ψ x) γ ∧
      maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ y'))) (modelQ M Ψ x) =
        pushDens M.atlas (fun _ => modelPot M L r) (modelQ M Ψ) x := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  set j := chartIdx M.atlas x with hjdef
  have hj : x ∈ (M.atlas.chart j).source := Classical.choose_spec (M.atlas.cover x)
  set u := M.atlas.chart j x with hudef
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  have huU : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x :=
    ⟨(M.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact mem_modelU M x⟩
  obtain ⟨hQa, hQd⟩ := modelQ_good_of_notMem M Ψ E x hx j hj
  set Q := modelQ M Ψ ∘ (M.atlas.chart j).symm with hQdef
  set Df := fderiv ℂ Q u with hDf
  have hdet : Df.det ≠ 0 := hQd
  set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe
  have hCe' : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = Df :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet
  have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
    rw [hCe']; exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph Q with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
  have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyt : Q u ∈ F.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hσu : F.symm (Q u) = u := by
    have := F.left_inv hus
    rwa [hFc] at this
  have hy0 : Q u = modelQ M Ψ x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  set γ₀ : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' => modelLift M x ((M.atlas.chart j).symm (F.symm y')) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := (analyticAt_lift_chart M x j huU).comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = modelLift M x x := by simp only [hγ₀, hσu, hsu]
  set ψ0 : (Fin e → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp ((analyticAt_segre_lift M Ψ x j huU).comp_of_eq hσa hσu) 0
  have hψ0u : ψ0 (Q u) ≠ 0 := by
    simp only [hψ0, hγ₀u]; exact psi_zero_ne_of_not_mem_bad M Ψ hx
  set c : (Fin e → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹
    with hcdef
  have hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0 := by
    intro y' h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp only [hcdef, Function.update_self]; exact hψ0a.inv hψ0u
    · simp only [hcdef, Function.update_of_ne hk]; exact analyticAt_const
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef
  have hγa : AnalyticAt ℂ γ (Q u) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)
  have hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y') := fun y' => by
    rw [← hprod y']; exact segre_smul (c y') (γ₀ y')
  refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
  · rw [← hy0, hseg]
    simp only [hψ0, hγ₀u]
    rfl
  · rw [← hy0]
    have hU : ∀ᶠ y' in 𝓝 (Q u),
        F.symm y' ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]; exact ((M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x)).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt,
      mcPts_smul hPh (c y') (hc_ne y' h0) ((modelLift_spec M x).1 _ hUy.2).1, ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, modelQ_eq_local M Ψ hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact (lift_mem M x).1
    have hH : cxHessian (fun y' => r * Real.log (L.h (γ y'))) (Q u) =
        cxHessian (fun y' => r * Real.log (L.h (γ₀ y'))) (Q u) := by
      set G : (Fin e → ℂ) → ℂ :=
        fun y' => ((-(r * (L.a k0 : ℝ)) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(r * (L.a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u]
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => r * Real.log (L.h (γ y'))) =ᶠ[𝓝 (Q u)]
          fun y' => r * Real.log (L.h (γ₀ y')) + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u,
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < L.h (γ₀ y') := L.pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ L.a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl, L.smul _ _ (hc_ne y' h0),
          prod_norm_update_zpow, Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => r * Real.log (L.h (γ₀ y'))) C
        (contDiffAt_const.mul (pot_contDiffAt hL hγ₀a hblk)) hGa]
    have hmd : maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ y'))) (Q u) =
        maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ₀ y'))) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd, maDensity_eq_maDens]
    have hcd : ∀ i : Fin e, ContDiffAt ℝ 2
        (fun v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v)))) (F.symm (Q u)) := by
      intro i
      rw [hσu]
      exact contDiffAt_const.mul (pot_contDiffAt hL (analyticAt_lift_chart M x j huU)
        (by rw [hsu]; exact (lift_mem M x).1))
    have hcomp : ReciprocityTheory.AnForm.maDens (fun (_ : Fin e) y' => r * Real.log (L.h (γ₀ y'))) (Q u) =
        ReciprocityTheory.AnForm.maDens
          (fun (_ : Fin e) v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v))))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp
        (fun (_ : Fin e) v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v))))
        F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    have hloc : ReciprocityTheory.AnForm.maDens
        (fun (_ : Fin e) v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v)))) u =
        locDens M.atlas (fun _ => modelPot M L r) j u := by
      unfold locDens
      rw [hsu]
      rfl
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    unfold pushDens
    rw [div_eq_mul_inv]

end ModelFibreSumAlmostEverywhere

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
