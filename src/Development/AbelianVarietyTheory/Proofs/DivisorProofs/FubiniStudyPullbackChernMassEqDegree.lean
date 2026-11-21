import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeComplexPointsProperClosedChartFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyHessianDeterminantRealPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFubiniStudyDensityEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartComplementDenseOpenNullField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCovering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDim
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LbH0EqChiStructureModuleOfKrullDimZero

section
open Set Filter Topology MeasureTheory

namespace GlobalTheory

theorem finrank_range_fderiv_lt_of_volume_image_eq_zero :
    ∀ (n : ℕ) (h : (Fin n → ℂ) → (Fin n → ℂ)) (W : Set (Fin n → ℂ)), IsOpen W → AnalyticOnNhd ℂ h W → volume (h '' W) = 0 → ∀ y ∈ W, Module.finrank ℂ (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) < n := by
  intro n h W hW ha h0 y hy
  by_contra hlt
  have hn : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  have hle := Submodule.finrank_le
    (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
  have htop : LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by omega)
  have hs : HasStrictFDerivAt h (fderiv ℂ h y) y := (ha y hy).hasStrictFDerivAt
  have hmap := hs.map_nhds_eq_of_surj htop
  have hmem : h '' W ∈ 𝓝 (h y) := by
    rw [← hmap]
    exact image_mem_map (hW.mem_nhds hy)
  exact (Measure.measure_pos_of_mem_nhds volume hmem).ne' h0

end GlobalTheory
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem finrank_range_fderiv_lt_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (A : FinHolAtlas D (CxPts p σ)) (A' : FinHolAtlas D (CxPts q σ)), IsAlgAtlas A → IsAlgAtlas A' → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) ≠ genericPoint X → ∀ j l, ∀ y ∈ (A'.chart j).target, PtsOver.map π hπ (spMap σ) ((A'.chart j).symm y) ∈ (A.chart l).source → Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart l ∘ PtsOver.map π hπ (spMap σ) ∘ (A'.chart j).symm) y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) < D := by
  intro k _ X Y _ _ p q σ D A A' hA hA' π hπ hgen j l y hy hyl
  set m := PtsOver.map π hπ (spMap σ) with hm_def
  have hm : ∀ z : CxPts q σ, (m z).1 = z.1 ≫ π := fun _ => rfl
  have hH := hA.holoMap hA' (f := π) hm
  set W := (A'.chart j).target ∩ (A'.chart j).symm ⁻¹' (m ⁻¹' (A.chart l).source) with hW_def
  have hWo : IsOpen W := (A'.chart j).isOpen_inter_preimage_symm
    ((A.chart l).open_source.preimage hH.1)
  have han : AnalyticOnNhd ℂ (A.chart l ∘ m ∘ (A'.chart j).symm) W := hH.2 j l
  set Z : Set X := closure {π (genericPoint Y)} with hZ_def
  have hZc : IsClosed Z := isClosed_closure
  have hZg : genericPoint X ∉ Z := by
    intro h
    have h1 : π (genericPoint Y) ⤳ genericPoint X := specializes_iff_mem_closure.2 h
    have h2 : genericPoint X ⤳ π (genericPoint Y) := genericPoint_specializes _
    exact hgen (h1.antisymm h2).eq
  have hZm : ∀ z : CxPts q σ, (m z).1 (IsLocalRing.closedPoint ℂ) ∈ Z := by
    intro z
    have hs : genericPoint Y ⤳ z.1 (IsLocalRing.closedPoint ℂ) := genericPoint_specializes _
    have := hs.map π.continuous
    rw [hm]
    exact specializes_iff_mem_closure.1 this
  obtain ⟨c, hc⟩ := hA l
  have hnull := GlobalTheory.T.volume_complexPoints_properClosed_chart_field k X p σ D Z hZc hZg c
  have hsub : (A.chart l ∘ m ∘ (A'.chart j).symm) '' W ⊆
      FinChart.toV D ⁻¹' (c.e '' (c.e.source ∩ {x : CxPts p σ | x.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨m ((A'.chart j).symm z), ⟨?_, hZm _⟩, ?_⟩
    · have := hz.2
      rw [hc] at this
      exact this
    · simp only [Function.comp_apply, hc]
      rfl
  have h0 : volume ((A.chart l ∘ m ∘ (A'.chart j).symm) '' W) = 0 :=
    measure_mono_null hsub (FinChart.measurePreserving_toV.quasiMeasurePreserving.preimage_null hnull)
  exact finrank_range_fderiv_lt_of_volume_image_eq_zero D _ W hWo han h0 y ⟨hy, hyl⟩

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_fderiv_lt_of_not_dominant_charts : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (A : FinHolAtlas D (CxPts p σ)) (A' : FinHolAtlas D (CxPts q σ)), IsAlgAtlas A → IsAlgAtlas A' → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) ≠ genericPoint X → ∀ j l, ∀ y ∈ (A'.chart j).target, PtsOver.map π hπ (spMap σ) ((A'.chart j).symm y) ∈ (A.chart l).source → Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart l ∘ PtsOver.map π hπ (spMap σ) ∘ (A'.chart j).symm) y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) < D := by
  atlas_forward_decl GlobalTheory.finrank_range_fderiv_lt_of_not_dominant
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory

theorem chernInt_pull_fubiniStudy_eq_zero_of_not_dominant : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), (∃ x : PSpace ℂ Y.dim, ¬ π (genericPoint Y.X) ⤳ x) → Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = 0 := by
  intro Y π hπ ⟨x, hx⟩
  have := ProjSpace.isIntegral_of_isDomain ℂ Y.dim
  obtain ⟨-, -, -, A', hA'⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  have hA : IsAlgAtlas (ProjAn.finAtlas ℂ (RingHom.id ℂ) Y.dim) := AnRead.isAlgAtlas_finAtlas _
  have hne : π (genericPoint Y.X) ≠ genericPoint (PSpace ℂ Y.dim) := fun h =>
    hx (h ▸ genericPoint_specializes x)
  have hc := (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf (RingHom.id ℂ)
  have hs := (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).isSmooth hA.anRead
  rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y _ _ (hc.pull π hπ)).2 A' hA',
    SameForm.mInt_eq (fun _ => hs.sameForm_pull hA hA' π hπ)]
  exact rankDrop _ A' _ (hA.holoMap hA' (f := π) fun _ => rfl)
    (GlobalTheory.T.finrank_range_fderiv_lt_of_not_dominant_charts ℂ _ _ _ _ _ _ _ A' hA hA' π hπ hne) _ (fun _ => hs.isPotential hA) _

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernInt_pull_fubiniStudy_eq_zero_of_not_specializes : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), (∃ x : PSpace ℂ Y.dim, ¬ π (genericPoint Y.X) ⤳ x) → Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = 0 := by
  atlas_forward_decl GlobalTheory.chernInt_pull_fubiniStudy_eq_zero_of_not_dominant
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projSpace_standardChart_fubiniStudy : ∀ N : ℕ, ∃ (c : AlgChart (PSpace.str ℂ N) (RingHom.id ℂ) N) (i : (ProjSpace.hermitianTwistingSheaf ℂ N).B.ι), c.e.source = ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) (ProjSpace.chart ℂ N 0) ∧ c.e.target = Set.univ ∧ c.e.source ⊆ ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) ((ProjSpace.hermitianTwistingSheaf ℂ N).B.U i) ∧ ∀ v, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).φ i (c.e.symm v) = Real.log (1 + ‖v‖ ^ 2) := by
  first | exact @GlobalTheory.StdProjChart.exists_stdChart | exact GlobalTheory.StdProjChart.exists_stdChart | (intros; apply GlobalTheory.StdProjChart.exists_stdChart <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_complexHessian_fubiniStudy_potential : ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), (ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v).det.re = ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹ := by
  first | exact @GlobalTheory.FSDet.det_fubiniStudy_hess | exact GlobalTheory.FSDet.det_fubiniStudy_hess | (intros; apply GlobalTheory.FSDet.det_fubiniStudy_hess <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fubiniStudy_density_eq_one' : ∀ n : ℕ, ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n, ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) = 1 := by
  first | exact @GlobalTheory.lintegral_fubiniStudy_density_eq_one | exact GlobalTheory.lintegral_fubiniStudy_density_eq_one | (intros; apply GlobalTheory.lintegral_fubiniStudy_density_eq_one <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.FSMass

theorem chern_mass_hermitian_O_one_projective : ∀ N : ℕ, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N 1 Set.univ = 1 ∧ ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N (-1) Set.univ = 0 := by
  intro N
  have hproj : IsProjOver (PSpace.str ℂ N) := ProjSpace.isProjOver_str ℂ N
  haveI : IsIntegral (PSpace ℂ N) := ProjSpace.isIntegral_of_isDomain ℂ N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).IsCInf := (ProjSpace.hermitianTwistingSheaf ℂ N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf ℂ N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := GlobalTheory.T.exists_projSpace_standardChart_fubiniStudy N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace ℂ N) ∈ ProjSpace.chart ℂ N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) (ProjSpace.chart ℂ N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace ℂ N)).mem_open_set_iff (ProjSpace.chart ℂ N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := GlobalTheory.T.chernPart_complement_dense_open_null_field ℂ (PSpace ℂ N) (PSpace.str ℂ N) (RingHom.id ℂ) N hproj _ hgen _
    ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)) 1
  rw [← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (GlobalTheory.T.lintegral_fubiniStudy_density_eq_one' N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, GlobalTheory.T.det_complexHessian_fubiniStudy_potential N v]
  simp
end GlobalTheory.FSMass
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_form_fubini_study_total : ∀ N : ℕ, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N 1 Set.univ = 1 ∧ ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N (-1) Set.univ = 0 := by
  atlas_forward_decl GlobalTheory.FSMass.chern_mass_hermitian_O_one_projective
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjFormulaTop

theorem topSelf_pull_eq_mul : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k] (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X ≤ D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom p; letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = (π.residueDegree (genericPoint Y) : ℤ) * topSelfIntersection k B D := by
  intro k _ X Y _ _ p q _ D hp hq hD π hπ hgen hdeg B hB
  obtain ⟨U, hU, hgU, hU', -, hfin, hfree, hrank⟩ :=
    GlobalTheory.T.exists_affine_etale_finite_free_nbhd k X Y p q hp hq π hπ hgen hdeg
  subst hπ
  letI := GlobalTheory.algebraΓOfHom p
  letI := GlobalTheory.algebraΓOfHom (π ≫ p)
  rw [topSelf_def, topSelf_def]
  letI := (π.app U).hom.toAlgebra
  have hfin' : Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := hfin
  exact GlobalTheory.FieldProj.interNum_pull_eq_mul k Y X p π hq hp U _ hgU hU hU'
    ⟨hfree, hfin', hrank⟩ D hD (fun _ => B) (fun _ => hB)

end GlobalTheory.ProjFormulaTop
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSelfIntersection_pullback_eq_degree_mul : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k] (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X ≤ D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom p; letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = (π.residueDegree (genericPoint Y) : ℤ) * topSelfIntersection k B D := by
  atlas_forward_decl GlobalTheory.ProjFormulaTop.topSelf_pull_eq_mul
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSelfIntersection_pullback_eq_zero_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver q → topologicalKrullDim X ≤ D → topologicalKrullDim Y ≤ D → ∀ (π : Y ⟶ X), π (genericPoint Y) ≠ genericPoint X → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = 0 := by
  first | exact @GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant | exact GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant | (intros; apply GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false
noncomputable section
open scoped Classical
open GlobalTheory.ChartGlue

namespace GlobalTheory.CoverDegField

theorem exists_open_covering_charts : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  intro k _ X Y _ _ p q σ D hpP hqP hsm π hπ hη hδ
  haveI : SmoothOfRelativeDimension D p := hsm
  haveI : CharZero k := RingHom.charZero σ
  obtain ⟨U₁, t₁, hU₁, hx₁, ht⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := p) (D := D) (genericPoint X)
  obtain ⟨U₂, hU₂, hx₂, hV₂, he₂, hf₂, hr₂⟩ := GlobalTheory.T.exists_affine_etale_finite_free_nbhd k X Y p q hpP hqP π hπ hη hδ
  obtain ⟨U, hxU, hG⟩ := GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover p π D _ _ U₁ U₂ hU₁ hx₁ ⟨t₁, ht⟩ hU₂ hx₂ hV₂ he₂ hf₂ hr₂
  refine ⟨U, hxU, fun y hy => ?_, fun y hy => ?_, fun z hz c hc => ?_⟩
  · rw [GlobalTheory.encard_fibre_eq_encard_ringHom π hπ U hG.1 hG.2.1 σ y hy]
    exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank (π.app U).hom _ hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2 _
  · obtain ⟨t, ht⟩ := hG.2.2.1
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hG.1 t ht hy
    exact ⟨c, hc⟩
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hV, hzV, h, hVe⟩ := GlobalTheory.CoverDeg.etale_pullback_coords π hπ D _ U hG c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hV _ hVe (mem_ptsIn.2 hzV)
    have key : ∀ w ∈ c''.e.source, w ∈ ptsIn q σ V ∧
        ∀ a, c''.e w a = ev q σ V ((π.appLE c.U V h).hom (c.x a)) w := by
      rcases c'' with ⟨e, U', aff, x', et, ss, ae, ho⟩
      dsimp only at hU'' hx'' ⊢
      subst hU''
      have hx : x' = fun a => (π.appLE c.U U' h).hom (c.x a) := hx''
      subst hx
      exact fun w hw => ⟨ss hw, ae w hw⟩
    have hS : IsOpen (c''.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
      (PtsOver.continuous_map π hπ (spMap σ)).continuousOn.isOpen_inter_preimage c''.e.open_source
        c.e.open_source
    refine ⟨c''.restr _ hS, ⟨hc'', hc'', hc⟩, fun w hw => ⟨hw.2.2, ?_⟩⟩
    have hw' : w ∈ c''.e.source := hw.1
    obtain ⟨hwV, hwe⟩ := key w hw'
    ext a
    change c''.e w a = c.e (PtsOver.map π hπ (spMap σ) w) a
    rw [hwe a, c.apply_eq _ hw.2.2 a]
    exact valR_appLE w.1 π h hwV _

end GlobalTheory.CoverDegField
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_covering_charts_generically_finite_field : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  atlas_forward_decl GlobalTheory.CoverDegField.exists_open_covering_charts
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverChernField

theorem chernPart_preimage_of_cover : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ n : ℕ, (∀ y ∈ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ) ⁻¹' U) = (n : ENNReal) * φ.chernPart D ε U := by
  intro k _ X Y _ _ p q σ D hp hq π hπ B φ hφ ε U hU n hfib hchart hlift
  have := CxPts.t2Space_cxPts_of_isProjOver σ hq
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq
  have hφ' := hφ.pull π hπ
  unfold Weight.chernPart
  refine GlobalTheory.CoverChern.glueMeas_preimage_of_cover_on (fun c c' => c.holo_trans c')
    (fun c c' y hy hy' => ?_)
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (PtsOver.continuous_map π hπ _) hU hfib (fun z hz => ?_) hU.measurableSet subset_rfl
  · rw [c.chernDens_trans c' hφ hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · rw [c.chernDens_trans c' hφ' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · obtain ⟨c, hc⟩ := hchart _ hz
    obtain ⟨c', hz', hc'⟩ := hlift z hz c hc
    exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2, by
      rw [GlobalTheory.PullChartDens.chernDens_pull_of_chart π hπ φ hφ c c' hc' w hw]⟩⟩

end GlobalTheory.CoverChernField
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMeasurePart_preimage_covering_field : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ n : ℕ, (∀ y ∈ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ) ⁻¹' U) = (n : ENNReal) * φ.chernPart D ε U := by
  atlas_forward_decl GlobalTheory.CoverChernField.chernPart_preimage_of_cover
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.ChernMassPull

theorem mass : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ ε : ℤˣ, (φ.pull π hπ).chernPart D ε Set.univ = (π.residueDegree (genericPoint Y) : ENNReal) * φ.chernPart D ε Set.univ := by
  intro k _ X Y _ _ p q σ D hX hY hsm π hπ hη hδ B φ hφ ε
  obtain ⟨U, hUη, hcard, hchart, hlift⟩ := GlobalTheory.T.exists_open_covering_charts_generically_finite_field k X Y p q σ D hX hY hsm π hπ hη hδ
  have hpre : PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U = ptsIn q σ (π ⁻¹ᵁ U) := by
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have h0Y := GlobalTheory.T.chernPart_complement_dense_open_null_field k Y q σ D hY (π ⁻¹ᵁ U) (by simp [hη, hUη]) _ (φ.pull π hπ) ε
  have h0X := GlobalTheory.T.chernPart_complement_dense_open_null_field k X p σ D hX U hUη B φ ε
  have h3 := GlobalTheory.T.chernMeasurePart_preimage_covering_field k X Y p q σ D hX hY π hπ B φ hφ ε (ptsIn p σ U) (isOpen_ptsIn U) _
    hcard hchart hlift
  rw [hpre] at h3
  rw [← measure_add_measure_compl (isOpen_ptsIn (π ⁻¹ᵁ U)).measurableSet, h0Y, add_zero, h3,
    ← measure_add_measure_compl (isOpen_ptsIn (p := p) (σ := σ) U).measurableSet, h0X, add_zero]

end GlobalTheory.ChernMassPull
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMass_pull_mul_degree_field : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ ε : ℤˣ, (φ.pull π hπ).chernPart D ε Set.univ = (π.residueDegree (genericPoint Y) : ENNReal) * φ.chernPart D ε Set.univ := by
  atlas_forward_decl GlobalTheory.ChernMassPull.mass
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem pspace_integral_dim_proj_smooth :
    ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PSpace k N) ∧ topologicalKrullDim (PSpace k N) = N ∧ IsProjOver (PSpace.str k N) ∧ SmoothOfRelativeDimension N (PSpace.str k N) :=
  fun k _ N => ⟨ProjSpace.isIntegral_of_isDomain k N, ProjSpace.topologicalKrullDim_eq k N,
    ⟨N, 𝟙 _, inferInstance, by simp⟩, inferInstance⟩

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveSpace_integral_smooth_projective_dim : ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PSpace k N) ∧ topologicalKrullDim (PSpace k N) = N ∧ IsProjOver (PSpace.str k N) ∧ SmoothOfRelativeDimension N (PSpace.str k N) := by
  atlas_forward_decl GlobalTheory.pspace_integral_dim_proj_smooth
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueDegree_genericPoint_ne_zero_projective_same_dim : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X = D → topologicalKrullDim Y = D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 := by
  first | exact @GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint | exact GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint | (intros; apply GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjSpaceDegree

theorem topSelf_O1_str : ∀ (k : Type) [Field k] (N : ℕ),
    letI := GlobalTheory.algebraΓOfHom (PSpace.str k N); topSelfIntersection k (ProjSpace.O1 k N) N = 1 :=
  fun k _ N => GlobalTheory.NefNumericsModel.selfIntersection_O1 k N

end GlobalTheory.ProjSpaceDegree
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_self_intersection_O1_projective : ∀ (k : Type) [Field k] (N : ℕ), letI := GlobalTheory.algebraΓOfHom (PSpace.str k N); topSelfIntersection k (ProjSpace.O1 k N) N = 1 := by
  atlas_forward_decl GlobalTheory.ProjSpaceDegree.topSelf_O1_str
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FubiniStudyPull

theorem fubiniStudy_pullback_chern_mass_eq_degree : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim)
    (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str),
    Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ
      (fun _ => 1) = (topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℝ) := by
  intro Y π hπ
  obtain ⟨hPI, hPdim, hPproj, hPsm⟩ := GlobalTheory.T.projectiveSpace_integral_smooth_projective_dim ℂ Y.dim
  haveI := hPI
  by_cases hη : π (genericPoint Y.X) = genericPoint (PSpace ℂ Y.dim)
  · have hδ := GlobalTheory.T.residueDegree_genericPoint_ne_zero_projective_same_dim ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim hPproj
      Y.isProjOver hPdim Y.topologicalKrullDim_eq π hπ hη
    have hm := fun ε => GlobalTheory.T.chernMass_pull_mul_degree_field ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str (RingHom.id ℂ)
      Y.dim hPproj Y.isProjOver hPsm π hπ hη hδ (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).B
      ((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)) ((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf _) ε
    obtain ⟨h1, h0⟩ := GlobalTheory.T.chern_form_fubini_study_total Y.dim
    have hi := GlobalTheory.T.topSelfIntersection_pullback_eq_degree_mul ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim hPproj
      Y.isProjOver hPdim.le π hπ hη hδ (ProjSpace.O1 ℂ Y.dim) (ProjSpace.O1_isLB ℂ Y.dim)
    have ht := GlobalTheory.T.top_self_intersection_O1_projective ℂ Y.dim
    rw [GdegPullProof.chernInt_one, hm 1, hm (-1), h1, h0]
    change _ = ((topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℤ) : ℝ)
    rw [hi, ht]
    simp
  · have hc := GlobalTheory.T.chernInt_pull_fubiniStudy_eq_zero_of_not_specializes Y π hπ ⟨genericPoint (PSpace ℂ Y.dim), fun h =>
      hη (h.antisymm (genericPoint_specializes _)).eq⟩
    have hn := GlobalTheory.T.topSelfIntersection_pullback_eq_zero_of_not_dominant ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim Y.isProjOver
      hPdim.le Y.topologicalKrullDim_eq.le π hη (ProjSpace.O1 ℂ Y.dim) (ProjSpace.O1_isLB ℂ Y.dim)
    rw [hc]
    change (0 : ℝ) = ((topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℤ) : ℝ)
    rw [hn]
    simp

end GlobalTheory.FubiniStudyPull

end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernInt_pull_fubiniStudy_eq_topSelf : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℝ) := by
  atlas_forward_decl GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree
end
