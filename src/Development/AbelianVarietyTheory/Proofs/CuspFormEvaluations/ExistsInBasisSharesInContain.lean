import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointsInterpolationGenericSections
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingAtPointsMulPowMemSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingProductsIndependentModuloDeepProducts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ArchimedeanFlatDecompositionIndexing
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankLowerBoundCuspFormVanishingLowCoeff
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingLowCoeffMemLeadingAddDeepSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAlgIndependentCoeffsFlatDatum
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBaseEmbeddingReadingForms
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaximalCuspsNoLowCoefficientIffFourierJacobi
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InBasisIffPointValuesLinearIndependentSpanStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsValueBasisInSpanningForms
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRdOfInBasis
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRhoROfAnFacts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NonemptyHeightOneSpectrumRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InContainMROfAnFacts

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_interpolation_genericSections : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → (∀ q, R.s w t 0 (xs q) ≠ 0 ∧ ∀ i : Fin (WeightFamilies.dimY D j), R.s w t i.succ (xs q) = 0) ∧ ∀ v : Fin δ → ℂ, ∃ f ∈ R.sp wF Set.univ, ∀ q, f (xs q) = v q := by
  first | exact @GlobalTheory.Shares.points_and_interp | exact GlobalTheory.Shares.points_and_interp | (intros; apply GlobalTheory.Shares.points_and_interp <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_vanishing_at_points_mul_pow_mem_span : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ k : ℕ, ∀ g ∈ R.sp (addL wF wL k) Set.univ, (∀ q, g (xs q) = 0) → ∃ m : ℕ, R.s w t 0 ^ (m + 1) * g ∈ R.deep w t (addL wF wL (k + m)) 1 := by
  first | exact @GlobalTheory.Shares.VanDiv.vanishing_division | exact GlobalTheory.Shares.VanDiv.vanishing_division | (intros; apply GlobalTheory.Shares.VanDiv.vanishing_division <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingProducts_independent_modulo_deepProducts : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → LinearIndependent ℂ (vals xs θ) → LinearIndependent ℂ (R.lead w t Tn (a0 D j Tn) θ) ∧ Disjoint (Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ))) (R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn)) := by
  first | exact @GlobalTheory.Shares.LeadDeep.main | exact GlobalTheory.Shares.LeadDeep.main | (intros; apply GlobalTheory.Shares.LeadDeep.main <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_flat_decomposition_indexing : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → Module.finrank ℂ (R.sp (addL wF wL Tn) Set.univ) ≤ δ * (Tn + 2 * WeightFamilies.dimY D j + 6).choose (WeightFamilies.dimY D j) := by
  first | exact @GlobalTheory.UpperRecord.upper | exact GlobalTheory.UpperRecord.upper | (intros; apply GlobalTheory.UpperRecord.upper <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_lower_bound_cuspForm_vanishing_low_coeff : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → MggOnto h j CR Tn c (addL wF wL Tn) → δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))) := by
  first | exact @GlobalTheory.LowerBound.lower_bound | exact GlobalTheory.LowerBound.lower_bound | (intros; apply GlobalTheory.LowerBound.lower_bound <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_vanishing_low_coeff_mem_leading_add_deep_span : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → (∀ F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tn c j (addL wF wL Tn), ∀ k : (T.U j T.σ₀).Comp, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → Submodule.span ℂ (Set.range (vals xs θ)) = ⊤ → R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn)) ≤ Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ)) ⊔ R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn) := by
  first | exact @GlobalTheory.Containment.main | exact GlobalTheory.Containment.main | (intros; apply GlobalTheory.Containment.main <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algIndependent_coeffs_flatDatum : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1), ∃ t : Idx D j N → ℂ, (∀ Q : MvPolynomial (Idx D j N) T.Q.c.F, Q ≠ 0 → MvPolynomial.eval₂ T.σ₀ t Q ≠ 0) ∧ Nonempty (FlatAt h j A t) := by
  first | exact @GlobalTheory.GenericFlat.exists_generic_flatAt | exact GlobalTheory.GenericFlat.exists_generic_flatAt | (intros; apply GlobalTheory.GenericFlat.exists_generic_flatAt <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_embedding_reading_forms : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)), ∃ (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e := by
  first | exact @GlobalTheory.Shares.exists_isRdgU | exact GlobalTheory.Shares.exists_isRdgU | (intros; apply GlobalTheory.Shares.exists_isRdgU <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem GlobalTheory.Shares.exists_anFacts_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (N : ℕ) (ka wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (CR c : ℝ), addL wF wL Tn = ka → Nonempty (ArchAt h j w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → TieMaxCuspSt h j CR Tn c ka → ∃ (R : Rdg (recPlusN h j hj n)) (t : Idx D j N → ℂ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t ∧ AnFacts R w t ka wF Tn (WeightFamilies.MggK n.base CR Tn c j ka) xs := by
  intro D T h j hj n N ka wL wF w Tn CR c hka hA hOn hM hTie
  subst hka
  obtain ⟨A⟩ := hA
  obtain ⟨R, e, hR⟩ := GlobalTheory.T.exists_base_embedding_reading_forms D T h j hj n
  obtain ⟨t, ht, ⟨Fl⟩⟩ := GlobalTheory.T.exists_algIndependent_coeffs_flatDatum D T h j hj N wL wF w Tn _ A
  classical
  let ι : Type := Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ
  have : Fintype ι := inferInstance
  let en : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let xs : Fin (Fintype.card ι) → R.Y := fun q =>
    e.symm ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩
  have hxs : ∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩ :=
    fun q => e.apply_symm_apply _
  have h1 := GlobalTheory.T.points_interpolation_genericSections D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn
  refine ⟨R, t, _, xs, ?_, h1.1, h1.2,
    GlobalTheory.T.cuspForm_vanishing_at_points_mul_pow_mem_span D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn,
    GlobalTheory.T.leadingProducts_independent_modulo_deepProducts D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    GlobalTheory.T.archimedean_flat_decomposition_indexing D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    GlobalTheory.T.finrank_lower_bound_cuspForm_vanishing_low_coeff D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs CR c rfl hM,
    GlobalTheory.T.cuspForm_vanishing_low_coeff_mem_leading_add_deep_span D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn CR c rfl ?_⟩
  · intro Q hQ
    have hσ : R.σ = T.σ₀ := RingHom.ext hR.1
    rw [hσ]
    exact ht Q hQ
  · exact fun F hF => (hTie F).1 hF
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFacts_of_thetaData_on_models : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (N : ℕ) (ka wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (CR c : ℝ), addL wF wL Tn = ka → Nonempty (ArchAt h j w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → TieMaxCuspSt h j CR Tn c ka → ∃ (R : Rdg (recPlusN h j hj n)) (t : Idx D j N → ℂ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t ∧ AnFacts R w t ka wF Tn (WeightFamilies.MggK n.base CR Tn c j ka) xs := by
  atlas_forward_decl GlobalTheory.Shares.exists_anFacts_record
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

set_option maxHeartbeats 1000000 in

theorem exists_inBasis_shares_inContain : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (G₀ : GlobalFamilyData (recPlusN h j hj n) ka wL wF) (Tn : ℕ) (CR c : ℝ) (S : Scal n.base), addL wF wL Tn = ka → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ Tn → Nonempty (ArchAt h j G₀.w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → LatAt n.base j ka → (∃ β : ℝ, ShortG (recPlusN h j hj n) ((recPlusN h j hj n).wF0 wL wF) ((recPlusN h j hj n).Thc S.s0 ((recPlusN h j hj n).wF0 wL wF)) β) → ∀ Sh : Set ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO Sh = ⊤ → ∃ (del : ℕ) (th' : Fin del → n.base.Cusp j wF), (∀ i, th' i ∈ Sh) ∧ ∀ rz alz th0 zc rq th iet et, (∀ la, InBasis (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) la) ∧ ShareRd (D := D) (j := j) Tn del ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ShareRhoR (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) S Tn ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ShareRhoP (D := D) (j := j) Tn (WeightFamilies.rhoP n.base CR Tn c j ka) ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ∀ la, InContainMR (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) la S CR Tn c := by
  intro D T h j hj n ka wL wF G₀ Tn CR c S hka hd2 hT hArch hRd hMgg hLat hShort Sh hSh

  obtain ⟨R, t, δ, xs, hgen, hA⟩ :=
    GlobalTheory.T.analyticFacts_of_thetaData_on_models D T h j hj n G₀.N ka wL wF G₀.w Tn CR c hka hArch hRd hMgg
      (GlobalTheory.T.maximalCusps_noLowCoefficient_iff_fourierJacobi D T h j hj ka CR (Tn : ℝ) c)

  obtain ⟨θ, hθS, hθ⟩ :=
    exists_valueBasis_in_spanning D n.base _ j (recPlusN h j hj n) ka wL wF G₀.N G₀.w R t Tn _ δ xs hA Sh hSh
  refine ⟨δ, θ, hθS, ?_⟩
  intro rz alz th0 zc rq th iet et
  have hdT : WeightFamilies.dimY D j < Tn := by nlinarith
  have hd0 : 0 < WeightFamilies.dimY D j := by omega

  have hA' : AnFacts R (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et).w t ka wF Tn
      (WeightFamilies.MggK n.base CR Tn c j ka) xs := hA
  have hB : ∀ la, InBasis (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) la := fun la =>
    (GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span D n.base _ j (recPlusN h j hj n) ka wL wF (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et)
      R t Tn _ δ xs hgen hA' hka la).2 ⟨hθ, rfl⟩

  obtain ⟨β, Sg, hSg, hspan, -⟩ := hShort
  have hle := Submodule.span_mono (R := n.base.KO) hSg
  rw [hspan] at hle
  have hTop := top_le_iff.mp hle
  obtain ⟨la₀⟩ := nonempty_heightOneSpectrum_ringOfIntegers n.base.KO
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · exact shareRd_of_inBasis D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn _ δ xs hgen hA' hka hdT hd0 hLat ⟨la₀, hB la₀⟩
  · exact shareRhoR_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn _ δ xs hgen hA' hka hd2 hT hLat S
  · exact shareRhoP_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF G₀.N G₀.w R t Tn CR c δ xs hA hd2 hT hLat
  · intro la
    exact Contain.inContainMR_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn CR c δ xs hgen hA' hka hdT.le S hTop la (hB la)

end GlobalTheory.Shares
end
