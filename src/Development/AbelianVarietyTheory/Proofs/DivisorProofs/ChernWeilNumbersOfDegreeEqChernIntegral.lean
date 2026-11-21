import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityComplexFormAevalDzWedgeDzbar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFieldDbarCohomologousTwoConnections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VarietyComplexPointsMapIsHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagGradedLineChernFormsSmoothDbarClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinement
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnDens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerPullbackHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormsFrameInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCohomologousEvenFormsAlgebraClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularEqEsymmFirstChernForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGradedMetricsWeightsOnLineBundles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumber

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernTopDens

variable {n : ℕ}

theorem coeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) (d : Fin n × Fin n →₀ ℕ) :
    coeff d (aeval (fun y => C c * X y) Q) = c ^ (d.sum fun _ e => e) * coeff d Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    have : aeval (fun y => C c * X y) (monomial u a) = monomial u (c ^ (u.sum fun _ e => e) * a) := by
      rw [aeval_monomial, monomial_eq]
      simp only [mul_pow, Finsupp.prod_mul, algebraMap_eq]
      rw [Finsupp.prod, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, C_mul, map_prod]
      simp only [map_pow]
      ring
    rw [this, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

section Rev

variable {r : Type} [Fintype r] [DecidableEq r]

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix r r A) :
    (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem charpolyRev_smul {A : Type} [CommRing A] (c : A) (M : Matrix r r A) :
    (c • M).charpolyRev = M.charpolyRev.comp (Polynomial.C c * Polynomial.X) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_compRingHom_apply, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

theorem aeval_chernPoly (c : ℂ) (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) :
    aeval (fun y => C c * X y) (chernPoly G v k) = c ^ k • chernPoly G v k := by
  let ψ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ :=
    (aeval fun y => C c * X y : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ).toRingHom
  have e : ∀ p, aeval (fun y => C c * X y) p = ψ p := fun _ => rfl
  have hM : (-curvPoly G v).map ψ = (C c : MvPolynomial (Fin n × Fin n) ℂ) • (-curvPoly G v) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, curvPoly, Matrix.of_apply, map_neg, map_sum,
      map_mul, smul_eq_mul, Finset.mul_sum, mul_neg, ← e, aeval_X, aeval_C, algebraMap_eq]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
    ring
  unfold chernPoly
  rw [e, ← Polynomial.coeff_map, ← charpolyRev_map, hM, charpolyRev_smul, Polynomial.comp_C_mul_X_coeff, smul_eq_C_mul,
    map_pow, mul_comm]

end Rev

theorem topCoeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (aeval (fun y => C c * X y) Q) = c ^ n * topCoeff Q := by
  unfold topCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hdeg : (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ).sum (fun _ e => e) = n := by
    change Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n
    simp [map_sum]
  rw [coeff_aeval_C_mul_X, hdeg]
  ring

theorem kappa_div : kappa ^ n / (Complex.I / 2) ^ n = (((Real.pi ^ n)⁻¹ : ℝ) : ℂ) := by
  rw [← div_pow, Complex.ofReal_inv, Complex.ofReal_pow, ← inv_pow]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [kappa]
  field_simp

end GlobalTheory.ChernTopDens

open GlobalTheory.ChernTopDens in

theorem GlobalTheory.ChernCalc.dens_chernAt_re (n : ℕ) (ι : Type) (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ)
    (v : V n) :
    (dens ((aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) : Ev n) : Alt n)).re =
      chernTop R G v := by
  let Φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Ev n := (aeval sym).comp (aeval fun y => C kappa * X y)
  have h1 : (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) =
      fun x => Φ (chernPoly (fun u => G u x.1) v x.2) := by
    funext x
    simp only [Φ, AlgHom.comp_apply, aeval_chernPoly, map_smul, chernAt]
  have h2 : aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) =
      aeval sym (aeval (fun y => C kappa * X y)
        (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R)) := by
    rw [h1, ← comp_aeval, AlgHom.comp_apply, aeval_map_algebraMap]
    rfl
  rw [h2, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_aeval_C_mul_X, mul_div_right_comm, kappa_div, Complex.re_ofReal_mul]
  rfl
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDensity_chernPolynomial_re_eq_chernPolyTopDensity : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ) (v : V n), (dens ((aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) : Ev n) : Alt n)).re = chernTop R G v := by
  atlas_forward_decl GlobalTheory.ChernCalc.dens_chernAt_re
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

open GlobalTheory.ChartGlue

namespace GlobalTheory.ChernCalc

theorem chartMeas_congr_source {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {n : ℕ}
    (e : OpenPartialHomeomorph Y (V n)) {ρ ρ' : Y → ENNReal} (h : ∀ y ∈ e.source, ρ y = ρ' y) :
    chartMeas e ρ = chartMeas e ρ' := by
  unfold chartMeas
  congr 1
  refine withDensity_congr_ae ?_
  refine (ae_restrict_iff' e.open_target.measurableSet).2 (Eventually.of_forall fun v hv => ?_)
  exact h _ (e.map_target hv)

theorem chernTopPart_eq_part : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), ∀ (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ), chernTopPart E H R ε = (atlas X σ).part (evalF (atlas X σ) (chernF E H) R) ε := by
  intro F _ σ X ι m E H R ε
  unfold chernTopPart HolAtlas.part glueMeas
  refine iSup_congr fun c => chartMeas_congr_source _ fun y hy => ?_
  have hx : (atlas X σ).loc (evalF (atlas X σ) (chernF E H) R) c (c.e y) =
      evalF (atlas X σ) (chernF E H) R ⟨(c, y), hy⟩ :=
    HolAtlas.loc_crd (atlas X σ) (evalF (atlas X σ) (chernF E H) R) ⟨(c, y), hy⟩
  show ENNReal.ofReal (_ * chernTop _ _ _) = ENNReal.ofReal (_ * (dens ((atlas X σ).loc _ c (c.e y))).re)
  rw [hx]
  congr 2
  exact (GlobalTheory.T.topDensity_chernPolynomial_re_eq_chernPolyTopDensity X.dim ι m R (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y)).symm

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTopFormSignedMeasure_eq_atlas_part : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), ∀ (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ), chernTopPart E H R ε = (atlas X σ).part (evalF (atlas X σ) (chernF E H) R) ε := by
  atlas_forward_decl GlobalTheory.ChernCalc.chernTopPart_eq_part
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isGramPair_of_isMetricFr : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H H' : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → IsMetricFr E H' → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (gramAt E H' τ) := by
  intro F _ σ X ι _ m k E H H' hH hH' τ
  have hA (y : CxPts X.str σ) := (E.nonempty (under y)).choose_spec
  refine ⟨fun y => ⟨(GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y _ (hA y) τ).1,
    (GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H' hH' y _ (hA y) τ).1⟩, fun y => ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E y _ (hA y)] with z hz
  have hP := (Fr.mem_iff hz).1 (hA z) τ
  have hT := GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X (m τ) _ z (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)
  refine ⟨_, _, _, hT, hT, hT, ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E z _ hz, GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E z _ (hA z)] with w h1 h2
  exact ⟨hH.trans w _ h1 _ h2 τ, hH'.trans w _ h1 _ h2 τ⟩

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGramConnectionPair_of_two_flagged_metrics : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H H' : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → IsMetricFr E H' → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (gramAt E H' τ) := by
  atlas_forward_decl GlobalTheory.ChernCalc.isGramPair_of_isMetricFr
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isForm_evalF_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ)
    (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ R : MvPolynomial (ι × ℕ) ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (chernF E H) R) := by
  intro F _ σ X ι _ m k E H h R
  exact ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (atlas X σ)).2.2.2.1 _ (chernF E H) R fun x =>
    (GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ (atlas X σ) _ _ _ (GlobalTheory.T.isGramConnectionPair_of_two_flagged_metrics F σ X ι m k E H H h h x.1) x.2).1).1

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_evalRealPoly_chernForms_flaggedMetric : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ R : MvPolynomial (ι × ℕ) ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (chernF E H) R) := by
  atlas_forward_decl GlobalTheory.ChernCalc.isForm_evalF_chernF
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem GlobalTheory.FlagCell2.univ_eq_of_local_preimage_eq : ∀ (M N : Type) [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] (π : N → M), Measurable π → ∀ (μ : Measure N) (ν : Measure M), (∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ T, MeasurableSet T → T ⊆ U → μ (π ⁻¹' T) = ν T) → μ Set.univ = ν Set.univ := by
  intro M N _ _ _ _ _ π hπ μ ν h
  choose U hUo hxU hU using h
  obtain ⟨S, hSc, hS⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  haveI : Countable S := hSc.to_subtype
  have hcov : ⋃ i : S, U i = Set.univ := by
    rw [← Set.biUnion_eq_iUnion S (fun i _ => U i), hS]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hxU x⟩
  have hmap : μ.map π = ν := by
    refine (Measure.ext_iff_of_iUnion_eq_univ hcov).2 fun i => ?_
    ext T hT
    have hm : MeasurableSet (T ∩ U i) := hT.inter (hUo i).measurableSet
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT, Measure.map_apply hπ hm]
    exact hU i _ hm Set.inter_subset_right
  have : μ Set.univ = μ.map π Set.univ := by
    rw [Measure.map_apply hπ MeasurableSet.univ, Set.preimage_univ]
  rw [this, hmap]
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem fibre_integral : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).integral ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) = (atlas X σ).integral α := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH α hα
  have hol := GlobalTheory.T.varietyComplexPointsMap_isHolomorphic F σ X Y f hf
  have hmet := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  have hgr := GlobalTheory.T.fullFlagGradedLineChernForms_smooth_dbarClosed F σ Y ι m E' _ hmet
  have hpb := (((GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.2 _ _ (atlas Y σ) _ hol).2 1 α α).2.2.2 hα
  have hev := ((GlobalTheory.formCalculus _ _ (atlas Y σ)).2.2.2.1 (Root m) (grF E' (pullGram E H φ f hf)) (fibrePoint m)
    fun x => (hgr x).1).1
  have hβ := (((GlobalTheory.formCalculus _ _ (atlas Y σ)).2.1 1 _ _ hpb.1 hev)).2.1
  have key : ∀ s : ℤˣ, (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
      evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s Set.univ = (atlas X σ).part α s Set.univ := by
    intro s
    refine GlobalTheory.FlagCell2.univ_eq_of_local_preimage_eq _ _ (ptMap σ f hf) hol.1.measurable _ _ fun x => ?_
    have := X.smooth_str
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := X.dim) (σ := σ) x
    obtain ⟨A, hA⟩ := E.nonempty (under x)
    refine ⟨c.e.source ∩ interior {z | A ∈ E.S (under z)}, c.e.open_source.inter isOpen_interior,
      ⟨hc, mem_interior_iff_mem_nhds.2 (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m 0 E x A hA)⟩, fun T hT hTU => ?_⟩
    exact GlobalTheory.FlagCell2.LocFib.part_preimage F σ X Y ι m E E' φ f hf hR H hH α hα hβ s c A _ (c.e.open_source.inter isOpen_interior)
      Set.inter_subset_left (fun z hz => (interior_subset (s := {z | A ∈ E.S (under z)}) hz.2 :)) T hT hTU
  rw [HolAtlas.integral, HolAtlas.integral, measureReal_def, measureReal_def, measureReal_def, measureReal_def, key, key]

end GlobalTheory.ChernCalc
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagBundle_fibreIntegral_pullback_mul_fibreClass : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).integral ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) = (atlas X σ).integral α := by
  atlas_forward_decl GlobalTheory.ChernCalc.fibre_integral
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem contDiffOn_holoMap {n d : ℕ} {U : Set (V n)} (hU : IsOpen U) {p : V n → V d}
    (hp : DifferentiableOn ℂ p U) : ContDiffOn ℂ ∞ p U := by
  rw [contDiffOn_piLp]
  intro i
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ U hU
    ((EuclideanSpace.proj i : V d →L[ℂ] ℂ).differentiable.comp_differentiableOn hp)

theorem pull_chern_of_eventually {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n)
    (A' : HolAtlas M' n') {r : Type} [Fintype r] [DecidableEq r] {f : M' → M} (hf : A.IsHolo A' f) (G : M → Matrix r r ℂ)
    (G' T : M' → Matrix r r ℂ) (p : A'.Pt) (c : A.ι) (hc : f p.pt ∈ (A.e c).source) (hG : SmoothUnitAt A G (f p.pt))
    (hT : HolUnitAt A' T p.pt) (h : ∀ᶠ z in 𝓝 p.pt, G' z = T z * G (f z) * (T z)ᴴ) (j : ℕ) :
    pull (fderiv ℂ (A.e c ∘ f ∘ p.ch.symm) p.crd) (A.chern G j ⟨(c, f p.pt), hc⟩ : Alt n) = (A'.chern G' j p : Alt n') := by
  have hp : p.pt ∈ p.ch.source := p.2
  have hinv : p.ch.symm p.crd = p.pt := p.ch.left_inv hp
  have hU : IsOpen (p.ch.target ∩ p.ch.symm ⁻¹' (f ⁻¹' (A.e c).source)) :=
    p.ch.isOpen_inter_preimage_symm ((A.e c).open_source.preimage hf.1)
  have hmem : p.crd ∈ p.ch.target ∩ p.ch.symm ⁻¹' (f ⁻¹' (A.e c).source) :=
    ⟨p.ch.map_source hp, by rw [Set.mem_preimage, hinv]; exact hc⟩
  set ψ : V n' → V n := A.e c ∘ f ∘ p.ch.symm with hψ
  have hs : ContDiffAt ℂ ∞ ψ p.crd := (contDiffOn_holoMap hU (hf.2 p.1.1 c)).contDiffAt (hU.mem_nhds hmem)
  have hv : ψ p.crd = A.e c (f p.pt) := by simp only [hψ, Function.comp_apply, hinv]
  have hg : MContDiffAt ∞ (fun u => G ((A.e c).symm u)) (ψ p.crd) := hv ▸ (hG.2 c hc).self_of_nhds
  have hu : IsUnit (G ((A.e c).symm (ψ p.crd))).det := by rw [hv, (A.e c).left_inv hc]; exact hG.1
  have h1 := ((GlobalTheory.T.curvature_power_pullback_holomorphic n n' r (fun u => G ((A.e c).symm u)) ψ p.crd (hs.of_le (by norm_cast)) hg hu).2 j).2
  have hg' : MContDiffAt ∞ (fun x => G ((A.e c).symm (ψ x))) p.crd := fun a b =>
    (hg a b).comp p.crd (hs.restrict_scalars ℝ)
  have hTu : IsUnit (T (p.ch.symm p.crd)).det := by rw [hinv]; exact hT.1
  have hTd := hT.2 p.1.1 hp
  have ht : Tendsto p.ch.symm (𝓝 p.crd) (𝓝 p.pt) := by
    have := p.ch.continuousAt_symm (p.ch.map_source hp)
    rwa [ContinuousAt, p.ch.left_inv hp] at this
  have he : ∀ᶠ x in 𝓝 p.crd, G' (p.ch.symm x) =
      T (p.ch.symm x) * G ((A.e c).symm (ψ x)) * (T (p.ch.symm x))ᴴ := by
    filter_upwards [ht.eventually h, hU.mem_nhds hmem] with x hx hx'
    rw [hx]
    simp only [hψ, Function.comp_apply]
    rw [(A.e c).left_inv hx'.2]
  have h2 := (GlobalTheory.T.chernTransgression_forms_frame_invariant n' r _ _ (fun x => G' (p.ch.symm x)) (fun x => G' (p.ch.symm x)) (fun x => T (p.ch.symm x))
    (fun x => T (p.ch.symm x)) (fun x => T (p.ch.symm x)) p.crd hg' hu hg' hu hTd hTu hTd hTu hTd hTu
    (he.mono fun x hx => ⟨hx, hx⟩) j).2.1
  show pull _ (chernAt _ (A.e c (f p.pt)) j : Alt n) = (chernAt (fun v => G' (p.ch.symm v)) p.crd j : Alt n')
  rw [h2, h1, hv]

theorem pullback_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ x : ι × ℕ, (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) (fld (atlas X σ) (chernF E H x)) = fld (atlas Y σ) (chernF E' (pullGram E H φ f hf) x) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH x
  funext p
  have hol := GlobalTheory.T.varietyComplexPointsMap_isHolomorphic F σ X Y f hf
  have hE := GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH
  have hA := (E.nonempty (under (ptMap σ f hf p.pt))).choose_spec
  have hB := (E'.nonempty (under p.pt)).choose_spec
  have hP := hR.sub (under p.pt) _ hB _ (by
    have := hA
    exact (congrArg (fun w => (E.nonempty (under (ptMap σ f hf p.pt))).choose ∈ E.S w) (hE p.pt).1).mp this) x.1
  refine pull_chern_of_eventually (atlas X σ) (atlas Y σ) hol (gramAt E H x.1 (ptMap σ f hf p.pt))
    (gramAt E' (pullGram E H φ f hf) x.1 p.pt)
    (fun z => (((E'.nonempty (under p.pt)).choose *
      (Mat.map (E.nonempty (under (ptMap σ f hf p.pt))).choose φ)⁻¹) x.1).map (ratVal · z)) p _ _
    (GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) _ _ hA x.1).1
    (GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ Y _ _ p.pt (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)) ?_ x.2
  filter_upwards [(hol.1.tendsto p.pt).eventually (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m 0 E _ _ hA),
    GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' _ _ hB] with z h1 h2
  exact (hE z).2 _ ((congrArg (fun w => (E.nonempty (under (ptMap σ f hf p.pt))).choose ∈ E.S w) (hE z).1).mp h1) _ h2 x.1

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForms_pullback_metric_flag_refinement : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ x : ι × ℕ, (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) (fld (atlas X σ) (chernF E H x)) = fld (atlas Y σ) (chernF E' (pullGram E H φ f hf) x) := by
  atlas_forward_decl GlobalTheory.ChernCalc.pullback_chernF
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem algHom_aeval_ev {m m' : ℕ} {ι : Type} (φ : Alt m →ₐ[ℂ] Alt m') (u : ι → Ev m) (u' : ι → Ev m')
    (h : ∀ i, φ (u i : Alt m) = (u' i : Alt m')) (P : MvPolynomial ι ℝ) :
    φ ((aeval u (P.map (algebraMap ℝ ℂ)) : Ev m) : Alt m) = ((aeval u' (P.map (algebraMap ℝ ℂ)) : Ev m') : Alt m') := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
    exact φ.commutes _
  | add p q hp hq =>
    simp only [map_add, Subalgebra.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, Subalgebra.coe_mul, hp, h]

theorem pullback_evalF : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n') (g : M' → M) (ι : Type) (w : ι → A.Pt → Ev n) (w' : ι → A'.Pt → Ev n'), (∀ i, A.pullback A' g (fld A (w i)) = fld A' (w' i)) → ∀ P : MvPolynomial ι ℝ, A.pullback A' g (evalF A w P) = evalF A' w' P := by
  intro M M' _ _ n n' A A' g ι w w' hw P
  funext x
  exact algHom_aeval_ev _ _ _ (fun i => congrFun (hw i) x) P

end GlobalTheory.LineForm
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_real_polynomial_even_form_fields : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n') (g : M' → M) (ι : Type) (w : ι → A.Pt → Ev n) (w' : ι → A'.Pt → Ev n'), (∀ i, A.pullback A' g (fld A (w i)) = fld A' (w' i)) → ∀ P : MvPolynomial ι ℝ, A.pullback A' g (evalF A w P) = evalF A' w' P := by
  atlas_forward_decl GlobalTheory.LineForm.pullback_evalF
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem integral_evalF_of_dbarCoh : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (ι : Type) (w w' : ι → A.Pt → Ev n), (∀ i, DbarCoh A (w i) (w' i)) → ∀ P : MvPolynomial ι ℝ, A.integral (evalF A w P) = A.integral (evalF A w' P) := by
  intro M _ _ _ _ _ _ n A ι w w' hw P
  obtain ⟨hD1, -, hDalg⟩ := dbarCoh_algebra M n A
  obtain ⟨-, hc, -, -, -⟩ := GlobalTheory.formCalculus M n A
  obtain ⟨hfin, hadd, -, -⟩ := GlobalTheory.LineForm.wInt_props M n A
  have key : DbarCoh A (fun x => aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ)))
      (fun x => aeval (fun i => w' i x) (P.map (algebraMap ℝ ℂ))) := by
    induction P using MvPolynomial.induction_on with
    | C a =>
      have h := (hDalg (a : ℂ) 1 1 1 1 hD1 hD1).1
      convert h using 1 <;> funext x <;> simp [Algebra.algebraMap_eq_smul_one]
    | add p q hp hq =>
      have h := (hDalg 1 _ _ _ _ hp hq).2.1
      convert h using 1 <;> funext x <;> simp
    | mul_X p i hp =>
      have h := (hDalg 1 _ _ _ _ hp (hw i)).2.2
      convert h using 1 <;> funext x <;> simp
  obtain ⟨-, hf', -, -, u, hu, eu⟩ := key
  have e1 : evalF A w P = evalF A w' P + A.dbar u := by
    show fld A _ = fld A _ + _
    rw [← eu]
    abel
  have hdu : A.IsForm (A.dbar u) := (hc 1 u u hu hu).2.2.2.2.1
  have int1 : ∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, Integrable (fun _ : M => (1 : ℝ)) (A.part α ε) := fun α h ε => by
    haveI := hfin α h ε
    exact integrable_const 1
  calc A.integral (evalF A w P) = wInt A (fun _ => 1) (evalF A w' P + A.dbar u) := by rw [wInt_one, e1]
    _ = wInt A (fun _ => 1) (evalF A w' P) + wInt A (fun _ => 1) (A.dbar u) :=
      (hadd _ _ _ hf' hdu (int1 _ hf') (int1 _ hdu)).2
    _ = A.integral (evalF A w' P) := by
      rw [wInt_one, wInt_one, (GlobalTheory.CxFormStokesBoth.stokes M n A u hu).2, add_zero]

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_realPoly_eq_of_dbarCohomologous : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (ι : Type) (w w' : ι → A.Pt → Ev n), (∀ i, DbarCoh A (w i) (w' i)) → ∀ P : MvPolynomial ι ℝ, A.integral (evalF A w P) = A.integral (evalF A w' P) := by
  atlas_forward_decl GlobalTheory.ChernCalc.integral_evalF_of_dbarCoh
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem ratVal_zero_var {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (y : CxPts X.str σ) :
    ratVal (0 : X.Fn) y = 0 := by
  have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial (0 : Γ(X.X, ⊤))
  rw [map_zero, ev_eq mem_ptsIn_top, map_zero] at e
  exact e

theorem isGramPair_ldPart (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (hH : IsMetricFr E H) (τ : ι) :
    IsGramPair (atlas X σ) (gramAt E H τ) (fun y z => ldPart (gramAt E H τ y z)) := by
  have hA : ∀ y : CxPts X.str σ, (E.nonempty (under y)).choose ∈ E.S (under y) :=
    fun y => (E.nonempty (under y)).choose_spec
  have hsm := fun y => GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H hH y _ (hA y) τ
  have hT : ∀ (A B : Mat m X.Fn) (w : CxPts X.str σ), A ∈ E.S (under w) → B ∈ E.S (under w) →
      HolUnitAt (atlas X σ) (fun z => ((B * A⁻¹) τ).map (ratVal · z)) w ∧
      ∀ i j : Fin (m τ), i < j → ((B * A⁻¹) τ).map (ratVal · w) i j = 0 := by
    intro A B w hAw hBw
    have hp := ((Fr.mem_iff hAw).1 hBw) τ
    refine ⟨GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X (m τ) ((B * A⁻¹) τ) w (fun i j => mem_O_ratOf.1 (hp.1 i j)) hp.2.1
      (mem_O_ratOf.1 hp.2.2.1), fun i j hij => ?_⟩
    rw [Matrix.map_apply, hp.2.2.2 i j i.2 hij]
    exact ratVal_zero_var w
  refine ⟨fun y => ⟨(hsm y).1, ?_⟩, fun y => ?_⟩
  · refine ⟨(GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ (hH.posDef y _ (hA y) τ)).2.2.2, fun c hc => ?_⟩
    filter_upwards [(hsm y).2 c hc] with v hv
    exact (GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth _ _ _ v hv.1 hv.2).1
  · have h1 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E y _ (hA y)
    filter_upwards [h1, h1.eventually_nhds] with z hz hz'
    have h2 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ (hA z)
    obtain ⟨hol, tri⟩ := hT _ _ z hz (hA z)
    refine ⟨_, _, fun w => Matrix.diagonal fun i =>
      (((E.nonempty (under z)).choose * (E.nonempty (under y)).choose⁻¹) τ).map (ratVal · w) i i,
      hol, hol, ⟨?_, fun c hc a b => ?_⟩, ?_⟩
    · rw [Matrix.det_diagonal, ← Matrix.det_of_lowerTriangular _ (fun i j hij => tri i j hij)]
      exact hol.1
    · by_cases hab : a = b
      · subst hab
        filter_upwards [hol.2 c hc a a] with v hv
        simpa only [Matrix.diagonal_apply_eq] using hv
      · exact Eventually.of_forall fun v => by
          simp only [Matrix.diagonal_apply_ne _ hab]
          exact differentiableAt_const _
    · filter_upwards [hz', h2] with w hwA hwB
      obtain ⟨holw, triw⟩ := hT _ _ w hwA hwB
      have e := hH.trans w _ hwA _ hwB τ
      change gramAt E H τ z w = _ * gramAt E H τ y w * _ at e
      refine ⟨e, ?_⟩
      rw [e]
      exact (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ (hH.posDef w _ hwA τ) triw holw.1).1

end GlobalTheory.ChernCalc
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGramConnectionPair_gram_lower_triangular_factor : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (fun y z => ldPart (gramAt E H τ y z)) := by
  atlas_forward_decl GlobalTheory.ChernCalc.isGramPair_ldPart
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem chernFld_ldPart_eq_esymm_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ j p, chernFld (atlas X σ) (fun y z => ldPart (gramAt E H τ y z)) j p = aeval (fun i => grF E H ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j) := by
  intro F _ σ X ι _ m E H hH τ j p
  set A := (E.nonempty (under p.pt)).choose with hAdef
  have hA : A ∈ E.S (under p.pt) := (E.nonempty (under p.pt)).choose_spec
  have hev := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H hH p.pt A hA τ).2 p.1.1 p.2)
  change ∀ᶠ v in 𝓝 p.crd, MContDiffAt ∞ (fun u => H A (p.ch.symm u) τ) v ∧ (H A (p.ch.symm v) τ).PosDef at hev
  have h0 := hev.self_of_nhds
  have hs := GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth X.dim (m τ) (fun u => H A (p.ch.symm u) τ) p.crd h0.1 h0.2
  have hp0 := GlobalTheory.T.gramLowerTriangularFactor_posDef_properties (m τ) _ h0.2
  show chernAt (fun v => ldPart (H A (p.ch.symm v) τ)) p.crd j = _
  refine (GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms X.dim (m τ) (fun v => ldPart (H A (p.ch.symm v) τ))
    (fun i v => grD (H A (p.ch.symm v) τ) i) p.crd hs.1 (fun i => (hp0.2.1 i).1) ?_ j).trans rfl
  filter_upwards [hev] with x hx
  have hpx := GlobalTheory.T.gramLowerTriangularFactor_posDef_properties (m τ) _ hx.2
  exact ⟨hpx.2.2.1, fun i => (hpx.2.1 i).2⟩

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForm_triangular_connection_eq_esymm_graded : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ j p, chernFld (atlas X σ) (fun y z => ldPart (gramAt E H τ y z)) j p = aeval (fun i => grF E H ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j) := by
  atlas_forward_decl GlobalTheory.ChernCalc.chernFld_ldPart_eq_esymm_grF
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernCalc

theorem evalF_rename_mul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α β : Type}
    (u : α → A.Pt → Ev n) (v : β → A.Pt → Ev n) (R : MvPolynomial α ℝ) (Q : MvPolynomial β ℝ) :
    evalF A (Sum.elim u v) (rename Sum.inl R * rename Sum.inr Q) = evalF A u R * evalF A v Q := by
  funext x
  simp only [evalF, LineForm.fld, Pi.mul_apply, Polynomial.map_mul, MvPolynomial.map_rename, map_mul, aeval_rename]
  rfl

theorem evalF_chernRoots {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (m : ι → ℕ)
    (c : ι × ℕ → A.Pt → Ev n) (g : Root m → A.Pt → Ev n)
    (h : ∀ τ j p, c (τ, j) p = aeval (fun i => g ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j))
    (R : MvPolynomial (ι × ℕ) ℝ) : evalF A c R = evalF A g (chernRoots m R) := by
  funext p
  simp only [evalF, LineForm.fld]
  congr 1
  rw [aeval_map_algebraMap, aeval_map_algebraMap, chernRoots, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext x
  rw [h x.1 x.2 p, aeval_rename, aeval_esymm_eq_multiset_esymm, aeval_esymm_eq_multiset_esymm]
  rfl

theorem integral_chernF_mul_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) (Q : MvPolynomial (Root m) ℝ), (atlas X σ).integral (evalF (atlas X σ) (chernF E H) R * evalF (atlas X σ) (grF E H) Q) = (atlas X σ).integral (evalF (atlas X σ) (grF E H) (chernRoots m R * Q)) := by
  intro F _ σ X ι _ m E H hH R Q
  let ld : ι × ℕ → (atlas X σ).Pt → Ev X.dim := fun x => chernFld (atlas X σ) (fun y z => ldPart (gramAt E H x.1 y z)) x.2
  have hc : ∀ i, DbarCoh (atlas X σ) (Sum.elim (chernF E H) (grF E H) i) (Sum.elim ld (grF E H) i) := by
    rintro (⟨τ, j⟩ | x)
    · exact GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ _ _ _ _ (GlobalTheory.T.isGramConnectionPair_gram_lower_triangular_factor F σ X ι m E H hH τ) j
    · exact GlobalTheory.T.fullFlagGradedLineChernForms_smooth_dbarClosed F σ X ι m E H hH x
  have key := GlobalTheory.T.integral_realPoly_eq_of_dbarCohomologous (CxPts X.str σ) X.dim (atlas X σ) _ _ _ hc (rename Sum.inl R * rename Sum.inr Q)
  rw [evalF_rename_mul, evalF_rename_mul] at key
  rw [key, evalF_chernRoots (atlas X σ) m ld (grF E H) (fun τ j p => GlobalTheory.T.chernForm_triangular_connection_eq_esymm_graded F σ X ι m E H hH τ j p) R]
  simp only [evalF, LineForm.fld, map_mul]
  rfl

end GlobalTheory.ChernCalc
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_chernForms_eq_esymm_gradedForms_flag : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) (Q : MvPolynomial (Root m) ℝ), (atlas X σ).integral (evalF (atlas X σ) (chernF E H) R * evalF (atlas X σ) (grF E H) Q) = (atlas X σ).integral (evalF (atlas X σ) (grF E H) (chernRoots m R * Q)) := by
  atlas_forward_decl GlobalTheory.ChernCalc.integral_chernF_mul_grF
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex :
    GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernWeilNumbers := by
  intro h F _ σ X Y ι _ m E E' φ f gr hR hG H hH R
  have hD : GlobalTheory.Published.ChernDegree := GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case h
  have hf : f ≫ X.str = Y.str := hR.hom.inducedModelMorphism_comp_structureMap
  have hform := GlobalTheory.T.isForm_evalRealPoly_chernForms_flaggedMetric F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) R
  have hM := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  have hu : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  choose L r ψ h1 h2 h3 using GlobalTheory.T.flag_graded_metrics_weights_on_line_bundles F σ Y ι m E' _ gr hG hM
  have e : grF E' (pullGram E H φ f hf) = fun x => c1W (ψ x) := funext fun x => (h3 x).symm
  unfold HasChernIntegral
  rw [hu]
  simp only [GlobalTheory.T.chernTopFormSignedMeasure_eq_atlas_part F σ X ι m E H R]
  refine ⟨fun ε => ?_, ?_⟩
  · have := (GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous _ _ (atlas X σ)).1 _ hform ε
    exact measure_ne_top _ _
  · refine (GlobalTheory.T.flagBundle_fibreIntegral_pullback_mul_fibreClass F σ X Y ι m E E' φ f hf hR H hH _ hform).symm.trans ?_
    rw [GlobalTheory.T.pullback_real_polynomial_even_form_fields _ _ _ _ _ _ _ _ _ _ (GlobalTheory.T.chernForms_pullback_metric_flag_refinement F σ X Y ι m E E' φ f hf hR H hH) R,
      GlobalTheory.T.integral_chernForms_eq_esymm_gradedForms_flag F σ Y ι m E' _ hM, e]
    exact GlobalTheory.T.integral_chernFormPoly_eq_intersectionNumber hD F σ Y _ gr L r ψ (fun a => ⟨h1 a, h2 a⟩) _
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernWeilNumbers_of_degree_eq_chernIntegral : GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernWeilNumbers := by
  atlas_forward_decl GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex
end
