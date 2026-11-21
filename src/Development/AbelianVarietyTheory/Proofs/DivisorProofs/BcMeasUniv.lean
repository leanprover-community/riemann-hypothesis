import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ArInt

noncomputable section

namespace GlobalTheory.FlagZ.Plane

theorem exists_chart_of_bijective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (U : X.Opens) (_ : IsAffineOpen U) (x : Fin D → Γ(X, U)), Function.Bijective (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x) → ∃ c : AlgChart p σ D, c.e.source = ptsIn p σ U ∧ c.e.target = Set.univ ∧ ∀ y ∈ c.e.source, ∀ a, c.e y a = CxPts.ev p σ U (x a) y := by
  intro k _ X p σ D U hU x hb
  let e := RingEquiv.ofBijective _ hb
  have he (P) : e.symm (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x P) = P := e.symm_apply_apply P
  let s (v : ReciprocityTheory.L2DbarEstimates.V D) : CxPts p σ :=
    ofHom hU ((MvPolynomial.eval₂Hom σ fun a => v a).comp e.symm.toRingHom) fun a => by
      have := he (MvPolynomial.C a)
      rw [MvPolynomial.eval₂Hom_C] at this
      exact (congrArg _ this).trans (MvPolynomial.eval₂Hom_C _ _ a)
  have hs (v) : s v ∈ ptsIn p σ U := ofHom_mem _ _ _
  have hev (v) (P) : CxPts.ev p σ U (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x P) (s v) =
      MvPolynomial.eval₂Hom σ (fun a => v a) P := (ev_ofHom _ _ _ _).trans (congrArg (MvPolynomial.eval₂Hom σ fun a => v a) (he P))
  have hd (a : Γ(X, U)) : DifferentiableOn ℂ (CxPts.ev p σ U a ∘ s) Set.univ := by
    obtain ⟨P, rfl⟩ := hb.2 a
    refine Differentiable.differentiableOn ?_
    rw [show CxPts.ev p σ U (MvPolynomial.eval₂Hom _ x P) ∘ s = fun v : ReciprocityTheory.L2DbarEstimates.V D =>
      MvPolynomial.eval₂Hom σ (fun a => v a) P from funext fun v => hev v P]
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
    | mul_X p n hp =>
      simp only [map_mul, MvPolynomial.eval₂Hom_X']
      exact hp.mul (EuclideanSpace.proj (𝕜 := ℂ) n : ReciprocityTheory.L2DbarEstimates.V D →L[ℂ] ℂ).differentiable
  have hh := holo_of_affine hU isOpen_univ (fun v _ => hs v) hd
  refine ⟨⟨{ toFun := fun z => WithLp.toLp 2 fun a => CxPts.ev p σ U (x a) z
             invFun := s
             source := ptsIn p σ U
             target := Set.univ
             map_source' := fun _ _ => trivial
             map_target' := fun v _ => hs v
             left_inv' := fun z hz => Subtype.ext (ext_of_valR hU (hs _) hz fun a => ?_)
             right_inv' := fun v _ => ?_
             open_source := isOpen_ptsIn _
             open_target := isOpen_univ
             continuousOn_toFun := (PiLp.continuous_toLp 2 _).comp_continuousOn
               (continuousOn_pi.2 fun a => continuousOn_ev _)
             continuousOn_invFun := hh.1 }, U, hU, x, RingHom.Etale.of_bijective hb, fun _ h => h, fun _ _ _ => rfl,
    hh.2⟩, rfl, rfl, fun _ _ _ => rfl⟩
  · obtain ⟨P, rfl⟩ := hb.2 a
    refine (hev _ P).trans (Eq.trans ?_ (ev_eq hz _).symm)
    refine RingHom.congr_fun (g := (evHom hz).comp (MvPolynomial.eval₂Hom _ x))
      (MvPolynomial.ringHom_ext (fun c => ?_) fun c => ?_) P
    · rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, ← ev_eq, MvPolynomial.eval₂Hom_C]
      exact (ev_algX hz c).symm
    · rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, ← ev_eq, MvPolynomial.eval₂Hom_X']
  · ext a
    have := hev v (MvPolynomial.X a)
    rwa [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X'] at this

theorem integral_log_dens : ∫ v : ReciprocityTheory.L2DbarEstimates.V 1, 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ * Real.log (ArithHeightModel.u v) = 1 := by
  have hd : Module.finrank ℝ (ReciprocityTheory.L2DbarEstimates.V 1) = 2 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (ReciprocityTheory.L2DbarEstimates.V 1)]; simp
  have hu (v : ReciprocityTheory.L2DbarEstimates.V 1) : ArithHeightModel.u v = 1 + ‖v‖ ^ 2 := by
    rw [ArithHeightModel.u, EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Complex.sq_norm, Complex.normSq_apply]
    ring
  have : Nontrivial (ReciprocityTheory.L2DbarEstimates.V 1) := inferInstance
  have h := integral_fun_norm_addHaar (volume : Measure (ReciprocityTheory.L2DbarEstimates.V 1))
    (fun r => 1 / Real.pi * ((1 + r ^ 2) ^ 2)⁻¹ * Real.log (1 + r ^ 2))
  have hr : ∫ r in Set.Ioi (0 : ℝ), r * (((1 + r ^ 2) ^ 2)⁻¹ * Real.log (1 + r ^ 2)) =
      0 - -(1 / 2 * (Real.log (1 + (0 : ℝ) ^ 2) / (1 + (0 : ℝ) ^ 2) + (1 + (0 : ℝ) ^ 2)⁻¹)) := by
    refine integral_Ioi_of_hasDerivAt_of_nonneg'
      (g := fun r => -(1 / 2 * (Real.log (1 + r ^ 2) / (1 + r ^ 2) + (1 + r ^ 2)⁻¹)))
      (fun r _ => ?_) (fun r hr => mul_nonneg (le_of_lt hr) (mul_nonneg (by positivity)
        (Real.log_nonneg (le_add_of_nonneg_right (sq_nonneg r))))) ?_
    · have h0 : (1 + r ^ 2) ≠ 0 := by positivity
      have h1 := (hasDerivAt_pow 2 r).const_add 1
      refine HasDerivAt.congr_deriv (((((h1.log h0).div h1 h0).add (h1.inv h0)).const_mul (1 / 2)).neg) ?_
      field_simp
      simp
      ring
    · have ht : Filter.Tendsto (fun r : ℝ => 1 + r ^ 2) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_left _ 1 (Filter.tendsto_pow_atTop two_ne_zero)
      have := (((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht).add
        (tendsto_inv_atTop_zero.comp ht)).const_mul (1 / 2)).neg
      simpa using this
  simp only [hu]
  rw [h, hd, Measure.real, AnReadModel.volume_ball_one, ENNReal.toReal_ofReal Real.pi_pos.le]
  simp only [smul_eq_mul, Nat.reduceSub, pow_one, mul_assoc (1 / Real.pi), mul_left_comm _ (1 / Real.pi), integral_const_mul, hr]
  have := Real.pi_pos
  field_simp
  norm_num

theorem chernInt_chart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X}
    [SecondCountableTopology (CxPts p σ)] {φ : Weight p σ B} (h : φ.IsCInf) (c : AlgChart p σ D)
    (ht : c.e.target = Set.univ) {ρ : ReciprocityTheory.L2DbarEstimates.V D → ℝ} (hρ : Continuous ρ) (h0 : ∀ v, 0 ≤ ρ v)
    (hc : ∀ v, c.chernDens φ (c.e.symm v) = ρ v) (f : CxPts p σ → ℝ) :
    φ.chernInt D c.e.source f = ∫ v, ρ v * f (c.e.symm v) := by
  have hm := (c.e.symm.isOpenEmbedding ht).measurableEmbedding
  have key (ε : ℤˣ) : (φ.chernPart D ε).restrict c.e.source =
      (volume.withDensity fun v => ENNReal.ofReal ((ε : ℤ) * ρ v)).map c.e.symm := by
    ext T hT
    rw [Measure.restrict_apply hT, Weight.chernPart_apply h ε c (hT.inter c.e.open_source.measurableSet)
      Set.inter_subset_right, hm.map_apply, withDensity_apply _ (hm.measurable hT), Set.inter_comm,
      c.e.image_source_inter_eq', ht, Set.univ_inter]
    simp only [hc]
  have hi (ε : ℤˣ) : ∫ y in c.e.source, f y ∂φ.chernPart D ε =
      ∫ v, (ENNReal.ofReal ((ε : ℤ) * ρ v)).toReal • f (c.e.symm v) := by
    rw [key, hm.integral_map, integral_withDensity_eq_integral_toReal_smul
      (hρ.measurable.const_mul _).ennreal_ofReal (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [Weight.chernInt, hi, hi]
  simp [ENNReal.ofReal_of_nonpos (neg_nonpos.2 (h0 _)), ENNReal.toReal_ofReal (h0 _)]

theorem chernInt_log_coord : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ), (ProjAn.fsO1 k σ 1).chernInt 1 (ptsIn (PSpace.str k 1) σ (chart k 1 0)) (fun y => Real.log ((ProjAn.fsO1 k σ 1).nsq (secVal (PSpace.str k 1) σ (ProjSpace.coord k 1 0)) y) / 2) = -(1 / 2) := by
  intro k _ σ
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] Γ(PSpace k 1, chart k 1 0) :=
    (MvPolynomial.renameEquiv k (finSuccAboveEquiv 0)).trans (chartAlgEquiv k 1 0)
  have he : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (PSpace.str k 1) (chart k 1 0))
      (fun a => ratio k 1 0 ((0 : Fin 2).succAbove a)) = (e : MvPolynomial (Fin 1) k →+* _) :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans (e.commutes a).symm)
      fun b => (MvPolynomial.eval₂Hom_X' _ _ b).trans
        ((congrArg (chartAlgEquiv k 1 0) (MvPolynomial.rename_X _ b)).trans
          (chartAlgEquiv_X k 1 0 (finSuccAboveEquiv 0 b))).symm
  obtain ⟨c, hs, ht, hx⟩ := exists_chart_of_bijective k _ (PSpace.str k 1) σ 1 _ (isAffineOpen_chart k 1 0)
    (fun a => ratio k 1 0 ((0 : Fin 2).succAbove a)) (by rw [he]; exact e.bijective)
  have hm (v) : c.e.symm v ∈ c.e.source := c.e.map_target (ht ▸ trivial)
  have hr (v) : c.e (c.e.symm v) = v := c.e.right_inv (ht ▸ trivial)
  have h1 (v) : CxPts.ev _ σ (chart k 1 0) (ratio k 1 0 0) (c.e.symm v) = 1 := by
    rw [ev_eq (hs ▸ hm v), ratio, ratioOn_self, map_one]
  have h2 (v) : CxPts.ev _ σ (chart k 1 0) (ratio k 1 0 1) (c.e.symm v) = v 0 :=
    (hx _ (hm v) 0).symm.trans (by rw [hr])
  have hφ (v) : (ProjAn.fsO1 k σ 1).φ (0 : Fin 2) (c.e.symm v) = Real.log (ArithHeightModel.u v) := by
    refine (Weight.fsBasis_φ _ _ _ _ _ _ _).trans (congrArg _ ?_)
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine (Fin.sum_univ_two _).trans ((congrArg₂ (fun a b : ℂ => ‖a‖ ^ 2 + ‖b‖ ^ 2) (h1 v) (h2 v)).trans ?_)
    simp only [norm_one, one_pow, ArithHeightModel.u, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hi : (ProjAn.fsO1 k σ 1).IsCInf := (hermitianTwistingSheaf k 1).cInf σ
  have hu : Continuous ArithHeightModel.u := continuous_iff_continuousAt.2 fun v =>
    (ArithHeightModel.hasFDerivAt_u v).continuousAt
  have := CxPts.secondCountableTopology_of_isProjOver σ (isProjOver_pspace_str k 1)
  rw [← hs, chernInt_chart hi c ht (ρ := fun v => 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹)
    (continuous_const.mul ((hu.pow 2).inv₀ fun v => (pow_pos (ArithHeightModel.u_pos v) 2).ne'))
    (fun v => by have := Real.pi_pos; positivity) fun v => ?_]
  · have hn (v) : (ProjAn.fsO1 k σ 1).nsq (secVal (PSpace.str k 1) σ (ProjSpace.coord k 1 0)) (c.e.symm v) =
        Real.exp (-Real.log (ArithHeightModel.u v)) := by
      refine (Weight.nsq_eq _ (secVal_mem _) (i := (0 : Fin 2)) (hs ▸ hm v)).trans ?_
      rw [hφ]
      exact (congrArg (fun a : ℂ => ‖a‖ ^ 2 * _) (h1 v)).trans (by simp)
    simp only [hn, Real.log_exp]
    rw [← mul_one (-(1 / 2) : ℝ), ← integral_log_dens, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun v => by ring)
  · rw [c.chernDens_eq hi (hm v) (i := (0 : Fin 2)) (hs ▸ hm v), Matrix.det_unique]
    have e₁ : c.hess (ProjAn.fsO1 k σ 1) (0 : Fin 2) (c.e.symm v) default default =
        ((ArithHeightModel.u v ^ 2)⁻¹ : ℝ) :=
      (congrArg₂ (fun F w => ReciprocityTheory.L2DbarEstimates.cHess 1 F w 0 0) (funext fun w => congrArg _ (hφ w)) (hr v)).trans
        (ArithHeightModel.cHess_log v)
    rw [e₁, Complex.ofReal_re]
    simp

theorem span_infty {A : Type} [CommRing A] : Ideal.span (Set.range (![0, 1] : Fin 2 → A)) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨1, rfl⟩)

def infty : Sp ℤ ⟶ PSpace ℤ 1 := pt (RingHom.id ℤ) ![0, 1] span_infty

instance : IsClosedImmersion infty := by
  have : IsClosedImmersion (infty ≫ PSpace.str ℤ 1) := by
    rw [toZ_ext (infty ≫ _) (𝟙 _)]; infer_instance
  exact IsClosedImmersion.of_comp infty (PSpace.str ℤ 1)

theorem exists_pt_eq {n : ℕ} (z : PSpace ℤ n) : ∃ (K : Type) (_ : Field K) (v : Fin (n + 1) → K)
    (hv : Ideal.span (Set.range v) = ⊤), pt (Int.castRingHom K) v hv (IsLocalRing.closedPoint K) = z := by
  obtain ⟨v, hv⟩ := projPt_surjective (Int.castRingHom ((PSpace ℤ n).residueField z))
    ⟨(PSpace ℤ n).fromSpecResidueField z, toZ_ext _ _⟩
  refine ⟨_, inferInstance, v.1, v.2, ?_⟩
  exact (congrArg (fun f => f.1 (IsLocalRing.closedPoint _)) hv).trans (Scheme.fromSpecResidueField_apply _ _)

theorem mem_range_infty {z : PSpace ℤ 1} (hz : z ∉ chart ℤ 1 0) : z ∈ Set.range infty := by
  obtain ⟨K, _, v, hv, rfl⟩ := exists_pt_eq z
  have h0 : v 0 = 0 := by
    by_contra h
    exact hz ((le_pt_preimage_chart_iff _ v hv 0).2 (Ne.isUnit h) (Opens.mem_top _))
  have h1 : v 1 ≠ 0 := fun h => span_range_eq_top_iff_ne_zero.1 hv (funext fun a => by fin_cases a <;> assumption)
  have e : spMap (Int.castRingHom K) ≫ infty = pt (Int.castRingHom K) v hv := by
    rw [infty, spMap_pt]
    exact (pt_eq_pt_iff _ _ _).2 ⟨Units.mk0 _ h1, funext fun a => by fin_cases a <;> simp [h0, Units.smul_def]⟩
  exact ⟨_, congrArg (fun f => f (IsLocalRing.closedPoint K)) e⟩

theorem height_infty {h : PSpace ℤ 1 → ℝ} (H : (hermitianTwistingSheaf ℤ 1).IsArithHeight h) : h (infty (genericPoint _)) = 0 := by
  have e : nonzeroLocus (GlobalTheory.secPull (ProjSpace.coord ℤ 1 1) infty) = ⊤ := by
    rw [GlobalTheory.nonzeroLocus_secPull, nonzeroLocus_coord]
    exact top_le_iff.1 ((le_pt_preimage_chart_iff _ _ _ 1).2 isUnit_one)
  have hu : genericPoint (Sp ℤ) ∈ nonzeroLocus (GlobalTheory.secPull (L := (hermitianTwistingSheaf ℤ 1).B) (ProjSpace.coord ℤ 1 1) infty) :=
    e.ge trivial
  rw [H.point _ infty ArithBase.isArithVar_int.charZero ArithBase.isArithVar_int.dim_eq _
    (Cartier.isRatSec_ratOfSec _ hu), HermLB.curveDeg_sec infty _ hu fun σ y => ptsIn_mono e.ge mem_ptsIn_top,
    finsum_eq_zero_of_forall_eq_zero, finsum_eq_zero_of_forall_eq_zero, sub_zero]
  · refine fun σ => finsum_eq_zero_of_forall_eq_zero fun y => ?_
    have hy : PtsOver.map infty rfl _ y = projPt σ ⟨![0, 1], span_infty⟩ := by
      refine Subtype.ext ?_
      change y.1 ≫ infty = pt σ ![0, 1] span_infty
      rw [toZ_ext y.1 (spMap σ), infty, spMap_pt]
      congr 1
      exact funext fun a => by fin_cases a <;> simp
    have hm : projPt σ ⟨![0, 1], span_infty⟩ ∈ ptsIn (PSpace.str ℤ 1) σ ((O1 ℤ 1).U (1 : Fin 2)) :=
      (le_pt_preimage_chart_iff σ _ span_infty 1).2 isUnit_one
    have e₁ := ProjAn.fubiniStudyWeight_projPoint ℤ σ 1 ⟨![0, 1], span_infty⟩ 1 one_ne_zero
    have e₂ := valR_pt_ratio σ ![0, 1] span_infty (i := 1) isUnit_one 1
    have e₃ : (ProjAn.fsO1 ℤ σ 1).nsq (secVal _ σ (ProjSpace.coord ℤ 1 1)) (projPt σ ⟨![0, 1], span_infty⟩) = 1 := by
      refine (Weight.nsq_eq (ProjAn.fsO1 ℤ σ 1) (secVal_mem _) hm).trans ?_
      refine (congrArg₂ (fun (a : ℂ) b => ‖a‖ ^ 2 * Real.exp (-b)) e₂ e₁).trans ?_
      simp
    rw [hy]
    exact (congrArg (Real.log · / 2) e₃).trans (by simp)
  · intro z
    refine mul_eq_zero_of_left (Int.cast_eq_zero.2 (by_contra fun hz => ?_)) _
    exact Cartier.notMem_supp_divOfSec.2 (e.ge trivial) (Cartier.CartierDiv.mem_supp_of_mult_ne_zero hz)

theorem height_eq_zero_off_chart : ∀ (h : PSpace ℤ 1 → ℝ), (hermitianTwistingSheaf ℤ 1).IsArithHeight h → ∀ z : PSpace ℤ 1, Order.coheight z = 1 → z ∉ chart ℤ 1 0 → h z = 0 := by
  intro h H z hz hn
  have := ProjSpace.isIntegral_of_isDomain ℤ 1
  obtain ⟨w, rfl⟩ := mem_range_infty hn
  have h₁ : infty w ≤ infty (genericPoint _) := (genericPoint_specializes w).map infty.continuous
  have h₂ : infty (genericPoint _) < genericPoint (PSpace ℤ 1) := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have h₃ : genericPoint (PSpace ℤ 1) ∈ chart ℤ 1 0 :=
      Cartier.gen_mem (x := chartι ℤ 1 0 (⊥ : PrimeSpectrum _)) (opensRange_chartι ℤ 1 0 ▸ ⟨_, rfl⟩)
    have h₄ : genericPoint (Sp ℤ) ∈ infty ⁻¹ᵁ chart ℤ 1 0 := by
      have e' : _ = genericPoint (PSpace ℤ 1) := (Specializes.antisymm e (genericPoint_specializes _)).eq
      exact show infty _ ∈ chart ℤ 1 0 from e'.symm ▸ h₃
    rw [infty, pt_preimage_chart] at h₄
    exact h₄ (Ideal.zero_mem _)
  by_cases hne : infty (genericPoint _) = infty w
  · exact hne ▸ height_infty H
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e => hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

theorem isometric_fubini_study_dim_zero {k : Type} [CommRing k] {n : ℕ} (hn : n = 0) :
    (hermitianTwistingSheaf k n).Isometric (HermLB.triv _) := by
  subst hn
  refine HermLB.isometric_of_chart (fun _ => PUnit.unit) (fun _ => le_top) (fun x j j' h h' => ?_) fun σ j y hy => ?_
  · obtain rfl : j = j' := Subsingleton.elim (α := Fin 1) _ _
    have e := (hermitianTwistingSheaf k 0).isLB.g_self j
    have e' := gm_res (𝟙 _) x (le_inf le_rfl le_rfl) h ((hermitianTwistingSheaf k 0).B.g j j)
    rw [← e']
    exact (congrArg _ e).trans ((map_one _).trans (map_one _).symm)
  · obtain ⟨v, rfl⟩ := projPt_surjective σ y
    have hu := (le_pt_preimage_chart_iff σ v.1 v.2 j).1 hy
    refine Eq.symm ((ProjAn.fubiniStudyWeight_projPoint k σ 0 v j hu.ne_zero).trans ?_)
    obtain rfl : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    rw [Fin.sum_univ_one, div_self hu.ne_zero, norm_one, one_pow, Real.log_one]
    rfl

theorem recursion_self {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) (hD : 1 ≤ D) {L : HermLB p} {h : X → ℝ} (H : L.IsArithHeight h) (u : L.B.Sec)
    (hu : genericPoint X ∈ nonzeroLocus u) (h0 : ∀ z, Order.coheight z = 1 → z ∉ nonzeroLocus u → h z = 0) :
    h (genericPoint X) = -∑ᶠ σ, (L.φ σ).chernInt D (ptsIn p σ (nonzeroLocus u)) fun y =>
      Real.log ((L.φ σ).nsq (secVal p σ u) y) / 2 := by
  have := hX.isLocallyNoetherian
  have e : nonzeroLocus (GlobalTheory.secPull u (𝟙 X)) = nonzeroLocus u := GlobalTheory.nonzeroLocus_secPull _ _
  have key {q : X ⟶ Sp k} (hq : 𝟙 X ≫ p = q) : h (genericPoint X) =
      -∑ᶠ σ, ((L.pull (𝟙 X) hq).φ σ).chernInt D (ptsIn q σ (nonzeroLocus u)) fun y =>
        Real.log ((L.φ σ).nsq (secVal p σ u) (PtsOver.map (𝟙 X) hq _ y)) / 2 := by
    subst hq
    have hu' : genericPoint X ∈ nonzeroLocus (GlobalTheory.secPull u (𝟙 X)) := e ▸ hu
    have h₁ := (H.recursion_sec (𝟙 X) u hu' hX.charZero hD hX.dim_eq).2
    rw [finsum_eq_zero_of_forall_eq_zero, zero_sub, e] at h₁
    · exact h₁
    intro z
    by_cases hz : (Cartier.divOfSec (L.restr (𝟙 X)).isLB _ hu').mult z = 0
    · rw [hz, Int.cast_zero, zero_mul]
    · refine mul_eq_zero_of_right _ (h0 z (Cartier.CartierDiv.coheight_eq_one_of_mult_ne_zero hz) fun hm => ?_)
      exact Cartier.notMem_supp_divOfSec.2 (e ▸ hm) (Cartier.CartierDiv.mem_supp_of_mult_ne_zero hz)
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y := Subtype.ext (Category.comp_id _)
  have hiso : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
    refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
      (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
    · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
        (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
      rw [Category.comp_id]
    · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))
  rw [key (Category.id_comp p)]
  simp only [hid, ← hiso.chernInt_eq]

theorem selfInter_line {n : ℕ} (hn : n = 1) [IsIntegral (PSpace ℤ n)] {a : ℝ} (ha : (hermitianTwistingSheaf ℤ n).IsSelfInter a) :
    a = 1 / 2 := by
  subst hn
  obtain ⟨h, H, rfl⟩ := ha
  have e : nonzeroLocus (ProjSpace.coord ℤ 1 0) = chart ℤ 1 0 := nonzeroLocus_coord ℤ 1 0
  have hg : genericPoint (PSpace ℤ 1) ∈ chart ℤ 1 0 :=
    Cartier.gen_mem (x := chartι ℤ 1 0 (⊥ : PrimeSpectrum _)) (opensRange_chartι ℤ 1 0 ▸ ⟨_, rfl⟩)
  rw [recursion_self (ProjSpace.isArithVar_int 1) le_rfl H (ProjSpace.coord ℤ 1 0) (e ▸ hg)
    (fun z h₁ h₂ => height_eq_zero_off_chart h H z h₁ (e ▸ h₂)),
    finsum_eq_single _ (Int.castRingHom ℂ) fun σ h => absurd (RingHom.ext_int _ _) h]
  refine neg_eq_iff_eq_neg.2 (Eq.trans ?_ (chernInt_log_coord ℤ (Int.castRingHom ℂ)))
  rw [← e]
  rfl

end GlobalTheory.FlagZ.Plane
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ProjSpace GlobalTheory.QCoh

namespace GlobalTheory.TautFlag

theorem resM_s_eq_ratioOn_smul (j j' : Fin 2) {V : (PSpace ℤ 1).Opens} (h : V ≤ chart ℤ 1 j) (h' : V ≤ chart ℤ 1 j') :
    resM K h' (s j') = ratioOn V j' h' j • resM K h (s j) := by
  have hm : Mono (kernel.ι quotMap) := equalizer.ι_mono
  refine injective_app_of_mono (kernel.ι quotMap) V ?_
  refine Eq.trans ?_ (kernel_ι_app_smul_resM_s j h _).symm
  rw [ratioOn_mul_ratioOn, ratioOn_mul_ratioOn]
  exact (app_resM _ _ _).trans ((congrArg (resM E h') (map_s j')).trans (resM_v j' h'))

theorem val_detUnit_rankOne_of_eq_smul {X : Scheme.{0}} {F : X.Modules} {U U' V : X.Opens} {a : Fin 1 → Γ(F, U)}
    {a' : Fin 1 → Γ(F, U')} (ha : IsFrame a) (ha' : IsFrame a') (h : V ≤ U) (h' : V ≤ U') (c : Γ(X, V))
    (hc : resM F h' (a' 0) = c • resM F h (a 0)) : (ha.detUnit ha' h h' : Γ(X, V)) = c := by
  rw [IsFrame.val_detUnit, Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply,
    hc, ← ha.basis_apply h, map_smul, Module.Basis.repr_self]
  simp

theorem det_g_adapt₀ (j j' : Fin 2) :
    (VB.det (flag.gr 0) 1).g (adapt₀ j).quot (adapt₀ j').quot = ((O1 ℤ 1).g j j')⁻¹ := by
  refine Units.ext (val_detUnit_rankOne_of_eq_smul _ _ _ _ _ ?_)
  refine (app_resM (VMetric.stepSeq flag 0).g inf_le_right (s j')).symm.trans ?_
  refine (congrArg ((VMetric.stepSeq flag 0).g.app _) (resM_s_eq_ratioOn_smul j j' inf_le_left inf_le_right)).trans ?_
  exact (Scheme.Modules.Hom.app_smul _ _ _).trans
    (congrArg (_ • ·) (app_resM (VMetric.stepSeq flag 0).g inf_le_left (s j)))

theorem grLB_zero_φ (σ : ℤ →+* ℂ) (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) :
    ((VMetric.grLB flag 0 stdH.cInf).φ σ).φ (adapt₀ j).quot y = -Real.log (nsqV j y).re := by
  have e := Met.quot_G ((stdH.h.stepMet flag 0).met σ) (VMetric.stepSeq_shortExact flag 0)
    (flag.isVB (Fin.castSucc 0)) (flag.isVB_gr 0) (adapt₀ j) hy
  refine congrArg (fun z : ℂ => -Real.log z.re) ((congrArg Matrix.det e).trans ((Matrix.det_fin_one _).trans ?_))
  refine Eq.trans ?_ (gram_adapt₀ j hy 0 0)
  have key (H : Matrix (Fin 0 ⊕ Fin 1) (Fin 0 ⊕ Fin 1) ℂ) : quotGram H 0 0 = H (.inr 0) (.inr 0) := by
    simp [quotGram, toBlocks₂₂]
  exact key _

theorem fubini_study_weight_eq_log_norm (σ : ℤ →+* ℂ) (j : Fin 2) (y : CxPts (PSpace.str ℤ 1) σ) :
    ((hermitianTwistingSheaf ℤ 1).φ σ).φ j y = Real.log (nsqV j y).re := by
  change (ProjAn.fsO1 ℤ σ 1).φ j y = _
  refine (Weight.fsBasis_φ _ _ _ _ _ _ _).trans (congrArg _ ?_)
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine (Fin.sum_univ_two _).trans ?_
  simp only [nsqV, Complex.mul_conj, Complex.add_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rfl

theorem isometric_grLB_zero :
    (VMetric.grLB TautFlag.flag 0 TautFlag.stdH.cInf).Isometric (ProjSpace.hermitianTwistingSheaf ℤ 1).dual :=
  HermLB.Isometric.symm (HermLB.isometric_of_chart (L := (hermitianTwistingSheaf ℤ 1).dual) (fun j => (adapt₀ j).quot)
    (fun _ => le_rfl) (fun x j j' _ _ => congrArg (gm (𝟙 _) x _) (det_g_adapt₀ j j').symm)
    fun σ j y hy => (grLB_zero_φ σ j hy).trans (congrArg (- ·) (fubini_study_weight_eq_log_norm σ j y).symm))

end GlobalTheory.TautFlag
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_first_isometric_dual_O1 : (VMetric.grLB TautFlag.flag 0 TautFlag.stdH.cInf).Isometric (ProjSpace.hermitianTwistingSheaf ℤ 1).dual := by
  atlas_forward_decl GlobalTheory.TautFlag.isometric_grLB_zero
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ProjSpace GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Points
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.TautFlag

theorem detUnit_chartSec_eq {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j : L.ι) :
    (isFrame_chartSec hL i).detUnit (isFrame_chartSec hL j) inf_le_left inf_le_right = L.g i j := by
  refine (Units.ext ?_ : L.g i j = _).symm
  have e : resM (toMod L) inf_le_right (LB.chartSec hL j) = (L.g i j : Γ(X, L.U i ⊓ L.U j)) •
      (isFrame_chartSec hL i).basis (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) 0 := by
    rw [IsFrame.basis_apply]
    refine ((LB.chartEquiv hL i inf_le_left).symm_apply_apply _).symm.trans ?_
    rw [LB.chartEquiv_symm_apply, LB.chartEquiv_apply]
    congr 1
    exact (resG_resG _ _ _).trans ((resG_resG _ _ _).trans (resG_self _ _))
  rw [IsFrame.val_detUnit, Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply,
    e, map_smul, Module.Basis.repr_self]
  simp

theorem detUnit_eq_g_of_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X.Modules} (φ : F ≅ toMod L)
    (i j : L.ι) {e : Fin 1 → Γ(F, L.U i)} {f : Fin 1 → Γ(F, L.U j)} (h : IsFrame e) (k : IsFrame f)
    (he : e = fun _ => φ.inv.app _ (LB.chartSec hL i)) (hf : f = fun _ => φ.inv.app _ (LB.chartSec hL j)) :
    h.detUnit k inf_le_left inf_le_right = L.g i j := by
  subst he hf
  exact (IsFrame.detUnit_map_iso (isFrame_chartSec hL i) (isFrame_chartSec hL j) φ.inv _ _).trans
    (detUnit_chartSec_eq hL i j)

theorem adapt₁_quot_e (j : Fin 2) : (adapt₁ j).quot.e = fun _ => (grIso₁ seq seq_shortExact isVB_seq₁
    (isVB_freeModule_fin _ 2) (isVB_toMod (O1_isLB ℤ 1))).inv.app _ (LB.chartSec (O1_isLB ℤ 1) j) := by
  have e : (VMetric.stepSeq flag 1).g = quotMap ≫ (grIso₁ seq seq_shortExact isVB_seq₁ (isVB_freeModule_fin _ 2)
    (isVB_toMod (O1_isLB ℤ 1))).inv := (Iso.eq_comp_inv _).2 π_grIso₁
  funext _
  exact (congrArg (fun φ => φ.app _ (t j)) e).trans ((app_app _ _ _ _).symm.trans (congrArg _ (quotMap_app_t_eq_chartSec j)))

theorem g_adapt₁_quot (j j' : Fin 2) :
    (VB.det (flag.gr 1) 1).g (adapt₁ j).quot (adapt₁ j').quot = (O1 ℤ 1).g j j' :=
  detUnit_eq_g_of_iso (O1_isLB ℤ 1) _ j j' _ _ (adapt₁_quot_e j) (adapt₁_quot_e j')

variable {σ : ℤ →+* ℂ}

theorem nsqV_eq_one_add (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) : nsqV j y = ((1 + ‖ipVT j y‖ ^ 2 : ℝ) : ℂ) := by
  rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1) with rfl | rfl
  · have r : ev _ σ _ (ratio ℤ 1 0 0) y = 1 := by rw [ev_eq hy, ratio, ratioOn_self, map_one]
    rw [nsqV, r, map_one, mul_one, Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one]
    rfl
  · have r : ev _ σ _ (ratio ℤ 1 1 1) y = 1 := by rw [ev_eq hy, ratio, ratioOn_self, map_one]
    rw [nsqV, r, map_one, mul_one, Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one,
      add_comm, ← norm_neg]
    rfl

theorem det_quotGram_one_add (b : ℂ) :
    (quotGram (Matrix.fromBlocks (Matrix.of fun (_ _ : Fin 1) => ((1 + ‖b‖ ^ 2 : ℝ) : ℂ))
      (Matrix.of fun (_ _ : Fin 1) => b) (Matrix.of fun (_ _ : Fin 1) => starRingEnd ℂ b) 1)).det =
      (((1 + ‖b‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have h : ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have e : starRingEnd ℂ b * b = ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) - 1 := by
    rw [mul_comm, Complex.mul_conj']
    push_cast
    ring
  rw [Complex.ofReal_inv]
  generalize ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) = n at h e
  simp only [quotGram, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.det_unique, Matrix.sub_apply, Matrix.mul_apply, Matrix.inv_subsingleton, Fintype.sum_unique]
  simp
  field_simp
  linear_combination -e

theorem fubini_study_weight_chart_eq (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) :
    ((hermitianTwistingSheaf ℤ 1).φ σ).φ j y = Real.log (1 + ‖ipVT j y‖ ^ 2) := by
  refine (Weight.fsBasis_φ _ _ (iSup_nonzeroLocus_coord ℤ 1) 1 (by simp) _ _).trans (congrArg _ ?_)
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine (Fin.sum_univ_two _).trans (Complex.ofReal_injective (Eq.trans ?_ (nsqV_eq_one_add j hy)))
  rw [nsqV, Complex.mul_conj', Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_pow]
  rfl

theorem isometric_grLB_one : (VMetric.grLB flag 1 stdH.cInf).Isometric (hermitianTwistingSheaf ℤ 1) := by
  refine HermLB.Isometric.symm (HermLB.isometric_of_chart (L := hermitianTwistingSheaf ℤ 1) (M := VMetric.grLB flag 1 stdH.cInf)
    (fun j : Fin 2 => (adapt₁ j).quot) (fun _ => le_rfl)
    (fun x j j' _ _ => congrArg (gm (𝟙 _) x _) (g_adapt₁_quot j j').symm) fun σ j y hy => ?_)
  have e := ((stdH.h.stepMet flag 1).met σ).quot_G (VMetric.stepSeq_shortExact flag 1)
    (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) (adapt₁ j) hy
  have e₂ := e.trans (congrArg quotGram (gram_adapt₁ j hy))
  refine (congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => -Real.log M.det.re) e₂).trans
    (Eq.trans ?_ (fubini_study_weight_chart_eq j hy).symm)
  beta_reduce
  rw [nsqV_eq_one_add j hy, det_quotGram_one_add, Complex.ofReal_re, Real.log_inv, neg_neg]

end GlobalTheory.TautFlag
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_second_isometric_O1 : (VMetric.grLB TautFlag.flag 1 TautFlag.stdH.cInf).Isometric (ProjSpace.hermitianTwistingSheaf ℤ 1) := by
  atlas_forward_decl GlobalTheory.TautFlag.isometric_grLB_one
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame

open scoped ComplexOrder

namespace GlobalTheory.TautDensity

def frameMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  fromBlocks 1 0 (of fun _ _ => w 0) 1

def gramMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  fromBlocks (of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0)) (of fun _ _ => w 0)
    (of fun _ _ => starRingEnd ℂ (w 0)) 1

theorem gramMat_eq (w : ReciprocityTheory.L2DbarEstimates.V 1) : gramMat w = (frameMat w)ᵀ * 1 * (frameMat w)ᴴᵀ := by
  ext (a | a) (b | b) <;>
    simp [gramMat, frameMat, mul_apply, Subsingleton.elim a 0, Subsingleton.elim b 0]

theorem det_frameMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : (frameMat w).det = 1 := by
  rw [frameMat, det_fromBlocks_zero₁₂]; simp

theorem hasFDerivAt_crd (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    HasFDerivAt (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => w 0)
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ) z :=
  (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ).hasFDerivAt

theorem contDiffAt_frameMat (z : ReciprocityTheory.L2DbarEstimates.V 1) (a b : Fin 1 ⊕ Fin 1) :
    ContDiffAt ℂ 1 (fun w => frameMat w a b) z := by
  rcases a with a | a <;> rcases b with b | b
  exacts [contDiffAt_const, contDiffAt_const,
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ).contDiff.contDiffAt,
    contDiffAt_const]

theorem mContDiffAt_frameMat (z : ReciprocityTheory.L2DbarEstimates.V 1) : MContDiffAt 1 frameMat z :=
  fun a b => (contDiffAt_frameMat z a b).restrict_scalars ℝ

theorem mdbar_frameMat (z η : ReciprocityTheory.L2DbarEstimates.V 1) : mdbar frameMat z η = 0 := by
  ext a b
  rw [mdbar_apply, dbar_eq_zero ((contDiffAt_frameMat z a b).differentiableAt one_ne_zero)]
  rfl

theorem mdel_frameMat (z ξ : ReciprocityTheory.L2DbarEstimates.V 1) :
    mdel frameMat z ξ = fromBlocks 0 0 (of fun _ _ => ξ 0) 0 := by
  ext a b
  rw [mdel_apply, del_eq_fderiv ((contDiffAt_frameMat z a b).differentiableAt one_ne_zero)]
  rcases a with a | a <;> rcases b with b | b
  · simp [frameMat]
  · simp [frameMat]
  · change fderiv ℂ (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => w 0) z ξ = ξ 0
    rw [(hasFDerivAt_crd z).fderiv]; rfl
  · simp [frameMat]

theorem mContDiffAt_gramMat (z : ReciprocityTheory.L2DbarEstimates.V 1) : MContDiffAt 1 gramMat z := by
  rw [funext gramMat_eq]
  exact ((mContDiffAt_frameMat z).transpose.mul (mContDiffAt_const 1)).mul
    (mContDiffAt_frameMat z).conjTranspose.transpose

theorem posDef_gramMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : (gramMat w).PosDef := by
  rw [gramMat_eq]
  exact posDef_chg ((isUnit_iff_isUnit_det _).2 (by rw [det_frameMat]; exact isUnit_one)) PosDef.one

theorem secondForm_gramMat (z ξ : ReciprocityTheory.L2DbarEstimates.V 1) :
    secondForm gramMat z ξ = of fun _ _ => ξ 0 := by
  have hu : IsUnit (frameMat z).det := by rw [det_frameMat]; exact isUnit_one
  have hi : (frameMat z)⁻¹ = fromBlocks 1 0 (of fun _ _ => -z 0) 1 := by
    refine inv_eq_left_inv ?_
    ext (a | a) (b | b) <;> obtain rfl := Subsingleton.elim a 0 <;>
      obtain rfl := Subsingleton.elim b 0 <;> simp [frameMat, mul_apply]
  rw [secondForm_eq, funext gramMat_eq, conn_changeFrame (H := fun _ => 1) (mContDiffAt_const 1)
    (by simp) (mContDiffAt_frameMat z) hu (mdbar_frameMat z), conn_const, Matrix.zero_mul, zero_add,
    mdel_frameMat, hi, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

theorem ofReal_u (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    ((ArithHeightModel.u z : ℝ) : ℂ) = 1 + z 0 * starRingEnd ℂ (z 0) := by
  rw [Complex.mul_conj, Complex.normSq_apply, ArithHeightModel.u]
  push_cast; ring

theorem inv_of_const (c : ℂ) : (of fun _ _ => c : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ = of fun _ _ => c⁻¹ := by
  ext a b
  simp [Ring.inverse_eq_inv', Subsingleton.elim a 0, Subsingleton.elim b 0]

theorem subGram_gramMat (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    subGram (gramMat z) = of fun _ _ => ((ArithHeightModel.u z : ℝ) : ℂ) := by
  rw [ofReal_u]; rfl

theorem quotGram_gramMat (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    quotGram (gramMat z) = of fun _ _ => ((ArithHeightModel.u z : ℝ) : ℂ)⁻¹ := by
  have h0 : ((ArithHeightModel.u z : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ArithHeightModel.u_pos z).ne'
  rw [quotGram, gramMat, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, ← ofReal_u, inv_of_const]
  ext a b
  simp only [Subsingleton.elim a 0, Subsingleton.elim b 0, Matrix.sub_apply, one_apply_eq, mul_apply,
    Fin.sum_univ_one, of_apply]
  field_simp
  rw [ofReal_u]; ring

theorem density_eq : ∀ v : ReciprocityTheory.L2DbarEstimates.V 1, 2 * diagVal (extTrace (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => (Matrix.fromBlocks (Matrix.of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0)) (Matrix.of fun _ _ => w 0) (Matrix.of fun _ _ => starRingEnd ℂ (w 0)) 1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)) v) (EuclideanSpace.single 0 1) = 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
  intro v
  change 2 * diagVal (extTrace gramMat v) (EuclideanSpace.single 0 1) = _
  have e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
  have ht : (secondForm gramMat v (EuclideanSpace.single 0 1) *
      secondFormAdj gramMat v (EuclideanSpace.single 0 1)).trace =
      (((ArithHeightModel.u v ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [secondFormAdj, secondForm_gramMat, subGram_gramMat, quotGram_gramMat, adj,
      ← transpose_nonsing_inv, inv_of_const]
    simp [trace, mul_apply, sq]
  rw [diagVal, extTrace_eq (mContDiffAt_gramMat v) (.of_forall posDef_gramMat), ← mul_assoc, e,
    Complex.re_ofReal_mul, ht, Complex.ofReal_re]
  ring

end GlobalTheory.TautDensity
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrix_green_value : ∀ v : ReciprocityTheory.L2DbarEstimates.V 1, 2 * diagVal (extTrace (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => (Matrix.fromBlocks (Matrix.of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0)) (Matrix.of fun _ _ => w 0) (Matrix.of fun _ _ => starRingEnd ℂ (w 0)) 1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)) v) (EuclideanSpace.single 0 1) = 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
  atlas_forward_decl GlobalTheory.TautDensity.density_eq
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.ProjSpace GlobalTheory.HermFrame GlobalTheory.ArInt

namespace GlobalTheory.TautFlag

theorem selfInter (HC : GlobalTheory.Published.ArCalc) : haveI := ProjSpace.isRegSurf_line.isIntegral;
    (ProjSpace.hermitianTwistingSheaf ℤ 1).IsSelfInter (1 / 2) ∧ (ProjSpace.hermitianTwistingSheaf ℤ 1).dual.IsSelfInter (1 / 2) := by
  have := ProjSpace.isRegSurf_line.isIntegral
  have hP := ProjSpace.isArithVar_int 1
  obtain ⟨Ψ, hΨ⟩ := ((HC.arExists ℤ _ _ 1 hP).2 Unit fun _ => hermitianTwistingSheaf ℤ 1).1
  have h₁ := ((HC.arIso ℤ _ _ 1 hP).2 Unit _ Ψ hΨ).1 ()
  have hval : Ψ (MvPolynomial.X () ^ (1 + 1)) = 1 / 2 := FlagZ.Plane.selfInter_line (n := 1) rfl h₁
  have hΦ := ((HC.arIso ℤ _ _ 1 hP).2 Unit _ Ψ hΨ).2.2 Unit (fun _ => (hermitianTwistingSheaf ℤ 1).dual) (fun _ _ => -1)
    fun _ => HermLB.icls_eq_iff.1 (by
      rw [icls_comb, HermLB.icls_dual, Fintype.sum_unique]
      exact neg_one_zsmul _)
  have h₂ := ((HC.arIso ℤ _ _ 1 hP).2 Unit _ _ hΦ).1 ()
  refine ⟨hval ▸ h₁, ?_⟩
  convert h₂ using 1
  rw [← hval]
  simp [lin]

theorem exists_chart (σ : ℤ →+* ℂ) (j : Fin 2) : ∃ c : AlgChart (PSpace.str ℤ 1) σ 1,
    c.e.source = ptsIn _ σ (chart ℤ 1 j) ∧ c.e.target = Set.univ ∧
      ∀ y ∈ c.e.source, c.e y 0 = ev _ σ (chart ℤ 1 j) (ratio ℤ 1 j (j.succAbove 0)) y := by
  let e : MvPolynomial (Fin 1) ℤ ≃ₐ[ℤ] Γ(PSpace ℤ 1, chart ℤ 1 j) :=
    (MvPolynomial.renameEquiv ℤ (finSuccAboveEquiv j)).trans (chartAlgEquiv ℤ 1 j)
  have he : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (PSpace.str ℤ 1) (chart ℤ 1 j))
      (fun a => ratio ℤ 1 j (j.succAbove a)) = (e : MvPolynomial (Fin 1) ℤ →+* _) :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans (e.commutes a).symm)
      fun b => (MvPolynomial.eval₂Hom_X' _ _ b).trans
        ((congrArg (chartAlgEquiv ℤ 1 j) (MvPolynomial.rename_X _ b)).trans
          (chartAlgEquiv_X ℤ 1 j (finSuccAboveEquiv j b))).symm
  obtain ⟨c, hs, ht, hx⟩ := FlagZ.Plane.exists_chart_of_bijective ℤ _ (PSpace.str ℤ 1) σ 1 _
    (isAffineOpen_chart ℤ 1 j) (fun a => ratio ℤ 1 j (j.succAbove a)) (by rw [he]; exact e.bijective)
  exact ⟨c, hs, ht, fun y hy => hx y hy 0⟩

theorem bcMeas_univ (σ : ℤ →+* ℂ) : ((stdH.h.stepMet flag 1).met σ).bcMeas (r := 1) (s := 1)
    (VMetric.stepSeq_shortExact flag 1) (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) Set.univ = 1 := by
  have := CxPts.secondCountableTopology_of_isProjOver σ (isProjOver_pspace_str ℤ 1)
  have H : ((stdH.h.stepMet flag 1).met σ).IsCInf := (stdH.cInf.restrict _ _) σ
  obtain ⟨c, hs, ht, hx⟩ := exists_chart σ 0
  obtain ⟨c', hs', -, hx'⟩ := exists_chart σ 1
  have hm : MeasurableSet c.e.source := c.e.open_source.measurableSet
  have hc (y : CxPts (PSpace.str ℤ 1) σ) (hy : y ∈ c.e.sourceᶜ) : y ∈ c'.e.source := by
    obtain ⟨j, hj⟩ := exists_mem_chart ℤ 1 (y.1 (IsLocalRing.closedPoint ℂ))
    rw [hs']
    rw [hs] at hy
    fin_cases j
    · exact absurd (mem_ptsIn.2 hj) hy
    · exact mem_ptsIn.2 hj
  have h₀ : ((stdH.h.stepMet flag 1).met σ).bcMeas (r := 1) (s := 1) (VMetric.stepSeq_shortExact flag 1)
      (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) c.e.sourceᶜ = 0 := by
    refine (Met.bcMeas_apply (r := 1) (s := 1) _ _ _ c' H hm.compl hc).trans
      (setLIntegral_measure_zero _ _ (measure_mono_null (t := {0}) ?_ (measure_singleton _)))
    rintro _ ⟨y, hy, rfl⟩
    have h₁ : c'.e y 0 = 0 := by
      rw [hx' y (hc y hy)]
      by_contra h
      have h₂ := (mem_ptsIn_basicOpen (hs' ▸ hc y hy) _).2 h
      rw [ratio, basicOpen_ratioOn] at h₂
      exact hy (hs ▸ (mem_ptsIn_inf.1 h₂).2)
    ext i
    rw [Subsingleton.elim i 0, h₁]
    rfl
  have hmem (v) : c.e.symm v ∈ c.e.source := c.e.map_target (ht ▸ trivial)
  have hr (v) : c.e (c.e.symm v) = v := c.e.right_inv (ht ▸ trivial)
  have hz (v) : ev _ σ (chart ℤ 1 0) (ratio ℤ 1 0 1) (c.e.symm v) = v 0 :=
    (hx _ (hmem v)).symm.trans (by rw [hr])
  have h1 (v) : ev _ σ (chart ℤ 1 0) (ratio ℤ 1 0 0) (c.e.symm v) = 1 := by
    rw [ev_eq (hs ▸ hmem v), ratio, ratioOn_self, map_one]
  have hG : (fun v => ((stdH.h.stepMet flag 1).met σ).gram (adapt₁ 0).frame (c.e.symm v)) =
      fun w : ReciprocityTheory.L2DbarEstimates.V 1 => (Matrix.fromBlocks (Matrix.of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0))
        (Matrix.of fun _ _ => w 0) (Matrix.of fun _ _ => starRingEnd ℂ (w 0)) 1 :
          Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) := funext fun v => by
    have e₁ : nsqV 0 (c.e.symm v) = 1 + v 0 * starRingEnd ℂ (v 0) := by
      rw [nsqV, h1, hz, map_one, mul_one]
    have e₂ : ipVT 0 (c.e.symm v) = v 0 := hz v
    rw [gram_adapt₁ 0 (hs ▸ hmem v), e₁, e₂]
  have hd (v) : ((stdH.h.stepMet flag 1).met σ).bcDens (r := 1) (s := 1) (VMetric.stepSeq_shortExact flag 1)
      (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) c (c.e.symm v) =
        1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
    refine (Met.bcDens_eq (r := 1) (s := 1) _ _ _ (adapt₁ 0) c H (hmem v) (hs ▸ hmem v)).trans ?_
    refine Eq.trans ?_ (GlobalTheory.T.hermitian_matrix_green_value v)
    exact congrArg₂ (fun K w => 2 * diagVal (extTrace K w) (EuclideanSpace.single 0 1)) hG (hr v)
  have hn (v : ReciprocityTheory.L2DbarEstimates.V 1) : 0 ≤ 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
    have := Real.pi_pos; positivity
  rw [← measure_add_measure_compl hm, h₀, add_zero]
  refine (Met.bcMeas_apply (r := 1) (s := 1) _ _ _ c H hm subset_rfl).trans ?_
  rw [c.e.image_source_eq_target, ht, Measure.restrict_univ]
  refine (lintegral_congr fun v => congrArg ENNReal.ofReal (hd v)).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero
    (ArithHeightModel.integral_dens.trans_ne one_ne_zero)) (.of_forall hn), ArithHeightModel.integral_dens,
    ENNReal.ofReal_one]

theorem flagBc_flag : stdH.h.FlagBcFinite flag ∧ stdH.h.flagBc flag = 1 := by
  have e (σ) : ((stdH.h.stepMet flag 0).met σ).bcMeas (VMetric.stepSeq_shortExact flag 0)
      (flag.isVB (Fin.castSucc 0)) (flag.isVB_gr 0) = 0 := Met.bcMeas_rank_zero _ _ _
  have e' (σ) : ((stdH.h.stepMet flag 1).met σ).bcMeas (VMetric.stepSeq_shortExact flag 1)
      (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) Set.univ = 1 := bcMeas_univ σ
  refine ⟨Fin.forall_fin_two.2 ⟨fun σ => ?_, fun σ => ?_⟩, ?_⟩
  · exact (congrArg (fun μ : Measure _ => μ Set.univ) (e σ)).trans_ne ENNReal.zero_ne_top
  · exact (e' σ).trans_ne ENNReal.one_ne_top
  · rw [VMetric.flagBc, Fin.sum_univ_two]
    refine (congrArg₂ (· + ·) (finsum_eq_zero_of_forall_eq_zero fun σ => ?_)
      ((finsum_eq_single _ (Int.castRingHom ℂ) fun σ h => absurd (RingHom.ext_int _ _) h).trans ?_)).trans
        (zero_add 1)
    · exact congrArg (fun μ : Measure _ => (μ Set.univ).toReal) (e σ)
    · exact congrArg ENNReal.toReal (e' _)

theorem exists_flag : GlobalTheory.Published.ArCalc → haveI := ProjSpace.isRegSurf_line.isIntegral;
    ∃ fl : Vert.Flag (HermVB.std (PSpace.str ℤ 1) 2).E 2,
      (VMetric.grLB fl 0 (HermVB.std (PSpace.str ℤ 1) 2).cInf).Isometric (ProjSpace.hermitianTwistingSheaf ℤ 1).dual ∧
        (HermVB.std (PSpace.str ℤ 1) 2).h.flagBc fl = 1 ∧
          VMetric.IsFlagCh2 (HermVB.std (PSpace.str ℤ 1) 2).cInf fl 0 := fun HC => by
  have := ProjSpace.isRegSurf_line.isIntegral
  obtain ⟨s₁, s₂⟩ := selfInter HC
  have hX := ProjSpace.isArithVar_int 1
  refine ⟨flag, GlobalTheory.T.graded_first_isometric_dual_O1, flagBc_flag.2, flagBc_flag.1, ![1 / 2, 1 / 2], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact GlobalTheory.T.graded_first_isometric_dual_O1.symm.isSelfInter hX s₂
    · exact GlobalTheory.T.graded_second_isometric_O1.symm.isSelfInter hX s₁
  · rw [flagBc_flag.2, Fin.sum_univ_two]
    norm_num

end GlobalTheory.TautFlag
end
end
