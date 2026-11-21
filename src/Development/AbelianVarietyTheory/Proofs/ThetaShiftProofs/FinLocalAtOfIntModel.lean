import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinSiteNormEqZpowSiteAlg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominators
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralElemOfIsAlgebraicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScalingStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLetters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLetterRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFrameChangeByConstants
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOfStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidArcOfMono
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecordAtOfIsArcFr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CorrOfValFieldExtension

section
noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Units

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem arcιR_isUnit_mul (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) :
    IsUnit (arcιR Dw V ϖ (PowerSeries.C ϖ * PowerSeries.X)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  exact isUnit_of_mul_isUnit_left h

theorem letMR_det_isUnit (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (τ : E →+* ℂ) :
    IsUnit (letMR Dw V ϖ τ).det := by
  classical
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  have h2 := isUnit_of_mul_isUnit_right h
  have h3 := isUnit_of_dvd_unit (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))
    (Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))) (Finset.mem_univ τ))) h2
  rw [RingHom.map_det] at h3
  exact h3

theorem arcιR_C_isUnit (Dw : Datum H) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {v : V} (hv : v ≠ 0) : IsUnit (arcιR Dw V ϖ (PowerSeries.C v)) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hϖ
  have h := arcιR_isUnit_mul Dw V ϖ
  rw [map_mul (arcιR Dw V ϖ)] at h
  rw [map_mul (PowerSeries.C (R := V)), map_pow (PowerSeries.C (R := V)), map_mul (arcιR Dw V ϖ),
    map_pow (arcιR Dw V ϖ)]
  exact ((u.isUnit.map _).map _).mul ((isUnit_of_mul_isUnit_left h).pow n)

end Units

theorem exists_lift_open {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {S : Type} [CommRing S] (g : c.F →+* S) (χ : Sp S ⟶ Y.X) (hcond : χ ≫ Y.s = spMap g ≫ spMap β)
    (hj : ∀ q : Sp S, χ q ∈ Set.range Y.j) :
    ∃ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = χ ∧ z ≫ pullback.snd _ _ = spMap g := by
  let p : Sp S ⟶ pullback Y.s (spMap β) := pullback.lift χ (spMap g) hcond
  have hr : Set.range p ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    obtain ⟨w, hw⟩ := hj q
    rw [← hw]
    have h2 : Y.jQ w ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨w, rfl⟩
    simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using h2
  have := Y.jQ_open
  refine ⟨IsOpenImmersion.lift Y.jQ p hr, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ p hr ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

theorem exists_dvr_frPt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Tv : CDVR) (ϖ : Tv.V) (f : c.F →+* Tv.Fr) (b : O →+* Tv.V) (a : ArcIn Dw l β Tv.V b) (χ : Sp (PowerSeries Tv.V) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR Tv.V)) (th : a.D₀.P.L.Sec), Irreducible ϖ → f.comp β = (algebraMap Tv.V Tv.Fr).comp b → (∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = f (embK c τ x)) → χ ≫ Y.s = spMap (PowerSeries.C (R := Tv.V)) ≫ spMap b → (∀ x : Sp (PowerSeries Tv.V), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ArcBasis W ρ e → ThNZ th → ∃ (_ : Algebra c.F (ArcSR Dw Tv.V ϖ)), (∀ (x : c.F) (v : Tv.V) (n : ℕ), f x * algebraMap Tv.V Tv.Fr ϖ ^ n = algebraMap Tv.V Tv.Fr v → algebraMap c.F (ArcSR Dw Tv.V ϖ) x * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ) ^ n = arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) v)) ∧ ∃ y₀ yR : FrPt Xo c (ArcSR Dw Tv.V ϖ), IsArcFr W e th (arcιR Dw Tv.V ϖ) y₀ ∧ FrChg (letMR Dw Tv.V ϖ) 1 y₀ yR := by
  intro L1 L2 E _ _ _ H Dw l Xo c O _ β Y Tv ϖ f b a χ W ρ e th hϖ hfb hρ hχ hj _ hpush hbasis hth
  let ι := arcιR Dw Tv.V ϖ
  let κ : Tv.V →+* ArcSR Dw Tv.V ϖ := ι.comp (PowerSeries.C (R := Tv.V))
  have hκ : ∀ y : nonZeroDivisors Tv.V, IsUnit (κ y) := fun y =>
    arcιR_C_isUnit Dw Tv.V hϖ (nonZeroDivisors.ne_zero y.2)
  let g : Tv.Fr →+* ArcSR Dw Tv.V ϖ := IsLocalization.lift hκ
  have hg : ∀ v, g (algebraMap Tv.V Tv.Fr v) = κ v := fun v => IsLocalization.lift_eq hκ v
  letI alg : Algebra c.F (ArcSR Dw Tv.V ϖ) := (g.comp f).toAlgebra
  have halg : ∀ x, algebraMap c.F (ArcSR Dw Tv.V ϖ) x = g (f x) := fun _ => rfl
  refine ⟨alg, ?_, ?_⟩
  · intro x v n h
    have h2 := congrArg g h
    rw [map_mul, map_pow, hg, hg] at h2
    exact h2
  · have hcomp : (algebraMap c.F (ArcSR Dw Tv.V ϖ)).comp β = ι.comp ((PowerSeries.C (R := Tv.V)).comp b) := by
      ext1 x
      have h1 : f (β x) = algebraMap Tv.V Tv.Fr (b x) := RingHom.congr_fun hfb x
      show g (f (β x)) = κ (b x)
      rw [h1, hg]
    have hcond : (spMap ι ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcSR Dw Tv.V ϖ)) ≫ spMap β := by
      rw [Category.assoc, hχ, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
    obtain ⟨z, hz1, hz2⟩ := exists_lift_open Y (algebraMap c.F (ArcSR Dw Tv.V ϖ)) (spMap ι ≫ χ) hcond (by
      intro q
      rw [Scheme.Hom.comp_apply]
      refine hj _ fun h => ?_
      have h' : ι (PowerSeries.C ϖ * PowerSeries.X) ∈ q.asIdeal := h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (arcιR_isUnit_mul Dw Tv.V ϖ)))
    have hflat := (GlobalTheory.LetterDenom.main E H Dw Tv ϖ hϖ.ne_zero).2.2.1
    obtain ⟨y₀, -, hy₀⟩ := exists_isArcFr L1 L2 E H Dw l Xo c O β Y Tv.V b a χ W ρ e th hbasis hth (Or.inr hpush)
      (ArcSR Dw Tv.V ϖ) ι z hflat hz1
      (by rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]; rfl)
      (fun τ x => by rw [halg, ← hρ, hg]; rfl)
    obtain ⟨yR, hyR⟩ := (frChg_exists_unique_units E H Dw l Xo c (ArcSR Dw Tv.V ϖ) (letMR Dw Tv.V ϖ) 1 y₀).1
      (letMR_det_isUnit Dw Tv.V ϖ) isUnit_one
    exact ⟨y₀, yR, hy₀, hyR⟩

end GlobalTheory.ArcQ
end
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcFramedPoint_value_isHomogeneous_letters : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁), algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  first | exact @GlobalTheory.ArcQ.evR_arc_isHomogeneous | exact GlobalTheory.ArcQ.evR_arc_isHomogeneous | (intros; apply GlobalTheory.ArcQ.evR_arc_isHomogeneous <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V), ϖ ≠ 0 → IsDomain (ArcSR Dw Tv.V ϖ) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (ArcSR Dw Tv.V ϖ)) ∧ ((arcιR Dw Tv.V ϖ).comp (PowerSeries.C (R := Tv.V))).Flat ∧ (∃ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) ∧ ∀ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) → (∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) → ∀ f : ArcSR Dw Tv.V ϖ, (∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr), algebraMap _ (ArcS Dw Tv.Fr) P = ψ f) → ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G := by
  first | exact @GlobalTheory.LetterDenom.main | exact GlobalTheory.LetterDenom.main | (intros; apply GlobalTheory.LetterDenom.main <;> assumption)
end

section
section
namespace GlobalTheory.LetterEval

open GlobalTheory.DiscEval

section General

variable {K : Type} [NormedField K] [CompleteSpace K] {V F : Type} [CommRing V] [Field F]
  (a : V →+* F) (ι : F →+* K) (hi : ∀ v, ‖(ι.comp a) v‖ ≤ 1) {ϖ : V} (hϖ : a ϖ ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1)

include hϖ ht0 in

theorem hasSum_laurent_of_mul_eq {q : LaurentSeries F} {g : PowerSeries V} {N : ℕ}
    (h : q * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.map a g)) :
    HasSum (fun k : ℤ => ι (q.coeff k) * t ^ k)
      (((ι (a ϖ) * t) ^ N)⁻¹ * discEval (ι.comp a) hi ht g) := by
  have h2 : (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.single (N : ℤ) (a ϖ ^ N) := by
    rw [← map_pow, mul_pow, ← map_pow PowerSeries.C, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  have h4 : a ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ
  have hc : ∀ n : ℤ, q.coeff n = if n + N < 0 then 0 else
      (a ϖ ^ N)⁻¹ * a (PowerSeries.coeff (n + N).natAbs g) := fun n => by
    have h3 := congrArg (fun g : LaurentSeries F => g.coeff (n + N)) h
    simp only [h2, HahnSeries.coeff_mul_single_add] at h3
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_map] at h3
    split_ifs at h3 ⊢
    · exact (mul_eq_zero.1 h3).resolve_right h4
    · rw [← h3]
      field_simp
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - N := fun k l hkl => by simpa using hkl
  rw [← hinj.hasSum_iff]
  · refine Eq.mpr (congrArg (HasSum · _) (funext fun k => ?_))
      ((hasSum_discEval (ι.comp a) hi ht g).mul_left (((ι (a ϖ) * t) ^ N)⁻¹))
    rw [Function.comp_apply, hc, sub_add_cancel, if_neg (by omega), Int.natAbs_natCast,
      zpow_sub₀ ht0, zpow_natCast, zpow_natCast, map_mul, map_inv₀, map_pow, RingHom.comp_apply,
      mul_pow, mul_inv]
    ring
  · intro n hn
    rw [hc, if_pos, map_zero, zero_mul]
    by_contra h0
    exact hn ⟨(n + N).toNat, by simp only; omega⟩

include hϖ ht0 in

theorem hasSum_lcoeffPoly {σ : Type} (Y : σ → K) {P : MvPolynomial σ (LaurentSeries F)}
    {G : MvPolynomial σ (PowerSeries V)} {N : ℕ}
    (h : P * MvPolynomial.C
        (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ F).comp (PowerSeries.map a)) G) :
    HasSum (fun k : ℤ => MvPolynomial.eval Y (MvPolynomial.map ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k)
      (((ι (a ϖ) * t) ^ N)⁻¹ * MvPolynomial.eval₂ (discEval (ι.comp a) hi ht) Y G) := by
  classical
  have hμ : ∀ μ, P.coeff μ *
      (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.map a (G.coeff μ)) := fun μ => by
    have := congrArg (MvPolynomial.coeff μ) h
    rwa [← map_pow, mul_comm, MvPolynomial.coeff_C_mul, mul_comm, MvPolynomial.coeff_map] at this
  set s := P.support ∪ G.support
  have hP : ∀ k : ℤ, GlobalTheory.ArcQ.lcoeffPoly P k =
      ∑ μ ∈ s, MvPolynomial.monomial μ ((P.coeff μ).coeff k) := fun k =>
    Finset.sum_subset Finset.subset_union_left fun μ _ hμ => by
      simp [MvPolynomial.notMem_support_iff.1 hμ]
  have hG : MvPolynomial.eval₂ (discEval (ι.comp a) hi ht) Y G =
      ∑ μ ∈ s, discEval (ι.comp a) hi ht (G.coeff μ) * ∏ k ∈ μ.support, Y k ^ μ k := by
    rw [MvPolynomial.eval₂_eq]
    exact Finset.sum_subset Finset.subset_union_right fun μ _ hμ => by
      simp [MvPolynomial.notMem_support_iff.1 hμ]
  rw [hG, Finset.mul_sum]
  simp_rw [← mul_assoc]
  refine Eq.mpr (congrArg (HasSum · _) (funext fun m => ?_))
    (hasSum_sum fun μ (_ : μ ∈ s) =>
      (hasSum_laurent_of_mul_eq a ι hi hϖ ht0 ht (hμ μ)).mul_right (∏ k ∈ μ.support, Y k ^ μ k))
  rw [hP, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.eval_monomial, Finsupp.prod]
  ring

end General

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem exists_eval : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  intro E _ _ _ H Dw Tv ϖ K _ _ _ ιT hϖ hi t Y ht0 ht hY
  have ht0' : t ≠ 0 := norm_pos_iff.1 ht0
  have hϖ' : algebraMap Tv.V Tv.Fr ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Tv.V Tv.Fr)).2 hϖ
  have hϖ'' : ιT (algebraMap Tv.V Tv.Fr ϖ) ≠ 0 := (map_ne_zero ιT).2 hϖ'
  have hi' : ∀ v, ‖(ιT.comp (algebraMap Tv.V Tv.Fr)) v‖ ≤ 1 := hi
  let g : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V) →+* K :=
    MvPolynomial.eval₂Hom (discEval _ hi' ht) Y
  have hgC : ∀ p, g (MvPolynomial.C p) = discEval _ hi' ht p := fun p =>
    MvPolynomial.eval₂Hom_C _ _ _
  have hgX : ∀ x, g (MvPolynomial.X x) = Y x := fun x => MvPolynomial.eval₂Hom_X' _ _ _
  have hϖX : discEval _ hi' ht (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) =
      ιT (algebraMap Tv.V Tv.Fr ϖ) * t := by
    rw [map_mul, discEval_C, discEval_X, RingHom.comp_apply]
  have hu : IsUnit (g (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw Tv.V)) := by
    rw [isUnit_iff_ne_zero, map_mul, hgC, hϖX]
    refine mul_ne_zero (mul_ne_zero hϖ'' ht0') ?_
    convert hY using 1
    rw [arcDetR, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    exact hgX _
  let ev : ArcSR Dw Tv.V ϖ →+* K := IsLocalization.Away.lift _ hu
  have hev : ∀ G, ev (algebraMap _ (ArcSR Dw Tv.V ϖ) G) = g G := fun G =>
    IsLocalization.Away.lift_eq _ hu G
  have hevι : ∀ p, ev (arcιR Dw Tv.V ϖ p) = discEval _ hi' ht p := fun p =>
    (hev _).trans (hgC p)
  refine ⟨ev, fun p => ?_, fun x => (hev _).trans (hgX x), fun f N G P hf hP => ?_⟩
  · rw [hevι, ← (hasSum_discEval _ hi' ht p).tsum_eq]
    rfl
  · have hs := hasSum_lcoeffPoly _ ιT hi' hϖ' ht0' ht Y hP
    refine ⟨by simpa using hs.summable.tendsto_cofinite_zero.norm, ?_⟩
    rw [hs.tsum_eq]
    have h1 := congrArg ev hf
    rw [map_mul, map_pow, hevι, hϖX, hev] at h1
    have h2 : (ιT (algebraMap Tv.V Tv.Fr ϖ) * t) ^ N ≠ 0 := pow_ne_zero _ (mul_ne_zero hϖ'' ht0')
    rw [eq_inv_mul_iff_mul_eq₀ h2, mul_comm]
    exact h1

end GlobalTheory.LetterEval
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  atlas_forward_decl GlobalTheory.LetterEval.exists_eval
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ.FrameCut

theorem lcoeffPoly_coeff {ι K₁ : Type} [Field K₁] (P : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ)
    (μ : ι →₀ ℕ) : (GlobalTheory.ArcQ.lcoeffPoly P m).coeff μ = (P.coeff μ).coeff m := by
  classical
  simp only [GlobalTheory.ArcQ.lcoeffPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; rfl

theorem lcoeffPoly_add {ι K₁ : Type} [Field K₁] (P Q : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (P + Q) m = GlobalTheory.ArcQ.lcoeffPoly P m + GlobalTheory.ArcQ.lcoeffPoly Q m := by
  ext μ
  simp only [lcoeffPoly_coeff, MvPolynomial.coeff_add, HahnSeries.coeff_add]

theorem lcoeffPoly_monomial {ι K₁ : Type} [Field K₁] (μ : ι →₀ ℕ) (f : LaurentSeries K₁) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.monomial μ f) m = MvPolynomial.monomial μ (f.coeff m) := by
  classical
  ext ν
  simp only [lcoeffPoly_coeff, MvPolynomial.coeff_monomial]
  split_ifs
  · rfl
  · rfl

theorem lcoeffPoly_C_mul_map {ι L : Type} [Field L] (g : LaurentSeries L) (Q : MvPolynomial ι L) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) Q) m =
      MvPolynomial.C (g.coeff m) * Q := by
  ext ν
  rw [lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm g,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]

theorem lcoeffPoly_const_mul {ι L : Type} [Field L] (x : L) (P : MvPolynomial ι (LaurentSeries L)) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.C (HahnSeries.C (Γ := ℤ) x) * P) m =
      MvPolynomial.C x * GlobalTheory.ArcQ.lcoeffPoly P m := by
  ext ν
  rw [lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, lcoeffPoly_coeff,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem exists_subst {ι K₁ L S : Type} [Field K₁] [Field L] [CommRing S] (io : K₁ →+* L)
    (Φ : MvPolynomial ι (LaurentSeries K₁) →+* S) (j : MvPolynomial ι (LaurentSeries L) →+* S)
    (q : ι → MvPolynomial ι L)
    (hC : ∀ f : LaurentSeries K₁, ∃ g : LaurentSeries L, (∀ m, g.coeff m = io (f.coeff m)) ∧
      Φ (MvPolynomial.C f) = j (MvPolynomial.C g))
    (hX : ∀ x, Φ (MvPolynomial.X x) = j (MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (q x)))
    (P : MvPolynomial ι (LaurentSeries K₁)) :
    ∃ P₁ : MvPolynomial ι (LaurentSeries L), j P₁ = Φ P ∧ ∀ m, GlobalTheory.ArcQ.lcoeffPoly P₁ m =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp io) q (GlobalTheory.ArcQ.lcoeffPoly P m) := by
  induction P using MvPolynomial.induction_on' with
  | monomial μ f =>
    obtain ⟨g, hg, hΦ⟩ := hC f
    refine ⟨MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (μ.prod fun x e => q x ^ e), ?_, fun m => ?_⟩
    · rw [MvPolynomial.monomial_eq, map_mul, map_mul, hΦ]
      simp only [Finsupp.prod, map_prod, map_pow, hX]
    · rw [lcoeffPoly_C_mul_map, lcoeffPoly_monomial, MvPolynomial.eval₂Hom_monomial, hg]
      rfl
  | add P Q hP hQ =>
    obtain ⟨P₁, h1, h2⟩ := hP
    obtain ⟨Q₁, h3, h4⟩ := hQ
    exact ⟨P₁ + Q₁, by rw [map_add, map_add, h1, h3], fun m => by
      rw [lcoeffPoly_add, lcoeffPoly_add, map_add, h2, h4]⟩

theorem eval_subst {ι K₁ L K : Type} [Field K₁] [Field L] [Field K] (io : K₁ →+* L) (ιT : L →+* K)
    (q : ι → MvPolynomial ι L) (Y : ι → K) (R : MvPolynomial ι K₁) :
    MvPolynomial.eval Y (MvPolynomial.map ιT (MvPolynomial.eval₂Hom (MvPolynomial.C.comp io) q R)) =
      MvPolynomial.eval (fun x => MvPolynomial.eval Y (MvPolynomial.map ιT (q x)))
        (MvPolynomial.map (ιT.comp io) R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp => simp only [map_mul, hp, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, MvPolynomial.eval_X]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem arcNum_of_poly {K₁ : Type} [Field K₁] (P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) :
    arcNum (algebraMap _ (ArcS Dw K₁) P) = P := by
  have hs : ∃ Q, algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) Q =
      algebraMap _ (ArcS Dw K₁) P := ⟨P, rfl⟩
  rw [arcNum, dif_pos hs]
  exact GlobalTheory.ArcConst.algebraMap_injective Dw K₁ hs.choose_spec

theorem wchar_gen {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : Ix Dw → Sˣ)
    (h : ∀ x, t (some x) = 1) : wchar (ex Dw a n) t = (t none : S) ^ n := by
  rw [wchar, Fintype.prod_option]
  simp [h, ex]

set_option maxHeartbeats 1600000 in

theorem frameBound_of_cut (hL : Out.Laws) (hL2 : Out.Laws2) {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hev : GlobalTheory.Reg.EvLaws Xo c) {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] {d : ArcDatum Xo c K₁}
    {w : HeightOneSpectrum (𝓞 K₁)} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {Fs : Set (Rul Xo c)}
    (hFs : ∀ F ∈ Fs, F ∈ sec Xo c a n) (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr)
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr) (hγ : γ ≠ 0)
    (hBc : BcRigidAt Dv γ lam Bm) (hRec : RecordAt Dv Fs) :
    FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) n d Fs := by
  intro F hF t ht Y hY hdet
  obtain ⟨φ, ψ, z₁, z₂, tγ, hφC, hφX, hψC, hψX, htγ, htγ', hm1, hm2, hb⟩ := hBc
  have hϖ : Dv.ϖ ≠ 0 := Dv.ϖ_irr.ne_zero
  obtain ⟨hdomR, -, -, -, hdiv⟩ := GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators E H Dw Dv.Tv Dv.ϖ hϖ
  have hdom1 := GlobalTheory.ArcConst.isDomain Dw K₁
  have hdom2 := GlobalTheory.ArcConst.isDomain Dw Dv.Tv.Fr
  have hinj := GlobalTheory.ArcConst.algebraMap_injective Dw Dv.Tv.Fr
  have hsec := hFs F hF
  obtain ⟨P, hP, -⟩ := GlobalTheory.T.arcFramedPoint_value_isHomogeneous_letters hL hL2 E H Dw l Xo c hev K₁ d a n F hsec
  have e1 := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw K₁)).1 _ φ _ _ hm1
  have e2 := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcSR Dw Dv.Tv.V Dv.ϖ)).1 _ ψ _ _ hm2
  have e3 := ((GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw Dv.Tv.Fr)).2 hdom2).1 tγ _ _ hb
  rw [wchar_gen a n tγ htγ', e1, e2, htγ, ← hP] at e3
  set f := evR Xo c F Dv.yR with hf
  let q : ArcLt Dw → MvPolynomial (ArcLt Dw) Dv.Tv.Fr := fun x =>
    ∑ l : Fin (Dw.mult x.1), MvPolynomial.X ⟨x.1, x.2.1, l⟩ * MvPolynomial.C (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹)
  obtain ⟨P₁, hP₁, hco⟩ := exists_subst Dv.io (φ.toRingHom.comp (algebraMap _ (ArcS Dw K₁)))
    (algebraMap _ (ArcS Dw Dv.Tv.Fr)) q hφC (fun x => by
      refine (hφX x).trans ?_
      simp only [q, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, arcX]) P
  have hγn : γ ^ n ≠ 0 := pow_ne_zero _ hγ
  let P₂ : MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr) :=
    MvPolynomial.C (HahnSeries.C (Γ := ℤ) (γ ^ n)⁻¹) * P₁
  have hP₂ : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₂ = ψ.toRingHom f := by
    have : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₁ = _ := hP₁.trans e3
    simp only [P₂]
    rw [map_mul, this, ← mul_assoc, ← map_pow, ← map_mul, ← map_pow, ← map_mul, ← map_pow, ← map_mul,
      inv_mul_cancel₀ hγn, map_one, map_one, map_one, one_mul]
    rfl
  have hψι : ψ.toRingHom.comp (arcιR Dw Dv.Tv.V Dv.ϖ) =
      (arcι Dw Dv.Tv.Fr).comp (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr)) := RingHom.ext fun p => hψC p
  obtain ⟨N, G, hG⟩ := hdiv ψ.toRingHom hψι hψX f ⟨P₂, hP₂⟩
  have hψalg : ψ.toRingHom.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Dv.Tv.V)) _) =
      (algebraMap _ (ArcS Dw Dv.Tv.Fr)).comp (MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr)))) := by
    refine MvPolynomial.ringHom_ext (fun p => ?_) (fun x => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      exact hψC p
    · simp only [RingHom.comp_apply, MvPolynomial.map_X]
      exact hψX x
  have hPG : P₂ * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr (PowerSeries.C (R := Dv.Tv.Fr)
      (algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ) * PowerSeries.X)) ^ N =
      MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr))) G := by
    apply hinj
    have h1 := congrArg ψ.toRingHom hG
    have h2 := RingHom.congr_fun hψalg G
    have h3 := RingHom.congr_fun hψι (PowerSeries.C (R := Dv.Tv.V) Dv.ϖ * PowerSeries.X)
    simp only [RingHom.comp_apply] at h2 h3
    rw [h2, map_mul, map_pow, h3, ← hP₂, map_mul (PowerSeries.map _), PowerSeries.map_C, PowerSeries.map_X] at h1
    rw [← h1, map_mul, map_pow]
    rfl
  have hdet0 : (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨ev, hevC, hevX, hevf⟩ := GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc E H Dw Dv.Tv Dv.ϖ Z.K Dv.ιT hϖ Dv.norm_le t Y
    (Z.S_disc t ht).1 (Z.S_disc t ht).2 hdet0
  obtain ⟨hT, hS⟩ := hevf f N G P₂ hG hPG
  have hbd := hRec F hF t ht Y hY hdet ev hevC hevX
  have hq : (fun x => MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (q x))) =
      frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y := by
    funext x
    simp only [q, frameSub, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.map_apply, map_inv₀, Finset.sum_mul, mul_assoc]
  have hterm : ∀ k : ℤ, MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (GlobalTheory.ArcQ.lcoeffPoly P₂ k)) * t ^ k =
      (Dv.ιT γ ^ n)⁻¹ * (MvPolynomial.eval (frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y)
        (MvPolynomial.map Z.ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k) := fun k => by
    simp only [P₂]
    rw [lcoeffPoly_const_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C, hco, eval_subst, hq,
      Dv.ιT_io, map_inv₀, map_pow, mul_assoc]
  have hγK : Dv.ιT γ ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 hγ)
  rw [← hP, arcNum_of_poly]
  simp only [hterm] at hT hS
  refine ⟨?_, ?_⟩
  · have := hT.const_mul ‖Dv.ιT γ ^ n‖
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    rw [← norm_mul, mul_inv_cancel_left₀ hγK]
  · rw [tsum_mul_left] at hS
    rw [← hS]
    exact hbd

theorem frame_of_cut : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Fs : Set (Rul Xo c)), (∀ F ∈ Fs, F ∈ sec Xo c a n) → (∀ (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr) (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr), γ ≠ 0 → (∀ τ k, lam τ k ≠ 0) → BcRigidAt Dv γ lam Bm → RecordAt Dv Fs → FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) n d Fs) ∧ ∀ (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ), FinLocalCutAt d w vth vη m Fs → FinLocalAt d w n vth vη m Fs := by
  intro hL hL2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d w a n Fs hFs
  refine ⟨fun Z Dv γ lam Bm hγ _ hBc hRec => frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec, ?_⟩
  rintro vth vη m ⟨Z, Dv, γ, lam, A, Bm, ⟨hγ, hγn⟩, hlam, ⟨hAB, hA⟩, hBc, hRec⟩
  refine ⟨Z, Dv.ιT γ, fun τ k => Dv.ιT (lam τ k), fun τ => (A τ).map Dv.ιT, fun τ => (Bm τ).map Dv.ιT,
    ⟨(map_ne_zero _).2 hγ, hγn⟩, fun τ k => ⟨(map_ne_zero _).2 (hlam τ k).1, (hlam τ k).2⟩,
    ⟨fun τ => ?_, fun τ k l => hA τ k l⟩, frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec⟩
  beta_reduce
  rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.ArcQ.FrameCut
end
end

section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.FrAgree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR hiding gw
open Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

section Local

variable {X Y Z : Scheme.{0}}

theorem exists_local (Z : Scheme.{0}) (z : Z) : ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (i : Sp A ⟶ Z),
    i (cpt A) = z ∧ Function.Injective (i.stalkMap (cpt A)).hom := by
  refine ⟨Z.presheaf.stalk z, inferInstance, inferInstance, Z.fromSpecStalk z, Scheme.fromSpecStalk_closedPoint, ?_⟩
  have e := Scheme.stalkClosedPointTo_fromSpecStalk (X := Z) z
  have i : Function.Injective (Scheme.stalkClosedPointTo (Z.fromSpecStalk z)).hom := by
    rw [e]
    exact (Iso.commRingCatIsoToRingEquiv _).injective
  exact Function.Injective.of_comp (f := (stalkClosedPointIso (Z.presheaf.stalk z)).hom.hom) i

def stU (r : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (r z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (r.stalkMap z).hom.toMonoidHom

theorem stU_injective (r : Z ⟶ Y) (z : Z) (h : Function.Injective (r.stalkMap z).hom) :
    Function.Injective (stU r z) := Units.map_injective h

theorem gm_comp (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)ˣ) :
    stU r z (gm g (r z) U a) = gm (r ≫ g) z U a := by
  symm
  by_cases h : g (r z) ∈ U
  · refine Units.ext ((gs_unit (r ≫ g) z U h a).symm.trans (Eq.trans ?_
      (congrArg (r.stalkMap z).hom (gs_unit g (r z) U h a))))
    rw [← gs_pull r g z U h, gs_stalkMap r z _ h, gs_pull (𝟙 Y) g (r z) U h, Category.id_comp]
  · have h' : (r ≫ g) z ∉ U := h
    rw [gm, dif_neg h', gm, dif_neg h]
    exact (map_one _).symm

end Local

section Gen

variable {B B' B₀ Y Y' : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type} [Fintype K] {ε : K → ℤ}
  {Φ : B ⟶ B'} {φ' : B' ⟶ B₀} {w' : LB.Iso M' (M₀.pull φ')} {w₁ : LB.Iso M (M'.pull Φ)}
  {w : LB.Iso M (M₀.pull (Φ ≫ φ'))}

theorem pmaps_of_genRelR (T : Tri w' w₁ w) (hw : PGen w) (hM : M.IsLB) (hM₀ : M₀.IsLB) {ψ : K → (Y ⟶ B)}
    {ψ' : K → (Y' ⟶ B')} (h : Y ⟶ Y') (hc : ∀ k, ψ k ≫ Φ = h ≫ ψ' k) (t : LB.Gen (LB.LinComb M ψ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb M' ψ' ε))
    (H : ∀ (A : Type) [CommRing A] [IsLocalRing A] (v : Sp A ⟶ Y) (pt₀ : K → (Sp A ⟶ B₀))
      (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)), t₀.IsGen → GenRelR w (LB.pullGen _ _ _ t v) t₀ →
      GenRelR w' (LB.pullGen _ _ _ t' (v ≫ h)) t₀) : PMaps w₁ ψ ψ' ε t t' h := by
  intro Z r z p q hp hq
  obtain ⟨A, _, _, i, rfl, inj⟩ := exists_local Z z
  apply stU_injective i _ inj
  refine (gm_comp i _ _ _ _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans
    (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) (gm_comp i _ _ _ _))))
    (gm_comp i _ _ _ _))).symm)
  obtain ⟨t₀, g₀, hv⟩ := exists_up hw hM₀ hM (LB.pullGen _ _ _ t (i ≫ r)) (pullGen_isGen _ _ _ _ ht _)
  have G := (genRelR_iff _ _ _).1 (H A (i ≫ r) _ t₀ g₀ ((genRelR_iff _ _ _).2 ⟨fun _ => rfl, fun j j₀ h₀ h₁ => by
    have := hv _ (𝟙 _) (cpt A) j₀ j (Set.mem_iInter.2 h₀) (Set.mem_iInter.2 h₁)
    simp only [pw, Category.id_comp] at this
    exact congrArg Units.val this.symm⟩))
  choose j₀ hj₀ using fun k => exists_chart hM₀ (φ' (Φ (ψ k (r (i (cpt A))))))
  have pe := fun k => pt_eq hc k (r (i (cpt A)))
  have a := Units.ext (G.2 p j₀ (fun k => (congrArg (fun y => φ' y ∈ M₀.U (j₀ k)) (pe k)).mpr (hj₀ k))
    (fun k => (congrArg (fun y => y ∈ M'.U (p k)) (pe k)).mpr (hp k)))
  have b := hv _ (𝟙 _) (cpt A) j₀ q (Set.mem_iInter.2 hj₀) (Set.mem_iInter.2 hq)
  have c := T.prod (ε := ε) hc _ (i ≫ r) (cpt A) j₀ p q hj₀ hp hq
  rw [b, gm_pullGen', gm_pullGen'] at a
  simp only [pw, Category.id_comp] at a
  rw [c, _root_.mul_assoc] at a
  have := mul_left_cancel a
  simpa only [gw, Category.assoc] using this

end Gen

section Fam

variable {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀]

theorem famφB_push {D : DegPre R₀} {D' : DegPre R} {f : Sp R ⟶ Sp R₀} {Φ : D'.P.A.left ⟶ D.P.A.left}
    (gp : IsGrpPullback D'.P.A D.P.A f Φ) {x : D'.X} {x₀ : D.X} (hc : (D'.c x).left ≫ Φ = f ≫ (D.c x₀).left)
    (κ : Fin 4) : D'.famφB x κ ≫ Φ = Φ ≫ D.famφB x₀ κ := by
  let P := pushHom gp D'.P.A
  have h1 : (P (𝟙 _)).left = Φ := Category.id_comp _
  have h2 : P (cP D' _ x) = cP D _ x₀ := Over.OverMorphism.ext (by
    show (D'.P.A.hom ≫ (D'.c x).left) ≫ Φ = (D'.P.A.hom ≫ f) ≫ (D.c x₀).left
    rw [Category.assoc, Category.assoc]
    exact congrArg _ hc)
  have key : ∀ (a : D'.P.A ⟶ D'.P.A) (b : D.P.A ⟶ D.P.A), P a = P (𝟙 _) ≫ b → a.left ≫ Φ = Φ ≫ b.left :=
    fun a b e => (congrArg (fun q => q.left) e).trans (congrArg (· ≫ b.left) h1)
  fin_cases κ
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · refine key (𝟙 _ * cP D' _ x) (𝟙 _ * cP D _ x₀) ?_
    rw [map_mul, MonObj.comp_mul, Category.comp_id, comp_cP, h2]
  · refine key (cP D' _ x) (cP D _ x₀) ?_
    rw [comp_cP, h2]
  · refine key 1 1 ?_
    rw [map_one, MonObj.comp_one]

theorem famφB_hom (D : DegPre R) (x : D.X) (κ : Fin 4) : D.famφB x κ ≫ D.P.A.hom = D.P.A.hom := by
  fin_cases κ
  exacts [Category.id_comp _, Over.w (𝟙 _ * cP D _ x), Over.w (cP D _ x), Over.w (1 : D.P.A ⟶ D.P.A)]

theorem Oφ_eq (D : DegPre R) {T : Over (Sp R)} (p : T ⟶ D.P.A) (x : D.X) (κ : Fin 4) :
    D.Oφ p x κ = p.left ≫ D.famφB x (![1, 2, 0, 3] κ) := by
  fin_cases κ
  · exact congrArg (fun z => z.left) ((MonObj.comp_mul p (𝟙 _) (cP D _ x)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ x))).symm
  · exact congrArg (fun z => z.left) (comp_cP D p x).symm
  · exact (Category.comp_id _).symm
  · exact congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) p).symm

end Fam

section Zero

variable {R : Type} [CommRing R] [IsDomain R] {B₀ : Scheme.{0}} {M₀ : LB B₀}

def ZeroTerm (D : DegPre R) {φ : D.P.A.left ⟶ B₀} (w : LB.Iso D.P.L (M₀.pull φ)) (th : M₀.Sec) (α : D.X)
    (s : D.SecB 1 α) : Prop :=
  ∀ (j : Fin 4 → D.P.L.ι) (j₀ : M₀.ι) (V : D.P.A.left.Opens) (h₁ : V ≤ LB.wchart D.P.L (D.famφB α) j)
    (h₂ : V ≤ (LB.div (M₀.pull φ) D.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ φ ⁻¹ᵁ M₀.U j₀),
    LB.Coh D.P.L (D.famφB α) j →
    (φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (w.s (fun _ => j₀, j 1)).val * resG _ h₁ (s.f j)

theorem zeroTerm_iff (D : DegPre R) {φ : D.P.A.left ⟶ B₀} (w : LB.Iso D.P.L (M₀.pull φ)) (th : M₀.Sec) (α : D.X)
    (s : D.SecB 1 α) : ZeroTerm D w th α s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (j : Fin 4 → D.P.L.ι)
      (j₀ : M₀.ι), LB.Coh D.P.L (D.famφB α) j → r z ∈ LB.wchart D.P.L (D.famφB α) j → φ (r z) ∈ M₀.U j₀ →
      r z ∈ D.P.L.U (j 1) → gs (r ≫ φ) z _ (th.f j₀) =
        (gw w r z j₀ (j 1)).val * gs r z (LB.wchart D.P.L (D.famφB α) j) (s.f j) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (j : Fin 4 → D.P.L.ι) (j₀ : M₀.ι)
      (V : D.P.A.left.Opens) (h₁ : V ≤ LB.wchart D.P.L (D.famφB α) j)
      (h₂ : V ≤ (LB.div (M₀.pull φ) D.P.L).U (fun _ => j₀, j 1)), r z ∈ V →
      gs r z V (resG _ h₂ (w.s (fun _ => j₀, j 1)).val * resG _ h₁ (s.f j)) =
        (gw w r z j₀ (j 1)).val * gs r z (LB.wchart D.P.L (D.famφB α) j) (s.f j) :=
    fun Z r z j j₀ V h₁ h₂ hz => (gs_mul r z V hz _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z h₂ hz _).trans (gs_unit r z _ (h₂ hz) _)) (gs_res r z h₁ hz _))
  constructor
  · intro H Z r z j j₀ hc h₁ h₃ h₂
    have hz : r z ∈ LB.wchart D.P.L (D.famφB α) j ⊓ (LB.div (M₀.pull φ) D.P.L).U (fun _ => j₀, j 1) ⊓
        φ ⁻¹ᵁ M₀.U j₀ := ⟨⟨h₁, mem_pull.2 h₃, h₂⟩, h₃⟩
    exact (gs_appLE φ _ _ inf_le_right r z hz _).symm.trans ((congrArg (gs r z _) (H j j₀ _
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right hc)).trans (key Z r z j j₀ _ _ _ hz))
  · intro H j j₀ V h₁ h₂ h₃ hc
    exact fn_ext fun y hy => (gs_appLE φ _ _ h₃ (𝟙 _) y hy _).trans
      ((H _ (𝟙 _) y j j₀ hc (h₁ hy) (h₃ hy) (h₂ hy).2).trans (key _ (𝟙 _) y j j₀ V h₁ h₂ hy).symm)

theorem famφB_one (D : DegPre R) {α : D.X} (h : α = 0) : D.famφB α 1 = 𝟙 _ := by
  subst h
  exact congrArg (fun z : D.P.A ⟶ D.P.A => z.left) (show 𝟙 _ * cP D _ 0 = 𝟙 _ by rw [cPoint_zero, _root_.mul_one])

theorem famφB_two (D : DegPre R) {α : D.X} (h : α = 0) : D.famφB α 2 = D.famφB α 3 := by
  subst h
  exact congrArg (fun z : D.P.A ⟶ D.P.A => z.left) (cPoint_zero _)

theorem zeroTerm_move {D D' : DegPre R} {Φ : D.P.A.left ⟶ D'.P.A.left} {φ' : D'.P.A.left ⟶ B₀}
    {w' : LB.Iso D'.P.L (M₀.pull φ')} {w₁ : LB.Iso D.P.L (D'.P.L.pull Φ)} {w : LB.Iso D.P.L (M₀.pull (Φ ≫ φ'))}
    (T : Tri w' w₁ w) (th : M₀.Sec) {α' : D'.X} (h0 : α' = 0) (hφ : ∀ κ, D.famφB 0 κ ≫ Φ = Φ ≫ D'.famφB α' κ)
    (s : D.SecB 1 0) (s' : D'.SecB 1 α')
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (p : Fin 4 → D'.P.L.ι) (q : Fin 4 → D.P.L.ι),
      (∀ κ, Φ (D.famφB 0 κ (r z)) ∈ D'.P.L.U (p κ)) → (∀ κ, D.famφB 0 κ (r z) ∈ D.P.L.U (q κ)) →
      gs (r ≫ Φ) z (LB.wchart D'.P.L (D'.famφB α') p) (s'.f p) =
        (∏ κ, gw w₁ (r ≫ D.famφB 0 κ) z (p κ) (q κ) ^ DegPre.famε 1 κ).val *
          gs r z (LB.wchart D.P.L (D.famφB 0) q) (s.f q))
    (H : ZeroTerm D' w' th α' s') : ZeroTerm D w th 0 s := by
  refine (zeroTerm_iff D w th 0 s).2 fun Z r z j j₀ hc h₁ h₃ h₂ => ?_
  choose J hJ using fun ψ : D'.P.A.left ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ (Φ (r z)))
  have m₁ : Φ (r z) ∈ D'.P.L.U (J (D'.famφB α' 1)) := by
    rw [famφB_one D' h0]; exact hJ (𝟙 _)
  have a := (zeroTerm_iff D' w' th α' s').1 H Z (r ≫ Φ) z (fun κ => J (D'.famφB α' κ)) j₀
    (fun a b e => congrArg J e) (Set.mem_iInter.2 fun κ => hJ _) h₃ m₁
  have b := hs Z r z (fun κ => J (D'.famφB α' κ)) j (fun κ =>
    (congrArg (fun q => q (r z) ∈ D'.P.L.U (J (D'.famφB α' κ))) (hφ κ)).mpr (hJ _)) (Set.mem_iInter.1 h₁)
  have c : ∏ κ, gw w₁ (r ≫ D.famφB 0 κ) z (J (D'.famφB α' κ)) (j κ) ^ DegPre.famε 1 κ =
      gw w₁ r z (J (D'.famφB α' 1)) (j 1) := by
    rw [Fin.prod_univ_four, famφB_one D rfl, Category.comp_id, hc 2 3 (famφB_two D rfl), famφB_two D rfl,
      famφB_two D' h0]
    show _ ^ (((1 : ℕ) : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
    simp
  rw [← Category.assoc, a, b, c, T Z r z j₀ _ _ h₃ m₁ h₂, Units.val_mul, _root_.mul_assoc]

end Zero

section Move

variable {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Sp (FractionRing R))} {G G' : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

set_option maxHeartbeats 1600000 in

theorem theta_move (U : UnifPre I D A G) (U' : UnifPre I D' A' G') {D₀ : DegPre R₀} {f : Sp R ⟶ Sp R₀}
    {φ : D.toPre.P.A.left ⟶ D₀.P.A.left} {φ' : D'.toPre.P.A.left ⟶ D₀.P.A.left}
    (gp : IsGrpPullback D.toPre.P.A D₀.P.A f φ) (gp' : IsGrpPullback D'.toPre.P.A D₀.P.A f φ')
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (w' : LB.Iso D'.toPre.P.L (D₀.P.L.pull φ')) (hw : w.IsGen) (hw' : w'.IsGen)
    (e : D₀.X ≃+ D.toPre.X) (e' : D₀.X ≃+ D'.toPre.X)
    (hc : ∀ y, (D.toPre.c (e y)).left ≫ φ = f ≫ (D₀.c y).left)
    (hc' : ∀ y, (D'.toPre.c (e' y)).left ≫ φ' = f ≫ (D₀.c y).left) (ψ : G ⟶ G')
    (wL : LB.Iso U.LG.L (U'.LG.L.pull ψ.left)) (hwL : wL.IsGen)
    (hlev : ∀ (n : ℕ) (ψn : (thickObj R I n G).left ⟶ (thickObj R I n G').left),
      ψn = ((Over.pullback (thick R I n)).map ψ).left →
      ((U.gt n).pG.left ≫ φ = ψn ≫ (U'.gt n).pG.left ≫ φ') ∧
      ∀ (A : Type) [CommRing A] [IsLocalRing A] (v : Sp A ⟶ (thickObj R I n G).left),
        (∀ (x : D₀.X) (pt₀ : Fin 4 → (Sp A ⟶ D₀.P.A.left)) (t₀ : LB.Gen (LB.LinComb D₀.P.L pt₀ Oinvε)),
          t₀.IsGen → GenRelR w (LB.pullGen _ _ _ ((U.gt n).t (e x)) v) t₀ →
          GenRelR w' (LB.pullGen _ _ _ ((U'.gt n).t (e' x)) (v ≫ ψn)) t₀) ∧
        ∀ (j₀ : D₀.P.L.ι) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
          ⊤ ≤ (v ≫ (U.gt n).pG.left) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀, jM) →
          ⊤ ≤ (v ≫ ψn ≫ (U'.gt n).pG.left) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ') D'.toPre.P.L).U (fun _ => j₀, jM') →
          ⊤ ≤ (v ≫ (fstG I n G).left) ⁻¹ᵁ (LB.div (U'.LG.L.pull ψ.left) U.LG.L).U (fun _ => jL', jL) →
          valR (v ≫ (U.gt n).pG.left) _ (w.s (fun _ => j₀, jM)).val *
              valR v _ ((U.w n).s (fun _ => jM, fun _ => jL)).val =
            valR (v ≫ ψn ≫ (U'.gt n).pG.left) _ (w'.s (fun _ => j₀, jM')).val *
              valR (v ≫ ψn) _ ((U'.w n).s (fun _ => jM', fun _ => jL')).val *
              valR (v ≫ (fstG I n G).left) _ (wL.s (fun _ => jL', jL)).val)
    (th : D₀.P.L.Sec) (σ' : H0 U'.LG.L 1) (fam' : ∀ x, D'.toPre.SecB 1 x) (θ' : LB.Sec U'.LG.L)
    (hE : ∀ n, U'.ExpandsAt n 1 σ' fam') (h0 : ZeroTerm D'.toPre w' th 0 (fam' 0)) (hσ : SectionOfLineBundleOne σ' θ') :
    ∃ (σ : H0 U.LG.L 1) (fam : ∀ x, D.toPre.SecB 1 x) (θ : LB.Sec U.LG.L), (∀ n, U.ExpandsAt n 1 σ fam) ∧
      ZeroTerm D.toPre w th 0 (fam 0) ∧ SectionOfLineBundleOne σ θ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) j k, ψ.left (r z) ∈ U'.LG.L.U j → r z ∈ U.LG.L.U k →
        gs (r ≫ ψ.left) z _ (θ'.f j) = (gw wL r z j k).val * gs r z _ (θ.f k) := by
  have hM := D.toPre.P.isLB
  have hM' := D'.toPre.P.isLB
  have hM₀ := D₀.P.isLB
  obtain ⟨Φ, rfl, hΦ⟩ : ∃ Φ : D.toPre.P.A.left ⟶ D'.toPre.P.A.left, Φ ≫ φ' = φ ∧
      Φ ≫ D'.toPre.P.A.hom = D.toPre.P.A.hom := ⟨gp'.1.lift _ _ gp.1.w, gp'.1.lift_fst _ _ _, gp'.1.lift_snd _ _ _⟩
  have pw := (isGen_iff w).1 hw
  have pw' := (isGen_iff w').1 hw'
  obtain ⟨w₁, T⟩ := exists_cancel hM₀ w' w pw' pw hM' hM
  have hw₁ := (isGen_iff w₁).2 (T.pgen_cancel hM₀ pw' pw)
  let xe : D.toPre.X ≃+ D'.toPre.X := e.symm.trans e'
  have hφ : ∀ x κ, D.toPre.famφB x κ ≫ Φ = Φ ≫ D'.toPre.famφB (xe x) κ := fun x κ => by
    obtain ⟨x₀, rfl⟩ := e.surjective x
    have ex : xe (e x₀) = e' x₀ := congrArg e' (e.symm_apply_apply x₀)
    rw [ex]
    apply gp'.1.hom_ext
    · rw [Category.assoc, Category.assoc, famφB_push gp (hc x₀), famφB_push gp' (hc' x₀), Category.assoc]
    · rw [Category.assoc, Category.assoc, famφB_hom, hΦ, famφB_hom]
  obtain ⟨σ, hσ₁, -⟩ := SecPull.existsUnique_secPull _ _ _ _ _ _ _ U'.LG.isLB U.LG.isLB wL hwL (Fin 1)
    (fun _ => 𝟙 G.left) (fun _ => 𝟙 G'.left) (fun _ => ((1 : ℕ) : ℤ)) ψ.left
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) σ'
  choose fam hfam using fun x => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ hM' hM w₁ hw₁ (Fin 4)
    (D.toPre.famφB x) (D'.toPre.famφB (xe x)) (DegPre.famε 1) Φ (hφ x) (fam' (xe x))).exists
  obtain ⟨θ, hθ⟩ := sec_pull_down ((isGen_iff wL).1 hwL) U'.LG.isLB U.LG.isLB θ'
  refine ⟨σ, fam, θ, fun n => ?_, ?_, fun j hj => fn_ext fun y hy => ?_, hθ⟩
  · obtain ⟨h, hh⟩ : ∃ h : (thickObj R I n G).left ⟶ (thickObj R I n G').left,
        h = ((Over.pullback (thick R I n)).map ψ).left := ⟨_, rfl⟩
    obtain ⟨l₁, l₂⟩ := hlev n h hh
    have hG : h ≫ (fstG I n G').left = (fstG I n G).left ≫ ψ.left := by
      rw [hh]; exact pullback.lift_fst _ _ _
    have hq : (U.gt n).pG.left ≫ Φ = h ≫ (U'.gt n).pG.left := by
      apply gp'.1.hom_ext
      · rw [Category.assoc, Category.assoc]; exact l₁
      · rw [Category.assoc, Category.assoc, hΦ, Over.w (U.gt n).pG, Over.w (U'.gt n).pG, ← Over.w (fstG I n G'),
          ← Over.w (fstG I n G), ← Over.w ψ, ← Category.assoc, ← hG, Category.assoc]
    have hO : ∀ x κ, D.toPre.Oφ (U.gt n).pG x κ ≫ Φ = h ≫ D'.toPre.Oφ (U'.gt n).pG (xe x) κ := fun x κ => by
      rw [Oφ_eq, Oφ_eq, Category.assoc, hφ, ← Category.assoc, hq, Category.assoc]
    refine expandsAt_transport R R I I D' D A' A G' G U' U Φ w₁ xe ψ.left wL hw₁ hwL hφ n n 1 h
      ⟨hG, ⟨hq, fun x => ⟨hO x, ?_⟩⟩, ?_⟩ σ' σ fam' fam hσ₁ hfam (hE n)
    · refine pmaps_of_genRelR T pw hM hM₀ h (hO x) _ ((U.gt n).t_gen x) _ fun A _ _ v pt₀ t₀ g₀ => ?_
      obtain ⟨x₀, rfl⟩ := e.surjective x
      have ex : xe (e x₀) = e' x₀ := congrArg e' (e.symm_apply_apply x₀)
      rw [ex]
      exact (l₂ A v).1 x₀ pt₀ t₀ g₀
    · intro Z r z jM' jM jL' jL m₁ m₂ m₃ m₄
      obtain ⟨A, _, _, i, rfl, inj⟩ := exists_local Z z
      apply stU_injective i _ inj
      refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_comp i _ _ _ _) (gm_comp i _ _ _ _))).trans (Eq.trans ?_
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_comp i _ _ _ _) (gm_comp i _ _ _ _))).symm)
      obtain ⟨j₀, m₀⟩ := exists_chart hM₀ (φ' (Φ ((U.gt n).pG.left (r (i (cpt A))))))
      have eq : (U'.gt n).pG.left (h (r (i (cpt A)))) = Φ ((U.gt n).pG.left (r (i (cpt A)))) :=
        congrArg (fun q => q (r (i (cpt A)))) hq.symm
      have eG : (fstG I n G').left (h (r (i (cpt A)))) = ψ.left ((fstG I n G).left (r (i (cpt A)))) :=
        congrArg (fun q => q (r (i (cpt A)))) hG
      have m₁' := eq ▸ m₁
      have m₀' := eq ▸ m₀
      have m₃' := eG ▸ m₃
      have H1 := (top_le_iff_cpt ((i ≫ r) ≫ (U.gt n).pG.left)
        ((LB.div (D₀.P.L.pull (Φ ≫ φ')) D.toPre.P.L).U (fun _ => j₀, jM))).2 ⟨mem_pull₂.2 m₀, m₂⟩
      have H2 := (top_le_iff_cpt ((i ≫ r) ≫ h ≫ (U'.gt n).pG.left)
        ((LB.div (D₀.P.L.pull φ') D'.toPre.P.L).U (fun _ => j₀, jM'))).2 ⟨mem_pull.2 m₀', m₁'⟩
      have H3 := (top_le_iff_cpt ((i ≫ r) ≫ (fstG I n G).left)
        ((LB.div (U'.LG.L.pull ψ.left) U.LG.L).U (fun _ => jL', jL))).2 ⟨mem_pull.2 m₃, m₄⟩
      have H4 := (top_le_iff_cpt (i ≫ r) ((LB.div (D.toPre.P.L.pull (U.gt n).pG.left)
        (U.LG.L.pull (fstG I n G).left)).U (fun _ => jM, fun _ => jL))).2 ⟨mem_pull.2 m₂, mem_pull.2 m₄⟩
      have H5 := (top_le_iff_cpt ((i ≫ r) ≫ h) ((LB.div (D'.toPre.P.L.pull (U'.gt n).pG.left)
        (U'.LG.L.pull (fstG I n G').left)).U (fun _ => jM', fun _ => jL'))).2 ⟨mem_pull.2 m₁', mem_pull.2 m₃'⟩
      have a := congrArg (toStkA (cpt A)) ((l₂ A (i ≫ r)).2 j₀ jM jM' jL jL' H1 H2 H3)
      rw [map_mul, map_mul, map_mul, toStkA_valR _ _ _ H1, toStkA_valR _ _ _ H2, toStkA_valR _ _ _ H3,
        toStkA_valR _ _ _ H4, toStkA_valR _ _ _ H5, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul] at a
      have b := T _ ((i ≫ r) ≫ (U.gt n).pG.left) (cpt A) j₀ jM' jM m₀ m₁ m₂
      rw [Category.assoc (i ≫ r), hq] at b
      have c := (congrArg (· * _) b).symm.trans (Units.ext a)
      rw [_root_.mul_assoc, _root_.mul_assoc] at c
      have d := mul_left_cancel c
      simp only [Category.assoc] at d
      exact d
  · exact zeroTerm_move T th (map_zero xe) (hφ 0) _ _ (hfam 0)
      ((show ∀ α, α = 0 → ZeroTerm D'.toPre w' th α (fam' α) by rintro _ rfl; exact h0) _ (map_zero xe))
  · obtain ⟨p, hp⟩ := exists_chart U'.LG.isLB (ψ.left y)
    have le : LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => p) ≤ U'.LG.L.U p := LB.wchart_le _ _ _ 0
    have a := hσ₁ _ (𝟙 _) y (fun _ => p) j (fun _ => hp) (Set.mem_iInter.1 hy)
    rw [hσ _ le, gs_res (𝟙 _ ≫ ψ.left) y le (Set.mem_iInter.2 fun _ => hp), hθ _ (𝟙 _) y p (j 0) hp (hj hy), Fin.prod_univ_one,
      Category.comp_id, zpow_natCast, pow_one] at a
    exact ((Units.mul_right_inj _).1 a).symm.trans (gs_res (𝟙 _) y hj hy _).symm

end Move

theorem cast_rig {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L₁ L₂ : RigLB G} (h : L₁ = L₂) {L₁' L₂' : RigLB G'} (h' : L₁' = L₂') {F : G.left ⟶ G'.left}
    (he : eSec G ≫ F = 𝟙 _ ≫ eSec G') (w : LB.Iso L₁.L (L₁'.L.pull F)) (g : w.IsGen)
    (m : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig
      (rigPullOf F (𝟙 _) he L₁'.L L₁'.rig)) (θ₁ : LB.Sec L₁.L) {θ₁' : LB.Sec L₁'.L} {θ₂' : LB.Sec L₂'.L}
    (hθ : HEq θ₂' θ₁')
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) j k, F (r z) ∈ L₁'.L.U j → r z ∈ L₁.L.U k →
      gs (r ≫ F) z _ (θ₁'.f j) = (gw w r z j k).val * gs r z _ (θ₁.f k)) :
    ∃ (w₂ : LB.Iso L₂.L (L₂'.L.pull F)) (θ₂ : LB.Sec L₂.L), w₂.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₂.rig
        (rigPullOf F (𝟙 _) he L₂'.L L₂'.rig) ∧ HEq θ₂ θ₁ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) j k, F (r z) ∈ L₂'.L.U j → r z ∈ L₂.L.U k →
        gs (r ≫ F) z _ (θ₂'.f j) = (gw w₂ r z j k).val * gs r z _ (θ₂.f k) := by
  subst h h'
  cases hθ
  exact ⟨w, θ₁, g, m, HEq.rfl, H⟩

theorem isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
    IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have a := congrArg (gs r z _) (h (fun _ => j) k)
    exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
  · intro h (i : PUnit → L.ι) k
    exact fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
        (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

theorem isLocalRing_dual (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem isLocalRing_thick (k : Type) [Field k] (n : ℕ) :
    IsLocalRing (DualNumber (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (n + 1))) := by
  have : Nontrivial (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 fun e => by
      rw [Ideal.pow_eq_top_iff, Ideal.span_singleton_eq_top] at e
      exact e.elim PowerSeries.X_prime.not_unit (Nat.succ_ne_zero n)
  have : IsLocalRing (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (n + 1)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  exact isLocalRing_dual _

theorem exists_factor {k S : Type} [Field k] [CommRing S] (io : PowerSeries k →+* S) (h : IsUnit (io PowerSeries.X)) :
    ∃ io' : FractionRing (PowerSeries k) →+* S, spMap io = spMap io' ≫ jK (PowerSeries k) := by
  have hu : ∀ y : nonZeroDivisors (PowerSeries k), IsUnit (io y) := fun y => by
    have hy : (y : PowerSeries k) ≠ 0 := nonZeroDivisors.ne_zero y.2
    rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := (y : PowerSeries k)), map_mul, map_pow]
    exact (h.pow _).mul ((PowerSeries.isUnit_divided_by_X_pow_order hy).map io)
  refine ⟨IsLocalization.lift hu, ?_⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.lift_comp]

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn Dw l (RingHom.id c.F) k bF}
  {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
  {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X} {W : Wit Y (a.restrict β) χ}
  {W' : Wit Y' (a.restrict β') χ'} {ψ : W.t.G ≅ W'.t.G}

theorem lieImg_move (hA : W.Agree W' ψ) (ν : GtPt a.D₀ (epsR k)) (v : epsR (PowerSeries k) ⟶ W.t.G)
    (h : LieImg W ν v) : LieImg W' ν (v ≫ ψ.hom) := by
  obtain ⟨-, -, -, he, wL, -, -, hlev⟩ := hA
  intro n ρ κ vn h₁ h₂ h₃ h₄ hb hf x
  have := isLocalRing_thick k n
  let ψn := (Over.pullback (thick (PowerSeries k) (Ideal.span {PowerSeries.X}) n)).mapIso ψ
  have e₁ : (vn ≫ ψn.inv.left) ≫ ψn.hom.left = vn := by
    rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id]
  have e₂ : ψn.inv.left ≫ (fstG (Ideal.span {PowerSeries.X}) n W.t.G).left =
      (fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left ≫ ψ.inv.left := pullback.lift_fst _ _ _
  have a := h n ρ κ (vn ≫ ψn.inv.left) h₁ h₂ h₃ h₄ (by rw [Category.assoc, Over.w ψn.inv]; exact hb) (by
    rw [Category.assoc, e₂, ← Category.assoc, hf, Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]) x
  have b := ((hlev n ψn.hom.left rfl).2 _ (vn ≫ ψn.inv.left)).1 x _ (LB.pullGen _ _ _ (ν.s x) (spMap κ))
    (pullGen_isGen _ _ _ _ (ν.isGen x) _) a
  rw [e₁] at b
  exact b

theorem thetaOf_move (hA : W.Agree W' ψ) (th : a.D₀.P.L.Sec) (θ' : LB.Sec W'.t.PP.L) (h : ThetaOf W' th θ') :
    ∃ (he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G) (w : LB.Iso W.t.PP.L (W'.t.PP.L.pull ψ.hom.left))
      (θ : LB.Sec W.t.PP.L), w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec W.t.G) (fun _ => 1)) W.t.PP.rig
        (rigPullOf ψ.hom.left (𝟙 _) he W'.t.PP.L W'.t.PP.rig) ∧ ThetaOf W th θ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ W.t.G.left) (z : Z) j k, ψ.hom.left (r z) ∈ W'.t.PP.L.U j → r z ∈ W.t.PP.L.U k →
        gs (r ≫ ψ.hom.left) z _ (θ'.f j) = (gw w r z j k).val * gs r z _ (θ.f k) := by
  obtain ⟨-, -, -, he, wL, g, m, hlev⟩ := hA
  obtain ⟨σ', fam', θ₁', hE, h0, hσ, hθ⟩ := h
  obtain ⟨σ, fam, θ₁, hE₁, h0₁, hσ₁, H⟩ := theta_move W.P.U.toUnifPre W'.P.U.toUnifPre W.spec.1 W'.spec.1 W.w W'.w
    W.spec.2.1 W'.spec.2.1 W.e.toAddEquiv W'.e.toAddEquiv W.spec.2.2.2.2.1 W'.spec.2.2.2.2.1 ψ.hom wL g hlev th σ' fam'
    θ₁' hE h0 hσ
  obtain ⟨w, θ, g₂, m₂, hθ₂, H₂⟩ := cast_rig W.P.bundle W'.P.bundle he wL g m θ₁ hθ H
  exact ⟨he, w, θ, g₂, m₂, ⟨σ, fam, θ₁, hE₁, h0₁, hσ₁, hθ₂⟩, H₂⟩

theorem isArcFr_move (hA : W.Agree W' ψ) (y₀ : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c)
    (hy : y₀ ≫ Y.j = jK (PowerSeries k) ≫ χ) (hy' : y₀ ≫ Y'.j = jK (PowerSeries k) ≫ χ') (hj : Mono Y.j)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec)
    (hu : ∀ θ₁ θ₂, ThetaOf W th θ₁ → ThetaOf W th θ₂ → θ₁ = θ₂) (θ' : LB.Sec W'.t.PP.L) (hθ' : ThetaOf W' th θ')
    {S : Type} [CommRing S] [Algebra c.F S] (io : PowerSeries k →+* S) (y : FrPt Xo c S)
    (hio : IsUnit (io PowerSeries.X)) (h : IsArcFr W e th io y) : IsArcFr W' e th io y := by
  obtain ⟨z, t', m1, m2, φ, zj, zx, φb, φ1, φ2, hv, θ, w1, w2, σ, s1, θ2, hth, r1, r2, i1, i2, p2, hg⟩ := h
  obtain ⟨he, w, θ₁, g, m, hθ₁, Hθ⟩ := thetaOf_move hA th θ' hθ'
  obtain rfl : θ = θ₁ := hu _ _ hth hθ₁
  have hmon := hA.1
  obtain ⟨io', hio'⟩ := exists_factor io hio
  have zj' : z ≫ Y'.j = spMap io ≫ χ' := by
    have : z = spMap io' ≫ y₀ := by
      rw [← cancel_mono Y.j, zj, hio', Category.assoc, Category.assoc, hy]
    rw [this, hio', Category.assoc, Category.assoc, hy']
  obtain ⟨n₁, e₁⟩ : ∃ n₁ : SABMap t' Y'.oF.t z, m1.φ = n₁.φ ≫ Y'.m0.toSABMap.φ := by
    refine (show ∀ (x : Sp S ⟶ Xo.X) (m : SABMap t' Xo.univ.t x), z ≫ pullback.fst _ _ = x →
      ∃ n₁ : SABMap t' Y'.oF.t z, m.φ = n₁.φ ≫ Y'.m0.toSABMap.φ from ?_) _ m1 zx
    rintro _ m rfl
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y'.m0.toSABMap m
  obtain ⟨n₂, e₂⟩ : ∃ n₂ : SABMap t' Y'.t (spMap io ≫ χ'), n₂.φ = n₁.φ ≫ Y'.m.φ := by
    rw [← zj']
    exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y'.m n₁
  obtain ⟨m2', e₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ W'.m n₂
  have e₄ : m2'.φ = m2.φ ≫ ψ.hom.left := by
    apply W'.m.cart.1.hom_ext
    · rw [Category.assoc]
      exact e₃.symm.trans (e₂.trans (hA.2.2.1 _ m2.φ φ n₁.φ φ2.symm (φ1.trans e₁)
        (φb.trans n₁.cart.1.w.symm)).symm)
    · rw [Category.assoc, Over.w ψ.hom]
      exact m2'.cart.1.w.trans m2.cart.1.w.symm
  obtain ⟨w2', r2', T⟩ := GlobalTheory.Reg.LiftUnique.cube_rig_comp (CubeMap.ofHom ψ.hom) m2.cm m2'.cm e₄
    (by rw [m2'.base, m2.base]; exact (Category.comp_id _).symm) _ _ _ w w2 ⟨g, m⟩ r2
  refine ⟨z, t', m1, m2', n₁.φ, zj', zx, n₁.cart.1.w, e₁.symm, e₂.symm.trans e₃, fun τ i => ?_,
    θ', w1, w2', σ, s1, thfPull _ m2'.φ θ', hθ', r1, r2', i1, ?_, fun _ _ => rfl, hg⟩
  · obtain ⟨v, u', a₁, a₂, a₃, a₄⟩ := hv τ i
    refine ⟨v ≫ ψ.hom, u', lieImg_move hA _ v a₁, a₂, ?_, a₄⟩
    rw [e₄, ← Category.assoc, a₃, Category.assoc, Over.comp_left]
  · refine (isoMaps_iff w2' σ _).2 fun Z r z j i hj hi =>
      (gs_appLE m2'.φ _ _ _ r z (mem_pull.2 hj) _).trans ?_
    obtain ⟨q, hq⟩ := exists_chart W.t.PP.isLB (m2.φ (r z))
    have le : (W.t.PP.L.pull m2.φ).U (fun _ => q) ≤ m2.φ ⁻¹ᵁ W.t.PP.L.U q := fun _ hx => mem_pull.1 hx
    have b := (isoMaps_iff w2 σ θ2).1 i2 Z r z q i hq hi
    rw [p2 (fun _ => q) le] at b
    have b' := (gs_appLE m2.φ _ _ le r z (mem_pull.2 hq) _).symm.trans b
    have hm : ψ.hom.left ((r ≫ m2.φ) z) ∈ W'.t.PP.L.U j :=
      (congrArg (fun f => f (r z) ∈ W'.t.PP.L.U j) e₄).mp hj
    have eg : r ≫ m2'.φ = (r ≫ m2.φ) ≫ ψ.hom.left := by rw [e₄, Category.assoc]
    refine (congrArg (fun f => gs f z _ (θ'.f j)) eg).trans ?_
    rw [Hθ Z (r ≫ m2.φ) z j q hm hq, b', T Z r z j q i hj hq hi, Units.val_mul, _root_.mul_assoc]
    rfl

end ThetaShiftProofs

end GlobalTheory.ArcQ.FrAgree

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem isArcFr_of_agree : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn Dw l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : Wit Y (a.restrict β) χ) (W' : Wit Y' (a.restrict β') χ') (ψ : W.t.G ≅ W'.t.G), W.Agree W' ψ → ∀ y₀ : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c, y₀ ≫ Y.j = Out.jK (PowerSeries k) ≫ χ → y₀ ≫ Y'.j = Out.jK (PowerSeries k) ≫ χ' → Mono Y.j → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec), ThNZ th → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries k →+* S) (y : FrPt Xo c S), IsUnit (ι PowerSeries.X) → IsArcFr W e th ι y → IsArcFr W' e th ι y := by
  intro hL hL2 E _ _ _ H Dw l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' ψ hA y₀ hy hy' hj e th hth S _ _ ι y hι h
  obtain ⟨θ', hθ', -⟩ := (GlobalTheory.T.existsUnique_thetaOf_alt hL hL2 E H Dw l Xo c O' β' Y' k _ (a.restrict β') χ' W' th hth).1
  exact FrAgree.isArcFr_move hA y₀ hy hy' hj e th
    (fun _ _ => (GlobalTheory.T.existsUnique_thetaOf_alt hL hL2 E H Dw l Xo c O β Y k _ (a.restrict β) χ W th hth).1.unique) θ' hθ' ι y hι h

end GlobalTheory.ArcQ
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem arc_rigidity_two_models_of_mono : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y = y' ∧ (Mono Y.j → ∃ ψ : W.t.G ≅ W'.t.G, W.Agree W' ψ) :=
  rigidArc_of_mono

end GlobalTheory
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ

theorem exists_generic_lift {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {k : Type} [Field k] (bF : c.F →+* k) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) (χ : Sp (PowerSeries k) ⟶ Y.X)
    (hχ : χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β))
    {S : Type} [CommRing S] [Nontrivial S] (ι : PowerSeries k →+* S) (hι : IsUnit (ι PowerSeries.X))
    (z : Sp S ⟶ Xo.XF c) (hz : z ≫ Y.j = spMap ι ≫ χ) :
    ∃ y : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c, y ≫ Y.j = Out.jK (PowerSeries k) ≫ χ ∧
      y ≫ pullback.snd _ _ = Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF := by
  have := Y.jQ_open
  have w : (Out.jK (PowerSeries k) ≫ χ) ≫ Y.s =
      (Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF) ≫ spMap β := by
    rw [Category.assoc, hχ, spMap_comp]; simp only [Category.assoc]
  obtain ⟨q⟩ : Nonempty (Sp S) := (inferInstance : Nonempty (PrimeSpectrum S))
  have hq : PowerSeries.X ∉ (spMap ι q).asIdeal := fun h =>
    q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ι PowerSeries.X ∈ q.asIdeal from h) hι)
  obtain ⟨p₀, hp₀⟩ := mem_range_jK _ hq
  have hr : Set.range (pullback.lift _ _ w) ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = p₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing (PowerSeries k))) _ _
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hp₀,
      ← Scheme.Hom.comp_apply, ← hz, Scheme.Hom.comp_apply]
    exact GlobalTheory.ThetaShiftProofs.j_mem_abLocus Y _
  have hy := IsOpenImmersion.lift_fac Y.jQ _ hr
  refine ⟨IsOpenImmersion.lift Y.jQ _ hr, ?_, ?_⟩
  · unfold Model.j
    rw [← Category.assoc, hy, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, hy, pullback.lift_snd]

theorem isArcFr_eq_of_overBase : Out.Laws → Out.Laws2 → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn Dw l (RingHom.id c.F) k bF) (V V' : ValuationSubring ℂ) (Y : Model Xo c (c.V V).subtype) (Y' : Model Xo c (c.V V').subtype) (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : Wit Y (a.restrict (c.V V).subtype) χ) (W' : Wit Y' (a.restrict (c.V V').subtype) χ'), χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V).subtype) → χ' ≫ Y'.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V').subtype) → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec), ThNZ th → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Nontrivial S] (ι : PowerSeries k →+* S) (y y' : FrPt Xo c S), IsUnit (ι PowerSeries.X) → IsArcFr W e th ι y → IsArcFr W' e th ι y' → y = y' := by
  intro h1 h2 h5 E _ _ _ H Dw l Xo c k _ bF a V V' Y Y' χ χ' W W' hχ hχ' e th hth S _ _ _ ι y y' hι hy hy'
  have hj : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  have hj' : Mono Y'.j := GlobalTheory.ThetaShiftProofs.mono_j Y' (mono_spMap_subtype _)
  obtain ⟨y₀, a₁, a₂⟩ := exists_generic_lift bF Y χ hχ ι hι hy.choose
    hy.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  obtain ⟨y₀', b₁, b₂⟩ := exists_generic_lift bF Y' χ' hχ' ι hι hy'.choose
    hy'.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  obtain ⟨rfl, hψ⟩ := GlobalTheory.arc_rigidity_two_models_of_mono h1 h2 h5 E H Dw l Xo c k bF a _ _ _ _ Y Y' χ χ' W W' y₀ y₀' a₁ b₁ a₂ b₂
  obtain ⟨ψ, hψ⟩ := hψ hj
  have hy₁ := GlobalTheory.ArcQ.isArcFr_of_agree h1 h2 E H Dw l Xo c k bF a _ _ _ _ Y Y' χ χ' W W' ψ hψ y₀ a₁ b₁ hj e th hth S ι y hι hy
  exact (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Y' k _ _ χ' W' e th hth S ι y' hy').1 hj' y hy₁

end GlobalTheory.ArcQ
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_framed_point_eq_of_models_over_base : Out.Laws → Out.Laws2 → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn Dw l (RingHom.id c.F) k bF) (V V' : ValuationSubring ℂ) (Y : Model Xo c (c.V V).subtype) (Y' : Model Xo c (c.V V').subtype) (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : Wit Y (a.restrict (c.V V).subtype) χ) (W' : Wit Y' (a.restrict (c.V V').subtype) χ'), χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V).subtype) → χ' ≫ Y'.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V').subtype) → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec), ThNZ th → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Nontrivial S] (ι : PowerSeries k →+* S) (y y' : FrPt Xo c S), IsUnit (ι PowerSeries.X) → IsArcFr W e th ι y → IsArcFr W' e th ι y' → y = y' := by
  atlas_forward_decl GlobalTheory.ArcQ.isArcFr_eq_of_overBase
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcRigidity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isUnit_prod_det (Dw : Datum H) (L : Type) [Field L] : IsUnit (∏ τ, (letM Dw L τ).det) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcS Dw L) (arcDet Dw L)
  have e : algebraMap _ (ArcS Dw L) (arcDet Dw L) = ∏ τ, (letM Dw L τ).det := by
    exact (map_prod _ _ _).trans (Finset.prod_congr rfl fun τ _ => RingHom.map_det _ _)
  exact e ▸ h

theorem exists_letterSub (Dw : Datum H) {K L : Type} [Field K] [Field L] (f : K →+* L)
    (N : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L) (hN : ∀ τ, IsUnit (N τ).det) :
    ∃ φ : ArcS Dw K →+* ArcS Dw L,
      (∀ g : LaurentSeries K, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) _ (MvPolynomial.C g)) =
        algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) _ (MvPolynomial.C (LetterMap.coeffMap f g))) ∧
      ∀ τ, (letM Dw K τ).map φ = letM Dw L τ * (N τ).map ((arcι Dw L).comp (PowerSeries.C (R := L))) := by
  let g : MvPolynomial (ArcLt Dw) (LaurentSeries K) →+* ArcS Dw L :=
    MvPolynomial.eval₂Hom ((algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) (ArcS Dw L)).comp
      (MvPolynomial.C.comp (LetterMap.coeffMap f)))
      fun x => (letM Dw L x.1 * (N x.1).map ((arcι Dw L).comp (PowerSeries.C (R := L)))) x.2.1 x.2.2
  have hg : IsUnit (g (arcDet Dw K)) := by
    have e : g (arcDet Dw K) = (∏ τ, (letM Dw L τ).det) *
        ∏ τ, (arcι Dw L).comp (PowerSeries.C (R := L)) (N τ).det := by
      rw [← Finset.prod_mul_distrib]
      refine (map_prod g _ _).trans (Finset.prod_congr rfl fun τ _ => ?_)
      rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
      congr 1
      ext i k : 2
      exact MvPolynomial.eval₂Hom_X' _ _ _
    rw [e]
    exact (isUnit_prod_det Dw L).mul (IsUnit.prod_univ_iff.2 fun τ => (hN τ).map _)
  refine ⟨IsLocalization.Away.lift (arcDet Dw K) hg, fun p => ?_, fun τ => ?_⟩
  · rw [IsLocalization.Away.lift_eq]
    exact MvPolynomial.eval₂Hom_C _ _ _
  · ext i k : 2
    exact (IsLocalization.Away.lift_eq (arcDet Dw K) hg _).trans (MvPolynomial.eval₂Hom_X' _ _ _)

theorem arcι_C (Dw : Datum H) {L : Type} [Field L] (x : L) : arcι Dw L (PowerSeries.C (R := L) x) =
    algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) _ (MvPolynomial.C (HahnSeries.C (Γ := ℤ) x)) := by
  rw [← HahnSeries.ofPowerSeries_C]
  rfl

theorem isUnit_arcι_X (Dw : Datum H) (L : Type) [Field L] : IsUnit (arcι Dw L PowerSeries.X) := by
  have h : HahnSeries.ofPowerSeries ℤ L PowerSeries.X ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).2 PowerSeries.X_ne_zero
  exact h.isUnit.map ((algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) (ArcS Dw L)).comp MvPolynomial.C)

theorem nontrivial_arcS (Dw : Datum H) (L : Type) [Field L] : Nontrivial (ArcS Dw L) :=
  (IsLocalization.injective (ArcS Dw L)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (LetterMap.det_ne_zero Dw L))).nontrivial

theorem exists_mul_pow (T : CDVR) {ϖ : T.V} (h : Irreducible ϖ) (y : T.Fr) :
    ∃ (v : T.V) (n : ℕ), y * algebraMap T.V T.Fr ϖ ^ n = algebraMap T.V T.Fr v := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors T.V) y
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero s.2) h
  exact ⟨a * u, n, by rw [← map_pow, ← hu, map_mul, ← mul_assoc, hs, map_mul]⟩

set_option maxHeartbeats 800000 in

theorem bcRigidAt_of_intModel : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (Wl : ValuationSubring ℂ) (Yw : Model Xo c (c.V Wl).subtype) (M : IntModel d Dv.Tv Dv.io Wl) (χw : Sp (PowerSeries Dv.Tv.V) ⟶ Yw.X) (Ww : Wit Yw M.aw χw) (y₀ : FrPt Xo c (ArcSR Dw Dv.Tv.V Dv.ϖ)) (ζ : K₁) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr) (A Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr), d.OverBase → d.Normal ζ → χw ≫ Yw.s = spMap (PowerSeries.C (R := Dv.Tv.V)) ≫ spMap M.b → (∀ (x : c.F) (v : Dv.Tv.V) (n : ℕ), (Dv.io.comp (algebraMap c.F K₁)) x * algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ ^ n = algebraMap Dv.Tv.V Dv.Tv.Fr v → algebraMap c.F (ArcSR Dw Dv.Tv.V Dv.ϖ) x * arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C (R := Dv.Tv.V) Dv.ϖ) ^ n = arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C (R := Dv.Tv.V) v)) → IsArcFr Ww M.ew M.thw (arcιR Dw Dv.Tv.V Dv.ϖ) y₀ → FrChg (letMR Dw Dv.Tv.V Dv.ϖ) 1 y₀ Dv.yR → M.γ ≠ 0 → (∀ τ k, lam τ k ≠ 0) → (∀ τ, A τ * Bm τ = 1) → (∀ τ k l, M.g τ k l = lam τ k * A τ k l) → BcRigidAt Dv (Dv.io ζ * M.γ) lam Bm := by
  intro h1 h2 hU h5 E _ _ _ H Dw l Xo c K₁ _ _ _ d w Z Dv Wl Yw M χw Ww y₀ ζ lam A Bm hd hN hχ hpin hy₀ hyR _ hlam hAB hg
  have calcu := frChg_calculus E H Dw l Xo c
  have exu := frChg_exists_unique_units E H Dw l Xo c
  have frbc := GlobalTheory.FramedBaseChange.exists_frMap h1 E H Dw l Xo c
  have := nontrivial_arcS Dw Dv.Tv.Fr

  let N : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr :=
    fun τ => Matrix.of fun i k => Bm τ i k * (lam τ k)⁻¹
  have hNg : ∀ τ, N τ * M.g τ = 1 := fun τ => by
    rw [← mul_eq_one_comm.1 (hAB τ)]
    ext i k
    simp only [Matrix.mul_apply, N, Matrix.of_apply, hg]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc, inv_mul_cancel_left₀ (hlam τ j)]
  let κ : Dv.Tv.Fr →+* ArcS Dw Dv.Tv.Fr := (arcι Dw Dv.Tv.Fr).comp (PowerSeries.C (R := Dv.Tv.Fr))

  obtain ⟨φ₀, hφC, hφX⟩ := exists_letterSub Dw Dv.io N fun τ => Matrix.isUnit_det_of_right_inverse (hNg τ)
  have hφι : φ₀.comp (arcι Dw K₁) = (arcι Dw Dv.Tv.Fr).comp (PowerSeries.map Dv.io) := RingHom.ext fun p =>
    (hφC _).trans (by rw [LetterMap.coeffMap_ofPowerSeries]; rfl)
  have hφc : ∀ x : K₁, φ₀ (cst Dw x) = κ (Dv.io x) := fun x =>
    (RingHom.congr_fun hφι (PowerSeries.C x)).trans (congrArg (arcι Dw Dv.Tv.Fr) (PowerSeries.map_C _ _))
  let φ : ArcS Dw K₁ →ₐ[c.F] ArcS Dw Dv.Tv.Fr :=
    { φ₀ with commutes' := fun r => (congrArg φ₀ (arcS_pin Dw K₁ r)).trans ((hφc _).trans (Dv.algW_eq r).symm) }
  obtain ⟨-, -, -, ⟨ψ₀, hψι, hψX⟩, -⟩ := GlobalTheory.LetterDenom.main E H Dw Dv.Tv Dv.ϖ Dv.ϖ_irr.ne_zero
  have hψc : ∀ v, ψ₀ (arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C v)) = κ (algebraMap Dv.Tv.V Dv.Tv.Fr v) := fun v =>
    (RingHom.congr_fun hψι (PowerSeries.C v)).trans (congrArg (arcι Dw Dv.Tv.Fr) (PowerSeries.map_C _ _))
  have hψa : ∀ r : c.F, ψ₀ (algebraMap c.F _ r) = algebraMap c.F _ r := fun r => by
    obtain ⟨v, n, hv⟩ := exists_mul_pow Dv.Tv Dv.ϖ_irr (Dv.io (algebraMap c.F K₁ r))
    have e := congrArg ψ₀ (hpin r v n hv)
    rw [map_mul ψ₀, map_pow ψ₀, hψc, hψc, ← hv, map_mul κ, map_pow κ] at e
    have hu : IsUnit (κ (algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ) ^ n) :=
      (((map_ne_zero_iff _ (IsFractionRing.injective Dv.Tv.V Dv.Tv.Fr)).2 Dv.ϖ_irr.ne_zero).isUnit.map κ).pow n
    exact (hu.mul_right_cancel e).trans (Dv.algW_eq r).symm
  let ψ : ArcSR Dw Dv.Tv.V Dv.ϖ →ₐ[c.F] ArcS Dw Dv.Tv.Fr := { ψ₀ with commutes' := hψa }
  have hψM : ∀ τ, (letMR Dw Dv.Tv.V Dv.ϖ τ).map ψ = letM Dw Dv.Tv.Fr τ := fun τ =>
    Matrix.ext fun i k => hψX ⟨τ, i, k⟩

  obtain ⟨th₁, th₂, t₁, t₂, t₃⟩ := M.th_tie
  obtain ⟨e₁, e₂, l₁, l₂, -, l₃⟩ := M.e_tie
  have bcK : InBC Dv.io (d.a.restrict (c.V d.Wp).subtype) (M.aK.restrict (c.V d.Wp).subtype) M.pK :=
    ⟨rfl, M.bcK.2⟩
  obtain ⟨w₁, -, -, -, n₁⟩ := (GlobalTheory.ArcQBC.baseChanges h1 h2 hU h5 E H Dw l Xo c _ _ Yw Dv.Tv.V Dv.Tv.Fr _ M.aw _
    (IsFractionRing.injective Dv.Tv.V Dv.Tv.Fr) _ M.bcw.1).2 (M.aK.restrict (c.V Wl).subtype) M.pw M.bcw
  obtain ⟨w₂, -, -, -, n₂⟩ := (GlobalTheory.ArcQBC.baseChanges h1 h2 hU h5 E H Dw l Xo c _ _ d.Y K₁ Dv.Tv.Fr _ (d.a.restrict (c.V d.Wp).subtype) _
    Dv.io.injective _ bcK.1).2 (M.aK.restrict (c.V d.Wp).subtype) M.pK bcK
  obtain ⟨W₁, hW₁⟩ := w₁ χw Ww
  obtain ⟨W₂, hW₂⟩ := w₂ d.χ d.W
  have nz : ThNZ d.th := by
    obtain ⟨_, _, _, _, h, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.exists_ne_zero_iff _ _).1 h
  have hj : Mono Yw.j := GlobalTheory.ThetaShiftProofs.mono_j Yw (mono_spMap_subtype _)
  have hj' : Mono d.Y.j := GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)

  obtain ⟨y₁, hy₁⟩ := frbc _ _ ψ y₀
  have a₁ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Yw _ _ _ χw Ww _ _ M.thw_nz _ _ y₀ hy₀).2 hj _ ψ y₁ hy₁
  have a₂ : IsArcFr W₁ e₁ th₁ (arcι Dw Dv.Tv.Fr) y₁ :=
    GlobalTheory.ArcQ.isArcFr_witBC h1 h2 E H Dw l Xo c _ _ Yw _ _ M.aw χw Ww _ _ (M.aK.restrict (c.V Wl).subtype) _ M.pw W₁ hj M.bcw hW₁ _ _ _ _ l₁ t₁ _ _ y₁ (hψι ▸ a₁)
  obtain ⟨y₂, hy₂⟩ := (exu _ (fun τ => (M.g τ).map κ) (κ M.γ) y₁).1
    (fun τ => by
      have := (Matrix.isUnit_det_of_left_inverse (hNg τ)).map κ
      rwa [RingHom.map_det] at this) ((Ne.isUnit ‹M.γ ≠ 0›).map κ)
  have a₃ : IsArcFr W₁ e₂ th₂ (arcι Dw Dv.Tv.Fr) y₂ :=
    GlobalTheory.ArcQ.isArcFr_of_frChg_const h1 h2 E H Dw l Xo c _ _ Yw _ _ _ _ W₁ e₁ e₂ th₁ th₂ M.g M.γ (n₁ _ _ t₁ M.thw_nz) l₃ t₃ _ _ y₁ y₂ hj a₂ hy₂

  obtain ⟨x₀, hx₀, hxF⟩ := hN
  obtain ⟨x₁, hx₁⟩ := frbc _ _ φ x₀
  have b₁ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ d.Y _ _ _ d.χ d.W _ _ nz _ _ x₀ hx₀).2 hj' _ φ x₁ hx₁
  have b₂ : IsArcFr W₂ e₂ th₂ (arcι Dw Dv.Tv.Fr) x₁ :=
    GlobalTheory.ArcQ.isArcFr_witBC h1 h2 E H Dw l Xo c _ _ d.Y _ _ (d.a.restrict (c.V d.Wp).subtype) d.χ d.W _ _
      (M.aK.restrict (c.V d.Wp).subtype) _ M.pK W₂ hj' bcK hW₂ _ _ _ _ l₂ t₂ _ _ x₁ (hφι ▸ b₁)

  have hC : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R'),
      spMap (PowerSeries.map f) ≫ spMap (PowerSeries.C (R := R)) = spMap (PowerSeries.C (R := R')) ≫ spMap f :=
    fun f => by
      rw [← spMap_comp, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C _ _)
  obtain rfl : y₂ = x₁ := GlobalTheory.T.arc_framed_point_eq_of_models_over_base h1 h2 h5 E H Dw l Xo c _ _ M.aK _ _ Yw d.Y _ _ W₁ W₂
    (by rw [Category.assoc, hχ, ← Category.assoc, hC, Category.assoc, ← spMap_comp, ← M.bcw.1])
    (by rw [Category.assoc, hd, ← Category.assoc, hC, Category.assoc, ← spMap_comp, RingHom.comp_assoc])
    e₂ th₂ (n₂ _ _ t₂ nz) _ _ y₂ x₁ (isUnit_arcι_X Dw _) a₃ b₂

  obtain ⟨z₁, hz₁⟩ := frbc _ _ φ d.yF
  obtain ⟨z₂, hz₂⟩ := frbc _ _ ψ Dv.yR
  have c₁ := ((calcu _).1 _ _ _ _ _ _ _ hy₂).1 (((calcu _).2.2.1 _ φ _ _ _ _ _ _ hxF hx₁).1 hz₁)
  have c₂ := ((calcu _).2.2.1 _ ψ _ _ _ _ _ _ hyR hy₁).1 hz₂
  have eM : (fun τ => (letM Dw K₁ τ).map φ * (M.g τ).map κ) = fun τ => 1 * (letMR Dw Dv.Tv.V Dv.ϖ τ).map ψ :=
    funext fun τ => by
      rw [hψM, one_mul]
      refine (congrArg (· * (M.g τ).map κ) (hφX τ)).trans ?_
      change letM Dw Dv.Tv.Fr τ * (N τ).map κ * (M.g τ).map κ = _
      rw [mul_assoc, ← Matrix.map_mul, hNg, Matrix.map_one _ (map_zero κ) (map_one κ), mul_one]
  have eS : φ (cst Dw ζ) * κ M.γ = κ (Dv.io ζ * M.γ) * ψ 1 := by
    rw [map_one, mul_one, map_mul]
    exact congrArg (· * κ M.γ) (hφc ζ)
  rw [eM, eS] at c₁
  have c₃ := ((calcu _).1 _ (fun _ => 1) _ _ _ _ _ c₂).2 c₁
  have hu := ((exu _ _ _ _).2.2.1 _ c₃).2
  refine ⟨φ, ψ, z₁, z₂, fun o => o.elim hu.unit fun _ => 1, fun f => ⟨_, fun _ => rfl, hφC f⟩, fun x => ?_,
    fun p => RingHom.congr_fun hψι p, hψX, arcι_C Dw _, fun _ => rfl, hz₁, hz₂,
    ((calcu _).2.2.2 _ _ _).2 ⟨fun _ => 1, fun τ i => Matrix.one_apply_eq i,
      fun τ i j h => Matrix.one_apply_ne h.ne, c₃⟩⟩
  refine (congrFun (congrFun (hφX x.1) x.2.1) x.2.2).trans ?_
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => congrArg (_ * ·) (arcι_C Dw _)

end GlobalTheory.ArcRigidity
end

section
noncomputable section

namespace GlobalTheory.FinLocalTan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

def origin (R : Type) [CommRing R] : Over.mk (𝟙 (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem gtTanR_iff (ν : GtPt D (epsR R)) : GtTanR ν ↔ origin R ≫ ν.b = 1 ∧
    ∀ χ y J, Good D.P.L y J → val (ν.s χ) (origin R).left y J = 1 := by
  constructor
  · rintro ⟨g₀, h₀, h⟩
    obtain ⟨h₁, h₂⟩ := (ConstLie.isZero_iff_zeroAlong (ρ := origin R) h).1 h₀
    refine ⟨h₁, fun χ y J hJ => ?_⟩
    have := h₂ χ _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · rintro ⟨h₁, h₂⟩
    obtain ⟨g₀, h⟩ := ConstLie.exists_isPullGt (origin R) ν
    obtain ⟨b, v⟩ := (TorusModel.isPull_iff _ _ _).1 h
    exact ⟨g₀, ⟨b.trans h₁, fun χ => corr_of_val D.P.isLB fun y J hJ =>
      (v χ y J hJ).trans ((h₂ χ y J hJ).trans (val_one _).symm)⟩, h⟩

theorem gtTanR_of_isZero {ν : GtPt D (epsR R)} (h : ν.IsZero) : GtTanR ν := by
  have hb : ν.b = 1 := h.1
  exact (gtTanR_iff ν).2 ⟨by rw [hb, MonObj.comp_one], fun χ y J hJ => (val_corr hJ (h.2 χ) _).trans (val_one _)⟩

theorem gtTanR_of_scale {a : R} {ν ν' : GtPt D (epsR R)} (h : GtPt.IsPull (spMap (epsScaleR a)) ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  have s : (origin R).left ≫ spMap (epsScaleR a) = (origin R).left :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by simp [epsScaleR]))
  refine (gtTanR_iff ν').2 ⟨Over.OverMorphism.ext ?_, fun χ y J hJ => ?_⟩
  · rw [← h₁, Over.comp_left, Over.comp_left, h.1, ← Category.assoc, s]
  · refine (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_)
    rw [s]
    exact h₂ χ y J hJ

theorem gtTanR_of_isAdd {ν ν' ν'' : GtPt D (epsR R)} (h : ν.IsAdd ν' ν'') (ht : GtTanR ν) (ht' : GtTanR ν') :
    GtTanR ν'' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  obtain ⟨h₁', h₂'⟩ := (gtTanR_iff ν').1 ht'
  have hb : ν''.b = ν.b * ν'.b := h.1
  refine (gtTanR_iff ν'').2 ⟨by rw [hb, MonObj.comp_mul, h₁, h₁', _root_.mul_one], fun χ y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) (origin R).left).trans (val_mul hJ _ _ _))
  have c := val_cub D.cub (origin R) hJ (DegPre.cT D (epsR R) χ) ν.b ν'.b
  rw [h₁', (isCub_cubV D.cub hJ).face₃] at c
  have e' := (congrArg₂ (· * ·) rfl c).symm.trans (e.trans (congrArg₂ (· * ·) (h₂ χ y J hJ) (h₂' χ y J hJ)))
  simpa using e'

theorem gtTanR_of_gtComb {m : ℕ} {cf : Fin m → R} {e : Fin m → GtPt D (epsR R)} {ν : GtPt D (epsR R)}
    (h : GtComb cf e ν) (he : ∀ i, GtTanR (e i)) : GtTanR ν := by
  obtain ⟨u, p, hu, h₀, ha, rfl⟩ := h
  have : ∀ i, GtTanR (p i) := fun i => Fin.induction (gtTanR_of_isZero h₀)
    (fun j ih => gtTanR_of_isAdd (ha j) ih (gtTanR_of_scale (hu j) (he j))) i
  exact this _

end

theorem gtTanR_of_letBC {K K' : Type} [Field K] [Field K'] {f : K →+* K'} {D : DegPre K} {D' : DegPre K'}
    {p : IsPullDeg f D D'} {ν : GtPt D (epsR K)} {ν' : GtPt D' (epsR K')} (h : LetBC p ν ν') (ht : GtTanR ν') :
    GtTanR ν := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν').1 ht
  rw [ArcQBC.letBC_iff] at h
  have sq : (origin K').left ≫ spMap (dualMap f) = spMap f ≫ (origin K).left := ArcQBC.dual_fst f
  have : Flat (spMap f) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have : Surjective (spMap f) := by
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    exact ⟨fun y => ⟨(default : PrimeSpectrum K'), Subsingleton.elim _ _⟩⟩
  have : Epi (spMap f) := Flat.epi_of_flat_of_surjective _
  have hb : origin K ≫ ν.b = 1 := by
    refine Over.OverMorphism.ext ((cancel_epi (spMap f)).1 ?_)
    have o : (origin K').left ≫ ν'.b.left = eSec D'.P.A := (congrArg (fun q => q.left) h₁).trans (Category.id_comp _)
    have o' : (1 : Over.mk (𝟙 (Sp K)) ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
    rw [o', Over.comp_left]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sq.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h.1.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) o).trans p.he)))))
  refine (gtTanR_iff ν).2 ⟨hb, fun χ y J hJ => ?_⟩
  obtain ⟨x, rfl⟩ := p.xe.surjective χ
  have C := corr_of_val_flat_surjective (spMap f) D.P.isLB
    (t := LB.pullGen D.P.L _ _ (ν.s (p.xe x)) (origin K).left) (t' := LB.oneGen D.P.L) fun z I hI => by
      obtain ⟨I', hI'⟩ := DegPull.exists_good' D'.P.isLB z
      have e := (ConstFam.pmaps_val (h.2 x).1 (h.2 x).2 (origin K').left hI hI').trans (congrArg (· * _)
        (FormalPoint.prod_gtφT (origin K') ν'.b x (ConstFam.wVal p.w z I I')))
      rw [h₁, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul, sq] at e
      exact (val_pull hI _ _ _).trans (e.trans ((h₂ x z I' hI').trans (val_one _).symm))
  have v := (val_pull hJ _ _ _).symm.trans ((val_corr hJ C (𝟙 _)).trans (val_one _))
  rwa [Category.id_comp] at v

end GlobalTheory.FinLocalTan

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem finLocal_vV_nonneg {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] {v : V} (hv : algebraMap V K v ≠ 0) : 0 ≤ vV V (algebraMap V K v) := by
  have h1 : valV V (algebraMap V K v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v
  have h2 := (WithZero.log_le_log (valV_ne_zero (V := V) hv) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  simp only [vV]
  omega

theorem finLocal_vV_pos {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] {v : V} (hv : Irreducible v) : 0 < vV V (algebraMap V K v) := by
  have h0 : algebraMap V K v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hv.ne_zero
  have h1 : valV V (algebraMap V K v) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem _ v).2 ((IsLocalRing.mem_maximalIdeal v).2 hv.not_isUnit)
  have h2 := (WithZero.log_lt_log (valV_ne_zero (V := V) h0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  simp only [vV]
  omega

theorem finLocalAt_of_intModel :
    Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (Yw : Model Xo c (c.V Wl).subtype) (M : IntModel d Tv io Wl) (la : HeightOneSpectrum (𝓞 c.F)) (eL : ℕ) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Tv.Fr) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Tv.Fr) (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ), d.OverBase → Tv.FinRes → OverLa w Tv.V io 1 → OverLa la Tv.V (io.comp (algebraMap c.F K₁)) eL → Yw.N4 → PushInvertible Yw.t.G Yw.t.PP.L → (∀ (χ : Sp (PowerSeries Tv.V) ⟶ Yw.X) (W : Wit Yw M.aw χ), ArcBasis W M.ρ M.ew) → (M.γ ≠ 0 ∧ vV Tv.V M.γ = vth) → (∀ τ k, lam τ k ≠ 0 ∧ vV Tv.V (lam τ k) = vη τ k) → (∀ τ, (A τ).det ≠ 0) → (∀ τ k l, M.g τ k l = lam τ k * A τ k l) → (∀ τ k l, A τ k l = 0 ∨ -(m : ℤ) ≤ vV Tv.V (A τ k l)) → ∀ a n, FinLocalAt d w n vth vη m (intAt Xo c a n la) := by
  intro h1 h2 hU h5 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d w Tv io Wl Yw M la eL lam A vth vη m hob hfin how hola h4
    hpush hbas hγ hlam hdet hg hA a n
  obtain ⟨Z, ιT, hc, hn, hs⟩ := (exists_finSite_norm_eq_zpow_siteAlg K₁ w).2 Tv io hfin how
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) Tv.V := by
    rw [← hϖ.maximalIdeal_eq]
    infer_instance
  obtain ⟨χ, hχ, -⟩ := h4 Tv.V M.b ϖ M.aw (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hbase, -, hgen, t, mm, P, φ, he, ww, e, hspec⟩ := (hχ χ).1 rfl
  let W : Wit Yw M.aw χ := ⟨t, mm, P, φ, he, ww, e, hspec⟩
  obtain ⟨algR, halg, y₀, yR, hfr, hchg⟩ := exists_dvr_frPt h1 h2 E H Dw l Xo c (c.V Wl) (c.V Wl).subtype Yw Tv ϖ
    (io.comp (algebraMap c.F K₁)) M.b M.aw χ W M.ρ M.ew M.thw hϖ
    (RingHom.ext fun x => (M.b_eq x).symm) M.ρ_eq hbase hgen (mono_spMap_subtype _) hpush (hbas χ W) M.thw_nz
  have hle : ∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := by
    intro v
    by_cases hv : algebraMap Tv.V Tv.Fr v = 0
    · rw [hv, map_zero, norm_zero]
      exact zero_le_one
    · rw [hn _ hv]
      exact zpow_le_one₀ Z.r_pos Z.r_lt.le (finLocal_vV_nonneg hv)
  have hlt : ‖ιT (algebraMap Tv.V Tv.Fr ϖ)‖ < 1 := by
    rw [hn _ ((map_ne_zero_iff _ (IsFractionRing.injective Tv.V Tv.Fr)).2 hϖ.ne_zero)]
    exact zpow_lt_one₀ Z.r_pos Z.r_lt (finLocal_vV_pos hϖ)
  let Dv : DvrFrame d w Z :=
    { Tv := Tv, io := io, ιT := ιT, ιT_io := hc, norm_le := hle, ϖ := ϖ, ϖ_irr := hϖ, norm_ϖ := hlt
      algR := algR
      algW := ((arcι Dw Tv.Fr).comp ((PowerSeries.C (R := Tv.Fr)).comp (io.comp (algebraMap c.F K₁)))).toAlgebra
      algW_eq := fun _ => rfl
      yR := yR }
  have htan : ∀ τ k, GtTanR (d.e τ k) := fun τ k => by
    obtain ⟨e₁, e₂, -, l₂, t₁, hc⟩ := M.e_tie
    exact FinLocalTan.gtTanR_of_letBC (l₂ τ k) (FinLocalTan.gtTanR_of_gtComb (hc τ k) (t₁ τ))
  obtain ⟨ζ, N, hN, hζ, hnorm', -⟩ := exists_normalForm h1 h2 E H Dw l Xo c K₁ d
  have hnorm := hnorm' htan
  have hAB : ∀ τ, A τ * (A τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ))
  have hbc : BcRigidAt Dv (io ζ * M.γ) lam (fun τ => (A τ)⁻¹) :=
    GlobalTheory.ArcRigidity.bcRigidAt_of_intModel h1 h2 hU h5 E H Dw l Xo c K₁ d w Z Dv Wl Yw M χ W y₀ ζ lam A (fun τ => (A τ)⁻¹) hob hnorm hbase
      halg hfr hchg hγ.1 (fun τ k => (hlam τ k).1) hAB hg
  have hmono : Mono Yw.j := by
    have := mono_spMap_subtype (c.V Wl)
    have := Yw.jQ_open
    unfold Model.j
    infer_instance
  have hrec : RecordAt Dv (intAt Xo c a n la) :=
    recordAt_of_isArcFr h1 h2 E H Dw l Xo c hev K₁ d w Z Dv (c.V Wl) (c.V Wl).subtype Yw M.b M.aw χ W M.ρ M.ew M.thw y₀ la eL
      hs hola M.ρ_eq halg hpush (hbas χ W) M.thw_nz hmono hfr hchg a n
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hζ
    exact zero_ne_one hζ
  have hζ1 : ‖ιT (io ζ)‖ = 1 := by
    have : ‖ιT (io ζ)‖ ^ N = 1 := by
      rw [← norm_pow, ← map_pow, ← map_pow, hζ, map_one, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 this
  refine (GlobalTheory.ArcQ.FrameCut.frame_of_cut h1 h2 E H Dw l Xo c hev K₁ d w a n (intAt Xo c a n la) (fun F hF => hF.1)).2 vth vη m
    ⟨Z, Dv, io ζ * M.γ, lam, A, fun τ => (A τ)⁻¹, ⟨mul_ne_zero ((map_ne_zero io).2 hζ0) hγ.1, ?_⟩,
      fun τ k => ⟨(hlam τ k).1, ?_⟩, ⟨hAB, fun τ k l => ?_⟩, hbc, hrec⟩
  · change ‖ιT (io ζ * M.γ)‖ = _
    rw [map_mul, norm_mul, hζ1, one_mul, hn _ hγ.1, hγ.2]
  · change ‖ιT (lam τ k)‖ = _
    rw [hn _ (hlam τ k).1, (hlam τ k).2]
  · change ‖ιT (A τ k l)‖ ≤ _
    by_cases h0 : A τ k l = 0
    · rw [h0, map_zero, norm_zero]
      exact (zpow_pos Z.r_pos _).le
    · rw [hn _ h0]
      exact zpow_le_zpow_right_of_le_one₀ Z.r_pos Z.r_lt.le ((hA τ k l).resolve_left h0)

end GlobalTheory.ArcQ
end
end
