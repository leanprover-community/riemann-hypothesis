import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHolomorphicTypeFamilyHolomorphicType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDomaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsActByScalarsHighestWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantMultilinearOfMatrixCoeffEqUnita
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentativeStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSobolevInequalityAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePowStatement

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.InterpolationCoefficientsInL2

lemma inner_iso_eigen {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (U : K →L[ℂ] K)
    (hU : ∀ x, ‖U x‖ = ‖x‖) {F : K} {c : ℂ} (hc : ‖c‖ = 1) (hF : U F = c • F) (G : K) :
    ⟪F, U G⟫_ℂ = c * ⟪F, G⟫_ℂ := by
  have h := (LinearIsometry.mk (U : K →ₗ[ℂ] K) hU).inner_map_map F G
  change ⟪U F, U G⟫_ℂ = _ at h
  rw [hF, inner_smul_left] at h
  have h1 : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  rw [← h, ← mul_assoc, h1, one_mul]

lemma rep_mul_apply {G K : Type*} [Monoid G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : G →* (K →L[ℂ] K))
    (a b : G) (F : K) : ρ (a * b) F = ρ a (ρ b F) := by
  rw [map_mul]; rfl

lemma inner_rep_one {G K : Type*} [Monoid G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : G →* (K →L[ℂ] K))
    (F : K) : ⟪F, ρ 1 F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_one, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
  simp

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ}

lemma holFn_congr {f g : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (h : ∀ u ∈ UG Hm, g u = f u) :
    HolFn Hm q x₀ w g := by
  obtain ⟨P, hP, hf⟩ := hf
  exact ⟨P, hP, fun u hu => (h u hu).trans (hf u hu)⟩

lemma holFn_const_mul {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (c : ℂ) :
    HolFn Hm q x₀ w fun u => c * f u := by
  obtain ⟨P, ⟨hP1, hP2⟩, hf⟩ := hf
  refine ⟨fun x => c * P x, ⟨hP1.const_mul c, fun x hx b hb => ?_⟩, fun u hu => ?_⟩
  · beta_reduce
    rw [hP2 x hx b hb]; ring
  · beta_reduce
    rw [hf u hu]

lemma holFn_sub {f g : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (hg : HolFn Hm q x₀ w g) :
    HolFn Hm q x₀ w fun u => f u - g u := by
  obtain ⟨P, ⟨hP1, hP2⟩, hf⟩ := hf
  obtain ⟨Q, ⟨hQ1, hQ2⟩, hg⟩ := hg
  refine ⟨fun x => P x - Q x, ⟨hP1.sub hQ1, fun x hx b hb => ?_⟩, fun u hu => ?_⟩
  · beta_reduce
    rw [hP2 x hx b hb, hQ2 x hx b hb]; ring
  · beta_reduce
    rw [hf u hu, hg u hu]

omit [Fintype ι] in
lemma one_mem_UG : (1 : ι → Mt n) ∈ UG Hm := by
  intro τ
  change (1 : Mt n)ᴴ * Hm τ * 1 = Hm τ
  simp

omit [Fintype ι] in
lemma mul_mem_UG {u u' : ι → Mt n} (hu : u ∈ UG Hm) (hu' : u' ∈ UG Hm) : u * u' ∈ UG Hm := by
  intro τ
  have h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
  have h2 : (u' τ)ᴴ * Hm τ * u' τ = Hm τ := hu' τ
  change (u τ * u' τ)ᴴ * Hm τ * (u τ * u' τ) = Hm τ
  calc (u τ * u' τ)ᴴ * Hm τ * (u τ * u' τ) = (u' τ)ᴴ * ((u τ)ᴴ * Hm τ * u τ) * u' τ := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hm τ := by rw [h1, h2]

lemma norm_prod_exp (w : Fin n → ℤ) (s : Fin n → ℝ) :
    ‖∏ a, Complex.exp ((s a : ℂ) * Complex.I) ^ w a‖ = 1 := by
  rw [norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [norm_zpow, Complex.norm_exp_ofReal_mul_I, _root_.one_zpow]

lemma norm_torCh (w : ι → Fin n → ℤ) (s : ι → Fin n → ℝ) : ‖torCh w s‖ = 1 := by
  unfold torCh
  rw [norm_prod]
  exact Finset.prod_eq_one fun τ _ => norm_prod_exp _ _

lemma eq_const_mul [DecidableEq ι] (hO : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {f g : (ι → Mt n) → ℂ} (c : ℂ)
    (hf : HolFn Hm q x₀ w f) (hg : HolFn Hm q x₀ w g)
    (hfl : ∀ u ∈ UG Hm, ∀ s, f (torEl x₀ s * u) = torCh w s * f u)
    (hgl : ∀ u ∈ UG Hm, ∀ s, g (torEl x₀ s * u) = torCh w s * g u) (hf1 : f 1 = c) (hg1 : g 1 = 1) :
    ∀ u ∈ UG Hm, f u = c * g u := fun u hu =>
  sub_eq_zero.1 (GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law n ι Hm q x₀ w hO _ (holFn_sub hf (holFn_const_mul hg c))
    (fun u hu s => by beta_reduce; rw [hfl u hu, hgl u hu]; ring)
    (by beta_reduce; rw [hf1, hg1, mul_one, sub_self]) u hu)

end Local

end GlobalTheory.HolDict.InterpolationCoefficientsInL2

open GlobalTheory.HolDict.InterpolationCoefficientsInL2 in

theorem GlobalTheory.HolDict.inner_reg_eq_coef_extremal : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ) F, HolForm θ M w J χ φ → Repr V μ 𝓕 F φ → ∀ u ∈ GinfC V, ⟪F, ρ u F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ := by
  classical
  intro D θ V S M w v hθ hS hW hv μ 𝓕 ρ hfin hreg J χ φ F hφ hF u₀ hu₀
  refine (GlobalTheory.RealLift.exists_real_lift D θ V hθ).elim fun L hL => ?_
  have hL1 := hL.1
  have hLmul := hL.2.1
  have hUG := hL.2.2.2.1
  have hLinv := hL.2.2.2.2.1
  have hB := (GlobalTheory.HolDict.holFn_coef_extVec D θ V S M w v hθ hS hW hv).1
  have hBt := (GlobalTheory.HolDict.holFn_coef_extVec D θ V S M w v hθ hS hW hv).2
  have hO : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) :=
    fun τ => ((GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.2.2 hS).1
  have hU : ∀ τ, IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) := fun τ => (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  have htm : ∀ s, torEl (x0Mat M) s ∈ UG (gramAt D V) := fun s => by
    simpa using TorusLaw.mul_torEl_mem hO s (one_mem_UG (Hm := gramAt D V))
  have hL0 : L 1 = 1 := by
    have h := hLmul 1 one_mem_UG 1 one_mem_UG
    rw [mul_one] at h
    exact mul_left_cancel (a := L 1) (by rw [← h, mul_one])

  have horb : ∀ x, HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => φ (x * L u) := by
    intro x
    obtain ⟨f, hf, hfx⟩ := hφ.hol x
    refine holFn_congr hf fun u hu => ?_
    rw [hfx _ (hL1 u hu).1]
    congr 1
    funext τ
    exact (hL1 u hu).2 τ
  have htor : ∀ s x, φ (x * L (torEl (x0Mat M) s)) = torCh w s * φ x := by
    intro s x
    obtain ⟨h1, h2⟩ := GlobalTheory.HolDict.smFn_and_killedFn_of_holFn _ _ _ _ _ _ hO _ (horb x)
    have := GlobalTheory.HolDict.torus_law_of_killed _ _ _ _ _ _ hO _ h1 h2 1 one_mem_UG s
    simpa [hL0] using this
  refine hφ.bdd.elim fun C hC => ?_
  have hR := (GlobalTheory.HolDict.RepresentativeL2.repr_properties D V μ 𝓕 ρ hfin hreg).2.2
  have hR3 := hR.1
  have hR4 := hR.2.1
  have hR5 := hR.2.2.1
  have hR6 := hR.2.2.2
  have hρt : ∀ s, ρ (L (torEl (x0Mat M) s)) F = torCh w s • F := by
    intro s
    have h1 := hR4 F φ (L (torEl (x0Mat M) s)) hF
    have h2 := hR5 F F φ φ (torCh w s - 1) hF hF
    have e1 : (torCh w s - 1) • F + F = torCh w s • F := by rw [sub_smul, one_smul, sub_add_cancel]
    have e2 : (torCh w s - 1) • φ + φ = rTr V (L (torEl (x0Mat M) s)) φ := by
      funext x
      simp only [rTr, htor, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2] at h2
    exact hR3 _ _ _ h1 h2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin.fin
  have hA : HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => ⟪F, ρ (L u) F⟫_ℂ := by
    have h := GlobalTheory.HolDict.holFn_integral _ _ _ _ _ w hO (GA D V) (μ.restrict 𝓕) (fun x u => star (φ x) * φ (x * L u)) (C * C)
      (fun x => holFn_const_mul (horb x) _)
      (fun x u _ => by
        rw [norm_mul, norm_star]
        exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))
      (fun u _ => (hR6 F _ φ _ hF (hR4 F φ (L u) hF)).1.aestronglyMeasurable)
    exact holFn_congr h fun u _ => (hR6 F _ φ _ hF (hR4 F φ (L u) hF)).2
  have key := eq_const_mul hO ((‖F‖ ^ 2 : ℝ) : ℂ) hA hB
    (fun u hu s => ((congrArg (fun g => ⟪F, ρ g F⟫_ℂ) (hLmul _ (htm s) _ hu)).trans
      (congrArg (fun G => ⟪F, G⟫_ℂ) (rep_mul_apply ρ _ _ F))).trans
      (inner_iso_eigen _ (hreg.iso _) (norm_torCh w s) (hρt s) _))
    (fun u hu s => by
      have a2 : ∀ τ, ⟪(v τ : M.H τ), M.rep τ ((torEl (x0Mat M) s * u) τ) (v τ : M.H τ)⟫_ℂ =
          (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) * ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ := by
        intro τ
        refine (congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ)
          ((hU τ).1.2 _ (htm s τ) _ (hu τ))).trans ?_
        exact inner_iso_eigen _ ((hU τ).2.1 _ (htm s τ)) (norm_prod_exp _ _) (hBt s τ) _
      exact (Finset.prod_congr rfl fun τ _ => a2 τ).trans Finset.prod_mul_distrib)
    ((congrArg (fun g => ⟪F, ρ g F⟫_ℂ) hL0).trans (inner_rep_one ρ F))
    (Finset.prod_eq_one fun τ _ => by
      refine (congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ) (hU τ).1.1).trans ?_
      change ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1
      rw [inner_self_eq_norm_sq_to_K, (hv τ).1]
      simp)
    _ (hUG u₀)
  exact (congrArg (fun g => ⟪F, ρ g F⟫_ℂ) (hLinv u₀ hu₀)).symm.trans key
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_rho_eq_normSq_mul_prod_of_holForm : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ) F, HolForm θ M w J χ φ → Repr V μ 𝓕 F φ → ∀ u ∈ GinfC V, ⟪F, ρ u F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.HolDict.inner_reg_eq_coef_extremal | exact GlobalTheory.HolDict.inner_reg_eq_coef_extremal | (intros; apply GlobalTheory.HolDict.inner_reg_eq_coef_extremal <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvCusp

section Abstract

variable {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
  {Γ : Subgroup N} [Countable Γ] {μ : Measure N} [μ.IsMulLeftInvariant] {𝓕 : Set N}

theorem fd_preimage (h : IsFundamentalDomain Γ 𝓕 μ) {z : N} (hz : ∀ n, z * n = n * z) :
    IsFundamentalDomain Γ ((fun n => z * n) ⁻¹' 𝓕) μ :=
  h.preimage_of_equiv (measurePreserving_mul_left μ z).quasiMeasurePreserving (e := id) Function.bijective_id
    fun γ n => by
      change z * ((γ : N) * n) = (γ : N) * (z * n)
      rw [← mul_assoc, hz, mul_assoc]

theorem inv_shift {B : Type} {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n)
    (γ : Γ) (n : N) : F (z * (γ • n)) = F (z * n) := by
  change F (z * ((γ : N) * n)) = _
  rw [← mul_assoc, hz, mul_assoc, hF]

theorem setIntegral_shift {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] (h : IsFundamentalDomain Γ 𝓕 μ)
    {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n) :
    ∫ n in 𝓕, F (z * n) ∂μ = ∫ n in 𝓕, F n ∂μ := by
  rw [h.setIntegral_eq (fd_preimage h hz) (f := fun n => F (z * n)) (inv_shift hz hF)]
  exact (measurePreserving_mul_left μ z).setIntegral_preimage_emb (MeasurableEquiv.mulLeft z).measurableEmbedding F 𝓕

theorem integrableOn_shift {B : Type} [NormedAddCommGroup B] (h : IsFundamentalDomain Γ 𝓕 μ)
    {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n)
    (hi : IntegrableOn F 𝓕 μ) : IntegrableOn (fun n => F (z * n)) 𝓕 μ := by
  rw [h.integrableOn_iff (fd_preimage h hz) (f := fun n => F (z * n)) (inv_shift hz hF)]
  exact ((measurePreserving_mul_left μ z).integrableOn_comp_preimage
    (MeasurableEquiv.mulLeft z).measurableEmbedding).2 hi

theorem setIntegral_eq_zero [SecondCountableTopology N] [SFinite μ] {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] (ν : Measure Z) [IsFiniteMeasure ν] (hν : ν ≠ 0) (i : Z → N) (hi : Continuous i)
    (hz : ∀ z n, i z * n = n * i z) (h : IsFundamentalDomain Γ 𝓕 μ) {F : N → ℂ} (hc : Continuous F)
    (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n) (h0 : ∀ n, ∫ z, F (i z * n) ∂ν = 0) : ∫ n in 𝓕, F n ∂μ = 0 := by
  by_cases hI : IntegrableOn F 𝓕 μ
  swap
  · exact integral_undef hI
  have hm : AEStronglyMeasurable (Function.uncurry fun (z : Z) (n : N) => F (i z * n)) (ν.prod (μ.restrict 𝓕)) :=
    (hc.comp ((hi.comp continuous_fst).mul continuous_snd)).aestronglyMeasurable
  have hp : Integrable (Function.uncurry fun (z : Z) (n : N) => F (i z * n)) (ν.prod (μ.restrict 𝓕)) := by
    refine (integrable_prod_iff hm).2 ⟨Filter.Eventually.of_forall fun z => integrableOn_shift h (hz z) hF hI, ?_⟩
    have e : (fun z : Z => ∫ n in 𝓕, ‖F (i z * n)‖ ∂μ) = fun _ => ∫ n in 𝓕, ‖F n‖ ∂μ :=
      funext fun z => setIntegral_shift h (hz z) (F := fun n => ‖F n‖) fun γ n => by rw [hF]
    exact e ▸ integrable_const _
  have key := integral_integral_swap hp
  simp only [h0, integral_zero, setIntegral_shift h (hz _) hF, integral_const, smul_eq_zero] at key
  exact key.resolve_left (by simpa [measureReal_eq_zero_iff] using hν)

end Abstract

section Mat

variable {R : Type} [CommRing R] {n r : ℕ} {m m' : Matrix (Fin n) (Fin n) R} {a : R} {C : Matrix (Fin n) (Fin r) R}
  {E : Matrix (Fin r) (Fin r) R} {P : Matrix (Fin r) (Fin n) R}

theorem mat_kill (ha : m = a • (C * E * P)) (h0 : P * C = 0) :
    m * C = 0 ∧ P * m = 0 ∧ ∀ x, P *ᵥ x = 0 → m *ᵥ x = C *ᵥ 0 := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [ha, Matrix.smul_mul, Matrix.mul_assoc, h0, Matrix.mul_zero, smul_zero]
  · rw [ha, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.zero_mul, smul_zero]
  · rw [ha, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, smul_zero, Matrix.mulVec_zero]

theorem mat_comm (ha : m - 1 = a • (C * E * P)) (h1 : (m' - 1) * C = 0) (h2 : P * (m' - 1) = 0) :
    m * m' = m' * m := by
  have e : Commute (m - 1) (m' - 1) := by
    rw [Commute, SemiconjBy, ha, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, h2, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, h1, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have := (e.add_left (Commute.one_left _)).add_right (Commute.one_right _)
  rw [sub_add_cancel, sub_add_cancel] at this
  exact this

theorem commute_closure {G : Type} [Group G] {s t : Set G} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {x y : G}
    (hx : x ∈ Subgroup.closure s) (hy : y ∈ Subgroup.closure t) : Commute x y := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h x hx y hy
    | one => exact Commute.one_right _
    | mul _ _ _ _ k k' => exact k.mul_right k'
    | inv _ _ k => exact k.inv_right
  | one => exact Commute.one_left _
  | mul _ _ _ _ k k' => exact k.mul_left k'
  | inv _ _ k => exact k.inv_left

end Mat

section Algebra

variable {D : D7} (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}

theorem vecMulVec_col (j : Fin r) :
    vecMulVec (fun i => C i j) ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (C i j)) ᵥ* V.gram) =
      C * Matrix.single j j (1 : D.host.E) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_single_apply_same, mul_one]
    rfl
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, zero_mul]
  · exact fun h => absurd (Finset.mem_univ j) h

theorem isoVec_col (hC : IsIsoFrame V C) (j : Fin r) : IsoVec V fun i => C i j := by
  refine ⟨hC.2.1.ne_zero j, ?_⟩
  have := congrFun (congrFun hC.2.2 j) j
  rw [Matrix.mul_assoc] at this
  exact this

theorem ZI_le (hC : IsIsoFrame V C) (j : Fin r) : ZI V (fun i => C i j) ≤ NI V C := by
  refine Subgroup.closure_mono ?_
  rintro g ⟨a, ha⟩
  have h0 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * C.map (incA D) = 0 := by
    rw [← Matrix.map_mul, hC.2.2, Matrix.map_zero _ (map_zero _)]
  rw [vecMulVec_col, Matrix.map_mul, Matrix.map_mul] at ha
  obtain ⟨k1, k2, k3⟩ := mat_kill ha h0
  refine ⟨k1, k2, fun x hx => ⟨0, k3 _ (funext fun i => ?_)⟩⟩
  have := RingHom.map_mulVec (incA D) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) x i
  rw [hx, Pi.zero_apply, map_zero] at this
  exact this.symm

theorem ZI_comm (j : Fin r) {z n : GA D V} (hz : z ∈ ZI V fun i => C i j) (hn : n ∈ NI V C) : Commute z n := by
  refine commute_closure ?_ hz hn
  rintro z ⟨a, ha⟩ n ⟨h1, h2, -⟩
  rw [vecMulVec_col, Matrix.map_mul, Matrix.map_mul] at ha
  exact Subtype.ext (Units.ext (mat_comm ha h1 h2))

end Algebra

theorem isCuspFun_of_zCusp : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ →
    ZCusp V φ → IsCuspFun V φ := by
  intro D θ V hθ φ hφ hZ r C hC μ 𝓕 hμ h𝓕 g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  let j : Fin r := ⟨0, hC.1⟩
  have hξ := isoVec_col V hC j
  obtain ⟨⟨ν, 𝓖, hν, h𝓖, -⟩, hm, -⟩ := GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ _ hξ
  obtain ⟨m0, m1⟩ := hm ν 𝓖 hν h𝓖
  have : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  let i : NIQ V C → GQ V := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ V => z.1) h))
  have : Countable (NIQ V C) := hi.countable
  have : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  have : IsFiniteMeasure (ν.restrict 𝓖) := isFiniteMeasure_restrict.2 m1
  refine setIntegral_eq_zero (ν.restrict 𝓖) (fun h => m0 (Measure.restrict_eq_zero.1 h))
    (Subgroup.inclusion (ZI_le V hC j)) (continuous_subtype_val.subtype_mk _)
    (fun z n => Subtype.ext (ZI_comm V j z.2 n.2)) h𝓕 (F := fun n => φ ((n : GA D V) * g))
    (hφ.cont.comp (continuous_subtype_val.mul continuous_const)) (fun γ n => ?_) fun n => ?_
  · rw [Subgroup.coe_mul, mul_assoc]
    exact hφ.left _ γ.2 _
  · simpa only [Subgroup.coe_mul, mul_assoc, Subgroup.coe_inclusion] using hZ _ hξ ν 𝓖 hν h𝓖 ((n : GA D V) * g)

end GlobalTheory.TransvCusp
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ → ZCusp V φ → IsCuspFun V φ := by
  atlas_forward_decl GlobalTheory.TransvCusp.isCuspFun_of_zCusp
end

section
section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise

namespace GlobalTheory.QuotRegular

section General

variable {G : Type} [Group G] (Γ : Subgroup G)

abbrev cl (g : G) : Quotient (QuotientGroup.rightRel Γ) := Quotient.mk _ g

theorem cl_mul (γ : Γ) (x : G) : cl Γ ((γ : G) * x) = cl Γ x := by
  refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
  simp

def tr (g : G) : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ) :=
  Quotient.map' (fun x => x * g) fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h

theorem tr_cl (g x : G) : tr Γ g (cl Γ x) = cl Γ (x * g) := rfl

theorem tr_one : tr Γ 1 = id := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (cl Γ) (mul_one x)

theorem tr_mul (g h : G) : tr Γ (g * h) = tr Γ h ∘ tr Γ g := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (cl Γ) (mul_assoc x g h).symm

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem measurable_cl : Measurable (cl Γ) := measurable_quotient_mk''

theorem measurable_tr (g : G) : Measurable (tr Γ g) := by
  rw [measurable_from_quotient]
  exact (measurable_cl Γ).comp (measurable_mul_const g)

variable {Γ} {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ] {𝓕 : Set G}

theorem ae_of_ae_quot (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {p : Quotient (QuotientGroup.rightRel Γ) → Prop}
    (hp : ∀ᵐ q ∂((μ.restrict 𝓕).map (cl Γ)), p q) : ∀ᵐ x ∂μ, p (cl Γ x) := by
  have h1 := ae_of_ae_map (measurable_cl Γ).aemeasurable hp
  rw [ae_restrict_iff'₀ h𝓕.nullMeasurableSet] at h1
  have h2 : ∀ᵐ y ∂μ, ∀ γ : Γ, (γ : G) * y ∈ 𝓕 → p (cl Γ ((γ : G) * y)) :=
    ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h1
  filter_upwards [h2, h𝓕.ae_covers] with y hy hc
  obtain ⟨γ, hγ⟩ := hc
  simpa only [cl_mul] using hy γ hγ

variable [μ.IsMulRightInvariant]

theorem measurePreserving_tr (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) :
    MeasurePreserving (tr Γ g) ((μ.restrict 𝓕).map (cl Γ)) ((μ.restrict 𝓕).map (cl Γ)) := by
  refine ⟨measurable_tr Γ g, Measure.ext fun A hA => ?_⟩
  have hA' : MeasurableSet (cl Γ ⁻¹' A) := measurable_cl Γ hA
  rw [Measure.map_apply (measurable_tr Γ g) hA, Measure.map_apply (measurable_cl Γ) hA,
    Measure.map_apply (measurable_cl Γ) (measurable_tr Γ g hA), Measure.restrict_apply hA',
    Measure.restrict_apply (measurable_cl Γ (measurable_tr Γ g hA))]
  have hD' : IsFundamentalDomain Γ ((fun x => x * g⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => by
        change ((γ : G) * x) * g⁻¹ = (γ : G) * (x * g⁻¹)
        rw [mul_assoc]
  have hinv : ∀ γ : Γ, (fun x => γ • x) ⁻¹' (cl Γ ⁻¹' A) = cl Γ ⁻¹' A := by
    intro γ
    ext x
    change cl Γ ((γ : G) * x) ∈ A ↔ cl Γ x ∈ A
    rw [cl_mul]
  rw [← hD'.measure_set_eq h𝓕 hA' hinv, ← measure_preimage_mul_right μ g (_ ∩ (fun x => x * g⁻¹) ⁻¹' 𝓕)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, tr_cl, mul_inv_cancel_right]

theorem measure_symmDiff_le (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {A : Set (Quotient (QuotientGroup.rightRel Γ))}
    (hA : MeasurableSet A) (g g₀ : G) :
    ((μ.restrict 𝓕).map (cl Γ)) ((tr Γ g ⁻¹' A) ∆ (tr Γ g₀ ⁻¹' A)) ≤
      μ (((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆ ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕))) := by
  set S := ((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆ ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) with hS
  have hU : μ.restrict 𝓕 (⋃ γ : Γ, γ • S) ≤ μ S := by
    rw [h𝓕.measure_eq_tsum S]
    refine (measure_iUnion_le _).trans (le_of_eq (tsum_congr fun γ => ?_))
    rw [Measure.restrict_apply₀' h𝓕.nullMeasurableSet]
  rw [Measure.map_apply (measurable_cl Γ) ((measurable_tr Γ g hA).symmDiff (measurable_tr Γ g₀ hA))]
  refine le_trans (measure_mono_ae ?_) hU
  have key : ∀ a b x : G, (∃ γ : Γ, γ • (x * a) ∈ 𝓕) → cl Γ (x * a) ∈ A → cl Γ (x * b) ∉ A →
      ∃ γ : Γ, (γ : G) * x * a ∈ cl Γ ⁻¹' A ∩ 𝓕 ∧ (γ : G) * x * b ∉ cl Γ ⁻¹' A ∩ 𝓕 := by
    rintro a b x ⟨γ, hγ⟩ h2 h3
    refine ⟨γ, ?_, fun h => h3 ?_⟩
    · rw [mul_assoc]
      exact ⟨by rw [mem_preimage, cl_mul]; exact h2, hγ⟩
    · have := h.1
      rwa [mem_preimage, mul_assoc, cl_mul] at this
  filter_upwards [ae_restrict_of_ae ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h𝓕.ae_covers),
    ae_restrict_of_ae ((measurePreserving_mul_right μ g₀).quasiMeasurePreserving.ae h𝓕.ae_covers)] with x e1 e2 hx
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩
  · obtain ⟨γ, k1, k2⟩ := key g g₀ x e1 a b
    exact mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inl ⟨k1, k2⟩)⟩
  · obtain ⟨γ, k1, k2⟩ := key g₀ g x e2 a b
    exact mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inr ⟨k1, k2⟩)⟩

def reg (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    G →* (Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ)) →L[ℂ] Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) where
  toFun g := (Lp.compMeasurePreservingₗᵢ ℂ (tr Γ g) (measurePreserving_tr h𝓕 g)).toContinuousLinearMap
  map_one' := by
    refine ContinuousLinearMap.ext fun F => Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 1)).trans ?_
    rw [tr_one]
    rfl
  map_mul' g h := by
    refine ContinuousLinearMap.ext fun F => Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 (g * h))).trans ?_
    refine EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (tr Γ h) (measurePreserving_tr h𝓕 h) F) (measurePreserving_tr h𝓕 g)).symm
    rw [tr_mul]
    exact ((measurePreserving_tr h𝓕 g).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 h))).symm

theorem reg_apply (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    reg h𝓕 g F = Lp.compMeasurePreserving (tr Γ g) (measurePreserving_tr h𝓕 g) F := rfl

theorem reg_val (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    ∀ᵐ x ∂μ, reg h𝓕 g F (cl Γ x) = F (cl Γ (x * g)) :=
  ae_of_ae_quot h𝓕 (p := fun q => reg h𝓕 g F q = F (tr Γ g q))
    (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 g))

theorem norm_reg (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    ‖reg h𝓕 g F‖ = ‖F‖ := Lp.norm_compMeasurePreserving F (measurePreserving_tr h𝓕 g)

theorem continuous_reg [LocallyCompactSpace G] [SecondCountableTopology G] [IsFiniteMeasureOnCompacts μ]
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    Continuous fun g => reg h𝓕 g F := by
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun F => Continuous fun g => reg h𝓕 g F)
    ?_ ?_ ?_ F
  · intro c A hA hμA
    rw [Lp.simpleFunc.coe_indicatorConst]
    simp only [reg_apply, Lp.indicatorConstLp_compMeasurePreserving]
    refine continuous_indicatorConstLp_set ENNReal.ofNat_ne_top fun g₀ => ?_
    let m : C(G, C(G, G)) := ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, by fun_prop⟩
    have ht : Tendsto (fun g => μ (((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆
        ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)))) (𝓝 g₀) (𝓝 0) :=
      tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) (f := m) (g := m g₀)
        (m.continuous.tendsto g₀) (Eventually.of_forall fun g => measurePreserving_mul_right μ g)
        (measurePreserving_mul_right μ g₀)
        ((measurable_cl Γ hA).nullMeasurableSet.inter h𝓕.nullMeasurableSet)
        (by
          rw [Measure.map_apply (measurable_cl Γ) hA, Measure.restrict_apply (measurable_cl Γ hA)] at hμA
          exact hμA.ne)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      fun g => measure_symmDiff_le h𝓕 hA g g₀
  · intro f g hf hg _ h1 h2
    simp only [map_add]
    exact h1.add h2
  · refine isClosed_of_closure_subset fun F hF => ?_
    refine TendstoUniformly.continuous (F := fun F' g => reg h𝓕 g F') (p := 𝓝 F) ?_
      (mem_closure_iff_frequently.1 hF)
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds F hε] with F' h g
    rw [dist_eq_norm, ← map_sub, norm_reg, ← dist_eq_norm, dist_comm]
    exact h

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.HolDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isReg : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    FinPair V μ 𝓕 → ∃ ρ, IsReg V μ 𝓕 ρ := by
  intro D V μ 𝓕 h
  obtain ⟨h1, h2, -, h4, h5, -, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := h.haar
  have := h.right
  exact ⟨reg h.fd, reg_val h.fd, norm_reg h.fd, continuous_reg h.fd⟩

end GlobalTheory.QuotRegular
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_representation_of_finite_pair : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), FinPair V μ 𝓕 → ∃ ρ, IsReg V μ 𝓕 ρ := by
  atlas_forward_decl GlobalTheory.QuotRegular.exists_isReg
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.SmoothMultilinear

theorem conj_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {g : Mt V.rank} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h1 := M.fr_gram τ
  have h2 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  show (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ)
  calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by
        rw [h1, hg']
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h2]; simp

theorem rep_one {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.rep τ 1 = 1 := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  unfold DSModel.rep
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

theorem rep_mul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {a b : Mt V.rank} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (a * b) = M.rep τ a * M.rep τ b := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
  unfold DSModel.rep
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = (M.fr τ * a * (M.fr τ)⁻¹) * (M.fr τ * b * (M.fr τ)⁻¹) := by
    calc _ = M.fr τ * a * ((M.fr τ)⁻¹ * M.fr τ) * b * (M.fr τ)⁻¹ := by
          rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (conj_mem M τ ha) _ (conj_mem M τ hb)

theorem prod_mem {n : ℕ} (H : Mt n) (l : List (Mt n)) (hl : ∀ g ∈ l, g ∈ Formalism.QuantumDeterminants.UH H) :
    l.prod ∈ Formalism.QuantumDeterminants.UH H := by
  induction l with
  | nil => show (1 : Mt n)ᴴ * H * 1 = H; simp
  | cons a l ih =>
    rw [List.prod_cons]
    exact CCRuleCW.UH_mul _ _ _ (hl a (by simp)) (ih fun g hg => hl g (by simp [hg]))

theorem exp_mem {n : ℕ} (H X : Mt n) (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  apply CCRuleCW.exp_mem_UH
  have := CCRuleCW.lie_smul H X hX t
  rwa [Complex.coe_smul] at this

theorem smooth_of_span {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Mt n)) (σ : Mt n → (H →L[ℂ] H)) (v : H) (hv : v ∈ Submodule.span ℂ {w | SmoothVec L σ w}) :
    SmoothVec L σ v := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro k Xs _; simp only [map_zero]; exact contDiff_const
  | add x y _ _ hx hy => intro k Xs h; simp only [map_add]; exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx => intro k Xs h; simp only [map_smul]; exact (hx k Xs h).const_smul c

theorem hasDerivAt_of_smooth {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Mt n)) (σ : Mt n → (H →L[ℂ] H)) (v : H) (hv : SmoothVec L σ v) (X : Mt n) (hX : X ∈ L) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0 := by
  have h := hv 1 (fun _ => X) (fun _ => hX)
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => (fun _ : Fin 1 => t)) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := h.comp h2
  have h4 : ContDiff ℝ ∞ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) := by
    convert h3 using 2
    simp
  exact (h4.differentiable (by simp) 0).hasDerivAt

theorem act_list {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K)
    (h : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y))
    (y : ∀ τ, M.H τ) (l : List (D.what₂.Tau × Mt V.rank))
    (hl : ∀ p ∈ l, p.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V p.1)) :
    ρ (l.map fun p => atTau θ V p.1 p.2).prod (Φ y) =
      Φ fun τ => M.rep τ (l.map fun p => if p.1 = τ then p.2 else 1).prod (y τ) := by
  induction l with
  | nil => simp [rep_one]
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V q.1) := fun q hq => hl q (by simp [hq])
    rw [List.map_cons, List.prod_cons, map_mul, ContinuousLinearMap.mul_apply, ih hl',
      ← h p.1 p.2 (hl p (by simp))]
    congr 1
    funext τ
    rw [List.map_cons, List.prod_cons]
    by_cases e : p.1 = τ
    · subst e
      rw [Function.update_self, if_pos rfl, rep_mul M _ (hl p (by simp)), ContinuousLinearMap.mul_apply]
      apply prod_mem
      intro g hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
      split_ifs with e
      · exact e ▸ hl' q hq
      · exact prod_mem _ [] (by simp)
    · rw [Function.update_of_ne (Ne.symm e), if_neg e, one_mul]

theorem smooth_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K)) (Φ : ContinuousMultilinearMap ℂ M.H K), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) → ∀ v : M.Vec, IsSmoothVector' θ V ρ (Φ fun τ => (v τ : M.H τ)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) = Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))) := by
  intro D θ V _ S M K _ _ ρ Φ h v
  have hs : ∀ τ, SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) := fun τ => smooth_of_span _ _ _ (v τ).2
  refine ⟨?_, ?_⟩
  · intro k τs Xs hX
    have e : (fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod (Φ fun τ => (v τ : M.H τ))) =
        fun t : Fin k → ℝ => Φ fun τ => M.rep τ
          (List.ofFn fun i => NormedSpace.exp (t i • (if τs i = τ then Xs i else 0))).prod (v τ : M.H τ) := by
      funext t
      have := act_list θ M ρ Φ h (fun τ => (v τ : M.H τ))
        (List.ofFn fun i => (τs i, NormedSpace.exp (t i • Xs i))) (by
          intro p hp
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
          exact exp_mem _ _ (hX i) _)
      simp only [List.map_ofFn] at this
      refine this.trans ?_
      congr 1
      funext τ
      congr 4
      funext i
      simp only [Function.comp]
      split_ifs <;> simp
    rw [e]
    have hΦ : ContDiff ℝ ∞ (Φ : (∀ τ, M.H τ) → K) := (Φ.contDiff (n := ∞)).restrict_scalars ℝ
    refine hΦ.comp (contDiff_pi.2 fun τ => ?_)
    refine hs τ k _ fun i => ?_
    split_ifs with e
    · exact e ▸ hX i
    · simp [lieAt]
  · intro τ X hX
    have e : (fun t : ℝ => ρ (oneP θ V τ X t) (Φ fun τ => (v τ : M.H τ))) =
        fun t : ℝ => (Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ)
          (M.rep τ (NormedSpace.exp (t • X)) (v τ)) := by
      funext t
      exact (h τ _ (exp_mem _ _ hX t) _).symm
    unfold dL2
    simp only
    rw [e]
    have h1 := hasDerivAt_of_smooth _ _ _ (hs τ) X hX
    exact (((Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1).deriv

end GlobalTheory.SmoothMultilinear
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K)) (Φ : ContinuousMultilinearMap ℂ M.H K), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) → ∀ v : M.Vec, IsSmoothVector' θ V ρ (Φ fun τ => (v τ : M.H τ)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) = Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))) := by
  first | exact @GlobalTheory.SmoothMultilinear.smooth_map | exact GlobalTheory.SmoothMultilinear.smooth_map | (intros; apply GlobalTheory.SmoothMultilinear.smooth_map <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_sobolev_inequality_adelic_unitary : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ μ : Measure (GA D V), μ.IsHaarMeasure → ∃ (S : List (List (D.what₂.Tau × Mt V.rank))) (Ω : Set (GA D V)) (C : ℝ), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ ∀ ψ : GA D V → ℂ, Continuous ψ → (∀ k ∈ U, k ∈ GfC V → ∀ g, ψ (g * k) = ψ g) → (∀ l : List (D.what₂.Tau × Mt V.rank), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → Continuous (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ)) → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) → ∀ y, ‖ψ y‖ ^ 2 ≤ C * (S.map fun l => ∫ x in Ω, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) (y * x)‖ ^ 2 ∂μ).sum := by
  first | exact @GlobalTheory.SobLoc.local_sobolev | exact GlobalTheory.SobLoc.local_sobolev | (intros; apply GlobalTheory.SobLoc.local_sobolev <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobolevGrowth

theorem lintegral_le_of_count {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {A : Set G} (hA : MeasurableSet A) {h : G → ℝ≥0∞} (hm : Measurable h) (hinv : ∀ γ ∈ Γ, ∀ g, h (γ * g) = h g)
    (M : ℝ) (hM : ∀ y, {γ : G | γ ∈ Γ ∧ γ * y ∈ A}.Finite ∧ (({γ : G | γ ∈ Γ ∧ γ * y ∈ A}.ncard : ℕ) : ℝ) ≤ M) :
    ∫⁻ x in A, h x ∂μ ≤ ENNReal.ofReal M * ∫⁻ x in 𝓕, h x ∂μ := by
  classical
  rw [← lintegral_indicator hA, h𝓕.lintegral_eq_tsum'' (A.indicator h), ← lintegral_tsum, ← lintegral_const_mul _ hm]
  · refine lintegral_mono fun y => ?_
    obtain ⟨hfin, hle⟩ := hM y
    have hfin' : {γ : Γ | (γ : G) * y ∈ A}.Finite := by
      refine Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn
      rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ.2, hγ⟩
    have hcard : hfin'.toFinset.card = {γ : G | γ ∈ Γ ∧ γ * y ∈ A}.ncard := by
      rw [← Set.ncard_eq_toFinset_card _ hfin', ← Set.ncard_image_of_injective _ Subtype.val_injective]
      congr 1
      ext g
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨γ.2, hγ⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨g, h1⟩, h2, rfl⟩
    rw [tsum_eq_sum (s := hfin'.toFinset)]
    · have : ∀ γ ∈ hfin'.toFinset, A.indicator h (γ • y) = h y := by
        intro γ hγ
        have h1 : (γ : G) * y ∈ A := by simpa using hγ
        change A.indicator h ((γ : G) * y) = h y
        rw [Set.indicator_of_mem h1, hinv _ γ.2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard]
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hle
    · intro γ hγ
      have h1 : (γ : G) * y ∉ A := by simpa using hγ
      change A.indicator h ((γ : G) * y) = 0
      exact Set.indicator_of_notMem h1 _
  · intro γ
    exact ((hm.indicator hA).comp (measurable_const_mul (γ : G))).aemeasurable

theorem lintegral_enorm_sq {Q : Type} [MeasurableSpace Q] (ν : Measure Q) (F : Lp ℂ 2 ν) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖F‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := ν) (p := 2) (by norm_num)
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)]
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  exact h.symm

theorem sum_sq_le {α : Type} (S : List α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (S.map fun a => f a ^ 2).sum ≤ (S.map f).sum ^ 2 := by
  induction S with
  | nil => simp
  | cons a S ih =>
    have : 0 ≤ (S.map f).sum := List.sum_nonneg (by simpa using fun a _ => hf a)
    simp only [List.map_cons, List.sum_cons]
    nlinarith [hf a, mul_nonneg (hf a) this]

theorem integral_le_of_count {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Q] (μ : Measure G) [μ.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (π : G → Q) (hmk : Measurable π)
    (hπ : ∀ γ ∈ Γ, ∀ g, π (γ * g) = π g) {Ω : Set G} (hΩ : IsCompact Ω) (z : G) (M : ℝ)
    (hM : ∀ y, {γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o}.ncard : ℕ) : ℝ) ≤ M)
    (F : Lp ℂ 2 ((μ.restrict 𝓕).map π)) (φ : G → ℂ) (hφ : Continuous φ) (hr : ∀ᵐ x ∂μ, F (π x) = φ x) :
    ∫ x in Ω, ‖φ (z * x)‖ ^ 2 ∂μ ≤ M ^ 2 * ‖F‖ ^ 2 := by
  have hFm : Measurable fun x => ‖F x‖ₑ ^ 2 := (Lp.stronglyMeasurable F).measurable.enorm.pow_const 2
  have hA : IsCompact ((fun o => z * o) '' Ω) := hΩ.image (continuous_const_mul z)
  have key := lintegral_le_of_count μ Γ h𝓕 hA.measurableSet (hFm.comp hmk)
    (fun γ hγ g => by simp only [Function.comp, hπ γ hγ g]) (M ^ 2) (fun y => by
      have e : {γ : G | γ ∈ Γ ∧ γ * y ∈ (fun o => z * o) '' Ω} = {γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o} :=
        Set.ext fun γ => and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ => eq_comm
      rw [e]
      refine ⟨(hM y).1, ?_⟩
      have h1 := (hM y).2
      generalize Set.ncard _ = n at h1
      have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) n
      exact h2.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) h1 2))
  have e1 : ∫⁻ x in 𝓕, ((fun x => ‖F x‖ₑ ^ 2) ∘ π) x ∂μ = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [← lintegral_enorm_sq]
    exact (lintegral_map hFm hmk).symm
  have e2 : ∫⁻ x in (fun o => z * o) '' Ω, ((fun x => ‖F x‖ₑ ^ 2) ∘ π) x ∂μ =
      ∫⁻ x in Ω, ‖φ (z * x)‖ₑ ^ 2 ∂μ := by
    rw [((measurePreserving_mul_left μ z).setLIntegral_comp_emb (measurableEmbedding_mulLeft z)
      (fun x => ‖φ x‖ₑ ^ 2) Ω)]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hr] with x hx
    simp only [Function.comp, hx]
  rw [e1, e2, ← ENNReal.ofReal_mul (sq_nonneg _)] at key
  have hc : Continuous fun x => ‖φ (z * x)‖ ^ 2 := (hφ.comp (continuous_const_mul z)).norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _) hc.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_of_eq_of_le ?_ key)
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem le_of_sums {α : Type} (S : List α) (I f : α → ℝ) (a C₁ C₂ n : ℝ) (N : ℕ) (hn : 0 ≤ n)
    (hI : ∀ l, 0 ≤ I l) (hf : ∀ l, 0 ≤ f l) (h1 : a ^ 2 ≤ C₁ * (S.map I).sum)
    (h2 : ∀ l ∈ S, I l ≤ (C₂ * n ^ N) ^ 2 * f l ^ 2) : a ≤ √|C₁| * |C₂| * n ^ N * (S.map f).sum := by
  have h2' : (S.map I).sum ≤ (S.map fun l => (C₂ * n ^ N) ^ 2 * f l ^ 2).sum := List.sum_le_sum h2
  rw [List.sum_map_mul_left] at h2'
  have h3 := sum_sq_le S f hf
  have h0 : 0 ≤ (S.map I).sum := List.sum_nonneg (by simpa using fun a _ => hI a)
  have hT : 0 ≤ (S.map f).sum := List.sum_nonneg (by simpa using fun a _ => hf a)
  refine le_of_sq_le_sq ?_ (by positivity)
  have e : (√|C₁| * |C₂| * n ^ N * (S.map f).sum) ^ 2 = |C₁| * ((C₂ * n ^ N) ^ 2 * (S.map f).sum ^ 2) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    ring
  rw [e]
  refine h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) h0).trans ?_)
  exact mul_le_mul_of_nonneg_left (h2'.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))) (abs_nonneg _)

variable {D : D7}

theorem integral_le_adelic (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hp : FinPair V μ 𝓕)
    {Ω : Set (GA D V)} (hΩ : IsCompact Ω) (z : GA D V) (M : ℝ)
    (hM : ∀ y, {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = z * o}.Finite ∧
      (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = z * o}.ncard : ℕ) : ℝ) ≤ M)
    (F : Lp ℂ 2 (nuQ V μ 𝓕)) (φ : GA D V → ℂ) (hφ : Continuous φ) (hr : Repr V μ 𝓕 F φ) :
    ∫ x in Ω, ‖φ (z * x)‖ ^ 2 ∂μ ≤ M ^ 2 * ‖F‖ ^ 2 := by
  obtain ⟨-, -, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := hp.haar
  exact integral_le_of_count μ (GQ V) hp.fd (autMk V) measurable_quotient_mk''
    (fun γ hγ g => Quotient.sound (QuotientGroup.rightRel_apply.2 (by
      rw [_root_.mul_inv_rev, mul_inv_cancel_left]
      exact (GQ V).inv_mem hγ))) hΩ z M hM F φ hφ hr

theorem level_of_repr (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    {ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))} (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ)
    {F : Lp ℂ 2 (nuQ V μ 𝓕)} {ψ : GA D V → ℂ} (hψ : Continuous ψ) (hr : Repr V μ 𝓕 F ψ) {k : GA D V} (hk : ρ k F = F)
    (g : GA D V) : ψ (g * k) = ψ g := by
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, huniq, -, htr, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  have h1 := htr F ψ k hr
  rw [hk] at h1
  exact congrFun (huniq F (rTr V k ψ) ψ (hψ.comp (continuous_mul_const k)) hψ h1 hr) g

theorem normInf_nonneg (θ : InfFam D) (V : HSp D) (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf
  positivity

theorem pointwise_growth : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ (N : ℕ) (S : List (List (D.what₂.Tau × Mt V.rank))), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ ∀ x, ∃ C : ℝ, ∀ F ψ, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → Continuous ψ → Repr V μ 𝓕 F ψ → ∀ u ∈ GinfC V, ‖ψ (x * u)‖ ≤ C * normInf θ V u ^ N * (S.map fun l => ‖l.foldr (dL2 θ V ρ) F‖).sum := by
  intro D θ V hθ μ 𝓕 ρ hp hρ U hU
  obtain ⟨S, Ω, C₁, hS, hΩ, hsob⟩ := GlobalTheory.T.local_sobolev_inequality_adelic_unitary D θ V hθ U hU μ hp.haar
  have hcount := GlobalTheory.T.ncard_rationalPoints_translatedCompact_le_pow D θ V hθ Ω hΩ
  refine hcount.elim fun N hN => ?_
  refine ⟨N, S, hS, fun x => ?_⟩
  refine (hN x).elim fun C₂ hC₂ => ?_
  refine ⟨√|C₁| * |C₂|, fun F ψ hF hlev hψ hr u hu => ?_⟩
  obtain ⟨ψ', hr', haut, hsm, hder⟩ := GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU F hF hlev
  have e : ψ' = ψ := (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.1 F ψ' ψ haut.cont hψ hr' hr
  subst e
  have h1 := hsob ψ' hψ (fun k hk hk' => level_of_repr V hp hρ hψ hr (hlev k hk hk')) (fun l hl => (hder l hl).1) hsm (x * u)
  have h2 := fun l hl => integral_le_adelic V hp hΩ (x * u) _ (hC₂ u hu) _ _ (hder l (hS l hl)).1 (hder l (hS l hl)).2
  have h3 := le_of_sums S
    (fun l => ∫ o in Ω, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ') (x * u * o)‖ ^ 2 ∂μ)
    (fun l => ‖l.foldr (dL2 θ V ρ) F‖) ‖ψ' (x * u)‖ C₁ C₂ (normInf θ V u) N (normInf_nonneg θ V u)
    (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun _ => norm_nonneg _) h1 h2
  exact h3

end GlobalTheory.SobolevGrowth
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_bound_for_smooth_vectors : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ (N : ℕ) (S : List (List (D.what₂.Tau × Mt V.rank))), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ ∀ x, ∃ C : ℝ, ∀ F ψ, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → Continuous ψ → Repr V μ 𝓕 F ψ → ∀ u ∈ GinfC V, ‖ψ (x * u)‖ ≤ C * normInf θ V u ^ N * (S.map fun l => ‖l.foldr (dL2 θ V ρ) F‖).sum := by
  atlas_forward_decl GlobalTheory.SobolevGrowth.pointwise_growth
end

section
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.HolDict.ZClosed

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem exists_bound_orbit (Γ : Subgroup G) [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ x : G, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) ≤ N := by
  classical
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have hKK : IsCompact (K * K⁻¹) := hK.mul hK.inv
  have hfin : (((↑) : Γ → G) ⁻¹' (K * K⁻¹)).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKK).finite_of_discrete
  refine ⟨hfin.toFinset.card, fun x => ?_⟩
  by_cases h : ∃ γ₀ : Γ, γ₀⁻¹ • x ∈ K
  · obtain ⟨γ₀, h₀⟩ := h
    have hs : ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) =
        ∑ γ ∈ hfin.toFinset.image (fun δ => γ₀ * δ⁻¹), K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) := by
      refine tsum_eq_sum fun γ hγ => Set.indicator_of_notMem (fun hx => hγ ?_) _
      refine Finset.mem_image.2 ⟨γ⁻¹ * γ₀, ?_, by group⟩
      rw [Set.Finite.mem_toFinset]
      refine ⟨_, hx, _, Set.inv_mem_inv.2 h₀, ?_⟩
      simp only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hs]
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun γ _ =>
      Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)) ?_
    simp only [nsmul_eq_mul, mul_one, Nat.cast_le]
    exact Finset.card_image_le
  · push_neg at h
    simp only [Set.indicator_of_notMem (h _), tsum_zero, zero_le]

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

theorem exists_lintegral_le (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {K : Set G} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ f : G → ℝ≥0∞, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      ∫⁻ x in K, f x ∂μ ≤ N * ∫⁻ x in 𝓕, f x ∂μ := by
  obtain ⟨N, hN⟩ := exists_bound_orbit Γ hK
  refine ⟨N, fun f hf hinv => ?_⟩
  have hKm := hK.measurableSet
  rw [← lintegral_indicator hKm, h𝓕.lintegral_eq_tsum', ← lintegral_tsum, ← lintegral_const_mul _ hf]
  · refine lintegral_mono fun x => ?_
    have : ∀ γ : Γ, K.indicator f (γ⁻¹ • x) = K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) * f x := by
      intro γ
      by_cases h : γ⁻¹ • x ∈ K
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
        exact hinv _ (γ⁻¹).2 x
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    simp only [this]
    rw [ENNReal.tsum_mul_right]
    exact mul_le_mul_left (hN x) _
  · intro γ
    exact ((hf.indicator hKm).comp (measurable_const_mul ((γ⁻¹ : Γ) : G))).aemeasurable

theorem lintegral_average_le (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] {X : Type} [MeasurableSpace X]
    (m : Measure X) [IsFiniteMeasure m] {j : X → G} (hj : Measurable j) {K Ω : Set G}
    (hΩ : IsCompact Ω) (hm : ∀ᵐ z ∂m, j z ∈ K) {h : G → ℂ} (hh : Continuous h) :
    ∫⁻ g in Ω, ‖∫ z, h (j z * g) ∂m‖ₑ ∂μ ≤ m Set.univ * ∫⁻ x in K * Ω, ‖h x‖ₑ ∂μ := by
  have hmeas : Measurable fun p : G × X => ‖h (j p.2 * p.1)‖ₑ :=
    hh.enorm.measurable.comp ((hj.comp measurable_snd).mul measurable_fst)
  calc _ ≤ ∫⁻ g in Ω, ∫⁻ z, ‖h (j z * g)‖ₑ ∂m ∂μ := lintegral_mono fun g => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ z, ∫⁻ g in Ω, ‖h (j z * g)‖ₑ ∂μ ∂m := lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ ∫⁻ _z, ∫⁻ x in K * Ω, ‖h x‖ₑ ∂μ ∂m := by
        refine lintegral_mono_ae (hm.mono fun z hz => ?_)
        have e := (measurePreserving_mul_left μ (j z)).setLIntegral_comp_emb
          (MeasurableEquiv.mulLeft (j z)).measurableEmbedding (fun x => ‖h x‖ₑ) Ω
        refine (le_of_eq e).trans (lintegral_mono_set ?_)
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨_, hz, _, hg, rfl⟩
    _ = _ := by rw [lintegral_const, mul_comm]

theorem average_eq_zero_of_mem_closure [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) {Q : Type} [MeasurableSpace Q] {π : G → Q} (hπ : Measurable π)
    (ρ : G → Lp ℂ 2 ((μ.restrict 𝓕).map π) → Lp ℂ 2 ((μ.restrict 𝓕).map π))
    (hρ : ∀ g F, ∀ᵐ x ∂μ, ρ g F (π x) = F (π (x * g)))
    {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]
    {j : X → G} (hj : Continuous j) {s : Set X} (hs : IsCompact s) (hm : ∀ᵐ z ∂m, z ∈ s)
    {φ ψ : G → ℂ} {F₀ F : Lp ℂ 2 ((μ.restrict 𝓕).map π)}
    (hφ : Continuous φ) (hφΓ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (hφ0 : ∀ g, ∫ z, φ (j z * g) ∂m = 0)
    (hF₀ : ∀ᵐ x ∂μ, F₀ (π x) = φ x)
    (hψ : Continuous ψ) (hψΓ : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (hF : ∀ᵐ x ∂μ, F (π x) = ψ x)
    (hcl : F ∈ closure (Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀} : Set (Lp ℂ 2 ((μ.restrict 𝓕).map π))))
    (g₀ : G) : ∫ z, ψ (j z * g₀) ∂m = 0 := by
  have hms : m.restrict s = m := Measure.restrict_eq_self_of_ae_mem hm
  have hint : ∀ h : G → ℂ, Continuous h → ∀ g, Integrable (fun z => h (j z * g)) m := by
    intro h hh g
    rw [← hms]
    exact (hh.comp (hj.mul continuous_const)).continuousOn.integrableOn_compact hs
  have hspan : ∀ H ∈ Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀}, ∃ h : G → ℂ, Continuous h ∧
      (∀ γ ∈ Γ, ∀ g, h (γ * g) = h g) ∧ (∀ g, ∫ z, h (j z * g) ∂m = 0) ∧ ∀ᵐ x ∂μ.restrict 𝓕, H (π x) = h x := by
    intro H hH
    induction hH using Submodule.span_induction with
    | mem H hH =>
      obtain ⟨u, rfl⟩ := hH
      refine ⟨fun x => φ (x * u), hφ.comp (continuous_id.mul continuous_const), fun γ hγ g => ?_, fun g => ?_,
        ae_restrict_of_ae ?_⟩
      · simp only [mul_assoc, hφΓ γ hγ]
      · simp only [mul_assoc, hφ0]
      · filter_upwards [hρ u F₀, (measurePreserving_mul_right μ u).quasiMeasurePreserving.ae hF₀] with x h1 h2
        rw [h1, h2]
    | zero =>
      refine ⟨0, continuous_const, fun _ _ _ => rfl, fun g => by simp, ?_⟩
      exact ae_of_ae_map hπ.aemeasurable (Lp.coeFn_zero ℂ 2 _)
    | add H H' _ _ h1 h2 =>
      obtain ⟨h, hc, hi, h0, ha⟩ := h1
      obtain ⟨h', hc', hi', h0', ha'⟩ := h2
      refine ⟨h + h', hc.add hc', fun γ hγ g => by simp only [Pi.add_apply, hi γ hγ, hi' γ hγ], fun g => ?_, ?_⟩
      · simp only [Pi.add_apply]
        rw [integral_add (hint h hc g) (hint h' hc' g), h0, h0', add_zero]
      · filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_add H H'), ha, ha'] with x e1 e2 e3
        rw [e1, Pi.add_apply, Pi.add_apply, e2, e3]
    | smul a H _ h1 =>
      obtain ⟨h, hc, hi, h0, ha⟩ := h1
      refine ⟨a • h, hc.const_smul a, fun γ hγ g => by simp only [Pi.smul_apply, hi γ hγ], fun g => ?_, ?_⟩
      · simp only [Pi.smul_apply]
        rw [integral_smul, h0, smul_zero]
      · filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_smul a H), ha] with x e1 e2
        rw [e1, Pi.smul_apply, Pi.smul_apply, e2]
  obtain ⟨Ω, hΩ, hg₀⟩ := exists_compact_mem_nhds g₀
  have hK : IsCompact (j '' s) := hs.image hj
  obtain ⟨N, hN⟩ := exists_lintegral_le Γ μ h𝓕 (hK.mul hΩ)
  set c : ℝ≥0∞ := m Set.univ * (N * μ 𝓕 ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) with hc
  have hc' : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_)
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hfin
    norm_num
  have hbd : ∀ H ∈ (Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀} : Set (Lp ℂ 2 ((μ.restrict 𝓕).map π))),
      ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - H‖ₑ := by
    intro H hH
    obtain ⟨h, hh, hi, h0, ha⟩ := hspan H hH
    have hd : Continuous (ψ - h) := hψ.sub hh
    have e1 : ∀ g, ∫ z, ψ (j z * g) ∂m = ∫ z, (ψ - h) (j z * g) ∂m := by
      intro g
      simp only [Pi.sub_apply]
      rw [integral_sub (hint ψ hψ g) (hint h hh g), h0, sub_zero]
    simp only [e1]
    refine (lintegral_average_le μ m hj.measurable hΩ (K := j '' s)
      (hm.mono fun z hz => Set.mem_image_of_mem j hz) hd).trans ?_
    rw [hc, mul_assoc, mul_assoc]
    refine mul_le_mul_right ((hN _ hd.enorm.measurable fun γ hγ g => ?_).trans (mul_le_mul_right ?_ _)) _
    · simp only [Pi.sub_apply, hψΓ γ hγ, hi γ hγ]
    · rw [← eLpNorm_one_eq_lintegral_enorm]
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (q := 2) one_le_two hd.aestronglyMeasurable).trans ?_
      rw [Measure.restrict_apply_univ, mul_comm, Lp.enorm_def,
        eLpNorm_map_measure (Lp.aestronglyMeasurable _) hπ.aemeasurable]
      refine le_of_eq (congrArg _ (eLpNorm_congr_ae ?_))
      filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_sub F H), ha, ae_restrict_of_ae hF] with x e1 e2 e3
      rw [Function.comp_apply, e1, Pi.sub_apply, Pi.sub_apply, e2, e3]
  have hz : ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ = 0 := by
    have hcont : Continuous fun H : Lp ℂ 2 ((μ.restrict 𝓕).map π) => c * ‖F - H‖ₑ :=
      (ENNReal.continuous_const_mul hc').comp (continuous_const.sub continuous_id).enorm
    have : ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - F‖ₑ :=
      closure_minimal (t := {H | ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - H‖ₑ}) hbd
        (isClosed_le continuous_const hcont) hcl
    simpa using this
  have hC : Continuous fun g => ∫ z, ψ (j z * g) ∂m := by
    have := continuous_parametric_integral_of_continuous (μ := m) (f := fun g z => ψ (j z * g))
      (hψ.comp ((hj.comp continuous_snd).mul continuous_fst)) hs
    rwa [hms] at this
  rw [lintegral_eq_zero_iff hC.enorm.measurable] at hz
  have hz' : (fun g => ∫ z, ψ (j z * g) ∂m) =ᵐ[μ.restrict (interior Ω)] fun _ => 0 := by
    refine ae_restrict_of_ae_restrict_of_subset interior_subset (hz.mono fun g hg => ?_)
    simpa using hg
  exact Measure.eqOn_open_of_ae_eq hz' isOpen_interior hC.continuousOn continuousOn_const
    (mem_interior_iff_mem_nhds.2 hg₀)

end Abstract

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem zcusp_of_mem_closure : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (φ ψ : GA D V → ℂ) F₀ F, IsAutFun V φ → ZCusp V φ → Repr V μ 𝓕 F₀ φ → IsAutFun V ψ → Repr V μ 𝓕 F ψ → F ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set (Lp ℂ 2 (nuQ V μ 𝓕))) → ZCusp V ψ := by
  intro D θ V hθ μ 𝓕 ρ hP hρ φ ψ F₀ F hφ hφ0 hF₀ hψ hF hcl ξ hξ ν 𝓖 hν h𝓖 g
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨ν₀, 𝓖₀, hν₀, h𝓖₀, hc⟩ := (GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ ξ hξ).1
  have hZ : IsClosed (ZI V ξ : Set (GA D V)) := (GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed D θ V hθ ξ hξ).2.1
  haveI : LocallyCompactSpace (ZI V ξ) := hZ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Countable ((GQ V).subgroupOf (ZI V ξ)) :=
    Function.Injective.countable (f := fun x : (GQ V).subgroupOf (ZI V ξ) => (⟨x.1.1, x.2⟩ : GQ V))
      fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : GQ V => (t : GA D V)) h))
  haveI : SecondCountableTopology (ZI V ξ) := TopologicalSpace.Subtype.secondCountableTopology (ZI V ξ : Set (GA D V))
  have h₁ : IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓖₀ ν :=
    h𝓖₀.mono (Measure.absolutelyContinuous_isHaarMeasure ν ν₀)
  haveI := hP.haar
  haveI := hP.right
  haveI : IsFiniteMeasure (ν.restrict 𝓖₀) :=
    isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hc.measure_lt_top).ne
  rw [h𝓖.setIntegral_eq h₁ (f := fun z : ZI V ξ => ψ ((z : GA D V) * g)) fun γ z => by
    have := hψ.left γ.1.1 γ.2 (z.1 * g)
    rw [← mul_assoc] at this
    exact this]
  exact average_eq_zero_of_mem_closure (GQ V) μ hP.fd hP.fin (π := autMk V) measurable_quotient_mk'' (fun u H => ρ u H)
    hρ.val (ν.restrict 𝓖₀) continuous_subtype_val hc
    ((ae_restrict_mem₀ h₁.nullMeasurableSet).mono fun z hz => subset_closure hz)
    hφ.cont hφ.left (hφ0 ξ hξ ν 𝓖₀ hν h₁) hF₀ hψ.cont hψ.left hF hcl g

end GlobalTheory.HolDict.ZClosed
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidality_preserved_in_closure : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (φ ψ : GA D V → ℂ) F₀ F, IsAutFun V φ → ZCusp V φ → Repr V μ 𝓕 F₀ φ → IsAutFun V ψ → Repr V μ 𝓕 F ψ → F ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set (Lp ℂ 2 (nuQ V μ 𝓕))) → ZCusp V ψ := by
  atlas_forward_decl GlobalTheory.HolDict.ZClosed.zcusp_of_mem_closure
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.BackForm

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem coe_update (y : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    (fun ρ => ((Function.update y τ w ρ : M.sm ρ) : M.H ρ)) = Function.update (fun ρ => (y ρ : M.H ρ)) τ (w : M.H τ) := by
  funext ρ
  by_cases h : ρ = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem word_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
    ∃ y', l.foldr (fun p f => Rder θ V p.1 p.2 f) (T y) = T y' := by
  induction l with
  | nil => exact ⟨y, rfl⟩
  | cons p l ih =>
    obtain ⟨y', h⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    exact ⟨_, by rw [List.foldr_cons, h]; exact hT y' p.1 p.2 hp ⟨_, hsm _ _ hp (y' p.1)⟩ rfl⟩

theorem rderC_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (w : M.sm τ) :
    ∃ w' : M.sm τ, (w' : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z w ∧
      RderC θ V τ Z (T (Function.update y τ w)) = T (Function.update y τ w') := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  refine ⟨⟨_, hsm τ _ h1 w⟩ + Complex.I • ⟨_, hsm τ _ h2 w⟩, rfl, ?_⟩
  rw [T.map_update_add, T.map_update_smul, RderC,
    hT (Function.update y τ w) τ _ h1 ⟨_, hsm τ _ h1 w⟩ (by simp),
    hT (Function.update y τ w) τ _ h2 ⟨_, hsm τ _ h2 w⟩ (by simp), Function.update_idem, Function.update_idem]

theorem wordC_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (Zs : List (Mt V.rank)) (w : M.sm τ) :
    ∃ w' : M.sm τ, (w' : M.H τ) = (Zs.map (dRepC (gramAt D V τ) (M.rep τ))).foldr (fun f acc => f acc) (w : M.H τ) ∧
      (Zs.map (RderC θ V τ)).foldr (fun f acc => f acc) (T (Function.update y τ w)) = T (Function.update y τ w') := by
  induction Zs with
  | nil => exact ⟨w, rfl, rfl⟩
  | cons Z Zs ih =>
    obtain ⟨w', h1, h2⟩ := ih
    obtain ⟨w'', h3, h4⟩ := rderC_value T hsm hT y τ Z w'
    refine ⟨w'', ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1, h3]
    · rw [List.map_cons, List.foldr_cons, h2, h4]

theorem gelf_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (k : ℕ) (c : ℂ) (w : M.sm τ)
    (hc : gelfRep (gramAt D V τ) (M.rep τ) k (w : M.H τ) = c • (w : M.H τ)) :
    gelf θ V τ k (T (Function.update y τ w)) = c • T (Function.update y τ w) := by
  choose W h1 h2 using fun idx : Fin (k + 1) → Fin V.rank =>
    wordC_value T hsm hT y τ (List.ofFn fun a : Fin (k + 1) => (Matrix.single (idx a) (idx (a + 1)) 1 : Mt V.rank)) w
  simp only [List.map_ofFn] at h1 h2
  have e : ∑ idx, W idx = c • w := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul, ← hc, gelfRep]
    exact Finset.sum_congr rfl fun idx _ => h1 idx
  rw [← T.map_update_smul, ← e, T.map_update_sum, gelf]
  exact Finset.sum_congr rfl fun idx _ => h2 idx

theorem zfin_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (hc : ∀ τ k, ∃ c : ℂ, ∀ w : M.sm τ, gelfRep (gramAt D V τ) (M.rep τ) k (w : M.H τ) = c • (w : M.H τ))
    (y : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ T y ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨Submodule.span ℂ {T y}, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := hc τ k
  have e : a • T y = T (Function.update y τ (a • y τ)) := by rw [T.map_update_smul, Function.update_eq_self]
  have := gelf_value T hsm hT y τ k c (a • y τ) (hc _)
  rw [← e] at this
  rw [this]
  exact Submodule.smul_mem _ _ hf

def lettersAt (τ : D.what₂.Tau) (l : List (D.what₂.Tau × Mt V.rank)) : List (Mt V.rank) :=
  (l.filter fun p => p.1 = τ).map Prod.snd

theorem lettersAt_mem {τ : D.what₂.Tau} {l : List (D.what₂.Tau × Mt V.rank)} (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    ∀ X ∈ lettersAt τ l, X ∈ lieAt V τ := by
  intro X hX
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hX
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hp
  have h3 : p.1 = τ := by simpa using h2
  exact h3 ▸ hl p h1

theorem word_mem (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    {τ : D.what₂.Tau} (l : List (Mt V.rank)) (hl : ∀ X ∈ l, X ∈ lieAt V τ) (w : M.sm τ) :
    l.foldr (dRep (M.rep τ)) (w : M.H τ) ∈ M.sm τ := by
  induction l with
  | nil => exact w.2
  | cons X l ih => exact hsm τ X (hl X List.mem_cons_self) ⟨_, ih fun q hq => hl q (List.mem_cons_of_mem _ hq)⟩

theorem word_map {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hΦ : ∀ (v : M.Vec) τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) =
      Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))))
    (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
    l.foldr (dL2 θ V ρ) (Φ fun τ => (y τ : M.H τ)) =
      Φ fun τ => (lettersAt τ l).foldr (dRep (M.rep τ)) (y τ : M.H τ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [List.foldr_cons, ih hl']
    have := hΦ (fun τ => ⟨_, word_mem hsm _ (lettersAt_mem hl') (y τ)⟩) p.1 p.2 (hl p List.mem_cons_self)
    refine this.trans ?_
    congr 1
    funext τ
    by_cases h : τ = p.1
    · subst h; simp [lettersAt]
    · have h' : ¬ p.1 = τ := fun e => h e.symm
      simp [lettersAt, Function.update_of_ne h, List.filter_cons, h']

theorem sum_bound {α β : Type} (a b : α → β → ℝ) (hb : ∀ l w, 0 ≤ b l w) (L : List α)
    (h : ∀ l ∈ L, ∃ c, ∀ w, a l w ≤ c * b l w) :
    ∃ C, 0 ≤ C ∧ ∀ w, (L.map fun l => a l w).sum ≤ C * (L.map fun l => b l w).sum := by
  induction L with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons l L ih =>
    obtain ⟨C, hC, ih⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨c, hc⟩ := h l List.mem_cons_self
    refine ⟨max c C, le_max_of_le_right hC, fun w => ?_⟩
    have h0 : 0 ≤ (L.map fun l => b l w).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
      exact hb q w)
    simp only [List.map_cons, List.sum_cons, mul_add]
    exact add_le_add ((hc w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hb l w)))
      ((ih w).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) h0))

theorem cont_value {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K) (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hΦ : ∀ (v : M.Vec) τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) =
      Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))))
    (L : List (List (D.what₂.Tau × Mt V.rank))) (hL : ∀ l ∈ L, ∀ p ∈ l, p.2 ∈ lieAt V p.1) (x : GA D V) (C : ℝ)
    (hC : ∀ y : M.Vec, ‖T y x‖ ≤ C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y τ : M.H τ))‖).sum)
    (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := by
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ((LinearMap.proj x : (GA D V → ℂ) →ₗ[ℂ] ℂ) ∘ₗ T.toLinearMap v τ)
  have hℓ' : ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := fun w => LinearMap.congr_fun hℓ w
  refine ⟨ℓ, ?_, hℓ'⟩
  obtain ⟨C', hC', hb⟩ := sum_bound
    (fun l (w : M.sm τ) => ‖l.foldr (dL2 θ V ρ) (Φ fun σ => ((Function.update v τ w σ : M.sm σ) : M.H σ))‖)
    (fun l (w : M.sm τ) => ‖(lettersAt τ l).foldr (dRep (M.rep τ)) (w : M.H τ)‖) (fun _ _ => norm_nonneg _) L (by
      intro l hl
      refine ⟨‖Φ.toContinuousLinearMap (fun σ => (lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)) τ‖, fun w => ?_⟩
      refine le_trans (le_of_eq ?_) (ContinuousLinearMap.le_opNorm _ _)
      rw [word_map ρ Φ hsm hΦ l (hL l hl), ContinuousMultilinearMap.toContinuousLinearMap_apply]
      congr 2
      funext σ
      by_cases h : σ = τ
      · subst h; simp
      · simp [Function.update_of_ne h])
  refine ⟨L.map (lettersAt τ), |C| * C', ?_, fun w hw => ?_⟩
  · intro l hl
    obtain ⟨l', h', rfl⟩ := List.mem_map.1 hl
    exact lettersAt_mem (hL l' h')
  · have hw' : w ∈ M.sm τ := Submodule.subset_span hw
    have h1 := hℓ' ⟨w, hw'⟩
    have h2 := hb ⟨w, hw'⟩
    have h3 := hC (Function.update v τ ⟨w, hw'⟩)
    rw [List.map_map, mul_assoc]
    simp only at h1
    rw [h1]
    refine h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (List.sum_nonneg ?_)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    intro x hx
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _

theorem continuous_rTr (k : GA D V) {f : GA D V → ℂ} (hf : Continuous f) : Continuous (rTr V k f) := by
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact hf.comp (continuous_mul_const k)

section L2

variable {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))}

theorem repr_add (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {F F' ψ ψ'} (h : Repr V μ 𝓕 F ψ) (h' : Repr V μ 𝓕 F' ψ') :
    Repr V μ 𝓕 (F + F') (ψ + ψ') := by
  simpa using (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.2.2.2.1 F F' ψ ψ' 1 h h'

theorem repr_smul (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) (a : ℂ) {F ψ} (h : Repr V μ 𝓕 F ψ) :
    Repr V μ 𝓕 (a • F) (a • ψ) := by
  have := (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.2.2.2.1 F F ψ ψ (a - 1) h h
  rwa [sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel] at this

theorem eig_closure {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (A : Set K) (k : GA D V) (c : ℂ) (hA : ∀ z ∈ A, ρ k z = c • z) {F : K}
    (hF : F ∈ closure (Submodule.span ℂ A : Set K)) : ρ k F = c • F := by
  have h1 : (Submodule.span ℂ A : Set K) ⊆ {z | ρ k z = c • z} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hA x hx
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add, hx, hy, smul_add]
    | smul a x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [map_smul, hx, smul_comm]
  exact closure_minimal h1 (isClosed_eq (ρ k).continuous (continuous_const_smul c)) hF

theorem exists_map_abs {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ρ : GA D V →* (K →L[ℂ] K)) {v : M.Vec} (hθ : IsInfFam θ) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1)
    (hiso : ∀ g F, ‖ρ g F‖ = ‖F‖) (F₀ : K)
    (hco : ∀ u ∈ GinfC V, ⟪F₀, ρ u F₀⟫_ℂ =
      ((‖F₀‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H K, (Φ fun τ => (v τ : M.H τ)) = F₀ ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
        Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) ∧
      (∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set K)) ∧
      ∀ k ∈ GfC V, ∀ c : ℂ, ρ k F₀ = c • F₀ → ∀ y, ρ k (Φ y) = c • Φ y := by
  obtain ⟨L, hL1, hL2, -, -, -, hL3, -, hL4, hL5⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have h1 : (1 : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V) := fun τ => by simp [Formalism.QuantumDeterminants.UH]
  have hone : L 1 = 1 := by
    have := hL2 1 h1 1 h1
    rw [mul_one] at this
    exact mul_eq_left.1 this.symm
  have a1 : ρ (L 1) = 1 := by rw [hone, map_one]
  have a2 : ∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), ρ (L (u * u')) = ρ (L u) * ρ (L u') :=
    fun u hu u' hu' => by rw [hL2 u hu u' hu', map_mul]
  have a3 : ∀ u ∈ UG (gramAt D V), ⟪F₀, ρ (L u) F₀⟫_ℂ =
      ((‖F₀‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ := fun u hu => by
    rw [hco (L u) (hL1 u hu).1]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [(hL1 u hu).2 τ]
  obtain ⟨Φ, e1, e2, e3⟩ := GlobalTheory.T.exists_equivariant_multilinear_of_matrixCoeff_eq_unitaryProduct V.rank D.what₂.Tau (gramAt D V) M.H M.rep K
    (fun u => ρ (L u)) (fun τ => (v τ : M.H τ)) F₀
    (fun τ => ⟨(hL5 τ).2, (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1, (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.1, hv τ⟩)
    a1 a2 (fun u _ y => hiso _ y) a3
  refine ⟨Φ, e1, fun τ g hg y => ?_, fun y => ?_, fun k hk c h0 y => ?_⟩
  · rw [hL3 τ g hg]; exact e2 τ g hg y
  · refine closure_mono (Submodule.span_mono ?_) (e3 y)
    rintro z ⟨u, -, hz⟩
    exact ⟨_, hz⟩
  · refine eig_closure ρ _ k c ?_ (e3 y)
    rintro z ⟨u, hu, hz⟩
    have : ρ k (ρ (L u) F₀) = ρ (L u) (ρ k F₀) := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, hL4 k hk _ (hL1 u hu).1, map_mul, ContinuousLinearMap.mul_apply]
    rw [hz, this, h0, map_smul]

theorem eig_class (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {φ : GA D V → ℂ}
    {F₀ : Lp ℂ 2 (nuQ V μ 𝓕)} (hF : Repr V μ 𝓕 F₀ φ) (k : GA D V) (c : ℂ) (hc : ∀ g, φ (g * k) = c * φ g) :
    ρ k F₀ = c • F₀ := by
  have hr := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  have h := hr.2.2.2.1 F₀ φ k hF
  have e : rTr V k φ = c • φ := funext hc
  rw [e] at h
  have h3 := hr.2.2.1 _ _ _ h (repr_smul hp hρ c hF)
  exact h3

theorem exists_map {w : D.what₂.Tau → Fin V.rank → ℤ} {v : M.Vec} (hθ : IsInfFam θ) (hs : HolShape M) (hw : WtIs M w)
    (hv : IsExtVec M v) (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {J : Set (GA D V)} {χ φ : GA D V → ℂ}
    (hφ : HolForm θ M w J χ φ) {F₀ : Lp ℂ 2 (nuQ V μ 𝓕)} (hF : Repr V μ 𝓕 F₀ φ) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H (Lp ℂ 2 (nuQ V μ 𝓕)), (Φ fun τ => (v τ : M.H τ)) = F₀ ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
        Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) ∧
      (∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set (Lp ℂ 2 (nuQ V μ 𝓕)))) ∧
      ∀ k ∈ GfC V, ∀ c : ℂ, (∀ g, φ (g * k) = c * φ g) → ∀ y, ρ k (Φ y) = c • Φ y := by
  have h1 := GlobalTheory.T.inner_rho_eq_normSq_mul_prod_of_holForm D θ V S M w v hθ hs hw hv μ 𝓕 ρ hp hρ J χ φ F₀ hφ hF
  have h2 := exists_map_abs (K := Lp ℂ 2 (nuQ V μ 𝓕)) (M := M) (v := v) ρ hθ (fun τ => (hv τ).1) hρ.iso F₀
  have h3 := h2 h1
  refine h3.imp fun Φ h => ⟨h.1, h.2.1, h.2.2.1, fun k hk c hc => ?_⟩
  have h4 := eig_class hp hρ hF k c hc
  exact h.2.2.2 k hk c h4

end L2

set_option maxHeartbeats 1000000 in

theorem exists_multMap : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → (∃ μ 𝓕, FinPair V μ 𝓕) → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ), J ⊆ (GfC V : Set (GA D V)) → HolForm θ M w J χ φ → ZCusp V φ → ∃ T : MMap M, IsMultMap θ M J χ T ∧ T v = φ := by
  rintro D θ V S M w v hθ hs hw hv ⟨μ, 𝓕, hp⟩ J χ φ hJ hφ hZ
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.regular_representation_of_finite_pair D V μ 𝓕 hp
  obtain ⟨r1, r2, -, r4, -, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  obtain ⟨F₀, hF⟩ := r1 φ hφ.aut.cont hφ.aut.left hφ.bdd
  obtain ⟨Φ, e1, e2, e3, e4⟩ := exists_map hθ hs hw hv hp hρ hφ hF
  obtain ⟨U, hU, hUφ⟩ := hφ.aut.level
  have hfix : ∀ y, ∀ k ∈ U, k ∈ GfC V → ρ k (Φ y) = Φ y := fun y k hk hk' => by
    simpa using e4 k hk' 1 (fun g => by rw [hUφ k hk hk', one_mul]) y
  have hsmM := GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines D θ V hθ S M _ ρ Φ e2
  choose ψ p1 p2 p3 p4 using fun y : M.Vec =>
    GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU (Φ fun τ => (y τ : M.H τ)) (hsmM y).1 (hfix _)
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have hH : ∀ τ, (gramAt D V τ).IsHermitian := GlobalTheory.SmoothAutCheck.gramAt_herm V
  have hdet : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero
  have hsv := fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1
  have hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ := fun τ X hX w =>
    Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 X hX).1
  have uniq : ∀ (y : M.Vec) f, Continuous f → Repr V μ 𝓕 (Φ fun τ => (y τ : M.H τ)) f → ψ y = f :=
    fun y f hf h => r2 _ _ _ (p2 y).cont hf (p1 y) h
  let T : MMap M := MultilinearMap.mk' ψ
    (fun y τ a b => by
      refine uniq _ _ ((p2 _).cont.add (p2 _).cont) ?_
      have := repr_add hp hρ (p1 (Function.update y τ a)) (p1 (Function.update y τ b))
      rw [coe_update, coe_update, ← Φ.map_update_add] at this
      rw [coe_update]
      exact this)
    (fun y τ c a => by
      refine uniq _ _ ((p2 _).cont.const_smul c) ?_
      have := repr_smul hp hρ c (p1 (Function.update y τ a))
      rw [coe_update, ← Φ.map_update_smul] at this
      rw [coe_update]
      exact this)
  have hTψ : ∀ y, T y = ψ y := fun _ => rfl
  have hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w) := by
    intro y τ X hX w hw
    obtain ⟨q1, q2⟩ := p4 y [(τ, X)] (by simpa using hX)
    simp only [List.foldr_cons, List.foldr_nil] at q1 q2
    refine (uniq _ _ q1 ?_).symm
    rw [coe_update, hw, ← (hsmM y).2 τ X hX]
    exact q2
  obtain ⟨N, L, hL, hgr⟩ := GlobalTheory.T.sobolev_bound_for_smooth_vectors D θ V hθ μ 𝓕 ρ hp hρ U hU
  refine ⟨T, ⟨fun y => ⟨p2 y, p3 y, ?_, N, fun l hl x => ?_⟩, fun y => ?_, fun y k hk g => ?_, fun τ g hg y z hz => ?_,
    fun τ y x => ?_⟩, uniq v φ hφ.aut.cont (e1 ▸ hF)⟩
  · refine zfin_value T hsm hT (fun τ k => ?_) y
    obtain ⟨-, m1, m2, m3⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
    obtain ⟨k1, k2⟩ := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hs hw hv τ
    obtain ⟨c, hc⟩ := GlobalTheory.T.gelfand_invariants_act_by_scalars_highest_weight V.rank (gramAt D V τ) _ _ (w τ) (M.H τ) (M.rep τ) (m3 hs).1 m1 m2 (v τ)
      (by rw [← norm_ne_zero_iff, (hv τ).1]; exact one_ne_zero) k1 k2 k
    exact ⟨c, fun z => hc z ((hsv τ).1 z z.2)⟩
  · obtain ⟨y', hy'⟩ := word_value T hsm hT l hl y
    obtain ⟨C, hC⟩ := hgr x
    refine ⟨C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y' τ : M.H τ))‖).sum, fun g hg => ?_⟩
    rw [hy', mul_right_comm]
    exact hC _ _ (hsmM y').1 (hfix _) (p2 y').cont (p1 y') g hg
  · exact GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero D θ V hθ _ (p2 y)
      (GlobalTheory.T.cuspidality_preserved_in_closure D θ V hθ μ 𝓕 ρ hp hρ φ (ψ y) F₀ _ hφ.aut hZ hF (p2 y) (p1 y) (e3 _))
  · have h1 := r4 _ _ k (p1 y)
    rw [e4 k (hJ hk) (χ k) (hφ.lev k hk)] at h1
    have h2 := r2 _ _ _ (continuous_rTr k (p2 y).cont) ((p2 y).cont.const_smul (χ k)) h1
      (repr_smul hp hρ (χ k) (p1 y))
    exact congrFun h2 g
  · refine uniq _ _ (continuous_rTr (atTau θ V τ g) (p2 y).cont) ?_
    rw [coe_update, hz, e2 τ g hg]
    exact r4 _ _ _ (p1 y)
  · obtain ⟨C, hC⟩ := hgr x
    refine cont_value ρ Φ T hsm (fun y => (hsmM y).2) L hL x (C * normInf θ V 1 ^ N) (fun y => ?_) τ y
    have := hC _ _ (hsmM y).1 (hfix _) (p2 y).cont (p1 y) 1 (one_mem _)
    rwa [mul_one] at this

end GlobalTheory.BackForm
end
end
