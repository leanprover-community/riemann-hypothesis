import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRealPlacesMatrixCoefficientProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClosedParabolicSubgroups

section
section
open MeasureTheory

namespace GlobalTheory

theorem unfolding_cover_bound (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H]
    (μ : Measure H) [μ.IsMulLeftInvariant] (ι : H →* G) (hι : Function.Injective ι)
    (Γ : Subgroup G) [Countable Γ] (Kc : Set H)
    (hK : ∀ h, ∃ δ ∈ Γ.comap ι, δ * h ∈ Kc) (F : G → ENNReal)
    (hF : ∀ γ : G, Measurable fun h => F (γ * ι h)) :
    ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ
      ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ := by
  classical
  haveI hcH : Countable (Γ.comap ι) := by
    have : Function.Injective (fun δ : Γ.comap ι => (⟨ι δ, δ.2⟩ : Γ)) := by
      intro a b hab
      apply Subtype.ext
      apply hι
      simpa using congrArg Subtype.val hab
    exact this.countable
  have step : ∀ g : G, ∫⁻ h, F (g * ι h) ∂μ
      ≤ ∑' δ : Γ.comap ι, ∫⁻ k in Kc, F (g * ι ((δ:H)⁻¹) * ι k) ∂μ := by
    intro g
    have hcov : (Set.univ : Set H) = ⋃ δ : Γ.comap ι, (fun h => (δ:H) * h) ⁻¹' Kc := by
      ext h
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_preimage, true_iff]
      obtain ⟨δ, hδ, hδK⟩ := hK h
      exact ⟨⟨δ, hδ⟩, hδK⟩
    calc ∫⁻ h, F (g * ι h) ∂μ
        = ∫⁻ h in ⋃ δ : Γ.comap ι, (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ := by
          rw [← hcov, Measure.restrict_univ]
      _ ≤ ∑' δ : Γ.comap ι, ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ :=
          lintegral_iUnion_le _ _
      _ = ∑' δ : Γ.comap ι, ∫⁻ k in Kc, F (g * ι ((δ:H)⁻¹) * ι k) ∂μ := by
          congr 1; funext δ
          set e := MeasurableEquiv.mulLeft ((δ:H)⁻¹) with he
          have hmap : μ.map e = μ := by
            rw [MeasurableEquiv.coe_mulLeft]; exact map_mul_left_eq_self μ _
          have hpre : e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc) = Kc := by
            ext k; simp [e]
          calc ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ
              = ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂(μ.map e) := by rw [hmap]
            _ = ∫⁻ h, F (g * ι h) ∂((μ.restrict (e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc))).map e) := by
                rw [e.restrict_map]
            _ = ∫⁻ k, F (g * ι (e k)) ∂(μ.restrict (e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc))) :=
                lintegral_map_equiv _ _
            _ = _ := by rw [hpre]; simp [e, mul_assoc]
  haveI : Countable (Γ ⧸ ι.range.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  let φ : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι → Γ := fun p =>
    (p.1.out : Γ) * ⟨ι ((p.2 : H)⁻¹), by simpa using Γ.inv_mem p.2.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨q₁, δ₁⟩ ⟨q₂, δ₂⟩ h
    have hv := congrArg Subtype.val h
    simp only [φ, Subgroup.coe_mul] at hv
    have hq : q₁ = q₂ := by
      rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      refine ⟨(δ₁:H)⁻¹ * (δ₂:H), ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((q₁.out : Γ) : G)⁻¹ * ((q₂.out : Γ) : G)
          = ((q₁.out : Γ) : G)⁻¹ * (((q₂.out : Γ) : G) * ι ((δ₂:H)⁻¹)) * ι (δ₂:H) by
            rw [map_inv]; group, ← hv]
      simp only [map_mul, map_inv]; group
    subst hq
    have h2 : ι ((δ₁:H)⁻¹) = ι ((δ₂:H)⁻¹) := mul_left_cancel hv
    have h3 : (δ₁:H)⁻¹ = (δ₂:H)⁻¹ := hι h2
    simp only [Prod.mk.injEq, true_and]
    exact Subtype.ext (inv_injective h3)
  calc ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ
      ≤ ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∑' δ : Γ.comap ι,
          ∫⁻ k in Kc, F (((φ (q, δ)) : G) * ι k) ∂μ := by
        refine ENNReal.tsum_le_tsum fun q => ?_
        exact step _
    _ = ∑' p, ∫⁻ k in Kc, F ((φ p : G) * ι k) ∂μ := ENNReal.tsum_prod.symm
    _ = ∫⁻ k in Kc, ∑' p, F ((φ p : G) * ι k) ∂μ :=
        (lintegral_tsum fun p => (hF _).aemeasurable).symm
    _ ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ :=
        lintegral_mono fun k => ENNReal.tsum_comp_le_tsum_of_injective hφ (fun γ : Γ => F (γ * ι k))

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_unfolding_le_of_translate_cover : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (μ : Measure H) [μ.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (Kc : Set H), (∀ h, ∃ δ ∈ Γ.comap ι, δ * h ∈ Kc) → ∀ F : G → ENNReal, (∀ γ : G, Measurable fun h => F (γ * ι h)) → ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ := by
  atlas_forward_decl GlobalTheory.unfolding_cover_bound
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem GlobalTheory.PoinAut.partialSum_bdd : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (v : ∀ τ, M.H τ), KDecay M v → Nonempty D.what₂.Tau → ∀ (c : GA D V) (a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (Kc : Set (GA D V)), IsCompact Kc → ∃ B : ℝ, ∀ x ∈ Kc, ∀ s : Finset (GQ V), ∑ γ ∈ s, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * x)‖ ≤ B := by
  intro D θ hθ V S M Λ 𝔪 hΛ v hv _ c a Kc hK
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hKdef
  set N := 2 * V.rank ^ 2 + 1 with hN
  obtain ⟨C₀, A₀, hI⟩ := GlobalTheory.T.poincareSeries_unitary_absolutelyConvergent_moderateGrowth D θ hθ V Λ hΛ c
  obtain ⟨C, hC, hCb⟩ := GlobalTheory.PoinAut.coefR_le_majorant D θ hθ V S M v (fun τ => (a τ : M.H τ)) N
    (fun τ => (hv τ).2 _ (a τ).2)
  obtain ⟨H, hH⟩ := hK.exists_bound_of_continuousOn (GlobalTheory.Grow.continuous_height V).continuousOn
  set P : ℝ := ∏ τ, (1 + hsn (cmp θ τ (1 : GA D V)⁻¹)) ^ N with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg fun τ _ =>
    pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) _
  have hKtop : ∀ y, y ∈ K → y ∈ congLev D.sp.cm V.gram Λ ⊤ := fun y hy => by
    rw [congLev_top]; exact ⟨hy.1, hy.2.1⟩
  refine ⟨C * P * (max C₀ 0 * H ^ A₀), fun x hx s => ?_⟩
  have hterm : ∀ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
      ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖ ≤
        C * P * ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := by
    intro γ hγ
    unfold coef
    rw [if_pos (Finset.mem_filter.1 hγ).2]
    have := hCb (c * (γ : GA D V) * x) 1
    rwa [mul_one] at this
  have hx0 : 0 ≤ height V x := (height_pos V x).le
  have hxH : height V x ≤ H := by
    have := hH x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg hx0] at this
  calc ∑ γ ∈ s, ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖
      = ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖ := by
        refine (Finset.sum_filter_of_ne fun γ _ h => ?_).symm
        by_contra hn
        exact h (by unfold coef; rw [if_neg hn, norm_zero])
    _ ≤ ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          C * P * ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := Finset.sum_le_sum hterm
    _ = C * P * ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ C * P * (C₀ * height V x ^ A₀) :=
        mul_le_mul_of_nonneg_left (hI x _ fun γ hγ => hKtop _ (Finset.mem_filter.1 hγ).2) (mul_nonneg hC hP)
    _ ≤ C * P * (max C₀ 0 * H ^ A₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hP)
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hx0 hxH _) (pow_nonneg hx0 _) (le_max_right _ _)
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSeries_partialSums_bounded_compact : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (v : ∀ τ, M.H τ), KDecay M v → Nonempty D.what₂.Tau → ∀ (c : GA D V) (a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (Kc : Set (GA D V)), IsCompact Kc → ∃ B : ℝ, ∀ x ∈ Kc, ∀ s : Finset (GQ V), ∑ γ ∈ s, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * x)‖ ≤ B := by
  atlas_forward_decl GlobalTheory.PoinAut.partialSum_bdd
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.CoefMeas

theorem measurable_coef : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v a : ∀ τ, M.H τ), Measurable (coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v a) := by
  intro D θ hθ V S M Λ 𝔪 hΛ h𝔪 v a
  classical
  have h1 := GlobalTheory.SepPer.CoefCont.continuous_coefR D θ hθ V S M v a
  have h2 := (congLev_open_compact V hΛ.1 h𝔪).1
  unfold coef
  exact Measurable.ite h2.measurableSet h1.measurable measurable_const

end GlobalTheory.SepPer.CoefMeas
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_level_indicator_coefficient_test_function : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v a : ∀ τ, M.H τ), Measurable (coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v a) := by
  atlas_forward_decl GlobalTheory.SepPer.CoefMeas.measurable_coef
end

section
section
open MeasureTheory

namespace GlobalTheory

theorem integral_haar_eq_zero_of_fibre_integrals_eq_zero :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ (P Q : Subgroup H), IsClosed (P : Set H) → IsClosed (Q : Set H) → (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) → (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) → (∀ h, h ∈ P → h ∈ Q → h = 1) → ∀ F : H → ℂ, (∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∫ p, F ((p : H) * q) ∂ν = 0) → ∫ h, F h ∂μ = 0 := by
  intro H _ _ _ _ _ _ _ _ μ hμ P Q hP hQ hcomm hgen hdisj F hF
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology (P : Set H)
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology (Q : Set H)
  haveI : BorelSpace P := Subtype.borelSpace (P : Set H)
  haveI : BorelSpace Q := Subtype.borelSpace (Q : Set H)
  let m : P × Q →* H :=
    { toFun := fun x => (x.1 : H) * x.2
      map_one' := by simp
      map_mul' := by
        rintro ⟨p, q⟩ ⟨p', q'⟩
        simp only [Prod.mk_mul_mk, Subgroup.coe_mul]
        have h := hcomm p' p'.2 q q.2
        calc (p : H) * p' * (q * q') = p * (p' * q) * q' := by simp only [mul_assoc]
          _ = p * (q * p') * q' := by rw [h]
          _ = p * q * (p' * q') := by simp only [mul_assoc] }
  have hm : ∀ x : P × Q, m x = (x.1 : H) * x.2 := fun _ => rfl
  have hcont : Continuous m :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hsurj : Function.Surjective m := by
    intro h
    obtain ⟨p, hp, q, hq, rfl⟩ := hgen h
    exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  have hinj : Function.Injective m := by
    rw [injective_iff_map_eq_one]
    rintro ⟨p, q⟩ h
    rw [hm] at h
    have h1 : (p : H) = (q : H)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hp1 : (p : H) = 1 := hdisj p p.2 (h1 ▸ Q.inv_mem q.2)
    have hq1 : (q : H) = 1 := by simpa [hp1] using h
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hq1)
  have hopen : IsOpenMap m := m.isOpenMap_of_sigmaCompact hsurj hcont
  let e : (P × Q) ≃* H := MulEquiv.ofBijective m ⟨hinj, hsurj⟩
  let φ : (P × Q) ≃ₜ H := e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen
  let νP : Measure P := Measure.haar
  let νQ : Measure Q := Measure.haar
  haveI : νP.IsHaarMeasure := inferInstance
  haveI : νQ.IsHaarMeasure := inferInstance
  haveI : (νP.prod νQ).IsHaarMeasure := inferInstance
  haveI : ((νP.prod νQ).map e).IsHaarMeasure :=
    e.isHaarMeasure_map (νP.prod νQ) φ.continuous φ.symm.continuous
  have hμeq := Measure.isMulLeftInvariant_eq_smul μ ((νP.prod νQ).map e)
  have hzero : ∫ h, F h ∂((νP.prod νQ).map e) = 0 := by
    have hemb : MeasurableEmbedding e := φ.measurableEmbedding
    rw [hemb.integral_map]
    by_cases hint : Integrable (fun x => F (e x)) (νP.prod νQ)
    · rw [integral_prod_symm _ hint]
      have : ∀ q : Q, ∫ p : P, F (e (p, q)) ∂νP = 0 := fun q => hF νP inferInstance q q.2
      simp [this]
    · exact integral_undef hint
  rw [hμeq, integral_smul_nnreal_measure, hzero, smul_zero]

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_haar_eq_zero_of_fibre_integrals_eq_zero_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ (P Q : Subgroup H), IsClosed (P : Set H) → IsClosed (Q : Set H) → (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) → (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) → (∀ h, h ∈ P → h ∈ Q → h = 1) → ∀ F : H → ℂ, (∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∫ p, F ((p : H) * q) ∂ν = 0) → ∫ h, F h ∂μ = 0 := by
  atlas_forward_decl GlobalTheory.integral_haar_eq_zero_of_fibre_integrals_eq_zero
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_parabolic_subgroups : GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ), (∀ τ, v τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → (∀ τ, a τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∀ (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∃ P Q : Subgroup (NI V C), IsClosed (P : Set (NI V C)) ∧ IsClosed (Q : Set (NI V C)) ∧ (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧ (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) ∧ (∀ h, h ∈ P → h ∈ Q → h = 1) ∧ ∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∀ x y : GA D V, ∫ p, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) ∂ν = 0 := by
  first | exact @GlobalTheory.FibreAtTau.fibre_integral_eq_zero | exact GlobalTheory.FibreAtTau.fibre_integral_eq_zero | (intros; apply GlobalTheory.FibreAtTau.fibre_integral_eq_zero <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PoinCusp

theorem poin_isCuspFun : GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsCuspFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro hP D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hT a
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  intro r C hC μ 𝓕 hμ h𝓕 g
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5; haveI := i7
  haveI : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  haveI : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := hμ
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK
  have hm : Measurable (coef θ M K v fun τ => (a τ : M.H τ)) := GlobalTheory.T.measurable_level_indicator_coefficient_test_function D θ hθ V S M Λ 𝔪 hΛ h𝔪 v _
  set f : GA D V → ℂ := fun y => coef θ M K v (fun τ => (a τ : M.H τ)) (c * y * g) with hf
  have hfm : ∀ γ : GA D V, Measurable fun h : NI V C => f (γ * (NI V C).subtype h) := fun γ =>
    hm.comp ((continuous_const.mul (continuous_const.mul continuous_subtype_val)).mul continuous_const).measurable
  obtain ⟨-, Kc, hKc, hcov⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩
  have hcov' : ∀ h : NI V C, ∃ δ ∈ (GQ V).comap (NI V C).subtype, δ * h ∈ Kc := fun h => by
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, by simpa using hk⟩
  obtain ⟨B, hB⟩ := GlobalTheory.T.poincareSeries_partialSums_bounded_compact D θ hθ V S M Λ 𝔪 hΛ v hv hT c a ((fun h : NI V C => (h : GA D V) * g) '' Kc)
    (hKc.image (continuous_subtype_val.mul continuous_const))
  have hpt : ∀ h ∈ Kc, ∑' γ : GQ V, ‖f (γ * (NI V C).subtype h) * 1‖ₑ ≤ ENNReal.ofReal B := by
    intro h hh
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have e : ∀ γ : GQ V, f (↑γ * (NI V C).subtype h) * 1 =
        coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * ((h : GA D V) * g)) := fun γ => by
      simp only [hf, mul_one, Subgroup.coe_subtype, mul_assoc]
    simp only [e, ← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hB _ ⟨h, hh, rfl⟩ s)
  have hfin : (∑' q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫⁻ h, ‖f ((q.out : GQ V) * (NI V C).subtype h) * 1‖ₑ ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.T.lintegral_unfolding_le_of_translate_cover (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) Kc hcov'
      (fun y => ‖f y * 1‖ₑ) (fun γ => ((hfm γ).mul_const 1).enorm))
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B)) (hKc.measure_lt_top (μ := μ)).ne) ?_
    calc _ ≤ ∫⁻ _ in Kc, ENNReal.ofReal B ∂μ := setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal B * μ Kc := setLIntegral_const _ _
  have hunf := GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) 𝓕 h𝓕 f (fun _ => 1)
    hfm measurable_const (fun _ _ _ => rfl) hfin
  have hzero : ∀ q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ = 0 := by
    intro q
    obtain ⟨τ⟩ := hT
    obtain ⟨P, Q, hPc, hQc, hcomm, hgen, htriv, hvan⟩ := GlobalTheory.T.exists_closed_parabolic_subgroups hP D θ hθ V S M K v (fun τ => (a τ : M.H τ))
      (fun τ => (hv τ).1) (fun τ => (a τ).2) τ r C hC
    have := GlobalTheory.T.integral_haar_eq_zero_of_fibre_integrals_eq_zero_alt (NI V C) μ hμ P Q hPc hQc hcomm hgen htriv
      (fun n => coef θ M K v (fun τ => (a τ : M.H τ)) ((c * (q.out : GQ V)) * (n : GA D V) * g))
      (fun ν hν q' hq' => hvan ν hν q' hq' _ g)
    simpa [hf, mul_assoc] using this
  have hsum0 : HasSum (fun q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) =>
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ) 0 := by
    simpa only [hzero] using (hasSum_zero : HasSum (fun _ : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) => (0:ℂ)) 0)
  have h0 := hunf.2.unique hsum0
  rw [← h0]
  refine integral_congr_ae (.of_forall fun n => ?_)
  simp only [poin, hf, mul_one, Subgroup.coe_subtype, mul_assoc]

end GlobalTheory.PoinCusp
end
end
