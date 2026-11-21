import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsBase
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure
import GroundTheory.AutomorphicForms.GKModules.VectorKernel
import GroundTheory.AutomorphicForms.GKModules.KernelCalculus

section
open MeasureTheory Set Filter Topology Function
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open AutomorphicForm RightCosetSpace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

def quotFun (F : normOneGL K n → ℂ) (hF : ∀ γ ∈ Γ₁, ∀ y, F (γ * y) = F y) :
    RightCosetSpace Γ₁ → ℂ :=
  Quotient.lift F fun a b hab => by
    obtain ⟨γ, rfl⟩ := hab
    exact hF γ γ.2 b

@[simp] theorem quotFun_mk (F : normOneGL K n → ℂ) (hF : ∀ γ ∈ Γ₁, ∀ y, F (γ * y) = F y)
    (y : normOneGL K n) : quotFun F hF (mk Γ₁ y) = F y := rfl

theorem continuous_quotFun {F : normOneGL K n → ℂ} (hF : ∀ γ ∈ Γ₁, ∀ y, F (γ * y) = F y)
    (hc : Continuous F) : Continuous (quotFun F hF) :=
  (isOpenQuotientMap_mk Γ₁).isQuotientMap.continuous_iff.2 hc

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def IsContRep (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (F : normOneGL K n → ℂ) : Prop :=
  Continuous F ∧ (∀ γ ∈ Γ₁, ∀ y, F (γ * y) = F y) ∧ (fun y => φ (mk Γ₁ y)) =ᵐ[μ] F

variable {μ}

theorem IsContRep.unique {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F F' : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) (h' : IsContRep μ φ F') : F = F' :=
  (h.1.ae_eq_iff_eq μ h'.1).1 (h.2.2.symm.trans h'.2.2)

theorem isContRep_zero : IsContRep μ (0 : Lp ℂ 2 (quotientMeasure Γ₁ μ)) 0 := by
  refine ⟨continuous_const, fun _ _ _ => rfl, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp
    (Lp.coeFn_zero ℂ 2 (quotientMeasure Γ₁ μ))] with y hy
  exact hy

theorem IsContRep.add {φ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F F' : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) (h' : IsContRep μ ψ F') : IsContRep μ (φ + ψ) (F + F') := by
  refine ⟨h.1.add h'.1, fun γ hγ y => by simp [h.2.1 γ hγ y, h'.2.1 γ hγ y], ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (Lp.coeFn_add φ ψ), h.2.2, h'.2.2]
    with y h1 h2 h3
  simp only [Function.comp_apply, Pi.add_apply] at h1
  rw [h1, h2, h3, Pi.add_apply]

theorem IsContRep.smul (c : ℂ) {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) : IsContRep μ (c • φ) (c • F) := by
  refine ⟨h.1.const_smul c, fun γ hγ y => by simp [h.2.1 γ hγ y], ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (Lp.coeFn_smul c φ), h.2.2]
    with y h1 h2
  simp only [Function.comp_apply, Pi.smul_apply] at h1
  rw [h1, h2, Pi.smul_apply]

theorem IsContRep.translate {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) (x : normOneGL K n) :
    IsContRep μ (rightRegularRep Γ₁ μ x φ) (fun y => F (y * x)) := by
  refine ⟨h.1.comp (continuous_mul_const x), fun γ hγ y => by
    show F (γ * y * x) = F (y * x)
    rw [mul_assoc, h.2.1 γ hγ], ?_⟩
  have h2 : (fun y => φ (mk Γ₁ (y * x))) =ᵐ[μ] fun y => F (y * x) :=
    (measurePreserving_mul_right μ x).quasiMeasurePreserving.ae_eq_comp h.2.2
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (coeFn_rightRegularRep Γ₁ μ x φ), h2]
    with y hy1 hy2
  simp only [Function.comp_apply, rightMul_mk] at hy1
  rw [hy1]
  exact hy2

variable (μ) in

theorem isContRep_rconv (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    IsContRep μ ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) φ)
      (rconv Γ₁ μ f φ) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  refine ⟨continuous_rconv Γ₁ μ f φ, fun γ hγ y => rconv_mul_left Γ₁ μ f φ hγ y, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (integrated_ae_eq_rconvQ Γ₁ μ f φ)]
    with y hy
  simp only [Function.comp_apply] at hy
  rw [hy, rconvQ_mk]

theorem IsContRep.ae_eq_quotFun {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) :
    (φ : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] quotFun F h.2.1 := by
  have hm : ∀ᵐ x ∂(Measure.map (mk Γ₁) (μ.restrict (fundamentalDomain Γ₁))),
      (φ : RightCosetSpace Γ₁ → ℂ) x = quotFun F h.2.1 x := by
    refine (ae_map_iff (measurable_mk Γ₁).aemeasurable
      (measurableSet_eq_fun (Lp.stronglyMeasurable φ).measurable
        (continuous_quotFun h.2.1 h.1).measurable)).2 ?_
    exact ae_restrict_of_ae (h.2.2.mono fun y hy => by simpa using hy)
  rwa [map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain Γ₁ μ)] at hm

variable (μ)
variable (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

theorem integrable_smul_archRep {γ : archGroup K n → ℂ} (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (w : cuspidalL2 μ) :
    Integrable (fun a => γ a • archRep μ a w) ν :=
  (hγ.smul ((archRep μ).continuous_orbit w)).integrable_of_hasCompactSupport hγc.smul_right

theorem coe_integrated_archRep {γ : archGroup K n → ℂ} (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (w : cuspidalL2 μ) :
    (((archRep μ).integrated ν γ w : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) =
      ∫ a, γ a • rightRegularRep Γ₁ μ (archP K n a) (w : Lp ℂ 2 (quotientMeasure Γ₁ μ)) ∂ν := by
  have e := (cuspidalL2 μ).subtypeL.integral_comp_comm (integrable_smul_archRep μ ν hγ hγc w)
  exact e.symm.trans (integral_congr_ae (Eventually.of_forall fun a => rfl))

set_option maxHeartbeats 1000000 in

theorem hasContRep_integrated_archRep {w : cuspidalL2 μ} {W : normOneGL K n → ℂ}
    (hW : IsContRep μ (w : Lp ℂ 2 (quotientMeasure Γ₁ μ)) W) {C : ℝ} (hWb : ∀ y, ‖W y‖ ≤ C)
    {γ : archGroup K n → ℂ} (hγ : Continuous γ) (hγc : HasCompactSupport γ) :
    IsContRep μ (((archRep μ).integrated ν γ w : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ))
      (fun y => ∫ a, γ a * W (y * archP K n a) ∂ν) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  obtain ⟨S, hS⟩ : ∃ S, S = tsupport γ := ⟨_, rfl⟩
  have hSc : IsCompact S := hS ▸ hγc.isCompact
  have hWc : Continuous W := hW.1
  have hpc : Continuous (archP K n) := continuous_archP

  have hJ : Continuous (uncurry fun (y : normOneGL K n) (a : archGroup K n) =>
      γ a * W (y * archP K n a)) :=
    (hγ.comp continuous_snd).mul (hWc.comp (continuous_fst.mul (hpc.comp continuous_snd)))
  have hset : ∀ y, ∫ a, γ a * W (y * archP K n a) ∂ν = ∫ a in S, γ a * W (y * archP K n a) ∂ν := by
    intro y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => ?_).symm
    have h0 : γ a = 0 := image_eq_zero_of_notMem_tsupport (by rw [← hS]; exact ha)
    rw [h0, zero_mul]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : normOneGL K n → ℂ, Ψ = fun y => ∫ a, γ a * W (y * archP K n a) ∂ν :=
    ⟨_, rfl⟩
  have hΨc : Continuous Ψ := by
    have : Ψ = fun y => ∫ a in S, γ a * W (y * archP K n a) ∂ν := hΨ.trans (funext hset)
    rw [this]
    exact continuous_parametric_integral_of_continuous hJ hSc
  have hΨinv : ∀ γ₀ ∈ Γ₁, ∀ y, Ψ (γ₀ * y) = Ψ y := by
    intro γ₀ hγ₀ y
    rw [hΨ]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show γ a * W (γ₀ * y * archP K n a) = γ a * W (y * archP K n a)
    rw [mul_assoc, hW.2.1 γ₀ hγ₀]
  rw [← hΨ]
  refine ⟨hΨc, hΨinv, ?_⟩

  obtain ⟨WQ, hWQ⟩ : ∃ WQ, WQ = quotFun W hW.2.1 := ⟨_, rfl⟩
  have hWQc : Continuous WQ := hWQ ▸ continuous_quotFun hW.2.1 hWc
  have hWQb : ∀ x, ‖WQ x‖ ≤ C := by
    intro x
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ x
    rw [hWQ, quotFun_mk]
    exact hWb y
  obtain ⟨ΨQ, hΨQ⟩ : ∃ ΨQ, ΨQ = quotFun Ψ hΨinv := ⟨_, rfl⟩
  have hΨQ_eq : ∀ x, ΨQ x = ∫ a, γ a * WQ (rightMul Γ₁ (archP K n a) x) ∂ν := by
    intro x
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ x
    rw [hΨQ, quotFun_mk, hΨ, hWQ]
    simp only [rightMul_mk, quotFun_mk]
  have hγi : Integrable γ ν := hγ.integrable_of_hasCompactSupport hγc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hWb 1)

  have hJQ : Continuous (uncurry fun (a : archGroup K n) (x : RightCosetSpace Γ₁) =>
      γ a * WQ (rightMul Γ₁ (archP K n a) x)) := by
    have hr : Continuous fun p : archGroup K n × RightCosetSpace Γ₁ =>
        rightMul Γ₁ (archP K n p.1) p.2 := by
      have h1 : Continuous fun p : RightCosetSpace Γ₁ × normOneGL K n => rightMul Γ₁ p.2 p.1 :=
        continuous_rightMul_prod Γ₁
      have h2 : Continuous fun p : archGroup K n × RightCosetSpace Γ₁ => (p.2, archP K n p.1) :=
        continuous_snd.prodMk (hpc.comp continuous_fst)
      have h3 := h1.comp h2
      exact h3
    have h4 := (hγ.comp continuous_fst).mul (hWQc.comp hr)
    exact h4
  have hint : ∀ s : Set (RightCosetSpace Γ₁), Integrable (uncurry fun (a : archGroup K n)
      (x : RightCosetSpace Γ₁) => γ a * WQ (rightMul Γ₁ (archP K n a) x))
        (ν.prod ((quotientMeasure Γ₁ μ).restrict s)) := by
    intro s
    refine Integrable.mono' ((hγi.norm.mul_prod (integrable_const C))) hJQ.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    obtain ⟨a, x⟩ := p
    show ‖γ a * WQ (rightMul Γ₁ (archP K n a) x)‖ ≤ ‖γ a‖ * C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hWQb _) (norm_nonneg _)
  have hΨQi : Integrable ΨQ (quotientMeasure Γ₁ μ) := by
    have := (hint univ).integral_prod_right
    rw [Measure.restrict_univ] at this
    exact this.congr (Eventually.of_forall fun x => (hΨQ_eq x).symm)

  obtain ⟨V, hV⟩ : ∃ V : Lp ℂ 2 (quotientMeasure Γ₁ μ),
      V = ∫ a, γ a • rightRegularRep Γ₁ μ (archP K n a) (w : Lp ℂ 2 (quotientMeasure Γ₁ μ)) ∂ν :=
    ⟨_, rfl⟩
  have hVi : Integrable (fun a => γ a • rightRegularRep Γ₁ μ (archP K n a)
      (w : Lp ℂ 2 (quotientMeasure Γ₁ μ))) ν :=
    (hγ.smul (((rightRegularRep Γ₁ μ).continuous_orbit _).comp hpc)).integrable_of_hasCompactSupport
      hγc.smul_right
  have hwQ : (w : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] WQ := hWQ ▸ hW.ae_eq_quotFun
  have hVeq : (V : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] ΨQ := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => ((Lp.memLp _).integrable one_le_two).integrableOn)
      (fun s _ _ => hΨQi.integrableOn) fun s hs hμs => ?_
    rw [← L2.inner_indicatorConstLp_one hs hμs.ne, hV, ← integral_inner hVi]
    have hcoef : ∀ a, ⟪indicatorConstLp 2 hs hμs.ne (1 : ℂ), γ a • rightRegularRep Γ₁ μ
        (archP K n a) (w : Lp ℂ 2 (quotientMeasure Γ₁ μ))⟫_ℂ =
        ∫ x in s, γ a * WQ (rightMul Γ₁ (archP K n a) x) ∂quotientMeasure Γ₁ μ := by
      intro a
      rw [inner_smul_right, L2.inner_indicatorConstLp_one, ← integral_const_mul]
      refine setIntegral_congr_ae hs ?_
      have h1 := coeFn_rightRegularRep Γ₁ μ (archP K n a) (w : Lp ℂ 2 (quotientMeasure Γ₁ μ))
      have h2 := (measurePreserving_rightMul μ (archP K n a)).quasiMeasurePreserving.ae_eq_comp hwQ
      filter_upwards [h1, h2] with x hx1 hx2
      intro _
      simp only [Function.comp_apply] at hx2
      exact congrArg (γ a * ·) (hx1.trans hx2)
    simp_rw [hcoef]
    refine (integral_integral_swap (hint s)).trans ?_
    exact setIntegral_congr_fun hs fun x _ => (hΨQ_eq x).symm
  have hcoe := (coe_integrated_archRep μ ν hγ hγc w).trans hV.symm
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp hVeq] with y hy
  simp only [Function.comp_apply] at hy
  refine (congrArg (fun f : Lp ℂ 2 (quotientMeasure Γ₁ μ) =>
    (f : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ y)) hcoe).trans ?_
  refine hy.trans ?_
  rw [hΨQ, quotFun_mk]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function Module

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace BanachRep

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [CompactSpace L]
  [TotallyDisconnectedSpace L] [T2Space L]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def fixedIn (σ : BanachRep L E) (W : Submodule ℂ E) (U : Subgroup L) : Submodule ℂ E where
  carrier := {w | w ∈ W ∧ ∀ u ∈ U, σ u w = w}
  add_mem' := fun {a b} ha hb =>
    ⟨W.add_mem ha.1 hb.1, fun u hu => by rw [map_add, ha.2 u hu, hb.2 u hu]⟩
  zero_mem' := ⟨W.zero_mem, fun u _ => map_zero _⟩
  smul_mem' := fun c w hw => ⟨W.smul_mem c hw.1, fun u hu => by rw [map_smul, hw.2 u hu]⟩

theorem exists_isOpen_forall_eq_of_finiteDimensional (σ : BanachRep L E) (v : E)
    (hv : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun g : L => σ g v))) :
    ∃ U : Subgroup L, IsOpen (U : Set L) ∧ ∀ u ∈ U, σ u v = v := by
  classical
  let _ : MeasurableSpace L := borel L
  have _ : BorelSpace L := ⟨rfl⟩
  set W := Submodule.span ℂ (Set.range fun g : L => σ g v) with hWdef
  have hWc : IsClosed (W : Set E) := Submodule.closed_of_finiteDimensional W
  have hσW : ∀ g, σ g v ∈ W := fun g => Submodule.subset_span ⟨g, rfl⟩
  set F : Subgroup L → Submodule ℂ E := fun U => fixedIn σ W U with hFdef
  have hFle : ∀ U, F U ≤ W := fun U w hw => hw.1
  have hFfin : ∀ U, FiniteDimensional ℂ (F U) := fun U => Submodule.finiteDimensional_of_le (hFle U)
  have hFanti : ∀ {U V : Subgroup L}, U ≤ V → F V ≤ F U :=
    fun hUV w hw => ⟨hw.1, fun u hu => hw.2 u (hUV hu)⟩

  set S : Set ℕ := {d | ∃ U : Subgroup L, IsOpen (U : Set L) ∧ finrank ℂ (F U) = d} with hSdef
  have hSne : S.Nonempty := ⟨_, ⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨finrank ℂ W, ?_⟩
    rintro _ ⟨U, -, rfl⟩
    exact Submodule.finrank_mono (hFle U)
  obtain ⟨U₀, hU₀, hU₀d⟩ := Nat.sSup_mem hSne hSbdd
  have hmax : ∀ U : Subgroup L, IsOpen (U : Set L) → finrank ℂ (F U) ≤ finrank ℂ (F U₀) :=
    fun U hU => hU₀d ▸ le_csSup hSbdd ⟨U, hU, rfl⟩
  have hstab : ∀ U : Subgroup L, IsOpen (U : Set L) → U ≤ U₀ → F U = F U₀ := by
    intro U hU hle
    have _ := hFfin U
    exact (Submodule.eq_of_le_of_finrank_le (hFanti hle) (hmax U hU)).symm
  have _ := hFfin U₀
  have hclosed : IsClosed (F U₀ : Set E) := Submodule.closed_of_finiteDimensional (F U₀)

  have hvF : v ∈ F U₀ := by
    change v ∈ (F U₀ : Set E)
    rw [← hclosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have hN : IsOpen ({g : L | ‖σ g v - v‖ < ε / 2} ∩ (U₀ : Set L)) :=
      (isOpen_lt ((σ.continuous_orbit v).sub continuous_const).norm continuous_const).inter hU₀
    have h1N : (1 : L) ∈ {g : L | ‖σ g v - v‖ < ε / 2} ∩ (U₀ : Set L) :=
      ⟨by simp [half_pos hε], U₀.one_mem⟩
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hN h1N
    set U : Subgroup L := H.toOpenSubgroup.toSubgroup with hUdef
    have hU : IsOpen (U : Set L) := H.toOpenSubgroup.isOpen
    have hUU₀ : U ≤ U₀ := fun u hu => (hH hu).2
    have hUN : ∀ u ∈ U, ‖σ u v - v‖ < ε / 2 := fun u hu => (hH hu).1
    have _ : CompactSpace U := isCompact_iff_compactSpace.1 (U.isClosed_of_isOpen hU).isCompact
    set ρ : Measure U := CuspidalSpectrum.haarProb U with hρ
    have hcont : Continuous fun u : U => σ (u : L) v :=
      (σ.continuous_orbit v).comp continuous_subtype_val
    have hint : Integrable (fun u : U => σ (u : L) v) ρ :=
      integrableOn_univ.1 (hcont.continuousOn.integrableOn_compact isCompact_univ)
    set e : E := ∫ u : U, σ (u : L) v ∂ρ with hedef
    have heW : e ∈ W :=
      Convex.integral_mem (W.restrictScalars ℝ).convex hWc (ae_of_all _ fun u => hσW u) hint
    have hefix : ∀ u ∈ U, σ u e = e := by
      intro u hu
      rw [hedef, ← (σ u).integral_comp_comm hint]
      have := integral_mul_left_eq_self (μ := ρ) (fun x : U => σ (x : L) v) ⟨u, hu⟩
      rw [← this]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [Subgroup.coe_mul]
      rw [map_mul_apply]
    have heF : e ∈ F U₀ := by
      rw [← hstab U hU hUU₀]
      exact ⟨heW, hefix⟩
    refine ⟨e, heF, ?_⟩
    have hdiff : e - v = ∫ u : U, (σ (u : L) v - v) ∂ρ := by
      rw [integral_sub hint (integrable_const v), integral_const, probReal_univ, one_smul]
    rw [dist_comm, dist_eq_norm, hdiff]
    calc ‖∫ u : U, (σ (u : L) v - v) ∂ρ‖ ≤ ε / 2 * ρ.real univ :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun u => (hUN u u.2).le)
      _ = ε / 2 := by rw [probReal_univ, mul_one]
      _ < ε := half_lt_self hε
  exact ⟨U₀, hU₀, fun u hu => hvF.2 u hu⟩

end BanachRep

namespace UnitaryRep

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [CompactSpace L]
  [TotallyDisconnectedSpace L] [T2Space L]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_isOpen_forall_eq_of_finiteDimensional (σ : UnitaryRep L H) (v : H)
    (hv : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun g : L => σ g v))) :
    ∃ U : Subgroup L, IsOpen (U : Set L) ∧ ∀ u ∈ U, σ u v = v := by
  have e : (Set.range fun g : L => BanachRep.ofUnitary σ g v) = Set.range fun g : L => σ g v := rfl
  rw [← e] at hv
  exact BanachRep.exists_isOpen_forall_eq_of_finiteDimensional (BanachRep.ofUnitary σ) v hv

variable {G : Type*} [Group G] [TopologicalSpace G]

def comapHom (σ : UnitaryRep G H) (f : L →* G) (hf : Continuous f) : UnitaryRep L H where
  toHom := σ.toHom.comp f
  continuous_orbit' v := (σ.continuous_orbit' v).comp hf

end UnitaryRep

namespace CuspidalSpectrum

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure]


end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open AutomorphicForm RightCosetSpace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def CuspL2 : Type _ := cuspidalL2 μ

instance : NormedAddCommGroup (CuspL2 μ) := inferInstanceAs (NormedAddCommGroup (cuspidalL2 μ))

instance : InnerProductSpace ℂ (CuspL2 μ) := inferInstanceAs (InnerProductSpace ℂ (cuspidalL2 μ))

instance : CompleteSpace (CuspL2 μ) := inferInstanceAs (CompleteSpace (cuspidalL2 μ))

def toLp : CuspL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ) := (cuspidalL2 μ).subtypeL

theorem toLp_mem (v : CuspL2 μ) : toLp μ v ∈ cuspidalL2 μ := (show cuspidalL2 μ from v).2

theorem norm_toLp (v : CuspL2 μ) : ‖toLp μ v‖ = ‖v‖ := rfl

theorem toLp_injective : Function.Injective (toLp μ) := Subtype.val_injective

def cuspRepT : UnitaryRep (normOneGL K n) (CuspL2 μ) := cuspRep μ

theorem toLp_cuspRepT (g : normOneGL K n) (v : CuspL2 μ) :
    toLp μ (cuspRepT μ g v) = rightRegularRep Γ₁ μ g (toLp μ v) := rfl

theorem toLp_mem_intertwiners : toLp μ ∈ (cuspRepT μ).intertwiners (rightRegularRep Γ₁ μ) :=
  fun _ _ => rfl

theorem toLp_integrated (f : normOneGL K n →₁[μ] ℂ) (v : CuspL2 μ) :
    toLp μ ((cuspRepT μ).integrated μ f v) = (rightRegularRep Γ₁ μ).integrated μ f (toLp μ v) :=
  congrArg (fun T => T v)
    (UnitaryRep.comp_integrated_of_mem_intertwiners (cuspRepT μ) μ (toLp_mem_intertwiners μ) f)

def archURepT : UnitaryRep (archGroup K n) (CuspL2 μ) :=
  (cuspRepT μ).comapHom (archP K n) continuous_archP

def archRepT : BanachRep (archGroup K n) (CuspL2 μ) := BanachRep.ofUnitary (archURepT μ)

theorem archRepT_apply (a : archGroup K n) (v : CuspL2 μ) :
    archRepT μ a v = cuspRepT μ (archP K n a) v := rfl

set_option maxHeartbeats 1000000 in

theorem exists_isOpen_forall_cuspRepT_finOne_eq (v : CuspL2 μ)
    (hv : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k :
      (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v))) :
    ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n),
      IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧ ∀ u ∈ U, cuspRepT μ (finOne K n u) v = v := by
  have hle : Submodule.span ℂ (Set.range fun u : AdelicGLn.integralFiniteGL K n =>
      (cuspRepT μ).comapHom (finOne K n) continuous_finOne u v) ≤
      Submodule.span ℂ (Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, rfl⟩
    exact Submodule.subset_span ⟨⟨finEmb K n u, finEmb_mem_maxCompact u.2⟩, rfl⟩
  have _ := hv
  exact UnitaryRep.exists_isOpen_forall_eq_of_finiteDimensional _ v
    (Submodule.finiteDimensional_of_le hle)

variable (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

theorem integrable_smul_archRepT {γ : archGroup K n → ℂ} (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (w : CuspL2 μ) :
    Integrable (fun a => γ a • archRepT μ a w) ν :=
  (hγ.smul ((archRepT μ).continuous_orbit w)).integrable_of_hasCompactSupport hγc.smul_right

theorem toLp_integrated_archRepT {γ : archGroup K n → ℂ} (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (w : CuspL2 μ) :
    toLp μ ((archRepT μ).integrated ν γ w) =
      ∫ a, γ a • rightRegularRep Γ₁ μ (archP K n a) (toLp μ w) ∂ν :=
  ((toLp μ).integral_comp_comm (integrable_smul_archRepT μ ν hγ hγc w)).symm.trans
    (integral_congr_ae (Eventually.of_forall fun a => (toLp μ).map_smul (γ a) _))

set_option maxHeartbeats 1000000 in

theorem isContRep_integrated_archRepT {w : CuspL2 μ} {W : normOneGL K n → ℂ}
    (hW : IsContRep μ (toLp μ w) W) {C : ℝ} (hWb : ∀ y, ‖W y‖ ≤ C)
    {γ : archGroup K n → ℂ} (hγ : Continuous γ) (hγc : HasCompactSupport γ) :
    IsContRep μ (toLp μ ((archRepT μ).integrated ν γ w))
      (fun y => ∫ a, γ a * W (y * archP K n a) ∂ν) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  obtain ⟨S, hS⟩ : ∃ S, S = tsupport γ := ⟨_, rfl⟩
  have hSc : IsCompact S := hS ▸ hγc.isCompact
  have hWc : Continuous W := hW.1
  have hpc : Continuous (archP K n) := continuous_archP

  have hJ : Continuous (uncurry fun (y : normOneGL K n) (a : archGroup K n) =>
      γ a * W (y * archP K n a)) :=
    (hγ.comp continuous_snd).mul (hWc.comp (continuous_fst.mul (hpc.comp continuous_snd)))
  have hset : ∀ y, ∫ a, γ a * W (y * archP K n a) ∂ν = ∫ a in S, γ a * W (y * archP K n a) ∂ν := by
    intro y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => ?_).symm
    have h0 : γ a = 0 := image_eq_zero_of_notMem_tsupport (by rw [← hS]; exact ha)
    rw [h0, zero_mul]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : normOneGL K n → ℂ, Ψ = fun y => ∫ a, γ a * W (y * archP K n a) ∂ν :=
    ⟨_, rfl⟩
  have hΨc : Continuous Ψ := by
    have : Ψ = fun y => ∫ a in S, γ a * W (y * archP K n a) ∂ν := hΨ.trans (funext hset)
    rw [this]
    exact continuous_parametric_integral_of_continuous hJ hSc
  have hΨinv : ∀ γ₀ ∈ Γ₁, ∀ y, Ψ (γ₀ * y) = Ψ y := by
    intro γ₀ hγ₀ y
    rw [hΨ]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show γ a * W (γ₀ * y * archP K n a) = γ a * W (y * archP K n a)
    rw [mul_assoc, hW.2.1 γ₀ hγ₀]
  rw [← hΨ]
  refine ⟨hΨc, hΨinv, ?_⟩

  obtain ⟨WQ, hWQ⟩ : ∃ WQ, WQ = quotFun W hW.2.1 := ⟨_, rfl⟩
  have hWQc : Continuous WQ := hWQ ▸ continuous_quotFun hW.2.1 hWc
  have hWQb : ∀ x, ‖WQ x‖ ≤ C := by
    intro x
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ x
    rw [hWQ, quotFun_mk]
    exact hWb y
  obtain ⟨ΨQ, hΨQ⟩ : ∃ ΨQ, ΨQ = quotFun Ψ hΨinv := ⟨_, rfl⟩
  have hΨQ_eq : ∀ x, ΨQ x = ∫ a, γ a * WQ (rightMul Γ₁ (archP K n a) x) ∂ν := by
    intro x
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ x
    rw [hΨQ, quotFun_mk, hΨ, hWQ]
    simp only [rightMul_mk, quotFun_mk]
  have hγi : Integrable γ ν := hγ.integrable_of_hasCompactSupport hγc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hWb 1)

  have hJQ : Continuous (uncurry fun (a : archGroup K n) (x : RightCosetSpace Γ₁) =>
      γ a * WQ (rightMul Γ₁ (archP K n a) x)) := by
    have hr : Continuous fun p : archGroup K n × RightCosetSpace Γ₁ =>
        rightMul Γ₁ (archP K n p.1) p.2 := by
      have h1 : Continuous fun p : RightCosetSpace Γ₁ × normOneGL K n => rightMul Γ₁ p.2 p.1 :=
        continuous_rightMul_prod Γ₁
      have h2 : Continuous fun p : archGroup K n × RightCosetSpace Γ₁ => (p.2, archP K n p.1) :=
        continuous_snd.prodMk (hpc.comp continuous_fst)
      have h3 := h1.comp h2
      exact h3
    have h4 := (hγ.comp continuous_fst).mul (hWQc.comp hr)
    exact h4
  have hint : ∀ s : Set (RightCosetSpace Γ₁), Integrable (uncurry fun (a : archGroup K n)
      (x : RightCosetSpace Γ₁) => γ a * WQ (rightMul Γ₁ (archP K n a) x))
        (ν.prod ((quotientMeasure Γ₁ μ).restrict s)) := by
    intro s
    refine Integrable.mono' ((hγi.norm.mul_prod (integrable_const C))) hJQ.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    obtain ⟨a, x⟩ := p
    show ‖γ a * WQ (rightMul Γ₁ (archP K n a) x)‖ ≤ ‖γ a‖ * C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hWQb _) (norm_nonneg _)
  have hΨQi : Integrable ΨQ (quotientMeasure Γ₁ μ) := by
    have := (hint univ).integral_prod_right
    rw [Measure.restrict_univ] at this
    exact this.congr (Eventually.of_forall fun x => (hΨQ_eq x).symm)

  obtain ⟨V, hV⟩ : ∃ V : Lp ℂ 2 (quotientMeasure Γ₁ μ),
      V = ∫ a, γ a • rightRegularRep Γ₁ μ (archP K n a) (toLp μ w) ∂ν :=
    ⟨_, rfl⟩
  have hVi : Integrable (fun a => γ a • rightRegularRep Γ₁ μ (archP K n a)
      (toLp μ w)) ν :=
    (hγ.smul (((rightRegularRep Γ₁ μ).continuous_orbit _).comp hpc)).integrable_of_hasCompactSupport
      hγc.smul_right
  have hwQ : (toLp μ w : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] WQ := hWQ ▸ hW.ae_eq_quotFun
  have hVeq : (V : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] ΨQ := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => ((Lp.memLp _).integrable one_le_two).integrableOn)
      (fun s _ _ => hΨQi.integrableOn) fun s hs hμs => ?_
    rw [← L2.inner_indicatorConstLp_one hs hμs.ne, hV, ← integral_inner hVi]
    have hcoef : ∀ a, ⟪indicatorConstLp 2 hs hμs.ne (1 : ℂ), γ a • rightRegularRep Γ₁ μ
        (archP K n a) (toLp μ w)⟫_ℂ =
        ∫ x in s, γ a * WQ (rightMul Γ₁ (archP K n a) x) ∂quotientMeasure Γ₁ μ := by
      intro a
      rw [inner_smul_right, L2.inner_indicatorConstLp_one, ← integral_const_mul]
      refine setIntegral_congr_ae hs ?_
      have h1 := coeFn_rightRegularRep Γ₁ μ (archP K n a) (toLp μ w)
      have h2 := (measurePreserving_rightMul μ (archP K n a)).quasiMeasurePreserving.ae_eq_comp hwQ
      filter_upwards [h1, h2] with x hx1 hx2
      intro _
      simp only [Function.comp_apply] at hx2
      exact congrArg (γ a * ·) (hx1.trans hx2)
    simp_rw [hcoef]
    refine (integral_integral_swap (hint s)).trans ?_
    exact setIntegral_congr_fun hs fun x _ => (hΨQ_eq x).symm
  have hcoe := (toLp_integrated_archRepT μ ν hγ hγc w).trans hV.symm
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp hVeq] with y hy
  simp only [Function.comp_apply] at hy
  refine (congrArg (fun f : Lp ℂ 2 (quotientMeasure Γ₁ μ) =>
    (f : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ y)) hcoe).trans ?_
  refine hy.trans ?_
  rw [hΨQ, quotFun_mk]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open scoped InnerProductSpace ContDiff

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

section Integrated

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (σ : UnitaryRep (normOneGL K n) H)
  (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
  (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure]
  {β : ArchMatrix K n → ℝ}

theorem inner_integrated_ccToL1_eq (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (w u : H) :
    ⟪w, σ.integrated μ (UnitaryRep.ccToL1 μ f) u⟫_ℂ = ∫ g, f g * ⟪w, σ g u⟫_ℂ ∂μ := by
  rw [UnitaryRep.inner_integrated]
  refine integral_congr_ae ((MemLp.coeFn_toLp (μ := μ)
    (f.continuous.memLp_of_hasCompactSupport (p := 1) f.hasCompactSupport)).mono fun g hg => ?_)
  dsimp only
  exact congrArg (· * ⟪w, σ g u⟫_ℂ) hg

theorem integrable_smul_archProj (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)) (u : H) :
    Integrable (fun A : ArchUnits K n => (β A : ℂ) • σ (archProj K n A) u) ν := by
  refine ((Complex.continuous_ofReal.comp (hβ.comp Units.continuous_val)).smul
    ((σ.continuous_orbit u).comp continuous_archProj)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_unitsSupport hβc hβu) fun A hA => ?_
  simp [image_eq_zero_of_notMem_tsupport (f := β) hA]

theorem integrated_archConv (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (w : H) :
    σ.integrated μ (UnitaryRep.ccToL1 μ (archConv ν hβ hβc hβu g)) w =
      ∫ A, (β A : ℂ) • σ (archProj K n A) (σ.integrated μ (UnitaryRep.ccToL1 μ g) w) ∂ν := by
  refine ext_inner_left ℂ fun w' => ?_
  set u := σ.integrated μ (UnitaryRep.ccToL1 μ g) w with hu
  rw [← integral_inner (integrable_smul_archProj σ ν hβ hβc hβu u) w']
  set S : Set (ArchUnits K n) := (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' tsupport β
  have hS : IsCompact S := isCompact_unitsSupport hβc hβu
  set Φ : ArchUnits K n → normOneGL K n → ℂ :=
    fun A x => (β A : ℂ) * g ((archProj K n A)⁻¹ * x) * ⟪w', σ x w⟫_ℂ with hΦ
  have hcont : Continuous (uncurry Φ) :=
    (((Complex.continuous_ofReal.comp (hβ.comp (Units.continuous_val.comp continuous_fst)))).mul
      (g.continuous.comp (((continuous_archProj.comp continuous_fst).inv).mul continuous_snd))).mul
      (continuous_const.inner ((σ.continuous_orbit w).comp continuous_snd))
  have hsupp : HasCompactSupport (uncurry Φ) := by
    refine HasCompactSupport.intro
      (hS.prod ((hS.image continuous_archProj).mul g.hasCompactSupport)) fun p hp => ?_
    obtain ⟨A, x⟩ := p
    show (β A : ℂ) * g ((archProj K n A)⁻¹ * x) * ⟪w', σ x w⟫_ℂ = 0
    by_cases h1 : A ∈ S
    · by_cases h2 : (archProj K n A)⁻¹ * x ∈ tsupport (g : normOneGL K n → ℂ)
      · exact absurd ⟨h1, ⟨archProj K n A, ⟨A, h1, rfl⟩, _, h2, mul_inv_cancel_left _ _⟩⟩ hp
      · rw [image_eq_zero_of_notMem_tsupport h2, mul_zero, zero_mul]
    · have : β A = 0 := image_eq_zero_of_notMem_tsupport (f := β) h1
      rw [this, Complex.ofReal_zero, zero_mul, zero_mul]
  have hint : Integrable (uncurry Φ) (ν.prod μ) := hcont.integrable_of_hasCompactSupport hsupp
  calc ⟪w', σ.integrated μ (UnitaryRep.ccToL1 μ (archConv ν hβ hβc hβu g)) w⟫_ℂ
      = ∫ x, archConvFun ν β g x * ⟪w', σ x w⟫_ℂ ∂μ := by
        rw [inner_integrated_ccToL1_eq]
        rfl
    _ = ∫ x, ∫ A, Φ A x ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ A, ∫ x, Φ A x ∂μ ∂ν := (integral_integral_swap hint).symm
    _ = ∫ A, ⟪w', (β A : ℂ) • σ (archProj K n A) u⟫_ℂ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun A => ?_)
        dsimp only
        rw [← integral_mul_left_eq_self (fun x => Φ A x) (archProj K n A), inner_smul_right,
          UnitaryRep.inner_map_right, hu, inner_integrated_ccToL1_eq, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hΦ, inv_mul_cancel_left]
        rw [UnitaryRep.inner_map_left, inv_inv, ← UnitaryRep.map_mul_apply]
        ring

end Integrated

theorem finAvg_eq_self (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    {g : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    (hg : ∀ u ∈ U, ∀ x, g (finOne K n u * x) = g x) : finAvg U hU g = g := by
  ext x
  rw [finAvg_apply]
  have := compactSpace_of_isOpen U hU
  have e : ∀ u : U, g ((finOne K n (u : AdelicGLn.integralFiniteGL K n))⁻¹ * x) = g x := fun u => by
    rw [← map_inv]
    exact hg _ (U.inv_mem u.2) x
  show (∫ u : U, g ((finOne K n (u : AdelicGLn.integralFiniteGL K n))⁻¹ * x) ∂haarProb U) = g x
  simp_rw [e]
  simp

variable (K n) in

def archGroupEquiv : archGroup K n ≃ₜ* ArchUnits K n where
  toMulEquiv := Subgroup.topEquiv
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

@[simp] theorem archGroupEquiv_apply (a : archGroup K n) :
    archGroupEquiv K n a = (a : ArchUnits K n) := rfl

theorem isHaarMeasure_map_val (ν' : Measure (archGroup K n)) [ν'.IsHaarMeasure] :
    (ν'.map (fun a : archGroup K n => (a : ArchUnits K n))).IsHaarMeasure :=
  (archGroupEquiv K n).isHaarMeasure_map ν'

theorem integral_map_val {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν' : Measure (archGroup K n)) (f : ArchUnits K n → E) :
    ∫ A, f A ∂(ν'.map (fun a : archGroup K n => (a : ArchUnits K n))) = ∫ a, f a ∂ν' :=
  (MeasurableEmbedding.subtype_coe MeasurableSet.univ).integral_map f

section Conversion

variable (K n) in
open scoped Classical in

def matExt (κ : archGroup K n → ℂ) (M : ArchMatrix K n) : ℂ :=
  if h : IsUnit M then κ ⟨h.unit, Subgroup.mem_top _⟩ else 0

theorem matExt_val (κ : archGroup K n → ℂ) (a : archGroup K n) :
    matExt K n κ ((a : ArchUnits K n) : ArchMatrix K n) = κ a := by
  unfold matExt
  rw [dif_pos (a : ArchUnits K n).isUnit]
  congr 1
  exact Subtype.ext (IsUnit.unit_of_val_units _)

theorem matExt_eq_zero {κ : archGroup K n → ℂ} {M : ArchMatrix K n}
    (hM : M ∉ (fun a : archGroup K n => ((a : ArchUnits K n) : ArchMatrix K n)) '' tsupport κ) :
    matExt K n κ M = 0 := by
  unfold matExt
  split_ifs with h
  · by_contra h0
    exact hM ⟨⟨h.unit, Subgroup.mem_top _⟩, subset_tsupport _ h0, rfl⟩
  · rfl

theorem contDiff_matExt {κ : archGroup K n → ℂ} (hκ : (isExpLieAlgebra K n).IsTestFunction κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (matExt K n κ) := by
  set h := isExpLieAlgebra K n with hh
  set S : Set (ArchMatrix K n) :=
    (fun a : archGroup K n => ((a : ArchUnits K n) : ArchMatrix K n)) '' tsupport κ with hSdef
  have hS : IsCompact S := hκ.2.isCompact.image (Units.continuous_val.comp continuous_subtype_val)
  set e := expPartialHomeomorph ℝ (ArchMatrix K n) with he
  let ι : ArchMatrix K n →L[ℝ] archLie K n :=
    LinearMap.toContinuousLinearMap
      (LinearMap.codRestrict ⊤ LinearMap.id fun _ => Submodule.mem_top)
  refine contDiff_iff_contDiffAt.2 fun M₀ => ?_
  by_cases hM₀ : IsUnit M₀
  · set g : archGroup K n := ⟨hM₀.unit, Subgroup.mem_top _⟩ with hg
    set gi : ArchMatrix K n := ((hM₀.unit⁻¹ : ArchUnits K n) : ArchMatrix K n) with hgi
    have hgix₀ : gi * M₀ = 1 := by
      rw [hgi]
      exact hM₀.val_inv_mul
    set V : Set (ArchMatrix K n) := {M | gi * M ∈ e.target} with hV
    have hVo : IsOpen V := e.open_target.preimage (continuous_const.mul continuous_id)
    have hM₀V : M₀ ∈ V := by
      show gi * M₀ ∈ e.target
      rw [hgix₀]
      exact one_mem_expPartialHomeomorph_target ℝ _
    have hmul : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun M : ArchMatrix K n => gi * M :=
      (ContinuousLinearMap.mul ℝ (ArchMatrix K n) gi).contDiff
    have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun M => κ (g * h.expG (ι (e.symm (gi * M))))) V :=
      ((h.isSmoothFun_iff).1 hκ.1 g).comp_contDiffOn (ι.contDiff.comp_contDiffOn
        ((contDiffOn_expPartialHomeomorph_symm ℝ _).comp hmul.contDiffOn fun M hM => hM))
    refine (hsm.congr fun M hM => ?_).contDiffAt (hVo.mem_nhds hM₀V)
    have hy : gi * M ∈ e.target := hM
    have hexpy : NormedSpace.exp (e.symm (gi * M)) = gi * M := e.right_inv hy
    have hMeq : M = ((g : ArchUnits K n) : ArchMatrix K n) * NormedSpace.exp (e.symm (gi * M)) := by
      rw [hexpy, ← mul_assoc, hg]
      show M = ((hM₀.unit : ArchUnits K n) : ArchMatrix K n) * gi * M
      rw [hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    have hMu : IsUnit M := by
      rw [hMeq]
      exact (g : ArchUnits K n).isUnit.mul (h.expG (ι (e.symm (gi * M))) : ArchUnits K n).isUnit
    unfold matExt
    rw [dif_pos hMu]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [IsUnit.unit_spec, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
    exact hMeq
  · have hnot : M₀ ∉ S := by
      rintro ⟨a, -, ha⟩
      exact hM₀ (ha ▸ (a : ArchUnits K n).isUnit)
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hnot] with M hM
    exact matExt_eq_zero hM

theorem hasCompactSupport_matExt {κ : archGroup K n → ℂ} (hκ : HasCompactSupport κ) :
    HasCompactSupport (matExt K n κ) :=
  HasCompactSupport.intro (hκ.isCompact.image (Units.continuous_val.comp continuous_subtype_val))
    fun _ hM => matExt_eq_zero hM

theorem tsupport_subset_of_matExt {κ : archGroup K n → ℂ} (hκ : HasCompactSupport κ)
    {f : ArchMatrix K n → ℝ} (hf : ∀ M, matExt K n κ M = 0 → f M = 0) :
    tsupport f ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) := by
  set S : Set (ArchMatrix K n) :=
    (fun a : archGroup K n => ((a : ArchUnits K n) : ArchMatrix K n)) '' tsupport κ
  have hS : IsCompact S := hκ.isCompact.image (Units.continuous_val.comp continuous_subtype_val)
  have hsub : tsupport f ⊆ S := by
    refine closure_minimal (fun M hM => ?_) hS.isClosed
    by_contra hMS
    exact hM (hf M (matExt_eq_zero hMS))
  refine hsub.trans ?_
  rintro _ ⟨a, -, rfl⟩
  exact ⟨a, rfl⟩

theorem exists_real_parts_of_isTestFunction {κ : archGroup K n → ℂ}
    (hκ : (isExpLieAlgebra K n).IsTestFunction κ) :
    ∃ βr βi : ArchMatrix K n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) βr ∧ HasCompactSupport βr ∧
      tsupport βr ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) βi ∧ HasCompactSupport βi ∧
      tsupport βi ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) ∧
      ∀ a : archGroup K n, κ a = (βr ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) +
        (βi ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * Complex.I := by
  have hs := contDiff_matExt hκ
  have hc := hasCompactSupport_matExt (K := K) (n := n) hκ.2
  refine ⟨fun M => (matExt K n κ M).re, fun M => (matExt K n κ M).im,
    Complex.reCLM.contDiff.comp hs, hc.comp_left Complex.zero_re,
    tsupport_subset_of_matExt hκ.2 fun M h0 => by simp [h0],
    Complex.imCLM.contDiff.comp hs, hc.comp_left Complex.zero_im,
    tsupport_subset_of_matExt hκ.2 fun M h0 => by simp [h0], fun a => ?_⟩
  dsimp only
  rw [matExt_val, Complex.re_add_im]

end Conversion

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open AutomorphicForm RightCosetSpace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem rconv_mul_of_left_inv {f : normOneGL K n → ℂ} {u : normOneGL K n}
    (hf : ∀ x, f (u⁻¹ * x) = f x) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (x : normOneGL K n) :
    rconv Γ₁ μ f φ (x * u) = rconv Γ₁ μ f φ x := by
  unfold rconv
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show f ((x * u)⁻¹ * y) * _ = f (x⁻¹ * y) * _
  rw [mul_inv_rev, mul_assoc, hf]

theorem archimedeanProjection_maximalCompact (k : archCompact K n) :
    archP K n (k : archGroup K n) =
      ⟨infEmb K n (k : archGroup K n), Reduction.maxCompact_le_normOneGL k.2⟩ :=
  archProj_of_mem (Reduction.maxCompact_le_normOneGL k.2)

variable {μ} in

theorem IsContRep.of_eq {φ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) (e : φ = ψ) : IsContRep μ ψ F := e ▸ h

variable {μ} in

theorem IsContRep.of_eq_fun {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F G : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) (e : F = G) : IsContRep μ φ G := e ▸ h

omit [μ.IsHaarMeasure] in

theorem smul_comb {E : Type*} [AddCommGroup E] [Module ℂ E] (X : E) (r i c : ℂ) :
    r • (c • X) + Complex.I • (i • (c • X)) = c • ((r + i * Complex.I) • X) := by
  simp only [smul_smul, ← add_smul]
  congr 1
  ring

variable (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

set_option maxHeartbeats 1000000 in

theorem exists_contRep_of_zkFinite (v : CuspL2 μ)
    (hs : (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) v)
    (hK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k :
      (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v)))
    (hZ : FiniteDimensional ℂ (Submodule.span ℂ ((fun z => (isExpLieAlgebra K n).uAction (archRepT μ) z
      ⟨v, hs⟩) '' ((isExpLieAlgebra K n).centerU : Set _)))) :
    ∃ (κ : archGroup K n → ℂ) (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (Φ : normOneGL K n → ℂ)
      (C : ℝ), (isExpLieAlgebra K n).IsTestFunction κ ∧ (archRepT μ).integrated ν κ v = v ∧
      IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
      IsContRep μ (toLp μ v) Φ ∧ (∀ y, ‖Φ y‖ ≤ C) ∧
      (∀ u ∈ U, ∀ x, Φ (x * finOne K n u) = Φ x) ∧
      ∀ r : ℕ, 0 < r → r < n → ∀ x : normOneGL K n,
        ∫ X in unipFundamentalDomain K n r, Φ (unipOne K n r X * x) ∂unipMeasure K n r = 0 := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ

  have hKarch : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : archCompact K n =>
      archRepT μ (k : archGroup K n) v)) := by
    have hle : Set.range (fun k : archCompact K n => archRepT μ (k : archGroup K n) v) ⊆
        Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
          cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v := by
      rintro _ ⟨k, rfl⟩
      exact ⟨⟨_, k.2⟩, (congrArg (fun g => cuspRepT μ g v) (archimedeanProjection_maximalCompact k)).symm⟩
    exact Submodule.finiteDimensional_of_le (Submodule.span_mono hle)

  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hKc⟩ := exists_archCartanData K n
  obtain ⟨κ, hκt, -, hκv⟩ := (isExpLieAlgebra K n).exists_integrated_eq_of_zkFinite (archRepT μ) ν
    (archCompact K n) B b ε hε horth hsymm hinv hKc ⟨v, hs⟩ hKarch hZ Filter.univ_mem

  obtain ⟨U, hU, hUv⟩ := exists_isOpen_forall_cuspRepT_finOne_eq μ v hK

  obtain ⟨F₀, c, hc, hF₀U, hF₀⟩ := exists_cc_integral_mul_eq μ ν U hU κ hκt.continuous hκt.2
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hint : Integrable (fun a => κ a • archRepT μ a v) ν :=
    integrable_smul_archRepT μ ν hκt.continuous hκt.2 v

  have hRv : (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ F₀) v = (c : ℂ) • v := by
    refine ext_inner_left ℂ fun w => ?_
    have hΘc : Continuous fun x : normOneGL K n => ⟪w, cuspRepT μ x v⟫_ℂ :=
      continuous_const.inner ((cuspRepT μ).continuous_orbit v)
    have hΘU : ∀ u ∈ U, ∀ x, ⟪w, cuspRepT μ (x * finOne K n u) v⟫_ℂ = ⟪w, cuspRepT μ x v⟫_ℂ :=
      fun u hu x => congrArg (fun z => ⟪w, z⟫_ℂ)
        (((cuspRepT μ).map_mul_apply x _ v).trans (congrArg (fun z => cuspRepT μ x z) (hUv u hu)))
    have e1 : ∫ a, κ a * ⟪w, cuspRepT μ (archP K n a) v⟫_ℂ ∂ν = ⟪w, v⟫_ℂ :=
      calc ∫ a, κ a * ⟪w, cuspRepT μ (archP K n a) v⟫_ℂ ∂ν
          = ∫ a, ⟪w, κ a • archRepT μ a v⟫_ℂ ∂ν :=
            integral_congr_ae (Eventually.of_forall fun a =>
              (inner_smul_right w (archRepT μ a v) (κ a)).symm)
        _ = ⟪w, (archRepT μ).integrated ν κ v⟫_ℂ := integral_inner hint w
        _ = ⟪w, v⟫_ℂ := congrArg (fun z => ⟪w, z⟫_ℂ) hκv
    calc ⟪w, (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ F₀) v⟫_ℂ
        = ∫ g, F₀ g * ⟪w, cuspRepT μ g v⟫_ℂ ∂μ := inner_integrated_ccToL1_eq (cuspRepT μ) μ F₀ w v
      _ = (c : ℂ) * ∫ a, κ a * ⟪w, cuspRepT μ (archP K n a) v⟫_ℂ ∂ν := hF₀ _ hΘc hΘU
      _ = (c : ℂ) * ⟪w, v⟫_ℂ := congrArg (fun t => (c : ℂ) * t) e1
      _ = ⟪w, (c : ℂ) • v⟫_ℂ := (inner_smul_right w v (c : ℂ)).symm

  have hsub : ∀ f : CompactlySupportedContinuousMap (normOneGL K n) ℂ,
      (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) (toLp μ v) =
        toLp μ ((cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ f) v) := fun f =>
    (toLp_integrated μ (UnitaryRep.ccToL1 μ f) v).symm
  have hrep0 : IsContRep μ ((c : ℂ) • toLp μ v) (rconv Γ₁ μ F₀ (toLp μ v)) :=
    (isContRep_rconv μ F₀ (toLp μ v)).of_eq
      ((hsub F₀).trans ((congrArg (toLp μ) hRv).trans ((toLp μ).map_smul (c : ℂ) v)))
  have hcancel : ∀ x : Lp ℂ 2 (quotientMeasure Γ₁ μ), (c : ℂ)⁻¹ • (c : ℂ) • x = x := fun x => by
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : normOneGL K n → ℂ,
      Φ = (c : ℂ)⁻¹ • rconv Γ₁ μ F₀ (toLp μ v) := ⟨_, rfl⟩
  have hrep : IsContRep μ (toLp μ v) Φ :=
    ((hrep0.smul (c : ℂ)⁻¹).of_eq (hcancel _)).of_eq_fun hΦ.symm

  obtain ⟨βr, βi, hr, hrc, hru, hi, hic, hiu, hκβ⟩ := exists_real_parts_of_isTestFunction hκt
  obtain ⟨νA, hνA⟩ : ∃ νA : Measure (ArchUnits K n),
      νA = ν.map (fun a : archGroup K n => (a : ArchUnits K n)) := ⟨_, rfl⟩
  have : νA.IsHaarMeasure := hνA ▸ isHaarMeasure_map_val ν
  obtain ⟨Br, hBr⟩ := exists_norm_rconv_le_uniform μ νA hr hrc hru U hU F₀
  obtain ⟨Bi, hBi⟩ := exists_norm_rconv_le_uniform μ νA hi hic hiu U hU F₀
  obtain ⟨fr, hfr⟩ : ∃ fr, fr = archConv νA hr.continuous hrc hru (finAvg U hU F₀) := ⟨_, rfl⟩
  obtain ⟨fi, hfi⟩ : ∃ fi, fi = archConv νA hi.continuous hic hiu (finAvg U hU F₀) := ⟨_, rfl⟩
  have hfin : (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ (finAvg U hU F₀)) v = (c : ℂ) • v :=
    (congrArg (fun g => (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ g) v)
      (finAvg_eq_self U hU hF₀U)).trans hRv
  have hpart : ∀ {β : ArchMatrix K n → ℝ} (hβ : Continuous β) (hβc : HasCompactSupport β)
      (hβu : tsupport β ⊆ Set.range (Units.val : ArchUnits K n → ArchMatrix K n)),
      (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ (archConv νA hβ hβc hβu (finAvg U hU F₀))) v =
        ∫ A, (β A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA := by
    intro β hβ hβc hβu
    exact (integrated_archConv (cuspRepT μ) μ νA hβ hβc hβu (finAvg U hU F₀) v).trans
      (integral_congr_ae (Eventually.of_forall fun A =>
        congrArg (fun z => (β A : ℂ) • cuspRepT μ (archProj K n A) z) hfin))
  have hIr := integrable_smul_archProj (cuspRepT μ) νA hr.continuous hrc hru ((c : ℂ) • v)
  have hIi := integrable_smul_archProj (cuspRepT μ) νA hi.continuous hic hiu ((c : ℂ) • v)
  have hpt : ∀ A : ArchUnits K n, (βr A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) +
      Complex.I • ((βi A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v)) =
        (c : ℂ) • (((βr A : ℂ) + (βi A : ℂ) * Complex.I) • cuspRepT μ (archProj K n A) v) := by
    intro A
    have hms : cuspRepT μ (archProj K n A) ((c : ℂ) • v) = (c : ℂ) • cuspRepT μ (archProj K n A) v :=
      (cuspRepT μ (archProj K n A)).map_smul (c : ℂ) v
    exact (congrArg₂ (fun s t => (βr A : ℂ) • s + Complex.I • ((βi A : ℂ) • t)) hms hms).trans
      (smul_comb _ _ _ _)
  have hcomb : (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fr) v +
      Complex.I • (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fi) v = (c : ℂ) • v := by
    have e1 : (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fr) v +
        Complex.I • (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fi) v =
        ∫ A, (βr A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA +
          Complex.I • ∫ A, (βi A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA := by
      rw [hfr, hfi]
      exact congrArg₂ (fun s t => s + Complex.I • t) (hpart hr.continuous hrc hru)
        (hpart hi.continuous hic hiu)
    have e2 : ∫ A, (βr A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA +
          Complex.I • ∫ A, (βi A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA =
        ∫ A, (c : ℂ) • (((βr A : ℂ) + (βi A : ℂ) * Complex.I) • cuspRepT μ (archProj K n A) v) ∂νA :=
      (congrArg (fun s => ∫ A, (βr A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA + s)
        (integral_smul Complex.I _).symm).trans
        ((integral_add hIr (hIi.smul Complex.I)).symm.trans
          (integral_congr_ae (Eventually.of_forall hpt)))
    have e3 : ∫ A, (c : ℂ) • (((βr A : ℂ) + (βi A : ℂ) * Complex.I) • cuspRepT μ (archProj K n A) v) ∂νA =
        ∫ a, (c : ℂ) • (κ a • archRepT μ a v) ∂ν := by
      rw [hνA]
      refine (integral_map_val ν (fun A => (c : ℂ) • (((βr A : ℂ) + (βi A : ℂ) * Complex.I) •
        cuspRepT μ (archProj K n A) v))).trans ?_
      exact integral_congr_ae (Eventually.of_forall fun a =>
        congrArg (fun t => (c : ℂ) • (t • archRepT μ a v)) (hκβ a).symm)
    have e4 : ∫ a, (c : ℂ) • (κ a • archRepT μ a v) ∂ν = (c : ℂ) • v :=
      (integral_smul (c : ℂ) _).trans (congrArg (fun z => (c : ℂ) • z) hκv)
    exact e1.trans (e2.trans (e3.trans e4))
  have hrepr : IsContRep μ ((c : ℂ) • toLp μ v)
      (rconv Γ₁ μ fr (toLp μ v) + Complex.I • rconv Γ₁ μ fi (toLp μ v)) := by
    refine ((isContRep_rconv μ fr (toLp μ v)).add
      ((isContRep_rconv μ fi (toLp μ v)).smul Complex.I)).of_eq ?_
    refine (congrArg₂ (fun s t => s + Complex.I • t) (hsub fr) (hsub fi)).trans ?_
    refine ((congrArg (fun t => toLp μ ((cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fr) v) + t)
      ((toLp μ).map_smul Complex.I ((cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fi) v)).symm).trans
      ((toLp μ).map_add _ _).symm).trans ?_
    exact (congrArg (toLp μ) hcomb).trans ((toLp μ).map_smul (c : ℂ) v)
  have hΦ2 : Φ = (c : ℂ)⁻¹ • (rconv Γ₁ μ fr (toLp μ v) + Complex.I • rconv Γ₁ μ fi (toLp μ v)) :=
    hrep.unique ((hrepr.smul (c : ℂ)⁻¹).of_eq (hcancel _))
  refine ⟨κ, U, Φ, ‖(c : ℂ)⁻¹‖ * (Br * ‖toLp μ v‖ + Bi * ‖toLp μ v‖), hκt, hκv, hU, hrep,
    fun y => ?_, ?_, ?_⟩
  · have h1 := hBr _ (toLp_mem μ v) y
    have h2 := hBi _ (toLp_mem μ v) y
    rw [← hfr] at h1
    rw [← hfi] at h2
    rw [hΦ2]
    show ‖(c : ℂ)⁻¹ • (rconv Γ₁ μ fr (toLp μ v) y + Complex.I • rconv Γ₁ μ fi (toLp μ v) y)‖ ≤ _
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 ?_)) (norm_nonneg _)
    rw [norm_smul, Complex.norm_I, one_mul]
    exact h2
  · intro u hu x
    rw [hΦ]
    simp only [Pi.smul_apply]
    congr 1
    refine rconv_mul_of_left_inv μ (fun z => ?_) _ x
    rw [← map_inv]
    exact hF₀U _ (U.inv_mem hu) z
  · intro r hr0 hrn x
    rw [hΦ]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_rconv_unip_eq_zero μ F₀ (toLp_mem μ v) hr0 hrn x, mul_zero]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open AutomorphicForm RightCosetSpace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

theorem retractOne_mul (g h : AdelicGLn.AdelicGL K n) :
    retractOne (g * h) = retractOne g * retractOne h := by
  ext1
  rw [coe_retractOne, Subgroup.coe_mul, coe_retractOne, coe_retractOne, map_mul,
    mul_comm (detModule K n g), map_mul, mul_inv_rev]
  simp only [mul_assoc]
  rw [← mul_assoc h (centralSection K n (detModule K n g))⁻¹,
    ← centralSection_inv_mul_comm (detModule K n g) h,
    mul_assoc (centralSection K n (detModule K n g))⁻¹]

theorem retractOne_coe (x : normOneGL K n) : retractOne (x : AdelicGLn.AdelicGL K n) = x := by
  ext1
  rw [coe_retractOne, (mem_normOneGL_iff_detModule).1 x.2, map_one, inv_one, mul_one]

theorem retractOne_mul_coe (g : AdelicGLn.AdelicGL K n) (x : normOneGL K n) :
    retractOne (g * (x : AdelicGLn.AdelicGL K n)) = retractOne g * x := by
  rw [retractOne_mul, retractOne_coe]

theorem retractOne_coe_mul (x : normOneGL K n) (g : AdelicGLn.AdelicGL K n) :
    retractOne ((x : AdelicGLn.AdelicGL K n) * g) = x * retractOne g := by
  rw [retractOne_mul, retractOne_coe]

theorem retractOne_mul_infEmb (g : AdelicGLn.AdelicGL K n) (a : archGroup K n) :
    retractOne (g * infEmb K n a) = retractOne g * archP K n a := by
  rw [retractOne_mul, retract_infEmb]

theorem retractOne_centralSection (s : {r : ℝ // 0 < r}) : retractOne (centralSection K n s) = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))
  · ext1
    rw [coe_retractOne, detModule_centralSection hn, mul_inv_cancel]
    rfl

def liftOne (F : normOneGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ := F (retractOne g)

theorem liftOne_coe (F : normOneGL K n → ℂ) (x : normOneGL K n) :
    liftOne F (x : AdelicGLn.AdelicGL K n) = F x := by
  rw [liftOne, retractOne_coe]

theorem liftOne_centralSection_mul (F : normOneGL K n → ℂ) (s : {r : ℝ // 0 < r})
    (g : AdelicGLn.AdelicGL K n) : liftOne F (centralSection K n s * g) = liftOne F g := by
  rw [liftOne, liftOne, retractOne_mul, retractOne_centralSection, one_mul]

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem exists_isContRep_of_mem_span {X : Set (Lp ℂ 2 (quotientMeasure Γ₁ μ))}
    (hX : ∀ x ∈ X, ∃ F, IsContRep μ x F) {w : Lp ℂ 2 (quotientMeasure Γ₁ μ)}
    (hw : w ∈ Submodule.span ℂ X) : ∃ F, IsContRep μ w F := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hX x hx
  | zero => exact ⟨0, isContRep_zero⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF⟩ := hx
    obtain ⟨G, hG⟩ := hy
    exact ⟨F + G, hF.add hG⟩
  | smul c x _ hx =>
    obtain ⟨F, hF⟩ := hx
    exact ⟨c • F, hF.smul c⟩

theorem finiteDimensional_span_liftOne (W : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ₁ μ)))
    [FiniteDimensional ℂ W] (hW : ∀ w ∈ W, ∃ F, IsContRep μ w F)
    (S : Set (AdelicGLn.AdelicGL K n → ℂ))
    (hS : ∀ f ∈ S, ∃ w ∈ W, ∃ F, IsContRep μ w F ∧ f = liftOne F) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  classical
  choose R hR using fun w : W => hW w w.2
  let T : W →ₗ[ℂ] (AdelicGLn.AdelicGL K n → ℂ) :=
    { toFun := fun w => liftOne (R w)
      map_add' := fun w₁ w₂ => by
        have e : R (w₁ + w₂) = R w₁ + R w₂ :=
          (hR (w₁ + w₂)).unique (((hR w₁).add (hR w₂)).of_eq (Submodule.coe_add w₁ w₂).symm)
        funext g
        simp only [liftOne, e, Pi.add_apply]
      map_smul' := fun c w => by
        have e : R (c • w) = c • R w :=
          (hR (c • w)).unique (((hR w).smul c).of_eq (Submodule.coe_smul c w).symm)
        funext g
        simp only [liftOne, e, Pi.smul_apply, RingHom.id_apply] }
  have hle : Submodule.span ℂ S ≤ LinearMap.range T := by
    rw [Submodule.span_le]
    intro f hf
    obtain ⟨w, hw, F, hF, rfl⟩ := hS f hf
    refine ⟨⟨w, hw⟩, ?_⟩
    show liftOne (R ⟨w, hw⟩) = liftOne F
    rw [(hR ⟨w, hw⟩).unique hF]
  exact Submodule.finiteDimensional_of_le hle

variable (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

theorem eq_integral_of_integrated_eq {v : CuspL2 μ} {Φ : normOneGL K n → ℂ}
    (hrep : IsContRep μ (toLp μ v) Φ) {C : ℝ} (hb : ∀ y, ‖Φ y‖ ≤ C) {κ : archGroup K n → ℂ}
    (hκt : (isExpLieAlgebra K n).IsTestFunction κ) (hκv : (archRepT μ).integrated ν κ v = v)
    (y : normOneGL K n) : Φ y = ∫ a, κ a * Φ (y * archP K n a) ∂ν :=
  congrFun (hrep.unique ((isContRep_integrated_archRepT μ ν hrep hb hκt.continuous hκt.2).of_eq
    (congrArg (toLp μ) hκv))) y

omit [μ.IsHaarMeasure] in

theorem slice_eq_integral {Φ : normOneGL K n → ℂ} {κ : archGroup K n → ℂ}
    (hΦκ : ∀ y, Φ y = ∫ a, κ a * Φ (y * archP K n a) ∂ν) (y : normOneGL K n) :
    (fun x : archGroup K n => Φ (y * archP K n x)) =
      fun x => ∫ a, (fun x : archGroup K n => Φ (y * archP K n x)) (x * a) * κ a ∂ν := by
  funext x
  refine (hΦκ (y * archP K n x)).trans (integral_congr_ae (Eventually.of_forall fun a => ?_))
  show κ a * Φ (y * archP K n x * archP K n a) = Φ (y * archP K n (x * a)) * κ a
  rw [map_mul, mul_assoc y, mul_comm]

omit [μ.IsHaarMeasure] in

theorem isSmoothFun_slice {Φ : normOneGL K n → ℂ} (hΦc : Continuous Φ) {κ : archGroup K n → ℂ}
    (hκt : (isExpLieAlgebra K n).IsTestFunction κ)
    (hΦκ : ∀ y, Φ y = ∫ a, κ a * Φ (y * archP K n a) ∂ν) (y : normOneGL K n) :
    (isExpLieAlgebra K n).IsSmoothFun (fun x : archGroup K n => Φ (y * archP K n x)) := by
  have hΨ : Continuous (fun x : archGroup K n => Φ (y * archP K n x)) :=
    hΦc.comp (continuous_const.mul continuous_archP)
  rw [slice_eq_integral ν hΦκ y]
  exact (isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΨ hκt

theorem exists_uAction_slice {v : CuspL2 μ} (hs : (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) v)
    {Φ : normOneGL K n → ℂ} (hΦc : Continuous Φ) {κ : archGroup K n → ℂ}
    (hκt : (isExpLieAlgebra K n).IsTestFunction κ) (hκv : (archRepT μ).integrated ν κ v = v)
    (hΦκ : ∀ y, Φ y = ∫ a, κ a * Φ (y * archP K n a) ∂ν) (u : UEnv K n) :
    ∃ γ : archGroup K n → ℂ, (isExpLieAlgebra K n).IsTestFunction γ ∧
      ((isExpLieAlgebra K n).uAction (archRepT μ) u ⟨v, hs⟩ : CuspL2 μ) =
        (archRepT μ).integrated ν γ v ∧
      ∀ y : normOneGL K n, ((isExpLieAlgebra K n).rightUAction (F := ℂ) u
          ⟨fun x => Φ (y * archP K n x), isSmoothFun_slice ν hΦc hκt hΦκ y⟩ : archGroup K n → ℂ) =
        fun x => ∫ a, Φ (y * archP K n (x * a)) * γ a ∂ν := by
  obtain ⟨γ, hγ, hvec, hfun⟩ := (isExpLieAlgebra K n).exists_uAction_integrated ν (archRepT μ) u hκt
  refine ⟨γ, hγ, ?_, fun y => ?_⟩
  · have e : (⟨v, hs⟩ : (isExpLieAlgebra K n).smoothVectors (archRepT μ)) =
        ⟨(archRepT μ).integrated ν κ v,
          (isExpLieAlgebra K n).isSmoothVector_integrated (archRepT μ) ν hκt v⟩ :=
      Subtype.ext hκv.symm
    exact (congrArg (fun w => ((isExpLieAlgebra K n).uAction (archRepT μ) u w : CuspL2 μ)) e).trans
      (hvec v)
  · have hΨ : Continuous (fun x : archGroup K n => Φ (y * archP K n x)) :=
      hΦc.comp (continuous_const.mul continuous_archP)
    have e : (⟨fun x => Φ (y * archP K n x), isSmoothFun_slice ν hΦc hκt hΦκ y⟩ :
        (isExpLieAlgebra K n).smoothFuns (F := ℂ)) =
        ⟨fun g => ∫ a, (fun x : archGroup K n => Φ (y * archP K n x)) (g * a) * κ a ∂ν,
          (isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΨ hκt⟩ :=
      Subtype.ext (slice_eq_integral ν hΦκ y)
    exact (congrArg (fun f => ((isExpLieAlgebra K n).rightUAction (F := ℂ) u f :
      archGroup K n → ℂ)) e).trans (hfun _ hΨ)

def IsZKFinite (v : CuspL2 μ) : Prop :=
  ∃ hs : (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) v,
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k :
      (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v)) ∧
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z => (isExpLieAlgebra K n).uAction (archRepT μ) z
      ⟨v, hs⟩) '' ((isExpLieAlgebra K n).centerU : Set _)))

set_option maxHeartbeats 1000000 in

theorem exists_cuspForm_of_isZKFinite (v : CuspL2 μ) (hv : IsZKFinite μ v) :
    ∃ φ : cuspForms K n,
      ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) = toLp μ v ∧
      ∀ (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n),
        (φ : AdelicGLn.AdelicGL K n → ℂ) (centralSection K n s * g) = (φ : AdelicGLn.AdelicGL K n → ℂ) g := by
  obtain ⟨hs, hK, hZ⟩ := hv
  have hνH : (Measure.haar : Measure (archGroup K n)).IsHaarMeasure := inferInstance
  obtain ⟨κ, U, Φ, C, hκt, hκv, hU, hrep, hb, hΦU, hcusp⟩ :=
    exists_contRep_of_zkFinite μ Measure.haar v hs hK hZ
  have hΦκ := eq_integral_of_integrated_eq μ Measure.haar hrep hb hκt hκv

  have hslice : ∀ g, archSlice (liftOne Φ) g = fun x => Φ (retractOne g * archP K n x) :=
    fun g => funext fun x => by
      rw [archSlice_apply, liftOne, retractOne_mul_infEmb]
  have hsm : IsArchSmooth (liftOne Φ) := fun g => by
    rw [hslice g]
    exact isSmoothFun_slice Measure.haar hrep.1 hκt hΦκ _

  have hfin : ∀ g, ∀ᶠ y in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n),
      liftOne Φ (g * finEmb K n y) = liftOne Φ g := by
    intro g
    filter_upwards [(finOpenSubgroup U hU).mem_nhds_one] with y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    show Φ (retractOne (g * finEmb K n (u : AdelicGLn.FiniteAdelicGL K n))) = Φ (retractOne g)
    rw [retractOne_mul_finEmb g u.2]
    exact hΦU u hu _

  have hli : IsLeftInvariant (liftOne Φ) := by
    intro γ g
    have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n := rationalGL_le_normOneGL ⟨γ, rfl⟩
    have hγΓ : (⟨AdelicGLn.diagonal K n γ, hγ1⟩ : normOneGL K n) ∈ Γ₁ := ⟨γ, rfl⟩
    exact (congrArg Φ (retractOne_coe_mul ⟨_, hγ1⟩ g)).trans (hrep.2.1 _ hγΓ _)

  have hKf : IsKFinite (liftOne Φ) := by
    unfold IsKFinite
    obtain ⟨W, hWdef⟩ : ∃ W : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ₁ μ)),
        W = Submodule.span ℂ (Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
          toLp μ (cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v)) := ⟨_, rfl⟩
    have hWfin : FiniteDimensional ℂ W := by
      have e : W = (Submodule.span ℂ (Set.range fun k :
          (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
            cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v)).map
              (toLp μ : CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ)) := by
        rw [hWdef, Submodule.map_span, ← Set.range_comp]
        rfl
      rw [e]
      infer_instance
    have hgen : ∀ k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
        IsContRep μ (toLp μ (cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v))
          (fun y => Φ (y * ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩)) :=
      fun k => (hrep.translate _).of_eq (toLp_cuspRepT μ _ v).symm
    refine finiteDimensional_span_liftOne μ W ?_ _ ?_
    · intro w hw
      rw [hWdef] at hw
      refine exists_isContRep_of_mem_span μ ?_ hw
      rintro _ ⟨k, rfl⟩
      exact ⟨_, hgen k⟩
    · rintro _ ⟨k, rfl⟩
      refine ⟨_, hWdef ▸ Submodule.subset_span ⟨k, rfl⟩, _, hgen k, ?_⟩
      funext g
      show Φ (retractOne (g * (k : AdelicGLn.AdelicGL K n))) = Φ (retractOne g * _)
      rw [← retractOne_mul_coe g ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩]

  have hder : ∀ u : UEnv K n, ∃ F : normOneGL K n → ℂ,
      IsContRep μ (toLp μ ((isExpLieAlgebra K n).uAction (archRepT μ) u ⟨v, hs⟩ : CuspL2 μ)) F ∧
        (uAction u ⟨liftOne Φ, hsm⟩ : AdelicGLn.AdelicGL K n → ℂ) = liftOne F := by
    intro u
    obtain ⟨γ, hγ, hvec, hfun⟩ := exists_uAction_slice μ Measure.haar hs hrep.1 hκt hκv hΦκ u
    refine ⟨fun y => ∫ a, γ a * Φ (y * archP K n a) ∂Measure.haar,
      (isContRep_integrated_archRepT μ Measure.haar hrep hb hγ.continuous hγ.2).of_eq
        (congrArg (toLp μ) hvec).symm, ?_⟩
    funext g
    rw [coe_uAction]
    have e : sliceL g ⟨liftOne Φ, hsm⟩ =
        ⟨fun x => Φ (retractOne g * archP K n x), isSmoothFun_slice Measure.haar hrep.1 hκt hΦκ _⟩ :=
      Subtype.ext (hslice g)
    show ((isExpLieAlgebra K n).rightUAction u (sliceL g ⟨liftOne Φ, hsm⟩) : archGroup K n → ℂ) 1 = _
    rw [e, hfun (retractOne g)]
    show ∫ a, Φ (retractOne g * archP K n (1 * a)) * γ a ∂Measure.haar =
      ∫ a, γ a * Φ (retractOne g * archP K n a) ∂Measure.haar
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show Φ (retractOne g * archP K n (1 * a)) * γ a = γ a * Φ (retractOne g * archP K n a)
    rw [one_mul, mul_comm]

  have hZf : IsZFinite (⟨liftOne Φ, hsm⟩ : archSmooth K n) := by
    unfold IsZFinite
    set X := (fun z => uAction z (⟨liftOne Φ, hsm⟩ : archSmooth K n)) ''
      ((isExpLieAlgebra K n).centerU : Set (UEnv K n)) with hX
    obtain ⟨W, hWdef⟩ : ∃ W : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ₁ μ)),
        W = Submodule.span ℂ ((fun z => toLp μ ((isExpLieAlgebra K n).uAction (archRepT μ) z ⟨v, hs⟩ :
          CuspL2 μ)) '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) := ⟨_, rfl⟩
    have hWfin : FiniteDimensional ℂ W := by
      have e : W = (Submodule.span ℂ ((fun z => (isExpLieAlgebra K n).uAction (archRepT μ) z ⟨v, hs⟩) ''
          ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))).map
            ((toLp μ : CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ)).comp
              ((isExpLieAlgebra K n).smoothVectors (archRepT μ)).subtype) := by
        rw [hWdef, Submodule.map_span, Set.image_image]
        rfl
      rw [e]
      infer_instance
    have hT : Function.Injective (archSmooth K n).subtype := Subtype.val_injective
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ ((archSmooth K n).subtype '' X)) := by
      refine finiteDimensional_span_liftOne μ W ?_ _ ?_
      · intro w hw
        rw [hWdef] at hw
        refine exists_isContRep_of_mem_span μ ?_ hw
        rintro _ ⟨z, -, rfl⟩
        obtain ⟨F, hF, -⟩ := hder z
        exact ⟨F, hF⟩
      · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        obtain ⟨F, hF, hFe⟩ := hder z
        exact ⟨_, hWdef ▸ Submodule.subset_span ⟨z, hz, rfl⟩, F, hF, hFe⟩
    rw [← Submodule.map_span] at hfd
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective (archSmooth K n).subtype hT (Submodule.span ℂ X)).symm

  have hmg : HasModerateGrowth (liftOne Φ) := ⟨C, 0, fun g => by
    rw [pow_zero, mul_one]
    exact hb _⟩

  have hcu : IsCuspidal (liftOne Φ) := by
    intro r hr hrn g
    rw [← hcusp r hr hrn (retractOne g)]
    unfold constantTerm
    refine setIntegral_congr_fun (measurableSet_unipFundamentalDomain (K := K) (n := n) (r := r))
      fun X _ => ?_
    show Φ (retractOne ((unipOne K n r X : AdelicGLn.AdelicGL K n) * g)) = _
    rw [retractOne_coe_mul]
  have haf : IsAutomorphicForm (liftOne Φ) :=
    { isLeftInvariant := hli
      isSmooth := ⟨hsm, hfin⟩
      isKFinite := hKf
      isZFinite := hZf
      hasModerateGrowth := hmg }
  refine ⟨⟨liftOne Φ, haf, hcu⟩, ?_, fun s g => liftOne_centralSection_mul Φ s g⟩
  refine Lp.ext ((coeFn_cuspToL2 μ ⟨liftOne Φ, haf, hcu⟩).trans (EventuallyEq.trans ?_
    hrep.ae_eq_quotFun.symm))
  refine Eventually.of_forall fun q => ?_
  obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
  rw [cuspQuot_mk, quotFun_mk]
  exact liftOne_coe Φ y




end CuspidalSpectrum

end

end GroundTheory.Automorphic
end
