import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGroupDictionary
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HaarPushforwardEqBallDensity
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumIntegralBound
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmFieldSmallIntegralBasis

section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_pushforward_eq_ball_density : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure], ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map Δ.π = c • (volume.restrict (ballDom F.q)).withDensity fun t => ENNReal.ofReal (ballDens F.q t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects | exact GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects <;> assumption)
end

section
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section Orbit

variable {G X : Type} [Group G] (p : G → X)

def trivPart (Γ₀ : Subgroup G) : Set Γ₀ := {γ | ∀ a, p ((γ : G) * a) = p a}

theorem encard_translates (Γ₀ Γ₁ : Subgroup G) (hle : Γ₁ ≤ Γ₀) (hidx : Γ₁.relIndex Γ₀ ≠ 0)
    (hact : ∀ u a b, p a = p b → p (u * a) = p (u * b)) (S : Set G)
    (hsat : ∀ a b, p a = p b → a ∈ S → b ∈ S)
    (hcov : ∀ a, ∃ γ ∈ Γ₁, γ * a ∈ S)
    (hsep : ∀ a ∈ S, ∀ γ ∈ Γ₁, γ * a ∈ S → p (γ * a) = p a)
    (hfin : (trivPart p Γ₀).Finite) (a : G)
    (hgood : ∀ γ : Γ₀, p ((γ : G) * a) = p a → γ ∈ trivPart p Γ₀) :
    {γ : Γ₀ | (γ : G) * a ∈ S}.encard =
      ((Γ₁.relIndex Γ₀ * Nat.card {z : Γ₀ // z ∈ trivPart p Γ₀ ∧ (z : G) ∈ Γ₁} : ℕ) : ℕ∞) := by
  classical
  set H : Subgroup Γ₀ := Γ₁.subgroupOf Γ₀ with hH
  have hHidx : H.index ≠ 0 := hidx
  haveI : H.FiniteIndex := ⟨hHidx⟩
  haveI : Finite (Γ₀ ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Finite (trivPart p Γ₀) := hfin
  set Z := {z : Γ₀ // z ∈ trivPart p Γ₀ ∧ (z : G) ∈ Γ₁} with hZ
  haveI : Finite Z := Finite.of_injective (fun z : Z => (⟨z.1, z.2.1⟩ : trivPart p Γ₀))
    (fun x y h => Subtype.ext (congrArg (fun w : trivPart p Γ₀ => w.1) h))
  have memH : ∀ u : Γ₀, u ∈ H ↔ (u : G) ∈ Γ₁ := fun u => Subgroup.mem_subgroupOf

  have hex : ∀ q : Γ₀ ⧸ H, ∃ g : Γ₀, (g : G) * a ∈ S ∧ (QuotientGroup.mk g⁻¹ : Γ₀ ⧸ H) = q := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨γ, hγ, hmem⟩ := hcov (((d⁻¹ : Γ₀) : G) * a)
    refine ⟨⟨γ, hle hγ⟩ * d⁻¹, by simpa [mul_assoc] using hmem, ?_⟩
    rw [QuotientGroup.eq, inv_inv, inv_mul_cancel_right, memH]
    exact hγ
  choose g hgS hgq using hex
  have hmaps : ∀ x : (Γ₀ ⧸ H) × Z, (((x.2.1 * g x.1 : Γ₀) : G) * a) ∈ S := by
    rintro ⟨q, z⟩
    have h1 := z.2.1 ((g q : G) * a)
    refine hsat _ _ h1.symm (hgS q) |> fun h => ?_
    simpa [mul_assoc] using h
  let Φ : (Γ₀ ⧸ H) × Z → {γ : Γ₀ | (γ : G) * a ∈ S} := fun x => ⟨x.2.1 * g x.1, hmaps x⟩
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨q, z⟩ ⟨q', z'⟩ h
      have h0 : z.1 * g q = z'.1 * g q' := congrArg Subtype.val h
      have hq : q = q' := by
        rw [← hgq q, ← hgq q', QuotientGroup.eq, inv_inv, memH]
        have e : g q * (g q')⁻¹ = z.1⁻¹ * z'.1 := by
          rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h0, mul_inv_cancel_right]
        rw [e]
        exact Γ₁.mul_mem (Γ₁.inv_mem z.2.2) z'.2.2
      subst hq
      have hz : z.1 = z'.1 := mul_right_cancel h0
      exact Prod.ext rfl (Subtype.ext hz)
    · rintro ⟨γ, hγ⟩
      set q : Γ₀ ⧸ H := QuotientGroup.mk γ⁻¹ with hq
      have h1 : g q * γ⁻¹ ∈ H := by
        have := hgq q
        rw [hq, QuotientGroup.eq, inv_inv] at this
        exact this
      have hu : γ * (g q)⁻¹ ∈ H := by
        have := H.inv_mem h1
        simpa using this
      have hu' : ((γ * (g q)⁻¹ : Γ₀) : G) ∈ Γ₁ := (memH _).1 hu
      have h2 := hsep _ (hgS q) _ hu' (by simpa [mul_assoc] using hγ)
      have h3 : p ((γ : G) * a) = p ((g q : G) * a) := by simpa [mul_assoc] using h2
      have h4 := hact ((g q : G)⁻¹) _ _ h3
      have h5 : p ((((g q)⁻¹ * γ : Γ₀) : G) * a) = p a := by
        simpa [mul_assoc] using h4
      have hw := hgood _ h5
      have htriv : (γ * (g q)⁻¹ : Γ₀) ∈ trivPart p Γ₀ := by
        intro x
        have h6 := hact (g q : G) _ _ (hw (((g q)⁻¹ : Γ₀) * x))
        simpa [mul_assoc] using h6
      refine ⟨(q, ⟨γ * (g q)⁻¹, htriv, hu'⟩), Subtype.ext ?_⟩
      simp [Φ]
  haveI : Finite {γ : Γ₀ | (γ : G) * a ∈ S} := Finite.of_surjective Φ hbij.2
  have hc := Nat.card_eq_of_bijective Φ hbij
  rw [Nat.card_prod] at hc
  have hfinT : {γ : Γ₀ | (γ : G) * a ∈ S}.Finite := Set.toFinite _
  rw [← hfinT.cast_ncard_eq, ← Nat.card_coe_set_eq, ← hc]
  rfl

theorem setLIntegral_eq_mul_of_count [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (Γ₀ : Subgroup G) [Countable Γ₀] (FD : Set G) (hFD : IsFundamentalDomain Γ₀ FD μ) (S : Set G)
    (hS : MeasurableSet S) (f : G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Γ₀, ∀ a, f (γ * a) = f a) (N : ℕ∞)
    (hN : ∀ᵐ a ∂μ, {γ : Γ₀ | (γ : G) * a ∈ S}.encard = N) :
    ∫⁻ a in S, f a ∂μ = (N : ℝ≥0∞) * ∫⁻ a in FD, f a ∂μ := by
  classical
  have hm : ∀ γ : Γ₀, AEMeasurable (fun x => S.indicator f (γ • x)) (μ.restrict FD) := fun γ =>
    ((hf.indicator hS).comp (measurable_const_smul γ)).aemeasurable
  rw [← lintegral_indicator hS, hFD.lintegral_eq_tsum'', ← lintegral_tsum hm, ← lintegral_const_mul _ hf]
  refine lintegral_congr_ae ((ae_restrict_of_ae hN).mono fun a ha => ?_)
  have e : ∀ γ : Γ₀, S.indicator f (γ • a) = ({γ : Γ₀ | (γ : G) * a ∈ S}).indicator (1 : Γ₀ → ℝ≥0∞) γ * f a := by
    intro γ
    have hs : γ • a = (γ : G) * a := rfl
    by_cases h : (γ : G) * a ∈ S
    · rw [hs, Set.indicator_of_mem h, Set.indicator_of_mem (by exact h), hinv γ γ.2 a]
      simp
    · rw [hs, Set.indicator_of_notMem h, Set.indicator_of_notMem (by exact h)]
      simp
  simp only [e]
  have e2 : ∑' i : Γ₀, ({γ : Γ₀ | (γ : G) * a ∈ S}).indicator (1 : Γ₀ → ℝ≥0∞) i =
      (({γ : Γ₀ | (γ : G) * a ∈ S}.encard : ℕ∞) : ℝ≥0∞) := by
    rw [← ENNReal.tsum_set_one]
    exact (tsum_subtype _ (fun _ => (1 : ℝ≥0∞))).symm
  rw [ENNReal.tsum_mul_right, e2, ha]

end Orbit

section Ball

open scoped ComplexOrder in

theorem isPreconnected_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    IsPreconnected (ballDom q) := by
  have h0 : (0 : Fin n → ℂ) ∈ ballDom q := by
    intro τ
    have : ballMat q (0 : Fin n → ℂ) τ = 0 := by ext a b; simp [ballMat]
    simp [this, Matrix.PosDef.one]
  have hs : StarConvex ℝ (0 : Fin n → ℂ) (ballDom q) := by
    intro t ht a b ha hb hab
    rw [smul_zero, zero_add]
    intro τ
    have hZ : ballMat q (b • t) τ = (b : ℂ) • ballMat q t τ := by
      ext x y
      simp [ballMat]
    have hb1 : b ≤ 1 := by linarith
    have hP := ht τ
    set Z := ballMat q t τ
    have e : 1 - (ballMat q (b • t) τ)ᴴ * ballMat q (b • t) τ =
        ((1 - b ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin j') (Fin j') ℂ) + ((b ^ 2 : ℝ) : ℂ) • (1 - Zᴴ * Z) := by
      rw [hZ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      push_cast
      rw [sub_smul, one_smul, pow_two]
      abel
    rw [e]
    rcases eq_or_lt_of_le hb1 with h1 | h1
    · subst h1
      simpa using hP
    · have hc : (0 : ℂ) < ((1 - b ^ 2 : ℝ) : ℂ) := by
        have : (0 : ℝ) < 1 - b ^ 2 := by nlinarith
        exact_mod_cast this
      have hd : (0 : ℂ) ≤ ((b ^ 2 : ℝ) : ℂ) := by
        have : (0 : ℝ) ≤ b ^ 2 := by positivity
        exact_mod_cast this
      exact (Matrix.PosDef.one.smul hc).add_posSemidef (hP.posSemidef.smul hd)
  exact (hs.isPathConnected h0).isConnected.isPreconnected

theorem measurable_ballDens {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    Measurable (ballDens q) := by
  have hm : ∀ τ, Continuous fun t : Fin n → ℂ => ballMat q t τ := fun τ =>
    continuous_matrix fun a b => continuous_apply _
  have hd : ∀ τ, Measurable fun t : Fin n → ℂ => Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re := fun τ =>
    Real.measurable_log.comp (Complex.continuous_re.comp
      (continuous_const.sub ((hm τ).matrix_conjTranspose.matrix_mul (hm τ))).matrix_det).measurable
  unfold ballDens ballPot
  exact Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun τ _ => hd τ).neg)

end Ball

section Index

theorem relIndex_map_range_ne_zero {L G : Type} [Group L] [Group G] (φ : L →* G) (H : Subgroup L) (hH : H.index ≠ 0) :
    (H.map φ).relIndex φ.range ≠ 0 := by
  have e : (H.map φ).subgroupOf φ.range = H.map φ.rangeRestrict := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, Subtype.ext rfl⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, congrArg Subtype.val h⟩
  rw [Subgroup.relIndex, e]
  intro h0
  have := Subgroup.index_map_dvd H φ.rangeRestrict_surjective
  rw [h0, zero_dvd_iff] at this
  exact hH this

end Index

section Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {F : UnivFam E Ψ j j' n g Λ}

local notation "𝐯" => Pi.basisFun E (Fin (j + j'))

theorem pi_mem_ball (Δ : GroupDict F) (a) : Δ.π a ∈ ballDom F.q := by
  rw [← Δ.π_range]
  exact ⟨a, rfl⟩

theorem pi_mul_congr (Δ : GroupDict F) (u a b) (h : Δ.π a = Δ.π b) : Δ.π (u * a) = Δ.π (u * b) := by
  rw [Δ.π_fibre] at h ⊢
  simpa [mul_assoc] using h

theorem pi_eq_of_eqvBy (Δ : GroupDict F) (γ : latticeStab Δ.h Δ.e.range) (a) (t' : Fin n → ℂ)
    (ht' : t' ∈ ballDom F.q) (h : (F.R (Δ.π a)).EqvBy (F.R t') (Δ.α γ).1) :
    Δ.π (archEmbed Δ.h 𝐯 γ * a) = t' := by
  obtain ⟨h₁, hh₁⟩ := h
  obtain ⟨h₂, hh₂⟩ := Δ.α_act γ a
  obtain ⟨t₀, -, huniq⟩ := F.univ (F.R t') (F.form_eq t') (F.sig t' ht')
  have A : t' = t₀ := huniq t' ⟨ht', LinearEquiv.refl ℂ _, fun x => rfl⟩
  have B : Δ.π (archEmbed Δ.h 𝐯 γ * a) = t₀ := by
    refine huniq _ ⟨pi_mem_ball Δ _, h₂.symm.trans h₁, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := (Δ.α γ).1.surjective x
    have e1 := hh₁ y
    have e2 := hh₂ y
    simp only [LinearEquiv.trans_apply]
    rw [e2, LinearEquiv.symm_apply_apply, ← e1]
    rfl
  rw [A, B]

theorem null_fixed (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h 𝐯)) [μ.IsHaarMeasure] (u : archUnitary Δ.h 𝐯)
    (hu : ∃ a, Δ.π (u * a) ≠ Δ.π a) : μ {a | Δ.π (u * a) = Δ.π a} = 0 := by
  obtain ⟨c, -, -, hc⟩ := GlobalTheory.T.haar_pushforward_eq_ball_density E Ψ j j' n g Λ F Δ μ
  obtain ⟨A, G, hA, -, hAπ, -⟩ := Δ.act u
  obtain ⟨a₀, ha₀⟩ := hu
  rw [hAπ] at ha₀
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha₀
  have hfd : DifferentiableOn ℂ (fun t => A t i - t i) (ballDom F.q) :=
    (differentiableOn_pi.1 hA i).sub (differentiable_apply i).differentiableOn
  have hfa := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn (BallInverse.isOpen_ballDom F.q) hfd
  have hz := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd (BallInverse.isOpen_ballDom F.q)
    (isPreconnected_ballDom F.q) hfa ⟨Δ.π a₀, pi_mem_ball Δ a₀, sub_ne_zero.2 hi⟩
  set Zr := {z | z ∈ ballDom F.q ∧ A z i - z i = 0} with hZr
  have hν : (μ.map Δ.π) Zr = 0 := by
    rw [hc, Measure.smul_apply, smul_eq_mul]
    have h1 : (volume.restrict (ballDom F.q)) Zr = 0 := Measure.restrict_le_self.absolutelyContinuous hz
    have h2 := withDensity_absolutelyContinuous (volume.restrict (ballDom F.q))
      (fun t => ENNReal.ofReal (ballDens F.q t)) h1
    rw [h2, mul_zero]
  refine measure_mono_null ?_ (le_antisymm ((Measure.le_map_apply Δ.π_cont.aemeasurable Zr).trans hν.le) bot_le)
  intro a ha
  refine ⟨pi_mem_ball Δ a, ?_⟩
  have ha' : Δ.π (u * a) = Δ.π a := ha
  rw [hAπ] at ha'
  simp [ha']

theorem finite_trivPart (Δ : GroupDict F) :
    (trivPart Δ.π (archLatticeGroup Δ.h 𝐯 Δ.e.range)).Finite := by
  haveI : DiscreteTopology (archLatticeGroup Δ.h 𝐯 Δ.e.range) :=
    ArchLatticeDiscrete.proof Δ.h 𝐯 Δ.e.range Δ.integral.isLattice
  have hK : IsCompact (Δ.M.stab : Set (archUnitary Δ.h 𝐯)) := MajorantStabCompact.proof Δ.h 𝐯 Δ.M
  have hcl : IsClosed ((archLatticeGroup Δ.h 𝐯 Δ.e.range : Subgroup _) : Set (archUnitary Δ.h 𝐯)) :=
    Subgroup.isClosed_of_discrete
  have hf : (((archLatticeGroup Δ.h 𝐯 Δ.e.range : Subgroup _) : Set (archUnitary Δ.h 𝐯)) ∩ Δ.M.stab).Finite :=
    (hK.inter_left hcl).finite
      ((isDiscrete_iff_discreteTopology.2 (inferInstanceAs (DiscreteTopology (archLatticeGroup Δ.h 𝐯 Δ.e.range)))).mono
        Set.inter_subset_left)
  refine (hf.preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨γ.2, ?_⟩
  have h1 : Δ.π ((γ : archUnitary Δ.h 𝐯) * 1) = Δ.π 1 := hγ 1
  have h2 := (Δ.π_fibre 1 (γ : archUnitary Δ.h 𝐯)).1 (by simpa using h1.symm)
  simpa using h2

end Dict

section Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {F : UnivFam E Ψ j j' n g Λ}

local notation "𝐯" => Pi.basisFun E (Fin (j + j'))

theorem exists_const_lintegral (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h 𝐯)) [μ.IsHaarMeasure]
    (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) (FD : Set (archUnitary Δ.h 𝐯)) (hΓ : F.IsArith Γ)
    (hFF : F.IsFundSet Γ FF) (hFD : IsFundamentalDomain (archLatticeGroup Δ.h 𝐯 Δ.e.range) FD μ) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ Φ : (Fin n → ℂ) → ℝ≥0∞, Measurable Φ →
      (∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → Φ t = Φ t') →
      ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) = C * ∫⁻ a in FD, Φ (Δ.π a) ∂μ := by
  classical
  obtain ⟨c, hc0, hcT, hc⟩ := GlobalTheory.T.haar_pushforward_eq_ball_density E Ψ j j' n g Λ F Δ μ
  set Γ₀ := archLatticeGroup Δ.h 𝐯 Δ.e.range with hΓ₀
  let φ : latticeStab Δ.h Δ.e.range →* archUnitary Δ.h 𝐯 := (archEmbed Δ.h 𝐯).comp (latticeStab Δ.h Δ.e.range).subtype
  let ψ : latticeStab Δ.h Δ.e.range →* (Λ ≃ₗ[𝓞 E] Λ) := (autGrp F.form).subtype.comp Δ.α.toMonoidHom
  have hrange : φ.range = Γ₀ := by
    rw [hΓ₀, archLatticeGroup, MonoidHom.range_comp, Subgroup.range_subtype]
  have hψ : ψ.range = autGrp F.form := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 Δ.α.surjective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set Γ₁ : Subgroup (archUnitary Δ.h 𝐯) := (Γ.comap ψ).map φ with hΓ₁
  have hle : Γ₁ ≤ Γ₀ := by
    rw [← hrange, hΓ₁]
    exact Subgroup.map_le_range _ _
  have hidx : Γ₁.relIndex Γ₀ ≠ 0 := by
    rw [← hrange]
    refine relIndex_map_range_ne_zero φ _ ?_
    rw [Subgroup.index_comap, hψ]
    exact hΓ.2
  haveI : Countable Γ₀ := by
    have : Countable Δ.h.unitaryGroup := countable_unitaryGroup Δ.h 𝐯
    have h1 : ((Γ₀ : Subgroup _) : Set (archUnitary Δ.h 𝐯)).Countable := by
      rw [hΓ₀, archLatticeGroup, Subgroup.coe_map]
      exact (Set.to_countable _).image _
    exact h1.to_subtype
  set S : Set (archUnitary Δ.h 𝐯) := Δ.π ⁻¹' FF with hS
  have hSm : MeasurableSet S := Δ.π_cont.measurable hFF.1
  have hact := pi_mul_congr Δ
  have hsat : ∀ a b, Δ.π a = Δ.π b → a ∈ S → b ∈ S := fun a b h ha => by
    simpa [hS, ← h] using ha
  have hcov : ∀ a, ∃ γ ∈ Γ₁, γ * a ∈ S := by
    intro a
    obtain ⟨t', ht', γ, hγ, hE⟩ := hFF.2.2.1 (Δ.π a) (pi_mem_ball Δ a)
    set s := Δ.α.symm ⟨γ, hΓ.1 hγ⟩ with hs
    have hαs : (Δ.α s).1 = γ := by simp [hs]
    refine ⟨φ s, ⟨s, ?_, rfl⟩, ?_⟩
    · show ψ s ∈ Γ
      show (Δ.α s).1 ∈ Γ
      rw [hαs]
      exact hγ
    · have := pi_eq_of_eqvBy Δ s a t' (hFF.2.1 ht') (by rw [hαs]; exact hE)
      show Δ.π (φ s * a) ∈ FF
      have e : φ s = archEmbed Δ.h 𝐯 s := rfl
      rw [e, this]
      exact ht'
  have hsep : ∀ a ∈ S, ∀ γ ∈ Γ₁, γ * a ∈ S → Δ.π (γ * a) = Δ.π a := by
    rintro a ha _ ⟨s, hs, rfl⟩ hγ
    refine (hFF.2.2.2 _ ha _ hγ ⟨(Δ.α s).1, hs, Δ.α_act s a⟩).symm
  have hfin := finite_trivPart Δ
  set N : ℕ := Γ₁.relIndex Γ₀ * Nat.card {z : Γ₀ // z ∈ trivPart Δ.π Γ₀ ∧ (z : archUnitary Δ.h 𝐯) ∈ Γ₁} with hN
  have hN0 : N ≠ 0 := by
    refine Nat.mul_ne_zero hidx ?_
    haveI : Finite (trivPart Δ.π Γ₀) := hfin
    haveI : Finite {z : Γ₀ // z ∈ trivPart Δ.π Γ₀ ∧ (z : archUnitary Δ.h 𝐯) ∈ Γ₁} :=
      Finite.of_injective (fun z => (⟨z.1, z.2.1⟩ : trivPart Δ.π Γ₀))
        (fun x y h => Subtype.ext (congrArg (fun w : trivPart Δ.π Γ₀ => w.1) h))
    haveI : Nonempty {z : Γ₀ // z ∈ trivPart Δ.π Γ₀ ∧ (z : archUnitary Δ.h 𝐯) ∈ Γ₁} :=
      ⟨⟨1, fun a => by simp, Γ₁.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hgood : ∀ᵐ a ∂μ, ∀ γ : Γ₀, Δ.π ((γ : archUnitary Δ.h 𝐯) * a) = Δ.π a → γ ∈ trivPart Δ.π Γ₀ := by
    rw [ae_all_iff]
    intro γ
    by_cases hγ : γ ∈ trivPart Δ.π Γ₀
    · exact ae_of_all _ fun _ _ => hγ
    · have hne : ∃ a, Δ.π ((γ : archUnitary Δ.h 𝐯) * a) ≠ Δ.π a := by
        by_contra hcon
        push Not at hcon
        exact hγ hcon
      have h0 := null_fixed Δ μ (γ : archUnitary Δ.h 𝐯) hne
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with a ha h1
      exact absurd h1 ha
  have hcount : ∀ᵐ a ∂μ, {γ : Γ₀ | (γ : archUnitary Δ.h 𝐯) * a ∈ S}.encard = ((N : ℕ) : ℕ∞) :=
    hgood.mono fun a ha =>
      encard_translates Δ.π Γ₀ Γ₁ hle hidx hact S hsat hcov hsep hfin a ha
  refine ⟨c⁻¹ * (N : ℝ≥0∞), ?_, ?_, fun Φ hΦ hinv => ?_⟩
  · exact mul_ne_zero (ENNReal.inv_ne_zero.2 hcT) (by exact_mod_cast hN0)
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) (ENNReal.natCast_ne_top N)
  have hπm : Measurable Δ.π := Δ.π_cont.measurable
  have hdens : Measurable fun t => ENNReal.ofReal (ballDens F.q t) :=
    ENNReal.measurable_ofReal.comp (measurable_ballDens F.q)
  have hfinv : ∀ γ ∈ Γ₀, ∀ a, Φ (Δ.π (γ * a)) = Φ (Δ.π a) := by
    rintro _ ⟨s, hs, rfl⟩ a
    exact (hinv _ (pi_mem_ball Δ a) _ (pi_mem_ball Δ _)
      ⟨(Δ.α ⟨s, hs⟩).1, (Δ.α ⟨s, hs⟩).2, Δ.α_act ⟨s, hs⟩ a⟩).symm
  have h1 := setLIntegral_eq_mul_of_count μ Γ₀ FD hFD S hSm (fun a => Φ (Δ.π a)) (hΦ.comp hπm) hfinv
    ((N : ℕ) : ℕ∞) hcount
  have h2 : ∫⁻ a in S, Φ (Δ.π a) ∂μ = c * ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) := by
    rw [hS, ← setLIntegral_map hFF.1 hΦ hπm, hc, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      restrict_withDensity hFF.1, lintegral_withDensity_eq_lintegral_mul _ hdens hΦ,
      Measure.restrict_restrict hFF.1, Set.inter_eq_left.2 hFF.2.1]
    congr 1
    refine lintegral_congr fun t => ?_
    simp [mul_comm]
  rw [h2] at h1
  calc ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t)
      = c⁻¹ * (c * ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hcT, one_mul]
    _ = c⁻¹ * (N : ℝ≥0∞) * ∫⁻ a in FD, Φ (Δ.π a) ∂μ := by
        rw [h1, mul_assoc]
        simp

end Dict

theorem lintegral_fundSet_eq_const_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure] (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) (FD : Set (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))), F.IsArith Γ → F.IsFundSet Γ FF → IsFundamentalDomain (archLatticeGroup Δ.h (Pi.basisFun E (Fin (j + j'))) Δ.e.range) FD μ → ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ Φ : (Fin n → ℂ) → ℝ≥0∞, Measurable Φ → (∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → Φ t = Φ t') → ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) = C * ∫⁻ a in FD, Φ (Δ.π a) ∂μ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F Δ μ _ Γ FF FD hΓ hFF hFD
  exact exists_const_lintegral Δ μ Γ FF FD hΓ hFF hFD

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_set_to_fundamental_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure] (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) (FD : Set (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))), F.IsArith Γ → F.IsFundSet Γ FF → IsFundamentalDomain (archLatticeGroup Δ.h (Pi.basisFun E (Fin (j + j'))) Δ.e.range) FD μ → ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ Φ : (Fin n → ℂ) → ℝ≥0∞, Measurable Φ → (∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → Φ t = Φ t') → ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) = C * ∫⁻ a in FD, Φ (Δ.π a) ∂μ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.lintegral_fundSet_eq_const_mul
end

section
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallMean

open GroundTheory.Heights₂.Heights.LowerBound

theorem weighted_mean {X : Type} [MeasurableSpace X] (m : Measure X) (S : Set X) (d U lam : X → ℝ) (f j' : ℕ) (vr rd : ℝ)
    (hd : Measurable d) (hdpos : ∀ x, 0 < d x)
    (h0 : ∫⁻ t in S, ENNReal.ofReal (d t) ∂m ≠ 0) (hT : ∫⁻ t in S, ENNReal.ofReal (d t) ∂m ≠ ⊤)
    (U_meas : Measurable U) (lam_meas : Measurable lam) (lam_pos : ∀ z, 0 < lam z) (U_nonneg : ∀ z, 0 ≤ U z)
    (U_le : ∀ z, U z ≤ f * j' * (2 * max 0 (Real.log (1 / lam z)) + Real.log (2 * f * j' * rd)))
    (hf : 1 ≤ f) (hj : 1 ≤ j') (hvr : 1 ≤ vr) (hrd : 1 ≤ rd)
    (mean : ∫⁻ t in S, ENNReal.ofReal (Real.log (vr ^ (-(1 / 2 : ℝ)) / lam t)) * ENNReal.ofReal (d t) ∂m ≤
      3 * ∫⁻ t in S, ENNReal.ofReal (d t) ∂m) :
    IntegrableOn d S m ∧ 0 < ∫ t in S, d t ∂m ∧ IntegrableOn (fun t => U t * d t) S m ∧
      ∫ t in S, U t * d t ∂m ≤
        f * j' * (6 + Real.log vr + Real.log (2 * f * j' * rd)) * ∫ t in S, d t ∂m := by
  set w : X → ℝ≥0∞ := fun t => ENNReal.ofReal (d t) with hw
  have hwm : Measurable w := hd.ennreal_ofReal
  have hwlt : ∀ᵐ x ∂(m.restrict S), w x < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  set V : ℝ≥0∞ := ∫⁻ t in S, w t ∂m with hV
  set ρ : Measure X := (m.restrict S).withDensity w with hρ
  have hρuniv : ρ Set.univ = V := by
    rw [hρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  set ν : Measure X := V⁻¹ • ρ with hν
  have hprob : IsProbabilityMeasure ν :=
    ⟨by simp [hν, hρuniv, ENNReal.inv_mul_cancel h0 hT]⟩
  have hinv0 : V⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hT
  have hinvT : V⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  have hdnn : ∀ x, 0 ≤ d x := fun x => (hdpos x).le
  have hwr : ∀ x, (w x).toReal = d x := fun x => ENNReal.toReal_ofReal (hdnn x)

  have hdint : Integrable d (m.restrict S) := by
    refine ⟨hd.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hdnn)]
    exact lt_top_iff_ne_top.2 hT
  have hdval : ∫ t in S, d t ∂m = V.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hdnn) hd.aestronglyMeasurable]
  have hVpos : 0 < V.toReal := ENNReal.toReal_pos h0 hT

  set r : ℝ := vr ^ (-(1 / 2 : ℝ)) with hr
  set L : X → ℝ := fun z => max 0 (Real.log (r / lam z)) with hL
  have hLm : Measurable L := measurable_const.max (Real.measurable_log.comp (lam_meas.const_div r))
  have hLnn : ∀ z, 0 ≤ L z := fun z => le_max_left _ _
  have hLof : ∀ z, ENNReal.ofReal (L z) = ENNReal.ofReal (Real.log (r / lam z)) := fun z => by
    rcases le_total 0 (Real.log (r / lam z)) with h | h
    · simp only [hL, max_eq_right h]
    · simp only [hL, max_eq_left h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have hlin : ∀ g : X → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂ν = V⁻¹ * ∫⁻ x in S, w x * g x ∂m := fun g hg => by
    rw [hν, lintegral_smul_measure, hρ, lintegral_withDensity_eq_lintegral_mul _ hwm hg]
    rfl
  have hLle : ∫⁻ x, ENNReal.ofReal (L x) ∂ν ≤ 3 := by
    rw [hlin _ hLm.ennreal_ofReal]
    have e : ∫⁻ x in S, w x * ENNReal.ofReal (L x) ∂m ≤ 3 * V := by
      refine le_of_eq_of_le (lintegral_congr fun x => ?_) mean
      rw [hLof, mul_comm]
    calc V⁻¹ * ∫⁻ x in S, w x * ENNReal.ofReal (L x) ∂m ≤ V⁻¹ * (3 * V) := by gcongr
      _ = 3 := by
        rw [mul_left_comm, ENNReal.inv_mul_cancel h0 hT, mul_one]
  have hLint : Integrable L ν := by
    refine ⟨hLm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hLnn)]
    exact lt_of_le_of_lt hLle (by simp)
  have hLmean : ∫ z, L z ∂ν ≤ 3 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hLnn) hLm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hLle)
  have H : MeanCuspWeight.Hyp ν U lam f j' vr rd :=
    { isProbability := hprob
      U_meas := U_meas
      lam_meas := lam_meas
      lam_pos := lam_pos
      U_nonneg := U_nonneg
      U_le := U_le
      one_le_f := hf
      one_le_j' := hj
      one_le_vr := hvr
      one_le_rd := hrd
      logPlus_integrable := hLint
      logPlus_mean := hLmean }
  have hbound := MeanCuspWeight.full X ν U lam f j' vr rd H

  have hvr0 : 0 < vr := lt_of_lt_of_le one_pos hvr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hvr0 _
  have hlogvr : 0 ≤ Real.log vr := Real.log_nonneg hvr
  have hlogr : Real.log r = -(1 / 2) * Real.log vr := Real.log_rpow hvr0 _
  have key : ∀ z, max 0 (Real.log (1 / lam z)) ≤ L z + 1 / 2 * Real.log vr := by
    intro z
    have hl := lam_pos z
    have e : Real.log (1 / lam z) = Real.log (r / lam z) + 1 / 2 * Real.log vr := by
      rw [Real.log_div one_ne_zero hl.ne', Real.log_div hr0.ne' hl.ne', hlogr, Real.log_one]
      ring
    refine max_le (by have := hLnn z; positivity) ?_
    rw [e]
    have : Real.log (r / lam z) ≤ L z := le_max_right _ _
    linarith
  have hfj : (0 : ℝ) ≤ (f : ℝ) * j' := by positivity
  have hUint : Integrable U ν := by
    have hg : Integrable (fun z => (f : ℝ) * j' * (2 * (L z + 1 / 2 * Real.log vr) +
        Real.log (2 * f * j' * rd))) ν :=
      (((hLint.add (integrable_const _)).const_mul 2).add (integrable_const _)).const_mul _
    refine hg.mono' U_meas.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (U_nonneg z)]
    refine (U_le z).trans (mul_le_mul_of_nonneg_left ?_ hfj)
    linarith [key z]
  have hUρ : Integrable U ρ := (integrable_smul_measure hinv0 hinvT).1 hUint
  have hUd : Integrable (fun t => U t * d t) (m.restrict S) := by
    have := (integrable_withDensity_iff_integrable_smul' hwm hwlt).1 hUρ
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul, hwr, mul_comm]
  have hval : ∫ z, U z ∂ν = (V.toReal)⁻¹ * ∫ t in S, U t * d t ∂m := by
    rw [hν, integral_smul_measure, hρ, integral_withDensity_eq_integral_toReal_smul hwm hwlt,
      ENNReal.toReal_inv, smul_eq_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul, hwr, mul_comm]
  refine ⟨hdint, by rw [hdval]; exact hVpos, hUd, ?_⟩
  rw [hval, inv_mul_le_iff₀ hVpos] at hbound
  rw [hdval]
  linarith

end GlobalTheory.CompanionTheory.Ar.Cusp.BallMean

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallMean

section Card

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hom_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  rw [injective_iff_map_eq_zero]
  have hk : RingHom.ker s = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [eq_bot_iff]
    intro m hm
    have h1 : s (algebraMap ℤ (𝓞 E) m) = 0 := hm
    have h2 : ((m : ℤ) : ℂ) = 0 := by simpa using h1
    simpa using (Int.cast_eq_zero.1 h2)
  intro a ha
  have : a ∈ RingHom.ker s := ha
  rw [hk] at this
  simpa using this

theorem finrank_eq_two_mul {Ψ : Type} [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) :
    Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  classical
  let e : (E →+* ℂ) ≃ (𝓞 E →+* ℂ) :=
    { toFun := fun φ => φ.comp (algebraMap (𝓞 E) E)
      invFun := fun s => IsFractionRing.lift (hom_injective s)
      left_inv := fun φ => by
        apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
        ext x
        simp
      right_inv := fun s => by
        ext x
        simp }
  haveI : Fintype (𝓞 E →+* ℂ) := Fintype.ofEquiv _ e
  have hc : Fintype.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
    rw [← Fintype.card_congr e]
    exact NumberField.Embeddings.card E ℂ
  let P : (𝓞 E →+* ℂ) → Prop := fun s => ∃ τ, σ τ = s
  let c : (𝓞 E →+* ℂ) → (𝓞 E →+* ℂ) := fun s => (starRingEnd ℂ).comp s
  have hcc : ∀ s, c (c s) = s := fun s => by
    ext x
    simp [c]
  have hP : ∀ s, P s ↔ ¬ P (c s) := hσ.2
  have e1 : {s // P s} ≃ Ψ := (Equiv.ofInjective σ hσ.1).symm
  have e2 : {s // ¬ P s} ≃ {s // P s} :=
    { toFun := fun s => ⟨c s.1, by
        by_contra hn
        exact s.2 ((hP s.1).2 hn)⟩
      invFun := fun s => ⟨c s.1, (hP s.1).1 s.2⟩
      left_inv := fun s => Subtype.ext (hcc s.1)
      right_inv := fun s => Subtype.ext (hcc s.1) }
  have := Fintype.card_congr (Equiv.sumCompl P)
  rw [Fintype.card_sum, Fintype.card_congr e2, Fintype.card_congr e1, hc] at this
  omega

theorem one_le_rd : 1 ≤ hostRd E := by
  unfold hostRd
  refine Real.one_le_rpow ?_ (by positivity)
  have h : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
  rw [← Int.cast_abs]
  exact_mod_cast h

end Card

section Dens

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem measurable_ballDens (q : Ψ × Fin j × Fin j' ≃ Fin n) : Measurable (ballDens q) := by
  have hZ : ∀ τ, Continuous fun t : Fin n → ℂ => ballMat q t τ := fun τ =>
    continuous_matrix fun a b => continuous_apply _
  have hdet : ∀ τ, Measurable fun t : Fin n → ℂ =>
      Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re := fun τ =>
    Real.measurable_log.comp (Complex.continuous_re.comp
      (continuous_const.sub ((hZ τ).matrix_conjTranspose.matrix_mul (hZ τ))).matrix_det).measurable
  have hpot : Measurable (ballPot q) := by
    unfold ballPot
    exact (Finset.measurable_sum _ fun τ _ => hdet τ).neg
  unfold ballDens
  exact Real.measurable_exp.comp (hpot.const_mul _)

theorem ballDens_pos (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : 0 < ballDens q t := Real.exp_pos _

end Dens

end GlobalTheory.CompanionTheory.Ar.Cusp.BallMean

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open BallMean

theorem fund_set_mean_cuspW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)), F.IsArith Γ → F.IsFundSet Γ FF → 1 ≤ j' → 3 * j' + 1 ≤ j + j' → IntegrableOn (ballDens F.q) FF ∧ 0 < ∫ t in FF, ballDens F.q t ∧ IntegrableOn (fun t => (F.R t).cuspW F.σ * ballDens F.q t) FF ∧ ∫ t in FF, (F.R t).cuspW F.σ * ballDens F.q t ≤ Fintype.card Ψ * j' * (6 + Real.log (2 * Fintype.card Ψ * hostRd E) + Real.log (2 * Fintype.card Ψ * j' * hostRd E)) * ∫ t in FF, ballDens F.q t := by
  classical
  intro E _ _ _ Ψ _ j j' n g Λ _ _ H F Γ FF hA hFS hj' hN
  obtain ⟨Δ⟩ := GlobalTheory.T.exists_group_dictionary E Ψ j j' n g Λ H F
  have hcard := finrank_eq_two_mul F.cm
  have hrd : 1 ≤ hostRd E := one_le_rd
  have hf : 1 ≤ Fintype.card Ψ := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hfR : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast hf
  have hjR : (1 : ℝ) ≤ j' := by exact_mod_cast hj'
  set vr : ℝ := 2 * Fintype.card Ψ * hostRd E with hvrdef
  have hvr : 1 ≤ vr := by nlinarith
  have hvr0 : 0 < vr := by linarith
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.cm_field_small_integral_basis E
  have ha2' : ∀ i (s : E →+* ℂ), ‖s (a i)‖ ≤ vr := fun i s => by
    have := ha2 i s
    rw [hcard] at this
    rw [hvrdef]
    simpa using this
  let μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j')))) := Measure.haar
  obtain ⟨FD, hFD, h0, hT, hmean⟩ := GlobalTheory.T.first_minimum_integral_bound E Ψ j j' n g Λ F Δ μ vr hj' hN hvr0 ⟨a, ha1, ha2'⟩
  obtain ⟨C, hC0, hCT, hC⟩ := GlobalTheory.T.fundamental_set_to_fundamental_domain E Ψ j j' n g Λ F Δ μ Γ FF FD hA hFS hFD
  obtain ⟨hcont, hUm, hopen, hinv⟩ := GlobalTheory.T.first_minimum_continuous_cusp_weight_measurable E Ψ j j' n g Λ F hj'
  have hu1 : ∀ t ∈ ballDom F.q, _ := fun t ht =>
    GlobalTheory.T.first_minimum_and_cusp_weight_bounds E g Λ Ψ (F.R t) F.σ j' F.cm (fun τ => (F.sig t ht τ).1) hj'
  obtain ⟨hFFm, hFFsub, -, -⟩ := hFS
  set B := ballDom F.q with hB
  have hBm : MeasurableSet B := hopen.measurableSet
  set lam : (Fin n → ℂ) → ℝ := B.piecewise (fun t => (F.R t).lam1) 1 with hlam
  set U : (Fin n → ℂ) → ℝ := B.indicator fun t => (F.R t).cuspW F.σ with hU
  have hlamB : ∀ t ∈ B, lam t = (F.R t).lam1 := fun t ht => Set.piecewise_eq_of_mem _ _ _ ht
  have hUB : ∀ t ∈ B, U t = (F.R t).cuspW F.σ := fun t ht => Set.indicator_of_mem ht _
  have hlamm : Measurable lam := hcont.measurable_piecewise continuousOn_const hBm
  have hlampos : ∀ z, 0 < lam z := fun z => by
    by_cases hz : z ∈ B
    · rw [hlamB z hz]
      exact (hu1 z hz).1
    · have h1 : lam z = 1 := Set.piecewise_eq_of_notMem _ _ _ hz
      rw [h1]
      exact one_pos
  have hUnn : ∀ z, 0 ≤ U z := fun z => by
    by_cases hz : z ∈ B
    · rw [hUB z hz]
      exact (hu1 z hz).2.2.2.1
    · simp [hU, Set.indicator_of_notMem hz]
  have hUle : ∀ z, U z ≤ Fintype.card Ψ * j' * (2 * max 0 (Real.log (1 / lam z)) +
      Real.log (2 * Fintype.card Ψ * j' * hostRd E)) := fun z => by
    by_cases hz : z ∈ B
    · rw [hUB z hz, hlamB z hz]
      exact (hu1 z hz).2.2.2.2
    · have h1 : U z = 0 := by simp [hU, Set.indicator_of_notMem hz]
      rw [h1]
      have hl : 0 ≤ Real.log (2 * Fintype.card Ψ * j' * hostRd E) := by
        refine Real.log_nonneg ?_
        have : (1 : ℝ) ≤ (Fintype.card Ψ : ℝ) * j' := by nlinarith
        nlinarith
      have hm : (0 : ℝ) ≤ max 0 (Real.log (1 / lam z)) := le_max_left _ _
      positivity

  have hvol : ∫⁻ t in FF, ENNReal.ofReal (ballDens F.q t) = C * μ FD := by
    have := hC (fun _ => 1) measurable_const (fun _ _ _ _ _ => rfl)
    simpa using this
  have hV0 : ∫⁻ t in FF, ENNReal.ofReal (ballDens F.q t) ≠ 0 := by
    rw [hvol]
    exact mul_ne_zero hC0 h0
  have hVT : ∫⁻ t in FF, ENNReal.ofReal (ballDens F.q t) ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.mul_ne_top hCT hT

  set r : ℝ := vr ^ (-(1 / 2 : ℝ)) with hr
  set Φ : (Fin n → ℂ) → ℝ≥0∞ := B.indicator fun t => ENNReal.ofReal (Real.log (r / lam t)) with hΦ
  have hΦm : Measurable Φ :=
    ((Real.measurable_log.comp (hlamm.const_div r)).ennreal_ofReal).indicator hBm
  have hΦB : ∀ t ∈ B, Φ t = ENNReal.ofReal (Real.log (r / lam t)) := fun t ht => Set.indicator_of_mem ht _
  have hΦinv : ∀ t ∈ B, ∀ t' ∈ B, F.Eqv (autGrp F.form) t t' → Φ t = Φ t' := fun t ht t' ht' he => by
    rw [hΦB t ht, hΦB t' ht', hlamB t ht, hlamB t' ht', (hinv t ht t' ht' he).1]
  have hπ : ∀ a, Δ.π a ∈ B := fun a => by
    rw [hB, ← Δ.π_range]
    exact Set.mem_range_self a
  have hmean' : ∫⁻ t in FF, ENNReal.ofReal (Real.log (r / lam t)) * ENNReal.ofReal (ballDens F.q t) ≤
      3 * ∫⁻ t in FF, ENNReal.ofReal (ballDens F.q t) := by
    have e1 : ∫⁻ t in FF, ENNReal.ofReal (Real.log (r / lam t)) * ENNReal.ofReal (ballDens F.q t) =
        ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) :=
      setLIntegral_congr_fun hFFm fun t ht => by rw [hΦB t (hFFsub ht)]
    have e2 : ∫⁻ a in FD, Φ (Δ.π a) ∂μ =
        ∫⁻ a in FD, ENNReal.ofReal (Real.log (vr ^ (-(1 / 2 : ℝ)) / (F.R (Δ.π a)).lam1)) ∂μ :=
      lintegral_congr fun a => by rw [hΦB _ (hπ a), hlamB _ (hπ a)]
    rw [e1, hC Φ hΦm hΦinv, hvol, e2]
    calc C * ∫⁻ a in FD, ENNReal.ofReal (Real.log (vr ^ (-(1 / 2 : ℝ)) / (F.R (Δ.π a)).lam1)) ∂μ
        ≤ C * (3 * μ FD) := by gcongr
      _ = 3 * (C * μ FD) := by rw [mul_left_comm]
  obtain ⟨i1, i2, i3, i4⟩ := weighted_mean volume FF (ballDens F.q) U lam (Fintype.card Ψ) j' vr (hostRd E)
    (measurable_ballDens F.q) (ballDens_pos F.q) hV0 hVT hUm hlamm hlampos hUnn hUle hf hj' hvr hrd hmean'
  have hUeq : ∀ t ∈ FF, U t * ballDens F.q t = (F.R t).cuspW F.σ * ballDens F.q t := fun t ht => by
    rw [hUB t (hFFsub ht)]
  refine ⟨i1, i2, i3.congr_fun hUeq hFFm, ?_⟩
  rw [← setIntegral_congr_fun hFFm hUeq]
  exact i4

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end
end

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_weight_integrable_on_fundamental_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)), F.IsArith Γ → F.IsFundSet Γ FF → 1 ≤ j' → 3 * j' + 1 ≤ j + j' → IntegrableOn (ballDens F.q) FF ∧ 0 < ∫ t in FF, ballDens F.q t ∧ IntegrableOn (fun t => (F.R t).cuspW F.σ * ballDens F.q t) FF ∧ ∫ t in FF, (F.R t).cuspW F.σ * ballDens F.q t ≤ Fintype.card Ψ * j' * (6 + Real.log (2 * Fintype.card Ψ * hostRd E) + Real.log (2 * Fintype.card Ψ * j' * hostRd E)) * ∫ t in FF, ballDens F.q t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW
end
