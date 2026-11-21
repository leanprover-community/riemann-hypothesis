import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermStronglyMeasurable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangians
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActEquivSymmApply
import BuildAid.ForwardExisting

section
section
open MeasureTheory MulAction
open scoped Pointwise ENNReal

namespace GlobalTheory

section SlopeTestRemainingChoices
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem setIntegral_subgroup_mul_left (ν : Measure G) [ν.IsMulLeftInvariant] {Λ : Subgroup G}
    (c : Λ) (f : G → ℂ) (s : Set G) :
    ∫ g in s, f ((c : G) * g) ∂ν = ∫ g in c • s, f g ∂ν := by
  have hpre : (fun g : G => (c : G) * g) ⁻¹' (c • s) = s := by
    ext g
    simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have h := (measurePreserving_mul_left ν (c : G)).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft (c : G)) f (c • s)
  rwa [hpre] at h

theorem setLIntegral_subgroup_mul_left (ν : Measure G) [ν.IsMulLeftInvariant] {Λ : Subgroup G}
    (c : Λ) (f : G → ℝ≥0∞) (s : Set G) :
    ∫⁻ g in s, f ((c : G) * g) ∂ν = ∫⁻ g in c • s, f g ∂ν := by
  have hpre : (fun g : G => (c : G) * g) ⁻¹' (c • s) = s := by
    ext g
    simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have h := (measurePreserving_mul_left ν (c : G)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft (c : G)) f (c • s)
  rwa [hpre] at h

theorem isFundamentalDomain_iUnion_inv_smul {ν : Measure G} [ν.IsMulLeftInvariant]
    {Λ : Subgroup G} [Countable Λ] {𝓖 : Set G} (h : IsFundamentalDomain Λ 𝓖 ν)
    (S : Subgroup Λ) [Countable (Λ ⧸ S)] :
    IsFundamentalDomain (S.map Λ.subtype) (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ν where
  nullMeasurableSet := .iUnion fun q => h.nullMeasurableSet_smul _
  ae_covers := by
    filter_upwards [h.ae_covers] with g hg
    obtain ⟨l, hl⟩ := hg
    have hs : ((QuotientGroup.mk l : Λ ⧸ S).out)⁻¹ * l ∈ S :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
    refine ⟨⟨(((QuotientGroup.mk l : Λ ⧸ S).out⁻¹ * l : Λ) : G), ⟨_, hs, rfl⟩⟩,
      Set.mem_iUnion.2 ⟨QuotientGroup.mk l, ?_⟩⟩
    rw [Set.mem_inv_smul_set_iff]
    simpa [Subgroup.smul_def, mul_assoc] using hl
  aedisjoint := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
    have hsub : (⟨Λ.subtype s', hs⟩ : S.map Λ.subtype) • (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ∩
        (⟨Λ.subtype t', ht⟩ : S.map Λ.subtype) • (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ⊆
        ⋃ q : Λ ⧸ S, ⋃ r : Λ ⧸ S, ((s' * (q.out)⁻¹) • 𝓖 ∩ (t' * (r.out)⁻¹) • 𝓖) := by
      rintro x ⟨hx1, hx2⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_iUnion] at hx1 hx2
      obtain ⟨q, hq⟩ := hx1
      obtain ⟨r, hr⟩ := hx2
      rw [Set.mem_inv_smul_set_iff] at hq hr
      refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨r, ?_, ?_⟩⟩
      · rw [Set.mem_smul_set_iff_inv_smul_mem]
        simpa [Subgroup.smul_def, mul_assoc] using hq
      · rw [Set.mem_smul_set_iff_inv_smul_mem]
        simpa [Subgroup.smul_def, mul_assoc] using hr
    refine measure_mono_null hsub (measure_iUnion_null fun q => measure_iUnion_null fun r => ?_)
    apply h.aedisjoint
    intro he
    apply hst
    have he' : (q.out) * s'⁻¹ = (r.out) * t'⁻¹ := by
      have := congrArg (·⁻¹) he
      simpa [mul_inv_rev] using this
    have hqr : q = r := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
      apply QuotientGroup.eq.mpr
      have : (q.out)⁻¹ * r.out = s'⁻¹ * t' := by
        rw [← mul_inv_eq_iff_eq_mul.mpr he'.symm]
        group
      rw [this]
      exact S.mul_mem (S.inv_mem hs') ht'
    subst hqr
    have : s' = t' := by simpa using he'
    subst this
    rfl

end SlopeTestRemainingChoices

theorem tsum_setIntegral_eq_zero_of_stabilizer :
    ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G)
    [ν.IsMulLeftInvariant], SFinite ν → ∀ (Λ : Subgroup G), Countable Λ → ∀ 𝓖 : Set G,
    IsFundamentalDomain Λ 𝓖 ν → ∀ (a : Λ → X → X), (∀ x, a 1 x = x) →
    (∀ γ δ x, a (γ * δ) x = a γ (a δ x)) → ∀ F : X → G → ℂ,
    (∀ γ x g, F (a γ x) g = F x ((γ : G)⁻¹ * g)) → (∀ x, AEStronglyMeasurable (F x) ν) →
    ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν ≠ ⊤ →
    (∀ x (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x = x) → ∀ 𝓓 : Set G,
      IsFundamentalDomain Γ 𝓓 ν → IntegrableOn (F x) 𝓓 ν → ∫ g in 𝓓, F x g ∂ν = 0) →
    ∑' x, ∫ g in 𝓖, F x g ∂ν = 0 := by
  intro G X _ _ _ ν _ _ Λ hΛ 𝓖 h𝓖 a ha1 ham F hF hmeas hfin hzero
  letI : MulAction Λ X := { smul := a, one_smul := ha1, mul_smul := ham }
  have hsmul : ∀ (γ : Λ) (x : X), γ • x = a γ x := fun _ _ => rfl
  set T : X → ℂ := fun x => ∫ g in 𝓖, F x g ∂ν with hTdef
  have hT : ∀ (γ : Λ) x, T (γ • x) = ∫ g in γ⁻¹ • 𝓖, F x g ∂ν := by
    intro γ x
    rw [← setIntegral_subgroup_mul_left ν γ⁻¹]
    simp only [hTdef, hsmul, hF, Subgroup.coe_inv]
  have hL : ∀ (γ : Λ) x, ∫⁻ g in 𝓖, ‖F (γ • x) g‖ₑ ∂ν = ∫⁻ g in γ⁻¹ • 𝓖, ‖F x g‖ₑ ∂ν := by
    intro γ x
    rw [← setLIntegral_subgroup_mul_left ν γ⁻¹]
    simp only [hsmul, hF, Subgroup.coe_inv]
  have hsum : Summable T := by
    refine Summable.of_norm ?_
    have h1 : ∑' x, ‖T x‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hfin
      (ENNReal.tsum_le_tsum fun x => enorm_integral_le_lintegral_enorm _)
    simpa using ENNReal.summable_toReal h1
  have horb : ∀ x₀ : X,
      HasSum (fun q : Λ ⧸ stabilizer Λ x₀ => T (ofQuotientStabilizer Λ x₀ q)) 0 := by
    intro x₀
    set S := stabilizer Λ x₀ with hSdef
    haveI : Countable (Λ ⧸ S) := QuotientGroup.mk_surjective.countable
    have hofq : ∀ q : Λ ⧸ S, ofQuotientStabilizer Λ x₀ q = q.out • x₀ := by
      intro q
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hinj : Function.Injective fun q : Λ ⧸ S => q.out • x₀ := by
      intro q r hqr
      exact injective_ofQuotientStabilizer Λ x₀ (by simpa only [hofq] using hqr)
    have hD := isFundamentalDomain_iUnion_inv_smul h𝓖 S
    have hdisj : Pairwise (Function.onFun (AEDisjoint ν) fun q : Λ ⧸ S => (q.out)⁻¹ • 𝓖) := by
      intro q r hqr
      refine h𝓖.aedisjoint fun e => hqr ?_
      exact Quotient.out_injective (inv_injective e)
    have hint : IntegrableOn (F x₀) (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ν := by
      refine ⟨(hmeas x₀).restrict, ?_⟩
      show ∫⁻ g in ⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν < ⊤
      calc ∫⁻ g in ⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν
          ≤ ∑' q : Λ ⧸ S, ∫⁻ g in (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν := lintegral_iUnion_le _ _
        _ = ∑' q : Λ ⧸ S, ∫⁻ g in 𝓖, ‖F (q.out • x₀) g‖ₑ ∂ν := by simp only [hL]
        _ ≤ ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun x => ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν)
        _ < ⊤ := hfin.lt_top
    have hmem : ∀ g, g ∈ S.map Λ.subtype ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x₀ = x₀ := by
      intro g
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h, hx⟩
        exact ⟨⟨g, h⟩, hx, rfl⟩
    have h0 := hzero x₀ (S.map Λ.subtype) hmem _ hD hint
    have hs := hasSum_integral_iUnion_ae (fun q => h𝓖.nullMeasurableSet_smul _) hdisj hint
    rw [h0] at hs
    simpa only [hofq, hT] using hs
  let e := selfEquivSigmaOrbitsQuotientStabilizer Λ X
  have h1 : HasSum (T ∘ e.symm) (∑' x, T x) := (e.symm.hasSum_iff).2 hsum.hasSum
  have h2 : HasSum (fun _ : Quotient (orbitRel Λ X) => (0 : ℂ)) (∑' x, T x) := by
    refine h1.sigma fun ω => ?_
    convert horb ω.out using 2 with q
    rfl
  exact h2.unique hasSum_zero

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_setIntegral_eq_zero_of_stabilizer_integrals : ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G) [ν.IsMulLeftInvariant], SFinite ν → ∀ (Λ : Subgroup G), Countable Λ → ∀ 𝓖 : Set G, IsFundamentalDomain Λ 𝓖 ν → ∀ (a : Λ → X → X), (∀ x, a 1 x = x) → (∀ γ δ x, a (γ * δ) x = a γ (a δ x)) → ∀ F : X → G → ℂ, (∀ γ x g, F (a γ x) g = F x ((γ : G)⁻¹ * g)) → (∀ x, AEStronglyMeasurable (F x) ν) → ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν ≠ ⊤ → (∀ x (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x = x) → ∀ 𝓓 : Set G, IsFundamentalDomain Γ 𝓓 ν → IntegrableOn (F x) 𝓓 ν → ∫ g in 𝓓, F x g ∂ν = 0) → ∑' x, ∫ g in 𝓖, F x g ∂ν = 0 := by
  atlas_forward_decl GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer
end

section
section
open MeasureTheory

namespace GlobalTheory

theorem tsum_setIntegral_prod_eq_zero_of_inner :
    ∀ {G X : Type} [MeasurableSpace G], Countable X → ∀ (ν : Measure G), SFinite ν → ∀ (𝓖 : Set G) (H : X → G × G → ℂ), (∀ x, AEStronglyMeasurable (H x) (ν.prod ν)) → ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' x, ‖H x (g₁, g₂)‖ₑ ∂ν ∂ν ≠ ⊤ → (∀ g₂, ∑' x, ∫⁻ g₁ in 𝓖, ‖H x (g₁, g₂)‖ₑ ∂ν ≠ ⊤ → ∑' x, ∫ g₁ in 𝓖, H x (g₁, g₂) ∂ν = 0) → ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν) = 0 := by
  intro G X _ hX ν hν 𝓖 H hH hfin hslice
  set μ := ν.restrict 𝓖 with hμ
  have hprod : (ν.prod ν).restrict (𝓖 ×ˢ 𝓖) = μ.prod μ := (Measure.prod_restrict 𝓖 𝓖).symm
  have hHm : ∀ x, AEStronglyMeasurable (H x) (μ.prod μ) := fun x => by
    rw [← hprod]; exact (hH x).restrict
  have hFm : AEMeasurable (fun p => ∑' x, ‖H x p‖ₑ) (μ.prod μ) :=
    AEMeasurable.ennreal_tsum fun x => (hHm x).enorm
  have hFint : ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) ≠ ⊤ := by
    rw [lintegral_prod _ hFm]; exact hfin
  have hsum : ∑' x, ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) = ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) :=
    (lintegral_tsum fun x => (hHm x).enorm).symm
  have hInt : ∀ x, Integrable (H x) (μ.prod μ) := fun x =>
    ⟨hHm x, by
      have : ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) ≤ ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) :=
        lintegral_mono fun p => ENNReal.le_tsum (f := fun x => ‖H x p‖ₑ) x
      exact lt_of_le_of_lt this (lt_top_iff_ne_top.2 hFint)⟩
  have hswap : ∀ x, ∫⁻ g₂, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ∂μ = ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) :=
    fun x => (lintegral_prod_symm _ (hHm x).enorm).symm
  have hLm : ∀ x, AEMeasurable (fun g₂ => ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ) μ := fun x =>
    ((hHm x).enorm.prod_swap).lintegral_prod_right'
  have hG2 : ∀ᵐ g₂ ∂μ, ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ≠ ⊤ := by
    have hm : AEMeasurable (fun g₂ => ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ) μ :=
      AEMeasurable.ennreal_tsum hLm
    have hi : ∫⁻ g₂, ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum hLm, tsum_congr hswap, hsum]; exact hFint
    filter_upwards [ae_lt_top' hm hi] with g₂ h using h.ne
  have hKm : ∀ x, AEStronglyMeasurable (fun g₂ => ∫ g₁, H x (g₁, g₂) ∂μ) μ := fun x =>
    (hHm x).prod_swap.integral_prod_right'
  have hKfin : ∑' x, ∫⁻ g₂, ‖∫ g₁, H x (g₁, g₂) ∂μ‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hFint ?_
    rw [← hsum]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [← hswap x]
    exact lintegral_mono fun g₂ => enorm_integral_le_lintegral_enorm _
  have key := integral_tsum hKm hKfin
  have h0 : ∫ g₂, ∑' x, ∫ g₁, H x (g₁, g₂) ∂μ ∂μ = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hG2] with g₂ h using hslice g₂ h
  calc ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν)
        = ∑' x, ∫ g₂, ∫ g₁, H x (g₁, g₂) ∂μ ∂μ := by
          refine tsum_congr fun x => ?_
          rw [hprod]; exact integral_prod_symm _ (hInt x)
    _ = 0 := by rw [← key, h0]

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_setIntegral_prod_eq_zero_of_inner' : ∀ {G X : Type} [MeasurableSpace G], Countable X → ∀ (ν : Measure G), SFinite ν → ∀ (𝓖 : Set G) (H : X → G × G → ℂ), (∀ x, AEStronglyMeasurable (H x) (ν.prod ν)) → ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' x, ‖H x (g₁, g₂)‖ₑ ∂ν ∂ν ≠ ⊤ → (∀ g₂, ∑' x, ∫⁻ g₁ in 𝓖, ‖H x (g₁, g₂)‖ₑ ∂ν ≠ ⊤ → ∑' x, ∫ g₁ in 𝓖, H x (g₁, g₂) ∂ν = 0) → ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν) = 0 := by
  atlas_forward_decl GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem conjTranspose_gram_mul_apply {D : D7} {n s t : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E)
    (A : Matrix (Fin n) (Fin s) D.host.E) (B : Matrix (Fin n) (Fin t) D.host.E) (a : Fin s) (c : Fin t) :
    (Aᴴ * G * B) a c = star (fun k => A k a) ⬝ᵥ G.mulVec (fun k => B k c) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum,
    Pi.star_apply, mul_assoc]
  rw [Finset.sum_comm]

theorem exists_isoFrame_comap_inl : ∀ (D : D7) (W : HSp D) (Y : Lag W), Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ →
    ∃ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I ∧
      Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) := by
  intro D W Y hY
  set I₁ := Y.1.comap (LinearMap.inl D.host.E (Fin W.rank → D.host.E) (Fin W.rank → D.host.E)) with hI₁
  have hpos : 0 < Module.finrank D.host.E I₁ :=
    Nat.pos_of_ne_zero fun h => hY (Submodule.finrank_eq_zero.mp h)
  let b := Module.finBasisOfFinrankEq D.host.E I₁ rfl
  have hsp : Submodule.span D.host.E (Set.range (I₁.subtype ∘ b)) = I₁ := by
    have h := congrArg (Submodule.map I₁.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  let I : Matrix (Fin W.rank) (Fin (Module.finrank D.host.E I₁)) D.host.E :=
    Matrix.of fun a j => (b j : Fin W.rank → D.host.E) a
  have hT : I.transpose = I₁.subtype ∘ b := by
    funext j a
    rfl
  refine ⟨_, I, ⟨hpos, ?_, ?_⟩, ?_⟩
  · rw [hT]
    exact b.linearIndependent.map' I₁.subtype (Submodule.ker_subtype I₁)
  · rw [GlobalTheory.MixModel.cT_sig]
    refine Matrix.ext fun a c => ?_
    rw [conjTranspose_gram_mul_apply, Matrix.zero_apply]
    have ha : LinearMap.inl D.host.E _ (Fin W.rank → D.host.E) (b a : Fin W.rank → D.host.E) ∈ Y.1 := (b a).2
    have hc : LinearMap.inl D.host.E _ (Fin W.rank → D.host.E) (b c : Fin W.rank → D.host.E) ∈ Y.1 := (b c).2
    have h := Y.2.2 _ ha _ hc
    simp only [LinearMap.inl_apply, star_zero, Matrix.mulVec_zero, dotProduct_zero] at h
    exact h
  · rw [hT]
    exact hsp

end GlobalTheory.RawLift
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropicFrame_lagrangian_first_summand : ∀ (D : D7) (W : HSp D) (Y : Lag W), Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → ∃ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I ∧ Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) := by
  atlas_forward_decl GlobalTheory.RawLift.exists_isoFrame_comap_inl
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCuspStab

open GlobalTheory.MixModel GlobalTheory.RallisCusp

variable {D : D7}

theorem inv_fix {n s : ℕ} (A B : Matrix (Fin n) (Fin n) (AE D)) (M : Matrix (Fin n) (Fin s) (AE D))
    (hBA : B * A = 1) (h : A ⬝ M = M) : B ⬝ M = M := by
  calc B ⬝ M = B ⬝ (A ⬝ M) := by rw [h]
    _ = M := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]

theorem inv_sub_one {n : ℕ} (A B : Matrix (Fin n) (Fin n) (AE D)) (hBA : B * A = 1) : B - 1 = -(B * (A - 1)) := by
  rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]

set_option maxHeartbeats 1000000 in

theorem ni_prop (W : HSp D) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E) (g : GA D W) (hg : g ∈ NI W I) :
    Formalism.L2.Theta.mt W g ⬝ I.map (incA D) = I.map (incA D) ∧
    ∀ x : Fin W.rank → D.host.E, (Iᴴ * W.gram) *ᵥ x = 0 →
      ∃ a : Fin s → AE D, (Formalism.L2.Theta.mt W g - 1) *ᵥ (fun i => incA D (x i)) = I.map (incA D) *ᵥ a := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    refine ⟨?_, fun x hx => hg.2.2 x hx⟩
    have h1 : (Formalism.L2.Theta.mt W g - 1) ⬝ I.map (incA D) = 0 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  | one =>
    refine ⟨by rw [GlobalTheory.MixModel.mt_one, Matrix.one_mul], fun x _ => ⟨0, ?_⟩⟩
    rw [GlobalTheory.MixModel.mt_one, sub_self, Matrix.zero_mulVec, Matrix.mulVec_zero]
  | mul x y _ _ hx hy =>
    refine ⟨by rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, hy.1, hx.1], fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hx.2 v hv
    obtain ⟨b, hb⟩ := hy.2 v hv
    refine ⟨b + a, ?_⟩
    have e : Formalism.L2.Theta.mt W (x * y) - 1 =
        Formalism.L2.Theta.mt W x * (Formalism.L2.Theta.mt W y - 1) + (Formalism.L2.Theta.mt W x - 1) := by
      rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
    rw [e, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hb, ha, Matrix.mulVec_mulVec, hx.1, Matrix.mulVec_add]
  | inv x _ hx =>
    obtain ⟨hx1, hx2⟩ := hx
    have hinv := inv_fix _ _ _ (GlobalTheory.MixModel.mt_inv_mul W x) hx1
    refine ⟨hinv, fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hx2 v hv
    refine ⟨-a, ?_⟩
    rw [inv_sub_one _ _ (GlobalTheory.MixModel.mt_inv_mul W x), Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, hinv, Matrix.mulVec_neg]

theorem exists_leftInv {m s : ℕ} (I : Matrix (Fin m) (Fin s) D.host.E) (hI : LinearIndependent D.host.E I.transpose) :
    ∃ L : Matrix (Fin s) (Fin m) D.host.E, L * I = 1 := by
  have hB : Function.Injective I.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    exact hI
  have hker : LinearMap.ker (Matrix.toLin' I) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact hB (by simpa [Matrix.toLin'_apply] using h)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' I) hker
  exact ⟨LinearMap.toMatrix' g, by
    rw [← LinearMap.toMatrix'_toLin' I, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]⟩

theorem descend {m s : ℕ} (I : Matrix (Fin m) (Fin s) D.host.E) (hI : LinearIndependent D.host.E I.transpose)
    (v : Fin m → D.host.E) (a : Fin s → AE D) (h : (fun i => incA D (v i)) = I.map (incA D) *ᵥ a) :
    ∃ b : Fin s → D.host.E, v = I *ᵥ b := by
  obtain ⟨L, hL⟩ := exists_leftInv I hI
  refine ⟨L *ᵥ v, ?_⟩
  have ha : a = fun j => incA D ((L *ᵥ v) j) := by
    have h1 : L.map (incA D) *ᵥ (fun i => incA D (v i)) = a := by
      rw [h, Matrix.mulVec_mulVec, ← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rw [← h1]
    funext j
    exact (RingHom.map_mulVec (incA D) L v j).symm
  funext i
  apply incA_injective
  have := congrFun h i
  rw [this, ha]
  exact (RingHom.map_mulVec (incA D) I (L *ᵥ v) i).symm

theorem fst_perp (W : HSp D) (Y : Lag W) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E)
    (hY : Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _))
    (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) (hy : y ∈ Y.1) : (Iᴴ * W.gram) *ᵥ y.1 = 0 := by
  funext a
  have hcol : ((I.transpose a, 0) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ∈ Y.1 := by
    have h : I.transpose a ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := hY ▸ Submodule.subset_span ⟨a, rfl⟩
    exact h
  have hiso := Y.2.2 _ hcol y hy
  simp only [star_zero, zero_dotProduct] at hiso
  rw [← Matrix.mulVec_mulVec]
  show _ = (0 : D.host.E)
  rw [← hiso]
  rfl

theorem lagAct_eq_of_mem_NI : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E),
    IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) →
    ∀ n : GQ W, (n : GA D W) ∈ NI W I → GlobalTheory.RallisCusp.lagAct W n Y = Y := by
  intro D W Y s I hI hY n hn
  have hn' : ((n⁻¹ : GQ W) : GA D W) ∈ NI W I := by
    rw [InvMemClass.coe_inv]
    exact inv_mem hn
  obtain ⟨-, hP⟩ := ni_prop W I _ hn'
  have hc : Formalism.L2.Theta.mt W ((n⁻¹ : GQ W) : GA D W) - 1 = (gqMat W n⁻¹ - 1).map (incA D) := by
    rw [← rat_gqMat, ← rat_one, ← rat_sub]
    rfl
  have hle : Y.1 ≤ (lagAct W n Y).1 := by
    intro y hy
    rw [mem_lagAct]
    obtain ⟨a, ha⟩ := hP y.1 (fst_perp W Y I hY y hy)
    obtain ⟨b, hb⟩ := descend I hI.2.1 ((gqMat W n⁻¹ - 1) *ᵥ y.1) a (by
      rw [← ha, hc]
      funext i
      exact RingHom.map_mulVec (incA D) _ _ i)
    have hIb : ((I *ᵥ b, 0) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ∈ Y.1 := by
      have h : I *ᵥ b ∈ Submodule.span D.host.E (Set.range I.col) := by
        rw [← Matrix.range_mulVecLin]
        exact ⟨b, rfl⟩
      have h' : I *ᵥ b ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := by
        rw [← hY]
        exact h
      exact h'
    have e : ((gqMat W n⁻¹ *ᵥ y.1, y.2) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) =
        y + (I *ᵥ b, 0) := by
      rw [← hb, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact Prod.ext (by simp) (by simp)
    rw [e]
    exact Y.1.add_mem hy hIb
  exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by rw [Y.2.1, (lagAct W n Y).2.1])).symm

end GlobalTheory.RallisCuspStab

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnitaryLagrangianAction_eq_of_mem_frameUnipotent : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ n : GQ W, (n : GA D W) ∈ NI W I → GlobalTheory.RallisCusp.lagAct W n Y = Y := by
  atlas_forward_decl GlobalTheory.RallisCuspStab.lagAct_eq_of_mem_NI
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCusp

open GlobalTheory.MixModel

variable {D : D7}

theorem mem_span_cols {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (v : Fin n → D.host.E) :
    v ∈ Submodule.span D.host.E (Set.range I.transpose) ↔ ∃ a, I *ᵥ a = v := by
  change v ∈ Submodule.span D.host.E (Set.range I.col) ↔ _
  rw [← Matrix.range_mulVecLin]; rfl

theorem exists_mul_eq_mul {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (M : Matrix (Fin n) (Fin n) D.host.E)
    (h : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      M *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose)) :
    ∃ A : Matrix (Fin s) (Fin s) D.host.E, M * I = I * A := by
  have h1 : ∀ j, ∃ b, I *ᵥ b = M *ᵥ I.transpose j := fun j =>
    (mem_span_cols I _).1 (h _ (Submodule.subset_span ⟨j, rfl⟩))
  choose f hf using h1
  refine ⟨Matrix.of fun i j => f j i, ?_⟩
  refine Matrix.ext fun k j => ?_
  have := congrFun (hf j) k
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at this
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simpa using this.symm

theorem frame_gram_mul {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (J c c' : Matrix (Fin n) (Fin n) D.host.E)
    (hc : c * c' = 1) (hu : cᴴ * J * c = J) : Iᴴ * J * c = (c' * I)ᴴ * J := by
  have h1 : (c * c')ᴴ = 1 := by rw [hc, Matrix.conjTranspose_one]
  calc Iᴴ * J * c = Iᴴ * (c * c')ᴴ * J * c := by rw [h1, Matrix.mul_one]
    _ = Iᴴ * c'ᴴ * (cᴴ * J * c) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (c' * I)ᴴ * J := by rw [hu, Matrix.conjTranspose_mul]

theorem mul_mul_mul_eq_zero {R : Type} [CommRing R] {n s : ℕ} (C C' m : Matrix (Fin n) (Fin n) R)
    (I : Matrix (Fin n) (Fin s) R) (A' : Matrix (Fin s) (Fin s) R) (h : C' * I = I * A') (h0 : m * I = 0) :
    C * m * C' * I = 0 := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.mul_assoc C, h0, Matrix.mul_zero, Matrix.zero_mul]

theorem mul_mul_mul_eq_zero' {R : Type} [CommRing R] {n s : ℕ} (C C' m : Matrix (Fin n) (Fin n) R)
    (K : Matrix (Fin s) (Fin n) R) (A' : Matrix (Fin s) (Fin s) R) (h : K * C = A' * K) (h0 : K * m = 0) :
    K * (C * m * C') = 0 := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_assoc A', h0, Matrix.mul_zero, Matrix.zero_mul]

set_option maxHeartbeats 2000000 in

theorem conj_mem_NI : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ γ : GQ W, GlobalTheory.RallisCusp.lagAct W γ Y = Y → ∀ n ∈ NI W I, (γ : GA D W) * n * (γ : GA D W)⁻¹ ∈ NI W I := by
  intro D W Y s I _ hS γ hY n hn
  set c := gqMat W γ with hc_def
  set c' := gqMat W γ⁻¹ with hc'_def
  have hcc' : c * c' = 1 := gqMat_mul_inv W γ
  have hc'c : c' * c = 1 := gqMat_inv_mul W γ
  have memS : ∀ v, v ∈ Submodule.span D.host.E (Set.range I.transpose) ↔ ((v, 0) : _ × _) ∈ Y.1 := by
    intro v; rw [hS, Submodule.mem_comap, LinearMap.inl_apply]
  have memY : ∀ y, y ∈ Y.1 ↔ (c' *ᵥ y.1, y.2) ∈ Y.1 := by
    intro y; conv_lhs => rw [← hY]
    exact mem_lagAct W γ Y y
  have hcS : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      c *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose) := by
    intro v hv
    rw [memS, memY]
    simpa [Matrix.mulVec_mulVec, hc'c] using (memS v).1 hv
  have hc'S : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      c' *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose) := by
    intro v hv
    rw [memS]
    exact (memY _).1 ((memS v).1 hv)
  obtain ⟨A, hA⟩ := exists_mul_eq_mul I c' hc'S
  obtain ⟨B, hB⟩ := exists_mul_eq_mul I c hcS
  have hIc : Iᴴ * W.gram * c = Aᴴ * (Iᴴ * W.gram) := by
    rw [frame_gram_mul I W.gram c c' hcc' (gqMat_unitary W γ), hA, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hIc' : Iᴴ * W.gram * c' = Bᴴ * (Iᴴ * W.gram) := by
    rw [frame_gram_mul I W.gram c' c hc'c (gqMat_unitary W γ⁻¹), hB, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hrat : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), M.map (incA D) = rat M := fun _ => rfl
  have hγ : mt W (γ : GA D W) = rat c := (rat_gqMat W γ).symm
  have hγ' : mt W ((γ : GA D W)⁻¹) = rat c' := (rat_gqMat W γ⁻¹).symm
  have hle : NI W I ≤ (NI W I).comap (MulAut.conj (γ : GA D W)).toMonoidHom := by
    unfold NI
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨h1, h2, h3⟩ := hg
    apply Subgroup.subset_closure
    have hm : (matHom W ((MulAut.conj (γ : GA D W)).toMonoidHom g)).1 - 1 = rat c * ((matHom W g).1 - 1) * rat c' := by
      change mt W ((γ : GA D W) * g * (γ : GA D W)⁻¹) - 1 = rat c * (mt W g - 1) * rat c'
      rw [mt_mul, mt_mul, hγ, hγ', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← rat_mul, hcc', rat_one]
    rw [cT_sig, hrat] at h2 h3
    rw [hrat] at h1
    have hA' : rat c' ⬝ rat I = rat I ⬝ rat A := by rw [← rat_mul, hA, rat_mul]
    have hIc2 : rat (Iᴴ * W.gram) ⬝ rat c = rat Aᴴ ⬝ rat (Iᴴ * W.gram) := by rw [← rat_mul, hIc, rat_mul]
    have hB' : rat c ⬝ rat I = rat I ⬝ rat B := by rw [← rat_mul, hB, rat_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm, hrat]
      exact mul_mul_mul_eq_zero (rat c) (rat c') _ (rat I) (rat A) hA' h1
    · rw [hm, cT_sig, hrat]
      exact mul_mul_mul_eq_zero' (rat c) (rat c') _ (rat (Iᴴ * W.gram)) (rat Aᴴ) hIc2 h2
    · intro x hx
      rw [cT_sig] at hx
      have hx' : (Iᴴ * W.gram) *ᵥ (c' *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hIc', ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      obtain ⟨a, ha⟩ := h3 (c' *ᵥ x) hx'
      refine ⟨rat B *ᵥ a, ?_⟩
      have hv : rat c' *ᵥ (fun i => incA D (x i)) = fun i => incA D ((c' *ᵥ x) i) := by
        funext i; exact (RingHom.map_mulVec (incA D) c' x i).symm
      rw [hm, hrat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, ha, Matrix.mulVec_mulVec, hB',
        Matrix.mulVec_mulVec]
  exact hle hn

end GlobalTheory.RallisCusp

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangianStabilizer_normalizes_frameUnipotent : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ γ : GQ W, GlobalTheory.RallisCusp.lagAct W γ Y = Y → ∀ n ∈ NI W I, (γ : GA D W) * n * (γ : GA D W)⁻¹ ∈ NI W I := by
  atlas_forward_decl GlobalTheory.RallisCusp.conj_mem_NI
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open scoped GlobalTheory.GaugeEx

noncomputable section
namespace GlobalTheory.RallisCusp

theorem nonGraph_sum_eq_zero : ∀ D : D7, EisAbs D → TermMove D → TermInv D → CuspKill D → (∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = 0 := by
  intro D hEis hMove hInv hKill hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ ha₁ hc₁ ha₂ hc₂
  haveI : Countable (Lag W) := lag_countable D W
  haveI : Countable D.host.E := countable_numberField_type D.host.E
  haveI := hS.haarW
  have hw := hS.weil
  have hpres : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (om p f) := hw.om_pres
  have hom : ∀ (g h : GA D W) f, om (1, g) (om (1, h) f) = om (1, g * h) f := by
    intro g h f
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

  have hmove : ∀ (γ : GQ W) (Y : Lag W) (g : GA D W) (F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₂ →
      lagTerm μ 𝓕 (fr (lagAct W γ Y)) (om (1, g) f₁) F₂ = lagTerm μ 𝓕 (fr Y) (om (1, (γ : GA D W)⁻¹ * g) f₁) F₂ := by
    intro γ Y g F₂ hF₂
    have h1 := (hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, g) f₁) F₂ (hpres _ _ hf₁) hF₂).1
      (lagAct W γ Y) _ (isLagFrame_lagAct W γ Y (fr Y) (hS.frame Y))
    have h2 := ((hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, (γ : GA D W)⁻¹ * g) f₁) F₂ (hpres _ _ hf₁) hF₂).2
      γ γ.2 (gqMat W γ) (gqMat_map W γ).symm).1 (fr Y)
    rw [← h1, ← h2, hom, mul_inv_cancel_left]

  have hslice : ∀ g₂ : GA D W, ∑' Y : NGLag W, ∫⁻ g in 𝓖, ‖star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)‖ₑ ∂νW ≠ ⊤ →
      ∑' Y : NGLag W, ∫ g in 𝓖, star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) ∂νW = 0 := by
    intro g₂ hfin
    have hF₂ := hpres (1, g₂) f₂ hf₂
    have hGQ : Countable (GQ W) := by
      haveI : Countable (Matrix (Fin W.rank) (Fin W.rank) D.host.E) :=
        inferInstanceAs (Countable (Fin W.rank → Fin W.rank → D.host.E))
      refine Function.Injective.countable (f := fun γ : GQ W => gqMat W γ) ?_
      intro γ δ h
      apply Subtype.ext
      apply GlobalTheory.MixModel.mt_injective W
      have := congrArg (fun c => c.map (incA D)) h
      simpa only [gqMat_map] using this
    refine GlobalTheory.T.tsum_setIntegral_eq_zero_of_stabilizer_integrals νW inferInstance (GQ W) hGQ 𝓖 hS.fdW (ngAct W) (ngAct_one W) (ngAct_mul W)
      (fun Y g => star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)) ?_ ?_ hfin ?_
    · intro γ Y g
      show star (φ₁ g) * lagTerm μ 𝓕 (fr (lagAct W γ Y.1)) _ _ = _
      rw [hmove γ Y.1 g _ hF₂, ha₁.left _ (inv_mem γ.2) g]
    · intro Y
      exact ((continuous_star.comp ha₁.cont).mul (hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ _ hf₁ hF₂ Y.1 Y.2)).aestronglyMeasurable
    · intro Y Γ hΓ 𝓓 h𝓓 hint
      obtain ⟨s, I, hI, hspan⟩ := GlobalTheory.T.exists_isotropicFrame_lagrangian_first_summand D W Y.1 Y.2
      have hle : Γ ≤ GQ W := fun g hg => ((hΓ g).1 hg).1
      have hfix : ∀ g (hg : g ∈ Γ), lagAct W ⟨g, hle hg⟩ Y.1 = Y.1 := by
        intro g hg
        obtain ⟨h, e⟩ := (hΓ g).1 hg
        exact congrArg Subtype.val e
      have key := hKill W νW hS.haarW s I hI Γ hle
        (fun n hn => (hΓ n).2 ⟨hn.2, Subtype.ext (GlobalTheory.T.rationalUnitaryLagrangianAction_eq_of_mem_frameUnipotent D W Y.1 s I hI hspan ⟨n, hn.2⟩ hn.1)⟩)
        (fun γ hγ n hn => GlobalTheory.T.lagrangianStabilizer_normalizes_frameUnipotent D W Y.1 s I hI hspan ⟨γ, hle hγ⟩ (hfix γ hγ) n hn) 𝓓 h𝓓
        (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)) (fun g => star (φ₁ g))
        (hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ _ hf₁ hF₂ Y.1 Y.2) ?_ ?_ ?_ ?_ ?_
      · rw [← key]
        congr 1
        funext g
        ring
      · intro γ hγ g
        show lagTerm μ 𝓕 (fr Y.1) (om (1, γ * g) f₁) (om (1, g₂) f₂) = lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)
        have := hmove ⟨γ, hle hγ⟩ Y.1 (γ * g) _ hF₂
        rw [hfix γ hγ] at this
        rw [this]
        congr 3
        exact congrArg (Prod.mk 1) (inv_mul_cancel_left γ g)
      · intro n hn g
        show lagTerm μ 𝓕 (fr Y.1) (om (1, n * g) f₁) (om (1, g₂) f₂) = lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)
        rw [← hom]
        exact hInv ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS Y.1 s I hI hspan n hn _ _ (hpres _ _ hf₁) hF₂
      · exact ⟨fun γ hγ g => by show star (φ₁ (γ * g)) = star (φ₁ g); rw [ha₁.left γ hγ g],
          by
            obtain ⟨U, hU, hk⟩ := ha₁.level
            exact ⟨U, hU, fun k hk1 hk2 g => by show star (φ₁ (g * k)) = star (φ₁ g); rw [hk k hk1 hk2 g]⟩,
          continuous_star.comp ha₁.cont⟩
      · intro r C hC μ' 𝓕' hμ' h𝓕' g
        have := hc₁ r C hC μ' 𝓕' hμ' h𝓕' g
        show ∫ n in 𝓕', (starRingEnd ℂ) (φ₁ ((n : GA D W) * g)) ∂μ' = 0
        rw [integral_conj, this, map_zero]
      · have e : (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) * star (φ₁ g)) =
            fun g => star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) := funext fun g => mul_comm _ _
        show IntegrableOn (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) * star (φ₁ g)) 𝓓 νW
        rw [e]
        exact hint
  have hφ₁c : Continuous φ₁ := ha₁.cont
  refine GlobalTheory.T.tsum_setIntegral_prod_eq_zero_of_inner' (X := NGLag W) inferInstance νW inferInstance 𝓖
    (fun Y p => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂)) ?_ ?_ ?_
  · intro Y
    have hm := GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hw hS.covol f₁ f₂ hf₁ hf₂ (fr Y.1)
    exact (((continuous_star.comp hφ₁c).comp continuous_fst).mul (ha₂.cont.comp continuous_snd)).aestronglyMeasurable.mul
      hm.aestronglyMeasurable
  · have h0 := hEis ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ hf₁ hf₂ φ₁ φ₂ ha₁ hc₁ ha₂ hc₂
    refine ne_top_of_le_ne_top h0 (lintegral_mono fun g₁ => lintegral_mono fun g₂ => ?_)
    have e : ∀ Y : NGLag W, ‖star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ =
        (fun Y : Lag W => ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ) Y.1 := by
      intro Y
      have hs : ‖star (φ₁ g₁)‖ₑ = ‖φ₁ g₁‖ₑ := by simp [enorm_eq_nnnorm]
      simp only
      rw [enorm_mul, enorm_mul, hs]
      ring
    rw [tsum_congr e]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
  · intro g₂ hfin
    by_cases h0 : φ₂ g₂ = 0
    · simp [h0]
    · have e1 : ∀ Y : NGLag W, ∫ g₁ in 𝓖, star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂) ∂νW =
          φ₂ g₂ * ∫ g₁ in 𝓖, star (φ₁ g₁) * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂) ∂νW := by
        intro Y
        rw [← integral_const_mul]
        congr 1
        funext g₁
        ring
      have e2 : ∀ Y : NGLag W, ∫⁻ g₁ in 𝓖, ‖star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ∂νW =
          ‖φ₂ g₂‖ₑ * ∫⁻ g₁ in 𝓖, ‖star (φ₁ g₁) * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ∂νW := by
        intro Y
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        congr 1
        funext g₁
        rw [enorm_mul, enorm_mul, enorm_mul]
        ring
      simp only at hfin ⊢
      rw [tsum_congr e2, ENNReal.tsum_mul_left] at hfin
      rw [tsum_congr e1, tsum_mul_left, hslice g₂ ?_, mul_zero]
      intro htop
      rw [htop, ENNReal.mul_top (enorm_ne_zero.2 h0)] at hfin
      exact hfin rfl

end GlobalTheory.RallisCusp
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallis_nonGraphLagrangian_sum_eq_zero_cuspidal : ∀ D : D7, EisAbs D → TermMove D → TermInv D → CuspKill D → (∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = 0 := by
  atlas_forward_decl GlobalTheory.RallisCusp.nonGraph_sum_eq_zero
end
