import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulScalar
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteCountableGQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.DoubleCosetAdjoint

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (φ : G → ℂ)

theorem pairing_shift (h : IsFundamentalDomain Γ 𝓕 μ) (hΓ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g)
    (c x y : G) :
    ∫ g in 𝓕, star (φ (g * (c * x))) * φ (g * (c * y)) ∂μ
      = ∫ g in 𝓕, star (φ (g * x)) * φ (g * y) ∂μ := by
  have := (GlobalTheory.fundamentalDomain_integral_mul_right μ Γ 𝓕
    (fun g => star (φ (g * x)) * φ (g * y)) c h
    (fun γ hγ g => by simp only [mul_assoc, hΓ γ hγ])).2
  simpa only [mul_assoc] using this

theorem pairing_integrable (h : IsFundamentalDomain Γ 𝓕 μ) (hc : Continuous φ)
    (hΓ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g)
    (hi : IntegrableOn (fun g => star (φ g) * φ g) 𝓕 μ) (x y : G) :
    IntegrableOn (fun g => star (φ (g * x)) * φ (g * y)) 𝓕 μ := by
  have h1 : ∀ z : G, IntegrableOn (fun g => star (φ (g * z)) * φ (g * z)) 𝓕 μ := fun z =>
    (GlobalTheory.fundamentalDomain_integral_mul_right μ Γ 𝓕
      (fun g => star (φ g) * φ g) z h
      (fun γ hγ g => by simp only [hΓ γ hγ])).1.1 hi
  refine Integrable.mono' ((h1 x).norm.add (h1 y).norm) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact (Continuous.mul (continuous_star.comp (hc.comp (continuous_mul_right x)))
      (hc.comp (continuous_mul_right y))).aestronglyMeasurable
  · simp only [norm_mul, norm_star, Pi.add_apply]
    nlinarith [sq_nonneg (‖φ (g * x)‖ - ‖φ (g * y)‖), norm_nonneg (φ (g * x)),
      norm_nonneg (φ (g * y)), mul_nonneg (norm_nonneg (φ (g * x))) (norm_nonneg (φ (g * y)))]

end

theorem eigenvalue_inv_eq_star : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ J : Subgroup G) [Countable Γ] (𝓕 : Set G) (φ : G → ℂ) (α : G) (R R' : Finset G) (a b : ℂ), IsFundamentalDomain Γ 𝓕 μ → Continuous φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → (∀ k ∈ J, ∀ g, φ (g * k) = φ g) → IntegrableOn (fun g => star (φ g) * φ g) 𝓕 μ → ∫ g in 𝓕, star (φ g) * φ g ∂μ ≠ 0 → Bridge.IsDC J α R → Bridge.IsDC J α⁻¹ R' → R.card = R'.card → (∀ g, ∑ γ ∈ R, φ (g * γ) = a * φ g) → (∀ g, ∑ γ ∈ R', φ (g * γ) = b * φ g) → star a = b := by
  intro G _ _ _ _ _ _ μ _ _ Γ J _ 𝓕 φ α R R' a b h hc hΓ hJ hi hne hR hR' hcard ha hb
  have e1 : ∀ γ ∈ R, ∫ g in 𝓕, star (φ (g * γ)) * φ (g * 1) ∂μ
      = ∫ g in 𝓕, star (φ (g * 1)) * φ (g * α⁻¹) ∂μ := by
    intro γ hγ
    obtain ⟨k₁, k₂, rfl⟩ := hR.1 γ hγ
    rw [← pairing_shift μ Γ 𝓕 φ h hΓ α 1 α⁻¹,
      ← pairing_shift μ Γ 𝓕 φ h hΓ (k₁ : G) (α * 1) (α * α⁻¹)]
    simp only [mul_one, mul_inv_cancel, ← mul_assoc, hJ _ k₁.2, hJ _ k₂.2]
  have e2 : ∀ γ ∈ R', ∫ g in 𝓕, star (φ (g * 1)) * φ (g * γ) ∂μ
      = ∫ g in 𝓕, star (φ (g * 1)) * φ (g * α⁻¹) ∂μ := by
    intro γ hγ
    obtain ⟨k₁, k₂, rfl⟩ := hR'.1 γ hγ
    rw [← pairing_shift μ Γ 𝓕 φ h hΓ (k₁ : G) 1 α⁻¹]
    simp only [mul_one, ← mul_assoc, hJ _ k₁.2, hJ _ k₂.2]
  have s1 : ∑ γ ∈ R, ∫ g in 𝓕, star (φ (g * γ)) * φ (g * 1) ∂μ
      = star a * ∫ g in 𝓕, star (φ g) * φ g ∂μ := by
    rw [← integral_finset_sum _ (fun γ _ => pairing_integrable μ Γ 𝓕 φ h hc hΓ hi γ 1),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [mul_one]
    rw [← Finset.sum_mul, ← star_sum, ha, star_mul', mul_assoc]
  have s2 : ∑ γ ∈ R', ∫ g in 𝓕, star (φ (g * 1)) * φ (g * γ) ∂μ
      = b * ∫ g in 𝓕, star (φ g) * φ g ∂μ := by
    rw [← integral_finset_sum _ (fun γ _ => pairing_integrable μ Γ 𝓕 φ h hc hΓ hi 1 γ),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [mul_one]
    rw [← Finset.mul_sum, hb]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_const, hcard] at s1
  rw [Finset.sum_congr rfl e2, Finset.sum_const, s1] at s2
  exact mul_right_cancel₀ hne s2

end GlobalTheory.DoubleCosetAdjoint
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.HeckeCompl

open Formalism.L2.NTheta (IsIdemAt IsHeckeElt LamHat)
open Formalism.IndefR.Bridge (IsDC)
open scoped Matrix

theorem isDC_of_local {G : Type} [Group G] {J L : Subgroup G} {x : G} {R : Finset G} (hx : x ∈ L) (hR : ∀ γ ∈ R, γ ∈ L)
    (hs : ∀ k ∈ J, ∃ a ∈ J, ∃ b ∈ J, a ∈ L ∧ Commute x b ∧ k = a * b)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ J ⊓ L, ∃ k₂ ∈ J ⊓ L, γ = k₁ * x * k₂)
    (h2 : ∀ y : G, (∃ k₁ ∈ J ⊓ L, ∃ k₂ ∈ J ⊓ L, y = k₁ * x * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * y ∈ J ⊓ L) : IsDC J x R := by
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := h1 γ hγ
    exact ⟨⟨k₁, hk₁.1⟩, ⟨k₂, hk₂.1⟩, e⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ha, b, hb, haL, hc, e⟩ := hs k₁ k₁.2
    obtain ⟨γ, ⟨hγ, hγJ⟩, hu⟩ := h2 (a * x) ⟨a, ⟨ha, haL⟩, 1, Subgroup.one_mem _, by simp⟩
    have eg : (k₁ : G) * x * k₂ = a * x * (b * k₂) := by
      rw [e, mul_assoc a b x, ← hc.eq]; group
    refine ⟨γ, ⟨hγ, ?_⟩, ?_⟩
    · rw [eg, ← mul_assoc]
      exact J.mul_mem hγJ.1 (J.mul_mem hb k₂.2)
    · rintro δ ⟨hδ, hδJ⟩
      refine hu δ ⟨hδ, ?_, L.mul_mem (L.inv_mem (hR δ hδ)) (L.mul_mem haL hx)⟩
      have := J.mul_mem hδJ (J.inv_mem (J.mul_mem hb k₂.2))
      rw [eg] at this
      simpa [mul_assoc] using this

theorem idem_pow {A : Type} [CommRing A] {e s p : A} (h : e * s = e * p) (n : ℕ) : e * s ^ n = e * p ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    linear_combination s * ih + p ^ n * h

theorem det_compl {A : Type} [CommRing A] {e s p d d' u u' : A} {n k : ℕ} (hk : k ≤ n) (h : e * s = e * p)
    (hd : d * d' = 1) (hu : e * u * u' = e) (h5 : e * d = e * p ^ k * u) :
    e * (s ^ n * d') = e * p ^ (n - k) * u' := by
  have h1 := idem_pow h n
  have h2 : p ^ n = p ^ (n - k) * p ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  rw [h2] at h1
  linear_combination d' * h1 - (p ^ (n - k) * p ^ k * d') * hu - (p ^ (n - k) * u' * d') * h5 +
    (e * p ^ (n - k) * u') * hd

theorem vec_upper {R : Type} [CommRing R] {n : ℕ} {M M' : Matrix (Fin n) (Fin n) R} (hM : M' * M = 1) {e s p : R}
    (h : e * s = e * p) {y z : Fin n → R} (hy : (fun a => e * (p * y a)) = fun a => e * M.mulVec z a) :
    (fun a => e * (s • M').mulVec y a) = fun a => e * z a := by
  have h1 : e • p • y = e • M *ᵥ z := hy
  change e • (s • M') *ᵥ y = e • z
  rw [Matrix.smul_mulVec, smul_smul, h, ← Matrix.mulVec_smul, mul_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hM,
    Matrix.one_mulVec]

theorem vec_lower {R : Type} [CommRing R] {n : ℕ} {M M' : Matrix (Fin n) (Fin n) R} (hM : M' * M = 1) {e s p : R}
    (he : e * e = e) (h : e * s = e * p) (y : Fin n → R) :
    (fun a => e * (p * y a)) = fun a => e * (s • M').mulVec (fun b => e * M.mulVec y b) a := by
  change e • p • y = e • (s • M') *ᵥ (e • M *ᵥ y)
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec, smul_smul, smul_smul, smul_smul, h,
    mul_right_comm, he]

variable {D : D7} {V : HSp D}

theorem mt_one : mt V 1 = 1 := rfl

theorem mt_inv_mul (α : GA D V) : mt V α⁻¹ * mt V α = 1 := by
  rw [← GlobalTheory.SplitCentral.hmul, inv_mul_cancel, mt_one]

theorem fin_inv_mul (α : GA D V) : finMat D.sp.cm.sig V.gram (α⁻¹ : GA D V) * finMat D.sp.cm.sig V.gram α = 1 := by
  rw [GlobalTheory.SplitCentral.hfin, GlobalTheory.SplitCentral.hfin, ← Matrix.map_mul, mt_inv_mul,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem fin_one : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 := by
  rw [GlobalTheory.SplitCentral.hfin, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem idem_fin {e : Formalism.L2.Theta.AE D} (he : e * e = e) : finPart D e * finPart D e = finPart D e := by
  rw [← map_mul, he]

theorem int_mem (ϖ : 𝓞 D.host.E) : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, ϖ, rfl⟩

theorem hecke_one {e : Formalism.L2.Theta.AE D} (he : e * e = e) (ϖ : 𝓞 D.host.E) : IsHeckeElt V e (ϖ : D.host.E) 0 1 := by
  have hm := (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  have h1 : finPart D 1 ∈ intAE D := by
    rw [map_one]; exact int_mem 1
  refine ⟨one_mem _, fun i j => ?_, fun y hy => ?_, fun y hy => ⟨_, hm _ (int_mem ϖ) y hy, ?_⟩, 1, 1, h1, h1, ?_, ?_⟩
  · rw [mt_one, sub_self, Matrix.zero_apply, mul_zero]
  · rw [fin_one, Matrix.one_mulVec]
    exact hm _ (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (idem_fin he)) y hy
  · rw [fin_one, Matrix.one_mulVec]
  · rw [mul_one, mul_one]
  · rw [mt_one, Matrix.det_one, pow_zero, mul_one, mul_one]

theorem hecke_compl {e s : Formalism.L2.Theta.AE D} (he : e * e = e) {ϖ : D.host.E} (hs : e * s = e * incA D ϖ) {ζ α : GA D V}
    (hζ : mt V ζ = s • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D))) {k : ℕ} (hk : k ≤ V.rank)
    (h : IsHeckeElt V e ϖ k α) (h0 : α⁻¹ * ζ ∈ GfC V) (h1 : SuppAt e V (α⁻¹ * ζ)) :
    IsHeckeElt V e ϖ (V.rank - k) (α⁻¹ * ζ) := by
  obtain ⟨-, -, h2, h3, u, u', hu, hu', h4, h5⟩ := h
  have hm := (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  have hF := GlobalTheory.SplitCentral.finMat_scalar α⁻¹ ζ s hζ
  have hup : finPart D e * finPart D s = finPart D e * finPart D (incA D ϖ) := by
    rw [← RingHom.map_mul, hs, RingHom.map_mul]
  refine ⟨h0, h1, fun y hy => ?_, fun y hy => ⟨_, h2 y hy, ?_⟩, u', u, hu', hu, ?_, ?_⟩
  · obtain ⟨z, hz, hyz⟩ := h3 y hy
    rw [hF, vec_upper (fin_inv_mul α) hup hyz]
    exact hm _ (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (idem_fin he)) z hz
  · rw [hF]
    exact vec_lower (fin_inv_mul α) (idem_fin he) hup y
  · rw [mul_right_comm, h4]
  · have hd : (mt V α).det * (mt V α⁻¹).det = 1 := by
      rw [mul_comm, ← Matrix.det_mul, mt_inv_mul, Matrix.det_one]
    rw [GlobalTheory.SplitCentral.hmul, hζ, Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
      mul_comm (mt V α⁻¹).det]
    exact det_compl hk hs hd h4 h5

theorem exists_unif (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
  have := Ideal.pow_succ_lt_pow P.ne_bot 1
  rw [pow_one] at this
  exact SetLike.exists_of_lt this

variable {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}

theorem exists_loc (V : HSp D) (he : IsIdemAt e P) :
    ∃ S : Subgroup (GA D V), (∀ g, g ∈ S ↔ SuppAt e V g) ∧ S ≤ GfC V ∧
      ∀ g ∈ S, ∀ g', SuppF V (1 - (e + cA D e)) g' → Commute g g' := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  obtain ⟨a, b, c, -⟩ := h3 P e _ (Or.inl ⟨he, rfl⟩)
  obtain ⟨⟨L, hL⟩, -, hc⟩ := h1 _ a b
  refine ⟨L, hL, fun g hg => c g ((hL g).1 hg), fun g hg g' hg' => hc _ g g' ?_ ((hL g).1 hg) hg'⟩
  rw [mul_sub, mul_one, a, sub_self]

theorem exists_central (V : HSp D) (he : IsIdemAt e P) {ϖ : D.host.E} (hϖ : ϖ ≠ 0) :
    ∃ ζ : GA D V, (∀ g, Commute ζ g) ∧
      ∀ k ≤ V.rank, ∀ α, IsHeckeElt V e ϖ k α → IsHeckeElt V e ϖ (V.rank - k) (ζ * α⁻¹) := by
  obtain ⟨S, hS, hf, -⟩ := exists_loc V he
  obtain ⟨s, hs, hss, hse⟩ := GlobalTheory.SplitCentral.exists_unitary (cA D) (GlobalTheory.SplitCentral.cA_cA D) e (incA D ϖ)
    (incA D ϖ⁻¹) he.1.1 he.1.2.1 (by rw [← RingHom.map_mul, mul_inv_cancel₀ hϖ, RingHom.map_one])
  obtain ⟨ζ, hζ⟩ := GlobalTheory.SplitCentral.exists_mt V s hs
  have hζS : ζ ∈ S := (hS ζ).2 fun i j => by
    rw [hζ]
    exact GlobalTheory.SplitCentral.supp_scalar _ _ hss i j
  have hcom : ∀ g, Commute ζ g := fun g => by
    refine GlobalTheory.SplitCentral.hinj (ζ * g) (g * ζ) ?_
    rw [GlobalTheory.SplitCentral.hmul, GlobalTheory.SplitCentral.hmul, hζ]
    exact GlobalTheory.SplitCentral.scalar_comm _ _
  refine ⟨ζ, hcom, fun k hk α hα => ?_⟩
  have hm : α⁻¹ * ζ ∈ S := S.mul_mem (S.inv_mem ((hS α).2 hα.2.1)) hζS
  rw [(hcom _).eq]
  exact hecke_compl he.1.1 hse hζ hk hα (hf hm) ((hS _).1 hm)

theorem exists_reps {G : Type} [Group G] {J S : Subgroup G} {K : Set G} {T : G → Prop} (hS : ∀ g, g ∈ S ↔ T g)
    (hK : ∀ g, T g → (g ∈ J ↔ g ∈ K)) (hs : ∀ k ∈ J, ∃ a ∈ J, ∃ b ∈ J, T a ∧ (∀ x ∈ S, Commute x b) ∧ k = a * b)
    (hθ : ∃ θ : G → G, (∀ g, T g → T (θ g)) ∧ (∀ x y, T x → T y → θ (x * y) = θ y * θ x) ∧ (∀ x, T x → θ (θ x) = x) ∧
      (∀ k ∈ {k | k ∈ K ∧ T k}, θ k ∈ K) ∧ ∀ g, T g → ∃ a ∈ {k | k ∈ K ∧ T k}, ∃ b ∈ {k | k ∈ K ∧ T k}, θ g = a * g * b)
    (hrep : ∀ g, T g → ∃ R : Finset G, (∀ γ ∈ R, T γ) ∧
      (∀ γ ∈ R, ∃ k₁ ∈ {k | k ∈ K ∧ T k}, ∃ k₂ ∈ {k | k ∈ K ∧ T k}, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ {k | k ∈ K ∧ T k}, ∃ k₂ ∈ {k | k ∈ K ∧ T k}, x = k₁ * g * k₂) →
        ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ {k | k ∈ K ∧ T k})
    {α : G} (hα : T α) : ∃ R R' : Finset G, IsDC J α⁻¹ R ∧ IsDC J α R' ∧ R.card = R'.card := by
  have hm : ∀ k, k ∈ {k | k ∈ K ∧ T k} ↔ k ∈ J ⊓ S := fun k => by
    rw [Subgroup.mem_inf, hS]
    exact and_congr_left fun hk => (hK k hk).symm
  simp only [hm] at hθ hrep
  simp only [← hS] at hθ hrep hα hs hK
  obtain ⟨θ, t1, t2, t3, t4, t5⟩ := hθ
  have hdc : ∀ x ∈ S, ∃ R : Finset G, (∀ γ ∈ R, γ ∈ S) ∧ IsDC J x R := by
    intro x hx
    obtain ⟨R, h1, h2, h3⟩ := hrep x hx
    refine ⟨R, h1, isDC_of_local hx h1 (fun k hk => ?_) h2 h3⟩
    obtain ⟨a, ha, b, hb, s1, s2, e1⟩ := hs k hk
    exact ⟨a, ha, b, hb, s1, s2 x hx, e1⟩
  obtain ⟨R, hR, d1⟩ := hdc _ (S.inv_mem hα)
  obtain ⟨R', hR', d2⟩ := hdc _ hα
  have u2 : ∀ x ∈ S, ∀ y ∈ S, θ (x * y) = θ y * θ x := fun x hx y hy => t2 x y hx hy
  have u4 : ∀ k ∈ J ⊓ S, θ k ∈ J := fun k hk => (hK _ (t1 k hk.2)).2 (t4 k hk)
  exact ⟨R, R', d1, d2, le_antisymm (GlobalTheory.DoubleCosetComm.card_le_inv u2 t3 u4 t1 t5 d1 (by rwa [inv_inv]) hR)
    (GlobalTheory.DoubleCosetComm.card_le_inv u2 t3 u4 t1 t5 d2 d1 hR')⟩

theorem central_and_complement : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (PP : Pl D.host.E), IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ P', P' ∈ L.Pg ∨ P' ∈ L.Q → P' ≠ PP ∧ ¬ IsConjPl P' PP) → Bridge.SplitOff PP ∅ → ∃ z : GA D V, (∀ g, Commute z g) ∧ IsHeckeAt V PP V.rank z ∧ ∀ k ≤ V.rank, ∃ (α : GA D V) (R R' : Finset (GA D V)), IsHeckeAt V PP k α ∧ IsHeckeAt V PP (V.rank - k) (z * α⁻¹) ∧ Bridge.IsDC (levG V β L) α⁻¹ R ∧ Bridge.IsDC (levG V β L) α R' ∧ R.card = R'.card := by
  intro D V β Λ N L P hβ hN hL hP
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hP.1
  obtain ⟨ϖ, h1, h2⟩ := exists_unif P
  have hϖ : (ϖ : D.host.E) ≠ 0 := fun e0 => h2 (by rw [show ϖ = 0 from Subtype.ext e0]; exact zero_mem _)
  obtain ⟨S, hS, -, hc⟩ := exists_loc V he
  obtain ⟨l1, -, l3⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N L hβ).2 P e _ (Or.inl ⟨he, rfl⟩) hN hL
  obtain ⟨hθ, hrep, hel⟩ := GlobalTheory.T.involution_spherical_hecke_anti V P e he
  obtain ⟨ζ, hcom, hco⟩ := exists_central V he hϖ
  refine ⟨ζ, hcom, ⟨e, ϖ, he, h1, h2, ?_⟩, fun k hk => ?_⟩
  · have := hco 0 (Nat.zero_le _) 1 (hecke_one he.1.1 ϖ)
    rwa [Nat.sub_zero, inv_one, mul_one] at this
  · obtain ⟨α, hα⟩ := (hel ϖ h1 h2).1 k hk
    obtain ⟨R, R', h⟩ := exists_reps (J := levG V β L) (K := KsphC V ∅) (T := SuppAt e V) hS l1 (fun k hk => by
      obtain ⟨x, hx, y, hy, s1, s2, e1⟩ := l3 k hk
      exact ⟨x, hx, y, hy, s1, fun g hg => hc g hg y s2, e1⟩) hθ (fun g hg => by
      obtain ⟨R, r1, r2, r3⟩ := hrep g hg
      exact ⟨R, r1, fun γ hγ => (r2 γ hγ).2, r3⟩) hα.2.1
    exact ⟨α, R, R', ⟨e, ϖ, he, h1, h2, hα⟩, ⟨e, ϖ, he, h1, h2, hco k hk α hα⟩, h⟩

end GlobalTheory.HeckeCompl
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_hecke_element_exists : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (PP : Pl D.host.E), IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ P', P' ∈ L.Pg ∨ P' ∈ L.Q → P' ≠ PP ∧ ¬ IsConjPl P' PP) → Bridge.SplitOff PP ∅ → ∃ z : GA D V, (∀ g, Commute z g) ∧ IsHeckeAt V PP V.rank z ∧ ∀ k ≤ V.rank, ∃ (α : GA D V) (R R' : Finset (GA D V)), IsHeckeAt V PP k α ∧ IsHeckeAt V PP (V.rank - k) (z * α⁻¹) ∧ Bridge.IsDC (levG V β L) α⁻¹ R ∧ Bridge.IsDC (levG V β L) α R' ∧ R.card = R'.card := by
  atlas_forward_decl GlobalTheory.HeckeCompl.central_and_complement
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.HeckeUnitary

theorem isDC_central {G : Type} [Group G] (J : Subgroup G) {z : G} (hz : ∀ g, Commute z g) :
    Bridge.IsDC J z {z} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k₁, k₂, rfl⟩
  refine ⟨z, ⟨Finset.mem_singleton_self z, ?_⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩
  rw [← (hz k₁).eq, mul_assoc, inv_mul_cancel_left]
  exact J.mul_mem k₁.2 k₂.2

theorem isDC_mul_central {G : Type} [Group G] [DecidableEq G] (J : Subgroup G) {z α : G} (hz : ∀ g, Commute z g)
    {R : Finset G} (h : Bridge.IsDC J α R) : Bridge.IsDC J (α * z) (R.image (· * z)) := by
  have e : ∀ k₁ k₂ : G, k₁ * (α * z) * k₂ = k₁ * α * k₂ * z := fun k₁ k₂ => by
    simp only [mul_assoc, (hz k₂).eq]
  have e' : ∀ a g : G, (a * z)⁻¹ * (g * z) = a⁻¹ * g := fun a g => by
    rw [mul_inv_rev, mul_assoc, ← mul_assoc a⁻¹, ← (hz (a⁻¹ * g)).eq, inv_mul_cancel_left]
  constructor
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
    exact ⟨k₁, k₂, (e _ _).symm⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := h.2 _ ⟨k₁, k₂, rfl⟩
    rw [e]
    refine ⟨a * z, ⟨Finset.mem_image_of_mem _ ha, by rwa [e']⟩, ?_⟩
    rintro y ⟨hy, hy'⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    rw [e'] at hy'
    rw [hu b ⟨hb, hy'⟩]

theorem star_eigenvalue_mul : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (PP : Pl D.host.E) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (c : ℕ → ℂ) (T : MMap M), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ P', P' ∈ L.Pg ∨ P' ∈ L.Q → P' ≠ PP ∧ ¬ IsConjPl P' PP) → Bridge.SplitOff PP ∅ → T ∈ Mult θ M (levG V β L : Set (GA D V)) (fun _ => 1) → ipM M μ 𝓕 T T ≠ 0 → (∀ k ≤ V.rank, ∀ α R, IsHeckeAt V PP k α → Bridge.IsDC (levG V β L) α⁻¹ R → heckeOn M R T = c k • T) → c V.rank ≠ 0 ∧ ∀ k ≤ V.rank, star (c k) * c V.rank = c (V.rank - k) := by
  intro D V S θ M β Λ N L PP μ 𝓕 c T hμ h𝓕 hβ hN hL hsp hT hip hc
  classical
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : SecondCountableTopology (GA D V) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have : Countable (GQ V) := (GlobalTheory.RationalCountable.discrete_countable_GQ D V).2
  have : μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT
  have hex : ∃ a, IsMultIP M μ 𝓕 T T a := by
    by_contra hne
    exact hip (by unfold ipM; rw [dif_neg hne])
  have hIP := ipM_spec M μ 𝓕 T T hex
  choose v hv hv0 using fun τ => (Submodule.ne_bot_iff _).1 (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  let w : M.Vec := fun τ => ⟨v τ, hv τ⟩
  obtain ⟨hint, hval⟩ := hIP w w
  have hne : ∫ g in 𝓕, star (T w g) * T w g ∂μ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero hip (Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 (hv0 τ))
  obtain ⟨g₀, hg₀⟩ : ∃ g, T w g ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hne (by simp [h0])
  have hc' : ∀ k ≤ V.rank, ∀ α R, IsHeckeAt V PP k α → Bridge.IsDC (levG V β L) α⁻¹ R →
      ∀ g, ∑ γ ∈ R, T w (g * γ) = c k * T w g := fun k hk α R h1 h2 g =>
    congrArg (fun T' : MMap M => T' w g) (hc k hk α R h1 h2)
  obtain ⟨z, hz, hzn, hk⟩ := GlobalTheory.T.central_hecke_element_exists V β Λ N L PP hβ hN hL hsp
  have hz' : ∀ g, Commute z⁻¹ g := fun g => (hz g).inv_left
  have hcen : ∀ g, T w (g * z⁻¹) = c V.rank * T w g := fun g => by
    simpa using hc' V.rank le_rfl z {z⁻¹} hzn (isDC_central _ hz') g
  have hn : c V.rank ≠ 0 := fun h0 => hg₀ (by simpa [h0] using hcen (g₀ * z))
  refine ⟨hn, fun k hkn => ?_⟩
  obtain ⟨α, R, R', h1, h2, h3, h4, h5⟩ := hk k hkn
  have h6 : ∀ g, ∑ γ ∈ R', T w (g * γ) = c (V.rank - k) / c V.rank * T w g := fun g => by
    have := hc' (V.rank - k) (Nat.sub_le _ _) (z * α⁻¹) (R'.image (· * z⁻¹)) h2
      (by rw [mul_inv_rev, inv_inv]; exact isDC_mul_central _ hz' h4) g
    rw [Finset.sum_image (fun a _ b _ hab => mul_right_cancel hab)] at this
    simp only [← mul_assoc, hcen, ← Finset.mul_sum] at this
    rw [div_mul_eq_mul_div, ← this, mul_div_cancel_left₀ _ hn]
  have h7 := GlobalTheory.DoubleCosetAdjoint.eigenvalue_inv_eq_star μ (GQ V) (levG V β L) 𝓕 (T w) α⁻¹ R R' (c k)
    (c (V.rank - k) / c V.rank) h𝓕 (hT'.aut w).cont (hT'.aut w).left
    (fun k hk g => by simpa using hT'.lev w k hk g) hint hne h3 (by rwa [inv_inv]) h5
    (hc' k hkn α R h1 h3) h6
  rw [h7, div_mul_cancel₀ _ hn]

end GlobalTheory.HeckeUnitary

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_eigenvalue_at_base_frame : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (PP : Pl D.host.E) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (c : ℕ → ℂ) (T : MMap M), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ P', P' ∈ L.Pg ∨ P' ∈ L.Q → P' ≠ PP ∧ ¬ IsConjPl P' PP) → Bridge.SplitOff PP ∅ → T ∈ Mult θ M (levG V β L : Set (GA D V)) (fun _ => 1) → ipM M μ 𝓕 T T ≠ 0 → (∀ k ≤ V.rank, ∀ α R, IsHeckeAt V PP k α → Bridge.IsDC (levG V β L) α⁻¹ R → heckeOn M R T = c k • T) → c V.rank ≠ 0 ∧ ∀ k ≤ V.rank, star (c k) * c V.rank = c (V.rank - k) := by
  atlas_forward_decl GlobalTheory.HeckeUnitary.star_eigenvalue_mul
end
