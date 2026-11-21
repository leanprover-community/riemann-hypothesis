import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetUniformSmoothBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelDomainOpenSubgroupBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementArchimedeanMatrixForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetArchimedeanNormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction

section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_function_line_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) (γ : ℝ → GAd σ J), Good σ J U A φ → IsRealLine σ J γ → Good σ J U A (lineDer γ φ) := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.good_lineDer | exact GlobalTheory.CompanionTheory.RapidDecay.good_lineDer | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.good_lineDer <;> assumption)
end

section
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem norm_le_of_unipRad_variation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → Continuous φ → IsCuspidal σ J φ → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), 0 < k → GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ (g : GAd σ J) (e : ℝ), (∀ m ∈ unipRad σ J Cc, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  intro F E _ _ _ _ _ σ hCM n J hJ φ hleft hcont hcusp k Cc hk hC g e he
  haveI := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  have hc : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipRad σ J Cc) := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  haveI hP := hc.isProbabilityMeasure
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ := hleft
  have h0 : GlobalTheory.Cusp.constTermOn (ratPts σ J) (unipRad σ J Cc) φ g = 0 :=
    (hc.constTermOn_eq_zero_iff (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ Measure.haar) hL g).2
      (hcusp k Cc ⟨hk, hC.1, hC.2⟩ _ _ inferInstance (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ _) g)
  have hI := hc.integrable hL hcont g
  have key : φ g = ∫ q, (φ g - φ ((q.out : unipRad σ J Cc) * g))
      ∂GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc) := by
    rw [integral_sub (integrable_const _) hI]
    have h0' : ∫ q, φ ((q.out : unipRad σ J Cc) * g)
        ∂GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc) = 0 := h0
    rw [h0', integral_const]
    simp
  rw [key]
  have hb := norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc))
    (f := fun q => φ g - φ ((q.out : unipRad σ J Cc) * g)) (C := e)
    (.of_forall fun q => by rw [norm_sub_rev]; exact he _ (q.out : unipRad σ J Cc).2)
  simpa using hb

end GlobalTheory.CompanionTheory.RapidDecay

end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_constant_term_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → Continuous φ → IsCuspidal σ J φ → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), 0 < k → GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ (g : GAd σ J) (e : ℝ), (∀ m ∈ unipRad σ J Cc, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RapidDecay.norm_le_of_unipRad_variation
end

section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_domain_open_subgroup_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω Cm : Set (GAd σ J)) (c : ℝ) (U : Subgroup (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact Cm → 0 < c → IsOpen (U : Set (GAd σ J)) → ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ∀ s : Fin r, ∀ m ∈ unipRad σ J (pre X s), ∃ γ ∈ ratPts σ J, ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧ κ ∈ finPts σ J ∧ m * (p * a * k) = γ * (p * a * k) * u * κ := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.near_cusp | exact GlobalTheory.CompanionTheory.RapidDecay.near_cusp | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.near_cusp <;> assumption)
end

section
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem param_le_rbar_pow {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    ∀ (k m : ℕ) (h : m < r), m + k + 1 = r → t ⟨m, h⟩ ≤ rbar t ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro m h e
    have h1 := ratio_le_rbar t ⟨m, h⟩
    have h2 : ¬ m + 1 < r := by omega
    simpa [ratio, h2] using h1
  | succ k ih =>
    intro m h e
    have hm : m + 1 < r := by omega
    have h1 := ih (m + 1) hm (by omega)
    have h2 := ratio_le_rbar t ⟨m, h⟩
    have h3 : t ⟨m, h⟩ / t ⟨m + 1, hm⟩ ≤ rbar t := by simpa [ratio, hm] using h2
    have h4 : t ⟨m, h⟩ ≤ rbar t * t ⟨m + 1, hm⟩ := (div_le_iff₀ (ht _)).1 h3
    have h5 : 0 ≤ rbar t := zero_le_one.trans (one_le_rbar t)
    calc t ⟨m, h⟩ ≤ rbar t * t ⟨m + 1, hm⟩ := h4
      _ ≤ rbar t * rbar t ^ (k + 1) := mul_le_mul_of_nonneg_left h1 h5
      _ = rbar t ^ (k + 1 + 1) := by ring

theorem param_le_rbar_pow_rank {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) (i : Fin r) : t i ≤ rbar t ^ r := by
  have h1 := param_le_rbar_pow ht (r - i.val - 1) i.val i.2 (by omega)
  exact h1.trans (pow_le_pow_right₀ (one_le_rbar t) (by omega))

theorem one_add_prod_le_rbar_pow {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    1 + ∏ i, t i ≤ 2 * rbar t ^ (r * r) := by
  have h1 : ∏ i, t i ≤ rbar t ^ (r * r) := by
    have := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin r))) (fun i _ => (ht i).le)
      fun i _ => param_le_rbar_pow_rank ht i
    simpa [pow_mul] using this
  have h2 : 1 ≤ rbar t ^ (r * r) := one_le_pow₀ (one_le_rbar t)
  linarith

theorem height_le_rbar_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ c : ℝ, 0 < c → ∃ b : ℕ, ∀ Ω Cm : Set (GAd σ J), IsCompact Ω → IsCompact Cm → ∃ H : ℝ, 0 ≤ H ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, (height σ J (p * a * k) : ℝ) ≤ H * rbar t ^ b := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW c hc
  have hc' : 0 < min 1 c ^ r := pow_pos (lt_min one_pos hc) _
  obtain ⟨Ch, Ah, hCh⟩ := @GlobalTheory.TorusHeight.height_torus_le F E _ _ _ _ _ σ hσ n J r X Y _ hc'
  refine ⟨r * r * Ah, fun Ω Cm hΩ hCm => ?_⟩
  have hcont : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  obtain ⟨R₁, hR₁⟩ := (hΩ.image hcont).bddAbove
  obtain ⟨R₂, hR₂⟩ := (hCm.image hcont).bddAbove
  set R₁' := max R₁ 0 with hR₁'
  set R₂' := max R₂ 0 with hR₂'
  set Ch' := max Ch 0 with hCh'
  have hR₁0 : 0 ≤ R₁' := le_max_right _ _
  have hR₂0 : 0 ≤ R₂' := le_max_right _ _
  have hCh0 : 0 ≤ Ch' := le_max_right _ _
  refine ⟨R₁' * (Ch' * 2 ^ Ah) * R₂', by positivity, fun p hp t ht a ha k hk => ?_⟩
  have h1 : (height σ J a : ℝ) ≤ Ch * (1 + ∏ i, t i) ^ Ah :=
    hCh t (GlobalTheory.SiegelHt.cone_low hc ht) a ha.1
      (@GlobalTheory.SiegelTorusMat.archMat_torus F E _ _ _ _ _ σ hσ n J hJ r X Y hW t
        (fun i => hc'.trans_le (GlobalTheory.SiegelHt.cone_low hc ht i)) a ha)
  have hprod0 : 0 ≤ 1 + ∏ i, t i := add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => (ht.1 i).le)
  have h2 := one_add_prod_le_rbar_pow (r := r) ht.1
  have h3 : (height σ J a : ℝ) ≤ Ch' * (2 * rbar t ^ (r * r)) ^ Ah :=
    h1.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hprod0 h2 _) (pow_nonneg hprod0 _) hCh0)
  have hpb : (height σ J p : ℝ) ≤ R₁' := (hR₁ ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  have hkb : (height σ J k : ℝ) ≤ R₂' := (hR₂ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
  have h5 : (height σ J (p * a * k) : ℝ) ≤ (height σ J p : ℝ) * height σ J a * height σ J k := by
    exact_mod_cast (height_mul_le σ J _ _).trans (mul_le_mul' (height_mul_le σ J _ _) le_rfl)
  calc (height σ J (p * a * k) : ℝ) ≤ (height σ J p : ℝ) * height σ J a * height σ J k := h5
    _ ≤ R₁' * (Ch' * (2 * rbar t ^ (r * r)) ^ Ah) * R₂' :=
        mul_le_mul (mul_le_mul hpb h3 (NNReal.coe_nonneg _) hR₁0) hkb (NNReal.coe_nonneg _)
          (mul_nonneg hR₁0 ((NNReal.coe_nonneg _).trans h3))
    _ = R₁' * (Ch' * 2 ^ Ah) * R₂' * rbar t ^ (r * r * Ah) := by
      rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.CompanionTheory.RapidDecay

end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bound_siegel_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ c : ℝ, 0 < c → ∃ b : ℕ, ∀ Ω Cm : Set (GAd σ J), IsCompact Ω → IsCompact Cm → ∃ H : ℝ, 0 ≤ H ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, (height σ J (p * a * k) : ℝ) ≤ H * rbar t ^ b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RapidDecay.height_le_rbar_pow
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology
noncomputable section

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem decay_step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {r : ℕ}
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) {Ω : Set (GAd σ J)} (hΩ : IsCompact Ω)
    (hΩP : Ω ⊆ minParOne σ J X) {c : ℝ} (hc : 0 < c) {U : Subgroup (GAd σ J)} (hU : IsOpen (U : Set (GAd σ J))) (A e m : ℕ)
    (hm : ∀ ψ, Good σ J U A ψ → ∀ Cm : Set (GAd σ J), IsCompact Cm → ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ‖ψ (p * a * k)‖ * rbar t ^ m ≤ B * rbar t ^ e)
    (ψ : GAd σ J → ℂ) (hψ : Good σ J U A ψ) (Cm : Set (GAd σ J)) (hCm : IsCompact Cm) :
    ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm,
      ‖ψ (p * a * k)‖ * rbar t ^ (m + 1) ≤ B * rbar t ^ e := by
  obtain ⟨q, b, Ω₀, Cv, δ₁, hb, hΩ₀, hδ₁, hCv, hmv⟩ := GlobalTheory.T.siegel_set_uniform_smooth_bound F E σ h n J hJ
  have hCm' : IsCompact ((fun x : GAd σ J × GAd σ J => x.1 * x.2) '' (Cm ×ˢ Ω₀)) :=
    (hCm.prod hΩ₀).image (by fun_prop)
  choose B hB using fun i => hm _ (GlobalTheory.T.good_function_line_derivative F E σ h n J hJ U A ψ (b i) hψ (hb i)) _ hCm'
  obtain ⟨B₀, hB₀⟩ := hm ψ hψ Cm hCm
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.siegel_domain_open_subgroup_bound F E σ h n J hJ r X Y hW Ω Cm c U hΩ hΩP hCm hc hU
  set R₀ := max 1 (M / δ₁) with hR₀
  have hR1 : 1 ≤ R₀ := le_max_left _ _
  have hSum : 0 ≤ ∑ i, |B i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨R₀ * |B₀| + Cv * M * ∑ i, |B i|, fun p hp t ht a ha k hk => ?_⟩
  have hR := one_le_rbar t
  have hRpos : 0 < rbar t := by linarith
  have hRe : 0 < rbar t ^ e := pow_pos hRpos e
  have hRm : 0 < rbar t ^ m := pow_pos hRpos m
  have hT : 0 ≤ Cv * M * ∑ i, |B i| := mul_nonneg (mul_nonneg hCv hM0) hSum
  by_cases hcase : rbar t ≤ R₀
  · calc ‖ψ (p * a * k)‖ * rbar t ^ (m + 1) = rbar t * (‖ψ (p * a * k)‖ * rbar t ^ m) := by ring
      _ ≤ R₀ * (|B₀| * rbar t ^ e) := by
          refine mul_le_mul hcase ((hB₀ p hp t ht a ha k hk).trans ?_) (by positivity) (by linarith)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hRe.le
      _ ≤ _ := by
          rw [← mul_assoc, add_mul]
          exact le_add_of_nonneg_right (mul_nonneg hT hRe.le)
  · push Not at hcase
    have hne : rbar t ≠ 1 := fun e' => by
      rw [e'] at hcase; linarith
    obtain ⟨s, hs⟩ := (rbar_eq t).resolve_left hne
    have hδ : M / rbar t ≤ δ₁ := by
      rw [div_le_iff₀ hRpos]
      have h1 : M / δ₁ ≤ R₀ := le_max_right _ _
      rw [div_le_iff₀ hδ₁] at h1
      nlinarith
    set g := p * a * k with hg
    set cc : Fin q → ℝ := fun i => |B i| * rbar t ^ e / rbar t ^ m with hcc
    have hcc' : ∀ i, ∀ x ∈ Ω₀, ‖lineDer (b i) ψ (g * x)‖ ≤ cc i := fun i x hx => by
      have := hB i p hp t ht a ha (k * x) ⟨(k, x), ⟨hk, hx⟩, rfl⟩
      rw [show p * a * (k * x) = g * x by rw [hg, mul_assoc (p * a)]] at this
      rw [hcc, le_div_iff₀ hRm]
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hRe.le)
    have hvar : ‖ψ g‖ ≤ Cv * (M / rbar t) * ∑ i, cc i := by
      refine GlobalTheory.T.cuspidal_constant_term_small F E σ h n J hJ ψ hψ.left hψ.cont hψ.cusp _ (pre X s) (Nat.succ_pos _)
        (GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ _) g _ fun m' hm' => ?_
      obtain ⟨γ, hγ, u, κ, hu, hκU, hκf, e'⟩ := hM p hp t ht a ha k hk s m' hm'
      rw [← hs] at hu
      have : ψ (m' * g) = ψ (g * u) := by
        rw [hg, e', hψ.level κ hκU hκf, mul_assoc γ, hψ.left γ hγ]
      rw [this]
      exact hmv ψ hψ.smooth g u _ (div_nonneg hM0 hRpos.le) hδ hu cc hcc'
    have hsum : ∑ i, cc i = (∑ i, |B i|) * rbar t ^ e / rbar t ^ m := by
      rw [hcc, Finset.sum_mul, Finset.sum_div]
    calc ‖ψ g‖ * rbar t ^ (m + 1) ≤ (Cv * (M / rbar t) * ∑ i, cc i) * rbar t ^ (m + 1) :=
          mul_le_mul_of_nonneg_right hvar (pow_pos hRpos _).le
      _ = (Cv * M * ∑ i, |B i|) * rbar t ^ e := by
          rw [hsum, pow_succ]
          field_simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hRe.le
          exact le_add_of_nonneg_left (by positivity)

theorem rapid_decrease : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ), IsCompact (K : Set (GAd σ J)) → IsCompact Ω → Ω ⊆ minParOne σ J X → 0 < c → ∀ φ : GAd σ J → ℂ, IsSmoothModerate σ J φ → IsCuspidal σ J φ → ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ siegelSet σ J X Y Ω c K, ‖φ g‖ * (height σ J g : ℝ) ^ N ≤ C := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW K Ω c hK hΩ hΩP hc φ hs hcu N
  obtain ⟨U, hU, hlev⟩ := hs.level
  obtain ⟨A, hA⟩ := hs.growth
  have hG : Good σ J U A φ := ⟨hs.left, hlev, hs.cont, hs.smooth, hA, hcu⟩
  obtain ⟨b, hb⟩ := GlobalTheory.T.height_bound_siegel_torus F E σ h n J hJ r X Y hW c hc
  set e := b * A with he
  have hbase : ∀ ψ, Good σ J U A ψ → ∀ Cm : Set (GAd σ J), IsCompact Cm → ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ‖ψ (p * a * k)‖ * rbar t ^ 0 ≤ B * rbar t ^ e := fun ψ hψ Cm hCm => by
    obtain ⟨H, hH0, hH⟩ := hb Ω Cm hΩ hCm
    obtain ⟨C, hC⟩ := hψ.growth [] (by simp)
    refine ⟨|C| * H ^ A, fun p hp t ht a ha k hk => ?_⟩
    have h1 := hC (p * a * k)
    have h2 := hH p hp t ht a ha k hk
    have h3 : (0 : ℝ) ≤ (height σ J (p * a * k) : ℝ) := NNReal.coe_nonneg _
    simp only [List.foldr_nil] at h1
    rw [pow_zero, mul_one, he, pow_mul, mul_assoc |C|, ← mul_pow]
    exact h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg h3 _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 A) (abs_nonneg _)))
  have hall : ∀ m : ℕ, ∀ ψ, Good σ J U A ψ → ∀ Cm : Set (GAd σ J), IsCompact Cm → ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ‖ψ (p * a * k)‖ * rbar t ^ m ≤ B * rbar t ^ e := fun m => by
    induction m with
    | zero => exact hbase
    | succ m ih => exact fun ψ hψ Cm hCm => decay_step h hJ hW hΩ hΩP hc hU A e m ih ψ hψ Cm hCm
  obtain ⟨B, hB⟩ := hall (b * N + e) φ hG _ hK
  obtain ⟨H, hH0, hH⟩ := hb Ω K hΩ hK
  refine ⟨|B| * H ^ N, ?_⟩
  rintro _ ⟨p, hp, t, ht, a, ha, k, hk, rfl⟩
  have hR := one_le_rbar t
  have hRpos : 0 < rbar t := by linarith
  have h1 := hB p hp t ht a ha k hk
  have h2 := hH p hp t ht a ha k hk
  have h3 : (0 : ℝ) ≤ (height σ J (p * a * k) : ℝ) := NNReal.coe_nonneg _
  have h4 : ‖φ (p * a * k)‖ * rbar t ^ (b * N) ≤ |B| := by
    rw [pow_add, ← mul_assoc] at h1
    have h5 := h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos hRpos e).le)
    exact le_of_mul_le_mul_right h5 (pow_pos hRpos e)
  calc ‖φ (p * a * k)‖ * (height σ J (p * a * k) : ℝ) ^ N ≤ ‖φ (p * a * k)‖ * (H * rbar t ^ b) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 N) (norm_nonneg _)
    _ = (‖φ (p * a * k)‖ * rbar t ^ (b * N)) * H ^ N := by rw [mul_pow, pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h4 (pow_nonneg hH0 _)

end GlobalTheory.CompanionTheory.RapidDecay

end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_rapid_decay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ), IsCompact (K : Set (GAd σ J)) → IsCompact Ω → Ω ⊆ minParOne σ J X → 0 < c → ∀ φ : GAd σ J → ℂ, IsSmoothModerate σ J φ → IsCuspidal σ J φ → ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ siegelSet σ J X Y Ω c K, ‖φ g‖ * (height σ J g : ℝ) ^ N ≤ C := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RapidDecay.rapid_decrease
end
