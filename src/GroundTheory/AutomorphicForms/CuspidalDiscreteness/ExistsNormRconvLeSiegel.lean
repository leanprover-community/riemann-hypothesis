import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.Reduction
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelFinite

section
namespace GroundTheory.Automorphic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_sub_translate_le {k : ℕ} {ρ : E → F} (hρ : ContDiff ℝ (k + 1) ρ)
    {B : ℝ} (hB : ∀ w, ‖iteratedFDeriv ℝ (k + 1) ρ w‖ ≤ B) (y w : E) :
    ‖iteratedFDeriv ℝ k (fun t => ρ (t + y) - ρ t) w‖ ≤ B * ‖y‖ := by
  have h1 : ContDiff ℝ k ρ := hρ.of_le (by exact_mod_cast Nat.le_succ k)
  have h2 : ContDiff ℝ k (fun t => ρ (t + y)) := h1.comp (contDiff_id.add contDiff_const)
  have hsub : iteratedFDeriv ℝ k (fun t => ρ (t + y) - ρ t) w =
      iteratedFDeriv ℝ k ρ (w + y) - iteratedFDeriv ℝ k ρ w := by
    have := iteratedFDeriv_sub_apply (x := w) (i := k) h2.contDiffAt h1.contDiffAt
    rw [show (fun t => ρ (t + y) - ρ t) = (fun t => ρ (t + y)) - ρ from rfl, this,
      iteratedFDeriv_comp_add_right]
  rw [hsub]
  have hdiff : Differentiable ℝ (fun x => iteratedFDeriv ℝ k ρ x) :=
    hρ.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (f := fun x => iteratedFDeriv ℝ k ρ x) (x := w) (y := w + y) (C := B)
    (fun x _ => hdiff x) (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hB x)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa using this

theorem norm_altSum_le : ∀ (k : ℕ) {ρ : E → F}, ContDiff ℝ k ρ → ∀ {B : ℝ},
    (∀ w, ‖iteratedFDeriv ℝ k ρ w‖ ≤ B) → ∀ (v : Fin k → E) (z : E),
      ‖altSum k ρ v z‖ ≤ B * ∏ i, ‖v i‖
  | 0, ρ, _, B, hB, v, z => by
    simpa [norm_iteratedFDeriv_zero] using hB z
  | k + 1, ρ, hρ, B, hB, v, z => by
    rw [altSum_succ, Fin.prod_univ_succ, ← mul_assoc]
    have hg : ContDiff ℝ k (fun t => ρ (t + v 0) - ρ t) :=
      ((hρ.of_le (by exact_mod_cast Nat.le_succ k)).comp (contDiff_id.add contDiff_const)).sub
        (hρ.of_le (by exact_mod_cast Nat.le_succ k))
    exact norm_altSum_le k hg (fun w => norm_iteratedFDeriv_sub_translate_le hρ hB (v 0) w)
      (Fin.tail v) z

theorem exists_norm_altSum_le {ρ : E → F} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) (k : ℕ) :
    ∃ B : ℝ, ∀ (v : Fin k → E) (z : E), ‖altSum k ρ v z‖ ≤ B * ∏ i, ‖v i‖ := by
  have hcont : Continuous fun x => iteratedFDeriv ℝ k ρ x :=
    hρ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support (hc.iteratedFDeriv k)
  exact ⟨B, norm_altSum_le k (hρ.of_le (by exact_mod_cast le_top)) hB⟩

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def unipBallMat (R : ℝ) : Set (ArchMatrix K n) := {A | ‖A - 1‖ ≤ R ∧ (A - 1) * (A - 1) = 0}

theorem isCompact_unipBallMat (R : ℝ) : IsCompact (unipBallMat (K := K) (n := n) R) := by
  refine (isCompact_closedBall (1 : ArchMatrix K n) R).of_isClosed_subset ?_ fun A hA => ?_
  · exact (isClosed_le (continuous_id.sub continuous_const).norm continuous_const).inter
      (isClosed_eq ((continuous_id.sub continuous_const).mul (continuous_id.sub continuous_const))
        continuous_const)
  · rw [Metric.mem_closedBall, dist_eq_norm]
    exact hA.1

theorem unipBallMat_subset_range (R : ℝ) :
    unipBallMat (K := K) (n := n) R ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) := by
  intro A hA
  refine ⟨⟨A, 2 - A, ?_, ?_⟩, rfl⟩
  · have := hA.2
    calc A * (2 - A) = 1 - (A - 1) * (A - 1) := by noncomm_ring
      _ = 1 := by rw [this, sub_zero]
  · have := hA.2
    calc (2 - A) * A = 1 - (A - 1) * (A - 1) := by noncomm_ring
      _ = 1 := by rw [this, sub_zero]

def unipBall (R : ℝ) : Set (ArchUnits K n) :=
  (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' unipBallMat R

theorem isCompact_unipBall (R : ℝ) : IsCompact (unipBall (K := K) (n := n) R) :=
  Units.isOpenEmbedding_val.isInducing.isCompact_preimage' (isCompact_unipBallMat R)
    (unipBallMat_subset_range R)

theorem altPoint_mul_altPoint {k : ℕ} {Y : Fin k → ArchMatrix K n} (hY : ∀ i j, Y i * Y j = 0)
    (ε : Fin k → Bool) : altPoint Y ε * altPoint Y ε = 0 := by
  unfold altPoint
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs <;> simp [hY]

theorem norm_altPoint_le {k : ℕ} {Y : Fin k → ArchMatrix K n} {R : ℝ} (hR : ∀ i, ‖Y i‖ ≤ R)
    (ε : Fin k → Bool) : ‖altPoint Y ε‖ ≤ k * R := by
  unfold altPoint
  calc ‖∑ i, if ε i then Y i else 0‖ ≤ ∑ i : Fin k, ‖if ε i then Y i else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, R := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · exact hR i
        · rw [norm_zero]; exact (norm_nonneg _).trans (hR i)
    _ = k * R := by simp

theorem altPoint_neg_mul {k : ℕ} (Y : Fin k → ArchMatrix K n) (a : ArchMatrix K n)
    (ε : Fin k → Bool) : altPoint (fun i => -(Y i * a)) ε = -(altPoint Y ε * a) := by
  unfold altPoint
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem val_inv_eq_of_val_eq {C : ArchUnits K n} {W : ArchMatrix K n} (hW : W * W = 0)
    (hC : (C : ArchMatrix K n) = 1 + W) : ((C⁻¹ : ArchUnits K n) : ArchMatrix K n) = 1 - W := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hC]
  calc (1 + W) * (1 - W) = 1 - W * W := by noncomm_ring
    _ = 1 := by rw [hW, sub_zero]

section Diff

variable (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure] {β : ArchMatrix K n → ℝ}

theorem integrable_archConv_integrand (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (h : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (C : ArchUnits K n)
    (w : normOneGL K n) :
    Integrable (fun A : ArchUnits K n =>
      (β ((C * A : ArchUnits K n) : ArchMatrix K n) : ℂ) * h ((archProj K n A)⁻¹ * w)) ν := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (Complex.continuous_ofReal.comp (hβ.comp (Units.continuous_val.comp
      (continuous_const.mul continuous_id)))).mul
      (h.continuous.comp ((continuous_archProj.inv).mul continuous_const))
  · refine HasCompactSupport.intro ((isCompact_unitsSupport hβc hβu).image
      (continuous_const_mul C⁻¹)) fun A hA => ?_
    have : ((C * A : ArchUnits K n) : ArchMatrix K n) ∉ tsupport β := fun h' =>
      hA ⟨C * A, h', by simp⟩
    rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]

theorem sum_altSign_archConvFun_eq (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (h : CompactlySupportedContinuousMap (normOneGL K n) ℂ) {k : ℕ} {Y : Fin k → ArchMatrix K n}
    (hY : ∀ i j, Y i * Y j = 0) {C : (Fin k → Bool) → ArchUnits K n}
    (hC : ∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) (w : normOneGL K n) :
    ∑ ε, (altSign ε : ℂ) * archConvFun ν β h ((archProj K n (C ε))⁻¹ * w) =
      ∫ A : ArchUnits K n, ((altSum k β (fun i => -(Y i * (A : ArchMatrix K n)))
        (A : ArchMatrix K n) : ℝ) : ℂ) * h ((archProj K n A)⁻¹ * w) ∂ν := by
  have hterm : ∀ ε, archConvFun ν β h ((archProj K n (C ε))⁻¹ * w) =
      ∫ A : ArchUnits K n, (β ((A : ArchMatrix K n) + altPoint (fun i => -(Y i *
        (A : ArchMatrix K n))) ε) : ℂ) * h ((archProj K n A)⁻¹ * w) ∂ν := by
    intro ε
    rw [← map_inv, archConvFun_archProj_mul]
    refine integral_congr_ae (Eventually.of_forall fun A => ?_)
    simp only
    rw [Units.val_mul, val_inv_eq_of_val_eq (altPoint_mul_altPoint hY ε) (hC ε),
      altPoint_neg_mul, sub_mul, one_mul, sub_eq_add_neg]
  simp_rw [hterm, ← integral_const_mul]
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Eventually.of_forall fun A => ?_)
    simp only
    rw [altSum_eq_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [zsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]
  · intro ε _
    refine (Integrable.const_mul ?_ _)
    have := integrable_archConv_integrand ν hβ hβc hβu h (C ε)⁻¹ w
    refine this.congr (Eventually.of_forall fun A => ?_)
    simp only
    rw [Units.val_mul, val_inv_eq_of_val_eq (altPoint_mul_altPoint hY ε) (hC ε),
      altPoint_neg_mul, sub_mul, one_mul, sub_eq_add_neg]

theorem val_inv_mul_eq {k : ℕ} {Y : Fin k → ArchMatrix K n} (hY : ∀ i j, Y i * Y j = 0)
    {C : ArchUnits K n} {ε : Fin k → Bool} (hC : (C : ArchMatrix K n) = 1 + altPoint Y ε)
    (A : ArchUnits K n) :
    ((C⁻¹ * A : ArchUnits K n) : ArchMatrix K n) =
      (A : ArchMatrix K n) + altPoint (fun i => -(Y i * (A : ArchMatrix K n))) ε := by
  rw [Units.val_mul, val_inv_eq_of_val_eq (altPoint_mul_altPoint hY ε) hC, altPoint_neg_mul,
    sub_mul, one_mul, sub_eq_add_neg]

theorem mem_unipBall_of_val_eq {k : ℕ} {Y : Fin k → ArchMatrix K n} (hY : ∀ i j, Y i * Y j = 0)
    {R : ℝ} (hR : ∀ i, ‖Y i‖ ≤ R) {C : ArchUnits K n} {ε : Fin k → Bool}
    (hC : (C : ArchMatrix K n) = 1 + altPoint Y ε) : C ∈ unipBall (k * R) := by
  refine ⟨?_, ?_⟩
  · rw [hC, add_sub_cancel_left]
    exact norm_altPoint_le hR ε
  · rw [hC, add_sub_cancel_left]
    exact altPoint_mul_altPoint hY ε

theorem exists_norm_sum_altSign_archConvFun_le (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (h : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (k : ℕ) (R : ℝ) :
    ∃ c : ℝ, ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ (C : (Fin k → Bool) → ArchUnits K n),
        (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) → ∀ w : normOneGL K n,
        ‖∑ ε, (altSign ε : ℂ) * archConvFun ν β h ((archProj K n (C ε))⁻¹ * w)‖ ≤
          c * ∏ i, ‖Y i‖ := by
  obtain ⟨Bk, hBk⟩ := exists_norm_altSum_le hβ hβc k
  set S' := unipBall (K := K) (n := n) (k * R) *
    (Units.val : ArchUnits K n → ArchMatrix K n) ⁻¹' tsupport β
  have hS' : IsCompact S' := (isCompact_unipBall _).mul (isCompact_unitsSupport hβc hβu)
  obtain ⟨Rβ, hRβ⟩ := hS'.exists_bound_of_continuousOn
    (Units.continuous_val (M := ArchMatrix K n)).continuousOn
  obtain ⟨Mh, hMh⟩ := h.continuous.bounded_above_of_compact_support h.hasCompactSupport
  set Bk' := max Bk 0
  set Rβ' := max Rβ 0
  set Mh' := max Mh 0
  refine ⟨Bk' * Rβ' ^ k * Mh' * ν.real S', fun Y hY hR C hC w => ?_⟩
  rw [sum_altSign_archConvFun_eq ν hβ.continuous hβc hβu h hY hC w]
  have hpt : ∀ A : ArchUnits K n, ‖((altSum k β (fun i => -(Y i * (A : ArchMatrix K n)))
      (A : ArchMatrix K n) : ℝ) : ℂ) * h ((archProj K n A)⁻¹ * w)‖ ≤
      S'.indicator (fun _ => Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k * Mh') A := by
    intro A
    by_cases hA : A ∈ S'
    · rw [indicator_of_mem hA, norm_mul, Complex.norm_real]
      refine mul_le_mul ?_ ((hMh _).trans (le_max_left _ _)) (norm_nonneg _) ?_
      · refine (hBk _ _).trans ?_
        have hA' : ‖(A : ArchMatrix K n)‖ ≤ Rβ' := (hRβ A hA).trans (le_max_left _ _)
        have hprod : ∏ i, ‖-(Y i * (A : ArchMatrix K n))‖ ≤ (∏ i, ‖Y i‖) * Rβ' ^ k := by
          rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
          refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
          rw [norm_neg]
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hA' (norm_nonneg _))
        calc Bk * ∏ i, ‖-(Y i * (A : ArchMatrix K n))‖
            ≤ Bk' * ∏ i, ‖-(Y i * (A : ArchMatrix K n))‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Finset.prod_nonneg fun i _ => norm_nonneg _)
          _ ≤ Bk' * ((∏ i, ‖Y i‖) * Rβ' ^ k) :=
              mul_le_mul_of_nonneg_left hprod (le_max_right _ _)
          _ = Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k := by ring
      · exact mul_nonneg (mul_nonneg (le_max_right _ _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _)) (pow_nonneg (le_max_right _ _) _)
    · rw [indicator_of_notMem hA]
      have hzero : altSum k β (fun i => -(Y i * (A : ArchMatrix K n))) (A : ArchMatrix K n) = 0 := by
        rw [altSum_eq_sum]
        refine Finset.sum_eq_zero fun ε _ => ?_
        rw [← val_inv_mul_eq hY (hC ε) A]
        by_cases hs : (((C ε)⁻¹ * A : ArchUnits K n) : ArchMatrix K n) ∈ tsupport β
        · exact absurd ⟨C ε, mem_unipBall_of_val_eq hY hR (hC ε), _, hs, mul_inv_cancel_left _ _⟩ hA
        · rw [image_eq_zero_of_notMem_tsupport hs, smul_zero]
      rw [hzero, Complex.ofReal_zero, zero_mul, norm_zero]
  calc ‖∫ A : ArchUnits K n, ((altSum k β (fun i => -(Y i * (A : ArchMatrix K n)))
        (A : ArchMatrix K n) : ℝ) : ℂ) * h ((archProj K n A)⁻¹ * w) ∂ν‖
      ≤ ∫ A, S'.indicator (fun _ => Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k * Mh') A ∂ν :=
        norm_integral_le_of_norm_le ((integrableOn_const hS'.measure_lt_top.ne).integrable_indicator
          hS'.measurableSet) (Eventually.of_forall hpt)
    _ = Bk' * (∏ i, ‖Y i‖) * Rβ' ^ k * Mh' * ν.real S' := by
        rw [integral_indicator hS'.measurableSet, setIntegral_const, smul_eq_mul, mul_comm]
    _ = Bk' * Rβ' ^ k * Mh' * ν.real S' * ∏ i, ‖Y i‖ := by ring

end Diff

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

section Abstract

variable {V : Type*} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
  {ν : Measure V} [ν.IsAddLeftInvariant] [ν.IsAddRightInvariant]
  {L : AddSubgroup V} [Countable L] {D : Set V}

theorem setIntegral_add_right_of_periodic (hD : IsAddFundamentalDomain L D ν) {h : V → ℂ}
    (hper : ∀ ξ ∈ L, ∀ s, h (ξ + s) = h s) (y : V) :
    ∫ t in D, h (t + y) ∂ν = ∫ t in D, h t ∂ν := by
  have hD' : IsAddFundamentalDomain L ((· + (-y)) ⁻¹' D) ν :=
    hD.preimage_of_equiv (measurePreserving_add_right ν (-y)).quasiMeasurePreserving
      (e := id) bijective_id fun g x => by
        simp only [id, AddSubgroup.vadd_def, vadd_eq_add, add_assoc]
  calc ∫ t in D, h (t + y) ∂ν
      = ∫ u in (· + (-y)) ⁻¹' D, (fun t => h (t + y)) (u + (-y)) ∂ν :=
        ((measurePreserving_add_right ν (-y)).setIntegral_preimage_emb
          (MeasurableEquiv.addRight (-y)).measurableEmbedding (fun t => h (t + y)) D).symm
    _ = ∫ u in (· + (-y)) ⁻¹' D, h u ∂ν := by
        simp only [neg_add_cancel_right]
    _ = ∫ t in D, h t ∂ν := hD'.setIntegral_eq hD fun ξ x => hper ξ ξ.2 x

theorem norm_le_of_forall_altSum_le (hD : IsAddFundamentalDomain L D ν) (hD1 : ν D = 1) :
    ∀ (k : ℕ) (h : V → ℂ), (∀ ξ ∈ L, ∀ s, h (ξ + s) = h s) →
      (∀ t, IntegrableOn (fun y => h (t + y)) D ν) → ∫ y in D, h y ∂ν = 0 →
      ∀ B : ℝ, (∀ y : Fin k → V, (∀ i, y i ∈ D) → ‖altSum k h y 0‖ ≤ B) → ‖h 0‖ ≤ B
  | 0, h, _, _, _, B, hB => by
    simpa using hB Fin.elim0 fun i => i.elim0
  | k + 1, h, hper, hint, hmean, B, hB => by
    have hi0 : IntegrableOn h D ν := by simpa using hint 0
    have hstep : ∀ y ∈ D, ‖h (0 + y) - h 0‖ ≤ B := by
      intro y hy
      set g : V → ℂ := fun t => h (t + y) - h t with hg
      have hper' : ∀ ξ ∈ L, ∀ s, g (ξ + s) = g s := fun ξ hξ s => by
        simp only [hg, add_assoc, hper ξ hξ]
      have hint' : ∀ t, IntegrableOn (fun y' => g (t + y')) D ν := by
        intro t
        have h1 := hint (t + y)
        have e : (fun y' => h (t + y + y')) = fun y' => h (t + y' + y) :=
          funext fun y' => by rw [add_right_comm]
        rw [e] at h1
        exact h1.sub (hint t)
      have hiy : IntegrableOn (fun t => h (t + y)) D ν := by
        have h1 := hint y
        have e : (fun y' => h (y + y')) = fun t => h (t + y) := funext fun t => by rw [add_comm]
        rwa [e] at h1
      have hmean' : ∫ t in D, g t ∂ν = 0 := by
        rw [show (∫ t in D, g t ∂ν) = (∫ t in D, h (t + y) ∂ν) - ∫ t in D, h t ∂ν from
          integral_sub hiy hi0, setIntegral_add_right_of_periodic hD hper y, sub_self]
      have hB' : ∀ z : Fin k → V, (∀ i, z i ∈ D) → ‖altSum k g z 0‖ ≤ B := by
        intro z hz
        have hmem : ∀ i, (Fin.cons y z : Fin (k + 1) → V) i ∈ D := by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hy
          · simpa using hz j
        have := hB (Fin.cons y z) hmem
        rwa [altSum_succ, Fin.cons_zero, Fin.tail_cons] at this
      have := norm_le_of_forall_altSum_le hD hD1 k g hper' hint' hmean' B hB'
      simpa [hg] using this
    have hfin : ν D < ⊤ := by rw [hD1]; exact ENNReal.one_lt_top
    have hkey : ∫ y in D, (h (0 + y) - h 0) ∂ν = -h 0 := by
      have hi0' : IntegrableOn (fun y => h (0 + y)) D ν := by simpa using hi0
      rw [integral_sub hi0' (integrableOn_const hfin.ne)]
      simp only [zero_add, hmean, setIntegral_const, measureReal_def, hD1, ENNReal.toReal_one,
        one_smul, zero_sub]
    calc ‖h 0‖ = ‖∫ y in D, (h (0 + y) - h 0) ∂ν‖ := by rw [hkey, norm_neg]
      _ ≤ B * ν.real D := norm_setIntegral_le_of_norm_le_const hfin hstep
      _ = B := by simp [measureReal_def, hD1]

end Abstract

section Scaled

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (K n) in

def scaledUnipFD (r M : ℕ) : Set (UPos n r → 𝔸[K]) :=
  {X | (fun p => algebraMap K 𝔸[K] ((M : K)⁻¹) * X p) ∈ unipFundamentalDomain K n r}

variable {r M : ℕ}

theorem mem_scaledUnipFD {X : UPos n r → 𝔸[K]} :
    X ∈ scaledUnipFD K n r M ↔
      ∀ p, algebraMap K 𝔸[K] ((M : K)⁻¹) * X p ∈ GroundTheory.Global.fundamentalSet K := by
  simp [scaledUnipFD, unipFundamentalDomain, Set.mem_pi]

theorem measurableSet_scaledUnipFD : MeasurableSet (scaledUnipFD K n r M) :=
  measurableSet_unipFundamentalDomain.preimage
    (continuous_pi fun p => continuous_const.mul (continuous_apply p)).measurable

theorem algebraMap_inv_mul_natCast (hM : 0 < M) :
    algebraMap K 𝔸[K] ((M : K)⁻¹) * (M : 𝔸[K]) = 1 := by
  have hM' : (M : K) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← map_natCast (algebraMap K 𝔸[K]) M, ← map_mul, inv_mul_cancel₀ hM', map_one]

theorem existsUnique_vadd_mem_scaledUnipFD (hM : 0 < M) (X : UPos n r → 𝔸[K]) :
    ∃! ξ : unipLattice K n r, ξ +ᵥ X ∈ scaledUnipFD K n r M := by
  have hM' : (M : K) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  set c := algebraMap K 𝔸[K] ((M : K)⁻¹) with hc
  choose k hk huniq using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (c * X p)
  have hmul : ∀ η : K, c * algebraMap K 𝔸[K] η = algebraMap K 𝔸[K] ((M : K)⁻¹ * η) := fun η => by
    rw [hc, map_mul]
  have hmem : (fun p => algebraMap K 𝔸[K] (-((M : K) * k p))) ∈ unipLattice K n r :=
    ⟨fun p => -((M : K) * k p), funext fun p => rfl⟩
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · show (fun p => algebraMap K 𝔸[K] (-((M : K) * k p))) + X ∈ scaledUnipFD K n r M
    rw [mem_scaledUnipFD]
    intro p
    change c * (algebraMap K 𝔸[K] (-((M : K) * k p)) + X p) ∈ GroundTheory.Global.fundamentalSet K
    rw [mul_add, hmul, show (M : K)⁻¹ * -((M : K) * k p) = -k p by field_simp, map_neg, add_comm,
      ← sub_eq_add_neg]
    exact hk p
  · rintro ⟨_, η, rfl⟩ hη
    rw [mem_scaledUnipFD] at hη
    refine Subtype.ext (funext fun p => ?_)
    have h1 := hη p
    change c * (algebraMap K 𝔸[K] (η p) + X p) ∈ GroundTheory.Global.fundamentalSet K at h1
    rw [mul_add, hmul, add_comm, ← sub_neg_eq_add, ← map_neg] at h1
    have h2 := huniq p _ h1
    change algebraMap K 𝔸[K] (η p) = algebraMap K 𝔸[K] (-((M : K) * k p))
    rw [← h2]
    congr 1
    field_simp

theorem isAddFundamentalDomain_scaledUnipFD (hM : 0 < M) :
    IsAddFundamentalDomain (unipLattice K n r) (scaledUnipFD K n r M) (unipMeasure K n r) :=
  IsAddFundamentalDomain.mk' measurableSet_scaledUnipFD.nullMeasurableSet
    (existsUnique_vadd_mem_scaledUnipFD hM)

theorem unipMeasure_scaledUnipFD (hM : 0 < M) :
    unipMeasure K n r (scaledUnipFD K n r M) = 1 := by
  rw [(isAddFundamentalDomain_scaledUnipFD hM).measure_eq
    isAddFundamentalDomain_unipFundamentalDomain, unipMeasure_unipFundamentalDomain]

theorem eq_natCast_mul_of_mem_scaledUnipFD (hM : 0 < M) {X : UPos n r → 𝔸[K]}
    (hX : X ∈ scaledUnipFD K n r M) (p : UPos n r) :
    X p = (M : 𝔸[K]) * (algebraMap K 𝔸[K] ((M : K)⁻¹) * X p) ∧
      algebraMap K 𝔸[K] ((M : K)⁻¹) * X p ∈ GroundTheory.Global.fundamentalSet K := by
  refine ⟨?_, mem_scaledUnipFD.1 hX p⟩
  rw [← mul_assoc, mul_comm (M : 𝔸[K]), algebraMap_inv_mul_natCast hM, one_mul]

theorem exists_finite_eq_natCast_mul (hM : 0 < M) {X : UPos n r → 𝔸[K]}
    (hX : X ∈ scaledUnipFD K n r M) (p : UPos n r) :
    ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
      (X p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a := by
  obtain ⟨h1, h2⟩ := eq_natCast_mul_of_mem_scaledUnipFD hM hX p
  refine ⟨(algebraMap K 𝔸[K] ((M : K)⁻¹) * X p).2, h2.2, ?_⟩
  conv_lhs => rw [h1]
  rfl

variable (K) in

def scaledInfSet (M : ℕ) : Set (InfiniteAdeleRing K) :=
  (fun x => (M : InfiniteAdeleRing K) * x) '' closure (GroundTheory.Global.fundamentalSetInfinite K)

theorem isCompact_scaledInfSet (M : ℕ) : IsCompact (scaledInfSet K M) :=
  (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite K).image (continuous_const_mul _)

theorem infinite_mem_scaledInfSet (hM : 0 < M) {X : UPos n r → 𝔸[K]}
    (hX : X ∈ scaledUnipFD K n r M) (p : UPos n r) : (X p).1 ∈ scaledInfSet K M := by
  obtain ⟨h1, h2⟩ := eq_natCast_mul_of_mem_scaledUnipFD hM hX p
  refine ⟨(algebraMap K 𝔸[K] ((M : K)⁻¹) * X p).1, subset_closure h2.1, ?_⟩
  conv_rhs => rw [h1]
  rfl

theorem exists_finite_sum_eq_natCast_mul (hM : 0 < M) {ι : Type*} (s : Finset ι)
    (y : ι → UPos n r → 𝔸[K]) (hy : ∀ i ∈ s, y i ∈ scaledUnipFD K n r M) (p : UPos n r) :
    ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
      ((∑ i ∈ s, y i) p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [Finset.sum_empty, mul_zero]
    rfl
  | insert i s hi ih =>
    obtain ⟨a, ha, hae⟩ := exists_finite_eq_natCast_mul hM (hy i (Finset.mem_insert_self i s)) p
    obtain ⟨b, hb, hbe⟩ := ih fun j hj => hy j (Finset.mem_insert_of_mem hj)
    refine ⟨a + b, add_mem ha hb, ?_⟩
    rw [Finset.sum_insert hi, Pi.add_apply,
      show (y i p + (∑ x ∈ s, y x) p).2 = (y i p).2 + ((∑ x ∈ s, y x) p).2 from rfl, hae, hbe,
      mul_add]

theorem exists_finite_altPoint_eq_natCast_mul (hM : 0 < M) {k : ℕ} (y : Fin k → UPos n r → 𝔸[K])
    (hy : ∀ i, y i ∈ scaledUnipFD K n r M) (ε : Fin k → Bool) (p : UPos n r) :
    ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
      ((altPoint y ε) p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a := by
  classical
  have : altPoint y ε = ∑ i ∈ Finset.univ.filter (fun i => ε i = true), y i := by
    rw [altPoint, Finset.sum_filter]
  rw [this]
  exact exists_finite_sum_eq_natCast_mul hM _ y (fun i _ => hy i) p

end Scaled

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

def truncInf {r : ℕ} (s : UPos n r → 𝔸[K]) : UPos n r → 𝔸[K] := fun p => ((s p).1, 0)

def truncFin {r : ℕ} (s : UPos n r → 𝔸[K]) : UPos n r → 𝔸[K] := fun p => (0, (s p).2)

theorem truncInf_add_truncFin {r : ℕ} (s : UPos n r → 𝔸[K]) : truncInf s + truncFin s = s := by
  funext p
  change ((s p).1 + 0, 0 + (s p).2) = s p
  rw [add_zero, zero_add]
  rfl

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem rconv_mul_right (f : normOneGL K n → ℂ) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ))
    {g : normOneGL K n} (hf : ∀ w, f (g⁻¹ * w) = f w) (y : normOneGL K n) :
    rconv Γ₁ μ f φ (y * g) = rconv Γ₁ μ f φ y := by
  unfold rconv
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  change f ((y * g)⁻¹ * z) * _ = f (y⁻¹ * z) * _
  rw [mul_inv_rev, mul_assoc, hf]

theorem exists_isCompact_superset_scaledUnipFD (r : ℕ) {M : ℕ} (hM : 0 < M) :
    ∃ C : Set (UPos n r → 𝔸[K]), IsCompact C ∧ scaledUnipFD K n r M ⊆ C := by
  set Cf : Set (FiniteAdeleRing (𝓞 K) K) := (fun a => (M : FiniteAdeleRing (𝓞 K) K) * a) ''
    (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))
  have hCf : IsCompact Cf := (GroundTheory.Global.isCompact_integralFiniteAdeles K).image (continuous_const_mul _)
  refine ⟨univ.pi fun _ => scaledInfSet K M ×ˢ Cf,
    isCompact_univ_pi fun _ => (isCompact_scaledInfSet M).prod hCf, fun X hX p _ => ?_⟩
  obtain ⟨a, ha, hXa⟩ := exists_finite_eq_natCast_mul hM hX p
  exact ⟨infinite_mem_scaledInfSet hM hX p, a, ha, hXa.symm⟩

theorem norm_rconv_le_of_altSum (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} (hφ : φ ∈ cuspidalL2 μ) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    {M : ℕ} (hM : 0 < M) (x : normOneGL K n) (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin k → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum k (fun s => rconv Γ₁ μ f φ (unipOne K n r s * x)) y 0‖ ≤ B) :
    ‖rconv Γ₁ μ f φ x‖ ≤ B := by
  set H : (UPos n r → 𝔸[K]) → ℂ := fun s => rconv Γ₁ μ f φ (unipOne K n r s * x)
  have hHc : Continuous H :=
    (continuous_rconv Γ₁ μ f φ).comp ((continuous_unipOne r).mul continuous_const)
  have hper : ∀ ξ ∈ unipLattice K n r, ∀ s, H (ξ + s) = H s := by
    intro ξ hξ s
    simp only [H]
    rw [unipOne_add, mul_assoc, rconv_mul_left Γ₁ μ f φ (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : ∀ t, IntegrableOn (fun y => H (t + y)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    fun t => ((hHc.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hC).mono_set hDC
  have hmean : ∫ y in scaledUnipFD K n r M, H y ∂unipMeasure K n r = 0 := by
    rw [hD.setIntegral_eq isAddFundamentalDomain_unipFundamentalDomain fun ξ s => hper ξ ξ.2 s]
    exact integral_rconv_unip_eq_zero μ f hφ hr hrn x
  have h0 := norm_le_of_forall_altSum_le hD (unipMeasure_scaledUnipFD hM) k H hper hint hmean B hB
  simpa [H, unipOne_zero] using h0

theorem norm_rconv_le_of_altSum_inf (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} (hφ : φ ∈ cuspidalL2 μ) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    {M : ℕ} (hM : 0 < M) (x : normOneGL K n)
    (hfin : ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
      (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
        (z p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a) →
      ∀ w, f ((x⁻¹ * unipOne K n r z * x)⁻¹ * w) = f w)
    (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin k → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum k (fun s => rconv Γ₁ μ f φ (unipOne K n r (truncInf s) * x)) y 0‖ ≤ B) :
    ‖rconv Γ₁ μ f φ x‖ ≤ B := by
  refine norm_rconv_le_of_altSum μ f hφ hr hrn hM x k fun y hy => ?_
  have key : ∀ ε : Fin k → Bool,
      rconv Γ₁ μ f φ (unipOne K n r (0 + altPoint y ε) * x) =
        rconv Γ₁ μ f φ (unipOne K n r (truncInf (0 + altPoint y ε)) * x) := by
    intro ε
    rw [zero_add]
    have hfinP := hfin (truncFin (altPoint y ε)) (fun p => rfl) fun p => by
      obtain ⟨a, ha, hPa⟩ := exists_finite_altPoint_eq_natCast_mul hM y hy ε p
      exact ⟨a, ha, hPa⟩
    have hP : unipOne K n r (altPoint y ε) * x = unipOne K n r (truncInf (altPoint y ε)) * x *
        (x⁻¹ * unipOne K n r (truncFin (altPoint y ε)) * x) := by
      simp only [mul_assoc, mul_inv_cancel_left]
      rw [← mul_assoc, ← unipOne_add, truncInf_add_truncFin]
    rw [hP]
    exact rconv_mul_right μ f φ hfinP _
  have heq : altSum k (fun s => rconv Γ₁ μ f φ (unipOne K n r s * x)) y 0 =
      altSum k (fun s => rconv Γ₁ μ f φ (unipOne K n r (truncInf s) * x)) y 0 := by
    rw [altSum_eq_sum, altSum_eq_sum]
    exact Finset.sum_congr rfl fun ε _ => congrArg (altSign ε • ·) (key ε)
  rw [heq]
  exact hB y hy

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def ccTranslate (g : normOneGL K n) (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    CompactlySupportedContinuousMap (normOneGL K n) ℂ :=
  ⟨⟨fun w => f (g⁻¹ * w), f.continuous.comp (continuous_const_mul _)⟩,
    f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft g⁻¹)⟩

theorem rconv_mul_eq (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (x g : normOneGL K n) :
    rconv Γ₁ μ f φ (x * g) = rconv Γ₁ μ (ccTranslate g f) φ x := by
  unfold rconv
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  change f ((x * g)⁻¹ * z) * _ = f (g⁻¹ * (x⁻¹ * z)) * _
  rw [mul_inv_rev, mul_assoc]

theorem sum_altSign_rconv_eq (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (x : normOneGL K n) {k : ℕ}
    (C : (Fin k → Bool) → ArchUnits K n) :
    ∑ ε, (altSign ε : ℂ) * rconv Γ₁ μ f φ (x * archProj K n (C ε)) =
      rconv Γ₁ μ (fun w => ∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w)) φ x := by
  simp_rw [rconv_mul_eq μ f φ x]
  unfold rconv
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun ε _ => (integrable_rconv Γ₁ μ _ φ x).const_mul _]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [ccTranslate]
  change _ * (f ((archProj K n (C ε))⁻¹ * (x⁻¹ * z)) * _) = _
  ring

theorem enorm_sum_altSign_rconv_sq_le (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (x : normOneGL K n) {k : ℕ} {𝒞 : Set (ArchUnits K n)}
    (h𝒞 : IsCompact 𝒞) (C : (Fin k → Bool) → ArchUnits K n) (hC : ∀ ε, C ε ∈ 𝒞) {b : ℝ}
    (hb : ∀ w, ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w)‖ ≤ b) {m : ℕ}
    (hm : ∀ z : normOneGL K n, {γ : Γ₁ | γ • z ∈ (fun y => x * y) ''
      (archProj K n '' 𝒞 * tsupport (f : normOneGL K n → ℂ))}.encard ≤ m) :
    ‖∑ ε, (altSign ε : ℂ) * rconv Γ₁ μ f φ (x * archProj K n (C ε))‖ₑ ^ 2 ≤
      ENNReal.ofReal b ^ 2 * μ (archProj K n '' 𝒞 * tsupport (f : normOneGL K n → ℂ)) *
        (m * ‖φ‖ₑ ^ 2) := by
  set Q := archProj K n '' 𝒞 * tsupport (f : normOneGL K n → ℂ)
  have hQ : IsCompact Q := (h𝒞.image continuous_archProj).mul f.hasCompactSupport
  have hsupp : ∀ w ∉ Q, ∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w) = 0 := by
    intro w hw
    refine Finset.sum_eq_zero fun ε _ => ?_
    have : (archProj K n (C ε))⁻¹ * w ∉ tsupport (f : normOneGL K n → ℂ) := fun h' =>
      hw ⟨archProj K n (C ε), ⟨C ε, hC ε, rfl⟩, _, h', mul_inv_cancel_left _ _⟩
    rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
  set Ψ : CompactlySupportedContinuousMap (normOneGL K n) ℂ :=
    ⟨⟨fun w => ∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w),
      continuous_finsetSum _ fun ε _ => continuous_const.mul
        (f.continuous.comp (continuous_const_mul _))⟩, HasCompactSupport.intro hQ hsupp⟩
  rw [sum_altSign_rconv_eq μ f φ x C]
  have hS : MeasurableSet ((fun y => x * y) '' Q) := (hQ.image (continuous_const_mul x)).measurableSet
  have h1 := enorm_rconv_sq_le Γ₁ μ Ψ φ x hS (fun y hy => hsupp _ fun hq => hy ⟨_, hq, by simp⟩) hm
  refine h1.trans ?_
  gcongr
  calc ∫⁻ y, ‖Ψ y‖ₑ ^ 2 ∂μ = ∫⁻ y in Q, ‖Ψ y‖ₑ ^ 2 ∂μ := by
        rw [← lintegral_indicator hQ.measurableSet]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ Q
        · rw [indicator_of_mem hy]
        · rw [indicator_of_notMem hy]
          change ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * y)‖ₑ ^ 2 = 0
          rw [hsupp y hy]
          simp
    _ ≤ ∫⁻ _ in Q, ENNReal.ofReal b ^ 2 ∂μ := by
        refine setLIntegral_mono' hQ.measurableSet fun y _ => ?_
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hb y)
    _ = ENNReal.ofReal b ^ 2 * μ Q := by rw [setLIntegral_const]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section
open NumberField IsDedekindDomain Set Matrix
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem siegel_le_pow_mul {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) :
    ∀ (k : ℕ) (m l : Fin n), (l : ℕ) = m + k → ρ l ≤ (max 1 t⁻¹) ^ k * ρ m
  | 0, m, l, h => by
    have : l = m := Fin.ext (by simpa using h)
    simp [this]
  | k + 1, m, l, h => by
    have hp : (m : ℕ) + k < n := by omega
    set p : Fin n := ⟨m + k, hp⟩
    have h1 : ρ l ≤ max 1 t⁻¹ * ρ p := by
      have := hs p l (by simp only [p]; omega)
      calc ρ l = t⁻¹ * (t * ρ l) := by field_simp
        _ ≤ t⁻¹ * ρ p := mul_le_mul_of_nonneg_left this (inv_nonneg.2 ht.le)
        _ ≤ max 1 t⁻¹ * ρ p := mul_le_mul_of_nonneg_right (le_max_right _ _) (hρ p).le
    have h2 := siegel_le_pow_mul ht hρ hs k m p rfl
    calc ρ l ≤ max 1 t⁻¹ * ρ p := h1
      _ ≤ max 1 t⁻¹ * ((max 1 t⁻¹) ^ k * ρ m) :=
          mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one (le_max_left _ _))
      _ = (max 1 t⁻¹) ^ (k + 1) * ρ m := by ring

theorem siegel_div_le_mul {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) {R : ℝ} (hR1 : 1 ≤ R)
    (hR : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) (l m : Fin n) :
    ρ l / ρ m ≤ (max 1 t⁻¹) ^ n * R := by
  have hc : 1 ≤ (max 1 t⁻¹) ^ n := one_le_pow₀ (le_max_left _ _)
  rcases lt_trichotomy l m with h | h | h
  · calc ρ l / ρ m ≤ R := hR l m h
      _ ≤ (max 1 t⁻¹) ^ n * R := le_mul_of_one_le_left (by linarith) hc
  · subst h
    rw [div_self (hρ l).ne']
    nlinarith
  · have hlm : (m : ℕ) < l := h
    have := siegel_le_pow_mul ht hρ hs ((l : ℕ) - m) m l (by omega)
    rw [div_le_iff₀ (hρ m)]
    calc ρ l ≤ (max 1 t⁻¹) ^ ((l : ℕ) - m) * ρ m := this
      _ ≤ (max 1 t⁻¹) ^ n * ρ m := by
          have := l.isLt
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) (by omega))
            (hρ m).le
      _ ≤ (max 1 t⁻¹) ^ n * R * ρ m :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hR1) (hρ m).le

theorem exists_norm_infAt_entry_le {S : Set (AdelicGLn.AdelicGL K n)} (hS : IsCompact S) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ g ∈ S, ∀ w : InfinitePlace K, ∀ i j : Fin n,
      ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤ β := by
  have hc : Continuous fun g : AdelicGLn.AdelicGL K n =>
      ∑ w : InfinitePlace K, ∑ i : Fin n, ∑ j : Fin n,
        ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i j‖ := by
    refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => ?_
    exact (((continuous_apply j).comp (continuous_apply i)).comp
      (Units.continuous_val.comp (continuous_infAt w))).norm
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun g hg w i j => ?_⟩
  have h1 := hC g hg
  rw [Real.norm_of_nonneg (by positivity)] at h1
  refine le_trans ?_ (h1.trans (le_max_left _ _))
  calc ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i j‖
      ≤ ∑ j' : Fin n, ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i j'‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin n, ∑ j' : Fin n, ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j' : Fin n,
          ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ w' : InfinitePlace K, ∑ i' : Fin n, ∑ j' : Fin n,
          ‖(infAt w' g : Matrix (Fin n) (Fin n) w'.Completion) i' j'‖ :=
        Finset.single_le_sum (f := fun w' : InfinitePlace K => ∑ i' : Fin n, ∑ j' : Fin n,
          ‖(infAt w' g : Matrix (Fin n) (Fin n) w'.Completion) i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (Finset.mem_univ w)

theorem norm_infAt_conj_le (w : InfinitePlace K) (b q : AdelicGLn.AdelicGL K n) (ρ : Fin n → ℝ)
    (hρ : ∀ i, 0 < ρ i) {β₁ β₂ β₃ L : ℝ}
    (h1 : ∀ i j, ‖(infAt w b : Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤ β₁)
    (h2 : ∀ i j, ‖(infAt w q : Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤ β₂)
    (h3 : ∀ i j, ‖(((infAt w b)⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion)
      i j‖ ≤ β₃)
    (hL : ∀ l m, ρ l / ρ m ≤ L) (hβ₁ : 0 ≤ β₁) (i j : Fin n) :
    ‖(infAt w (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * q *
      (diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)))⁻¹ * b⁻¹) :
        Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤ (n : ℝ) ^ 2 * (β₁ * (L * β₂) * β₃) := by
  set d : Fin n → w.Completion := fun l =>
    ((GroundTheory.Global.posRealToUnits w ⟨ρ l ^ w.mult, pow_pos (hρ l) _⟩ : (w.Completion)ˣ) :
      w.Completion) with hd_def
  set d' : Fin n → w.Completion := fun l =>
    (((GroundTheory.Global.posRealToUnits w ⟨ρ l ^ w.mult, pow_pos (hρ l) _⟩)⁻¹ : (w.Completion)ˣ) :
      w.Completion) with hd'_def
  have hd : ∀ l, ‖d l‖ = ρ l := fun l => norm_posRealToUnits w (hρ l)
  have hd' : ∀ l, ‖d' l‖ = (ρ l)⁻¹ := fun l => by
    simp only [d', Units.val_inv_eq_inv_val, norm_inv]
    rw [norm_posRealToUnits w (hρ l)]
  set B := (infAt w b : Matrix (Fin n) (Fin n) w.Completion)
  set B' := (((infAt w b)⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion)
  set Qm := (infAt w q : Matrix (Fin n) (Fin n) w.Completion)
  have hmat : (infAt w (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * q *
      (diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)))⁻¹ * b⁻¹) :
        Matrix (Fin n) (Fin n) w.Completion) = B * (diagonal d * Qm * diagonal d') * B' := by
    rw [infAt_mul, infAt_mul, infAt_mul, infAt_mul, infAt_inv w (diagUnits n _), infAt_inv w b,
      infAt_diagUnits_posIdele, ← map_inv (diagUnits n)]
    simp only [Units.val_mul, coe_diagUnits, Pi.inv_apply, mul_assoc]
    rfl
  have hE : ∀ l m, (diagonal d * Qm * diagonal d') l m = d l * Qm l m * d' m := by
    intro l m
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hEn : ∀ l m, ‖(diagonal d * Qm * diagonal d') l m‖ ≤ L * β₂ := by
    intro l m
    rw [hE, norm_mul, norm_mul, hd, hd']
    calc ρ l * ‖Qm l m‖ * (ρ m)⁻¹ = ρ l / ρ m * ‖Qm l m‖ := by ring
      _ ≤ L * β₂ := mul_le_mul (hL l m) (h2 l m) (norm_nonneg _)
          ((div_pos (hρ l) (hρ m)).le.trans (hL l m))
  rw [hmat, Matrix.mul_apply]
  calc ‖∑ m, (B * (diagonal d * Qm * diagonal d')) i m * B' m j‖
      ≤ ∑ m : Fin n, ∑ l : Fin n, β₁ * (L * β₂) * β₃ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        rw [norm_mul, Matrix.mul_apply]
        have hterm : ∀ l, ‖B i l * (diagonal d * Qm * diagonal d') l m‖ ≤ β₁ * (L * β₂) := by
          intro l
          rw [norm_mul]
          exact mul_le_mul (h1 i l) (hEn l m) (norm_nonneg _) hβ₁
        have hnn : ∀ l, 0 ≤ β₁ * (L * β₂) := fun l => (norm_nonneg _).trans (hterm l)
        calc ‖∑ l, B i l * (diagonal d * Qm * diagonal d') l m‖ * ‖B' m j‖
            ≤ (∑ l : Fin n, β₁ * (L * β₂)) * β₃ :=
              mul_le_mul ((norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hterm l)) (h3 m j)
                (norm_nonneg _) (Finset.sum_nonneg fun l _ => hnn l)
          _ = ∑ l : Fin n, β₁ * (L * β₂) * β₃ := Finset.sum_mul _ _ _
    _ = (n : ℝ) ^ 2 * (β₁ * (L * β₂) * β₃) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem exists_encard_le_siegel {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω) {t : ℝ}
    (ht : 0 < t) {Q : Set (normOneGL K n)} (hQ : IsCompact Q) :
    ∃ (C : ℝ) (N : ℕ), ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ x : normOneGL K n,
      (x : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * k →
      ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) →
      ∃ m : ℕ, (m : ℝ) ≤ C * R ^ N ∧ ∀ z : normOneGL K n,
        {γ : rationalGLOne K n | γ • z ∈ (fun y => x * y) '' Q}.encard ≤ m := by
  classical
  set Q' : Set (AdelicGLn.AdelicGL K n) :=
    (fun p : AdelicGLn.AdelicGL K n × normOneGL K n × normOneGL K n =>
      p.1 * (p.2.1 : AdelicGLn.AdelicGL K n) * (p.2.2 : AdelicGLn.AdelicGL K n)⁻¹ * p.1⁻¹) ''
      (((maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)) ×ˢ
        (Q ×ˢ Q)) with hQ'_def
  have hQ' : IsCompact Q' := by
    refine (isCompact_maxCompact.prod (hQ.prod hQ)).image ?_
    exact (((continuous_fst.mul (continuous_subtype_val.comp (continuous_fst.comp
      continuous_snd))).mul (continuous_subtype_val.comp (continuous_snd.comp
        continuous_snd)).inv).mul continuous_fst.inv)
  set 𝒦 : Set (FiniteAdeleRing (𝓞 K) K) := ⋃ i : Fin n, ⋃ j : Fin n,
    (fun p : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ((AdelicGLn.prodEquiv K n (p.1 * p.2 * p.1⁻¹)).2 :
        Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) i j) '' (ω ×ˢ Q') with h𝒦_def
  have h𝒦 : IsCompact 𝒦 := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => (hω.prod hQ').image ?_
    exact ((continuous_apply j).comp (continuous_apply i)).comp (Units.continuous_val.comp
      (continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp
        ((continuous_fst.mul continuous_snd).mul continuous_fst.inv))))
  obtain ⟨C₀, N, hC₀⟩ := exists_ncard_ratGLBox_le n h𝒦
  obtain ⟨β₁, hβ₁0, hβ₁⟩ := exists_norm_infAt_entry_le hω
  obtain ⟨β₂, hβ₂0, hβ₂⟩ := exists_norm_infAt_entry_le hQ'
  obtain ⟨β₃, hβ₃0, hβ₃⟩ := exists_norm_infAt_entry_le (hω.image continuous_inv)
  set c := (max 1 t⁻¹) ^ n
  have hc0 : 0 ≤ c := by positivity
  set A := (n : ℝ) ^ 2 * (β₁ * (c * β₂) * β₃)
  have hA : 0 ≤ A := by positivity
  refine ⟨max C₀ 0 * (1 + A) ^ N, N, ?_⟩
  intro b hb ρ hρ hs k hk x hx R hR1 hR
  set a := diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) with ha_def
  set Y : Set (GL (Fin n) K) :=
    {γ | ∃ q ∈ Q', AdelicGLn.diagonal K n γ = b * a * q * a⁻¹ * b⁻¹} with hY_def
  have hT : 0 ≤ A * R := mul_nonneg hA (by linarith)
  have hYbox : Y ⊆ ratGLBox n 𝒦 (A * R) := by
    rintro γ ⟨q, hq, hγ⟩ i j
    refine ⟨?_, fun w => ?_⟩
    · have e1 : algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) =
          (((b * a * q * a⁻¹ * b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) i j).2 := by
        rw [← hγ, AdelicGLn.diagonal_apply]
        rfl
      have e2 : (((b * a * q * a⁻¹ * b⁻¹ : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K]) i j).2 =
          ((AdelicGLn.prodEquiv K n (b * q * b⁻¹)).2 :
            Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) i j := by
        rw [← AdelicGLn.prodEquiv_apply_snd]
        simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, ha_def,
          prodEquiv_diagUnits_posIdele_snd, mul_one, inv_one]
      rw [e1, e2]
      exact mem_iUnion₂.2 ⟨i, j, (b, q), ⟨hb, hq⟩, rfl⟩
    · have e1 : w ((γ : Matrix (Fin n) (Fin n) K) i j) =
          ‖(infAt w (b * a * q * a⁻¹ * b⁻¹) : Matrix (Fin n) (Fin n) w.Completion) i j‖ := by
        rw [infAt_apply, ← hγ, AdelicGLn.diagonal_apply, ← GroundTheory.Global.norm_algebraMap_apply]
        rfl
      rw [e1]
      have hL : ∀ l m, ρ l / ρ m ≤ c * R := siegel_div_le_mul ht hρ hs hR1 hR
      have h3 : ∀ i j, ‖(((infAt w b)⁻¹ : GL (Fin n) w.Completion) :
          Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤ β₃ := fun i j => by
        rw [← infAt_inv]
        exact hβ₃ _ ⟨b, hb, rfl⟩ w i j
      calc ‖(infAt w (b * a * q * a⁻¹ * b⁻¹) : Matrix (Fin n) (Fin n) w.Completion) i j‖
          ≤ (n : ℝ) ^ 2 * (β₁ * (c * R * β₂) * β₃) :=
            norm_infAt_conj_le w b q ρ hρ (hβ₁ b hb w) (hβ₂ q hq w) h3 hL hβ₁0 i j
        _ = A * R := by simp only [A]; ring
  obtain ⟨hfin, hcard⟩ := hC₀ (A * R) hT
  have hYfin : Y.Finite := hfin.subset hYbox
  refine ⟨Y.ncard, ?_, fun z => ?_⟩
  · calc (Y.ncard : ℝ) ≤ ((ratGLBox n 𝒦 (A * R)).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hYbox hfin
      _ ≤ C₀ * (1 + A * R) ^ N := hcard
      _ ≤ max C₀ 0 * ((1 + A) * R) ^ N := by
          gcongr
          · exact le_max_left _ _
          · nlinarith
      _ = max C₀ 0 * (1 + A) ^ N * R ^ N := by rw [mul_pow]; ring
  · set S := {γ : rationalGLOne K n | γ • z ∈ (fun y => x * y) '' Q}
    rcases eq_empty_or_nonempty S with h | ⟨γ₀, hγ₀⟩
    · rw [h, encard_empty]
      simp
    have hrat : ∀ δ : rationalGLOne K n, ∃ γ : GL (Fin n) K,
        AdelicGLn.diagonal K n γ = ((δ : normOneGL K n) : AdelicGLn.AdelicGL K n) := fun δ =>
      Subgroup.mem_subgroupOf.1 δ.2
    set f : rationalGLOne K n → GL (Fin n) K := fun δ => Function.invFun (AdelicGLn.diagonal K n)
      (((δ * γ₀⁻¹ : rationalGLOne K n) : normOneGL K n) : AdelicGLn.AdelicGL K n)
    have hf : ∀ δ, AdelicGLn.diagonal K n (f δ) =
        (((δ * γ₀⁻¹ : rationalGLOne K n) : normOneGL K n) : AdelicGLn.AdelicGL K n) := fun δ =>
      Function.invFun_eq (hrat _)
    have hmaps : MapsTo f S Y := by
      intro δ hδ
      obtain ⟨q₁, hq₁, h₁⟩ := hδ
      obtain ⟨q₂, hq₂, h₂⟩ := hγ₀
      have e : ((δ * γ₀⁻¹ : rationalGLOne K n) : normOneGL K n) = x * q₁ * q₂⁻¹ * x⁻¹ := by
        have h₁'' : x * q₁ = (δ : normOneGL K n) * z := h₁
        have h₂'' : x * q₂ = (γ₀ : normOneGL K n) * z := h₂
        have h₁' : (δ : normOneGL K n) = x * q₁ * z⁻¹ := by rw [h₁'', mul_inv_cancel_right]
        have h₂' : (γ₀ : normOneGL K n) = x * q₂ * z⁻¹ := by rw [h₂'', mul_inv_cancel_right]
        rw [Subgroup.coe_mul, Subgroup.coe_inv, h₁', h₂']
        group
      refine ⟨k * (q₁ : AdelicGLn.AdelicGL K n) * (q₂ : AdelicGLn.AdelicGL K n)⁻¹ * k⁻¹,
        ⟨(k, q₁, q₂), ⟨hk, hq₁, hq₂⟩, rfl⟩, ?_⟩
      rw [hf, e]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx]
      group
    have hinj : InjOn f S := by
      intro δ₁ _ δ₂ _ h
      have := congrArg (AdelicGLn.diagonal K n) h
      rw [hf, hf] at this
      exact mul_right_cancel (Subtype.ext (Subtype.ext this))
    calc S.encard ≤ Y.encard := encard_le_encard_of_injOn hmaps hinj
      _ = Y.ncard := hYfin.cast_ncard_eq.symm

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

theorem exists_archProj_eq {g : normOneGL K n} (hg : (AdelicGLn.prodEquiv K n g).2 = 1) :
    ∃ C : ArchUnits K n, archProj K n C = g ∧
      (C : ArchMatrix K n) = archMat K n ((g : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) := by
  set h := (AdelicGLn.prodEquiv K n g).1
  set C : ArchUnits K n := ((archEquiv K n h : archGroup K n) : ArchUnits K n)
  have hincl : archIncl K n C = g := by
    have h1 := infEmb_mul_finEmb (K := K) (n := n) g
    rw [hg, map_one, mul_one] at h1
    exact h1
  refine ⟨C, ?_, ?_⟩
  · rw [archProj_of_mem (hincl ▸ g.2)]
    exact Subtype.ext hincl
  · rfl

theorem prodEquiv_conj_snd {r : ℕ} (x : AdelicGLn.AdelicGL K n) (P : UPos n r → 𝔸[K])
    (hP : ∀ p, (P p).2 = 0) : (AdelicGLn.prodEquiv K n (x⁻¹ * unipGL P * x)).2 = 1 := by
  rw [map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, prodEquiv_unipGL_snd]
  have : (fun p => (P p).2) = 0 := funext hP
  rw [this, unipGL_zero, mul_one, inv_mul_cancel]

theorem coe_conj_unipGL {r : ℕ} (x : AdelicGLn.AdelicGL K n) (P : UPos n r → 𝔸[K]) :
    ((x⁻¹ * unipGL P * x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      1 + ((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
        (x : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  rw [Units.val_mul, Units.val_mul, coe_unipGL, unipMatrix, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Units.inv_mul]

variable (K n) in

def conjArch {r : ℕ} (x : AdelicGLn.AdelicGL K n) : (UPos n r → 𝔸[K]) →+ ArchMatrix K n where
  toFun P := archMat K n (((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
    blockEntry P * (x : Matrix (Fin n) (Fin n) 𝔸[K]))
  map_zero' := by simp [blockEntry_zero]
  map_add' P Q := by simp [blockEntry_add, Matrix.mul_add, Matrix.add_mul]

theorem conjArch_mul_conjArch {r : ℕ} (x : AdelicGLn.AdelicGL K n) (P Q : UPos n r → 𝔸[K]) :
    conjArch K n x P * conjArch K n x Q = 0 := by
  change archMat K n _ * archMat K n _ = 0
  rw [← map_mul]
  have : ((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
      (x : Matrix (Fin n) (Fin n) 𝔸[K]) * (((x⁻¹ : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry Q * (x : Matrix (Fin n) (Fin n) 𝔸[K])) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x : Matrix (Fin n) (Fin n) 𝔸[K]), Units.mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (blockEntry P), blockEntry_mul_blockEntry, Matrix.zero_mul,
      Matrix.mul_zero]
  rw [this, map_zero]

theorem exists_archProj_eq_conj {r : ℕ} (x : normOneGL K n) (P : UPos n r → 𝔸[K])
    (hP : ∀ p, (P p).2 = 0) :
    ∃ C : ArchUnits K n, archProj K n C = x⁻¹ * unipOne K n r P * x ∧
      (C : ArchMatrix K n) = 1 + conjArch K n (x : AdelicGLn.AdelicGL K n) P := by
  obtain ⟨C, hC1, hC2⟩ := exists_archProj_eq (g := x⁻¹ * unipOne K n r P * x)
    (prodEquiv_conj_snd (x : AdelicGLn.AdelicGL K n) P hP)
  refine ⟨C, hC1, ?_⟩
  rw [hC2]
  have h1 : ((x⁻¹ * unipOne K n r P * x : normOneGL K n) : AdelicGLn.AdelicGL K n) =
      (x : AdelicGLn.AdelicGL K n)⁻¹ * unipGL P * (x : AdelicGLn.AdelicGL K n) := rfl
  rw [h1, coe_conj_unipGL, map_add, map_one]
  rfl

theorem map_altPoint {V W : Type*} [AddCommGroup V] [AddCommGroup W] (φ : V →+ W) {k : ℕ}
    (y : Fin k → V) (ε : Fin k → Bool) : φ (altPoint y ε) = altPoint (fun i => φ (y i)) ε := by
  unfold altPoint
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

variable (n) in

def truncInfHom (r : ℕ) : (UPos n r → 𝔸[K]) →+ (UPos n r → 𝔸[K]) where
  toFun := truncInf
  map_zero' := rfl
  map_add' _ _ := funext fun _ => Prod.ext rfl (add_zero (0 : FiniteAdeleRing (𝓞 K) K)).symm

@[simp] theorem truncInfHom_apply {r : ℕ} (s : UPos n r → 𝔸[K]) : truncInfHom n r s = truncInf s :=
  rfl

theorem encard_le_of_subset_biUnion {α ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → Set α)
    {m : ℕ} (hm : ∀ i ∈ s, (A i).encard ≤ m) {B : Set α} (hB : B ⊆ ⋃ i ∈ s, A i) :
    B.encard ≤ s.card * m := by
  induction s using Finset.induction_on generalizing B with
  | empty =>
    have : B = ∅ := Set.subset_empty_iff.1 (by simpa using hB)
    simp [this]
  | insert a s ha ih =>
    have hB' : B ⊆ A a ∪ ⋃ i ∈ s, A i := by
      intro z hz
      obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.1 (hB hz)
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Or.inl hz
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, hz⟩)
    calc B.encard ≤ (A a ∪ ⋃ i ∈ s, A i).encard := Set.encard_le_encard hB'
      _ ≤ (A a).encard + (⋃ i ∈ s, A i).encard := Set.encard_union_le _ _
      _ ≤ m + s.card * m := add_le_add (hm a (Finset.mem_insert_self _ _))
          (ih (fun i hi => hm i (Finset.mem_insert_of_mem hi)) subset_rfl)
      _ = (insert a s).card * m := by
          rw [Finset.card_insert_of_notMem ha]
          push_cast
          ring

theorem encard_le_of_subset_mul {x : normOneGL K n} {Q V : Set (normOneGL K n)}
    (s : Finset (normOneGL K n)) (hQ : Q ⊆ ⋃ g ∈ s, (fun y => y * g) '' V) {m : ℕ}
    (hm : ∀ z : normOneGL K n, {γ : Γ₁ | γ • z ∈ (fun y => x * y) '' V}.encard ≤ m)
    (z : normOneGL K n) :
    {γ : Γ₁ | γ • z ∈ (fun y => x * y) '' Q}.encard ≤ s.card * m := by
  classical
  refine encard_le_of_subset_biUnion s (fun g => {γ : Γ₁ | γ • (z * g⁻¹) ∈ (fun y => x * y) '' V})
    (fun g _ => hm _) fun γ hγ => ?_
  obtain ⟨q, hq, hqz⟩ := hγ
  obtain ⟨g, hg, hqg⟩ := Set.mem_iUnion₂.1 (hQ hq)
  obtain ⟨v, hv, rfl⟩ := hqg
  refine Set.mem_iUnion₂.2 ⟨g, hg, v, hv, ?_⟩
  change x * v = γ • (z * g⁻¹)
  rw [Subgroup.smul_def, smul_eq_mul] at hqz ⊢
  rw [← mul_assoc, ← hqz, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (ArchUnits K n))
  [ν.IsHaarMeasure]

theorem exists_norm_rconv_le_siegel {β : ArchMatrix K n → ℝ}
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)))
    {t : ℝ} (ht : 0 < t) {r : ℕ} (hr : 0 < r) (hrn : r < n) :
    ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ φ ∈ cuspidalL2 μ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ x : normOneGL K n,
      (x : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk →
      ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) →
      ‖rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) φ x‖ ≤
        C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) ^ k * √(R ^ N) * ‖φ‖ := by
  obtain ⟨V₀, hV₀c, hV₀⟩ := exists_compact_mem_nhds (1 : normOneGL K n)
  obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hω ht hV₀c
  refine ⟨N, fun k => ?_⟩
  set h := finAvg U hU g
  set f := archConv ν hβ.continuous hβc hβu h
  obtain ⟨M, hM, hMconj⟩ := exists_natCast_conj_unipGL_mem U hU hω r
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr hrn
    (isCompact_scaledInfSet (K := K) M)
  set C₁' := max C₁ 0
  set R₁ := C₁' * t⁻¹
  obtain ⟨c, hc⟩ := exists_norm_sum_altSign_archConvFun_le ν hβ hβc hβu h k R₁
  set c' := max c 0
  have h𝒞 := isCompact_unipBall (K := K) (n := n) (k * R₁)
  set Q := archProj K n '' unipBall (K := K) (n := n) (k * R₁) * tsupport (f : normOneGL K n → ℂ)
  have hQ : IsCompact Q := (h𝒞.image continuous_archProj).mul f.hasCompactSupport
  obtain ⟨s, -, hs⟩ := hQ.elim_nhds_subcover (fun g => (fun y => y * g) '' V₀) fun g _ => by
    have := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds hV₀
    simpa using this
  refine ⟨c' * C₁' ^ k * √(μ.real Q * (s.card * max Cc 0)), ?_⟩
  intro φ hφ b hb ρ hρ hsieg kk hkk x hx R hR1 hR
  obtain ⟨m₀, hmC₀, hm₀⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = s.card * m₀ := ⟨_, rfl⟩
  have hm : ∀ z : normOneGL K n, {γ : Γ₁ | γ • z ∈ (fun y => x * y) '' Q}.encard ≤ m := by
    intro z
    have := encard_le_of_subset_mul s hs hm₀ z
    rw [hmdef]
    exact_mod_cast this
  have hmC : (m : ℝ) ≤ s.card * Cc * R ^ N := by
    rw [hmdef, Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC₀ (Nat.cast_nonneg _)
  set gain := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hgain0 : 0 ≤ gain := div_nonneg (hρ _).le (hρ _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨r - 1, by omega⟩ ⟨r, hrn⟩ (by simp; omega)
    rw [div_le_iff₀ (hρ _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  set b₀ := c' * (C₁' * gain) ^ k
  have hb₀ : 0 ≤ b₀ := mul_nonneg hc'0 (pow_nonneg (mul_nonneg hC₁'0 hgain0) _)
  have hfinal : ‖rconv Γ₁ μ f φ x‖ ≤ b₀ * √(μ.real Q * m) * ‖φ‖ := by
    refine norm_rconv_le_of_altSum_inf μ f hφ hr hrn hM x ?_ k ?_
    · intro z hz1 hz2 w
      obtain ⟨u, hu⟩ := hMconj b hb ρ hρ kk hkk z hz1 hz2
      have hxu : x⁻¹ * unipOne K n r z * x = finOne K n (u : AdelicGLn.integralFiniteGL K n) := by
        refine Subtype.ext ?_
        change (x : AdelicGLn.AdelicGL K n)⁻¹ * unipGL z * (x : AdelicGLn.AdelicGL K n) =
          finEmb K n _
        rw [hx]
        exact hu
      rw [hxu, ← map_inv, ← Subgroup.coe_inv]
      exact archConvFun_finOne_mul ν h _ (fun y => finAvgFun_finOne_mul U hU g u⁻¹ y) w
    · intro y hy
      set Y : Fin k → ArchMatrix K n :=
        fun i => conjArch K n (x : AdelicGLn.AdelicGL K n) (truncInf (y i))
      have hYY : ∀ i j, Y i * Y j = 0 := fun i j => conjArch_mul_conjArch _ _ _
      have hYn : ∀ i, ‖Y i‖ ≤ C₁' * gain := by
        intro i
        have h1 := hC₁ b hb ρ hρ hsieg kk hkk (truncInf (y i)) (fun p => rfl)
          (fun p => infinite_mem_scaledInfSet hM (hy i) p)
        have h2 : Y i = archMat K n ((((b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) *
            kk)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
            blockEntry (truncInf (y i)) * ((b * diagUnits n (fun i => posIdele (K := K) (ρ i)
              (hρ i)) * kk : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
          simp only [Y, conjArch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hx]
        rw [h2]
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0)
      have hYR : ∀ i, ‖Y i‖ ≤ R₁ := fun i =>
        (hYn i).trans (mul_le_mul_of_nonneg_left hgain hC₁'0)
      have hex : ∀ ε : Fin k → Bool, ∃ C : ArchUnits K n,
          archProj K n C = x⁻¹ * unipOne K n r (truncInf (altPoint y ε)) * x ∧
            (C : ArchMatrix K n) = 1 + altPoint Y ε := by
        intro ε
        obtain ⟨C, hC1, hC2⟩ := exists_archProj_eq_conj x (truncInf (altPoint y ε)) fun p => rfl
        refine ⟨C, hC1, ?_⟩
        rw [hC2, ← truncInfHom_apply, map_altPoint (truncInfHom n r),
          map_altPoint (conjArch K n (x : AdelicGLn.AdelicGL K n))]
        rfl
      choose Cε hCε1 hCε2 using hex
      have hsum : altSum k (fun s => rconv Γ₁ μ f φ (unipOne K n r (truncInf s) * x)) y 0 =
          ∑ ε, (altSign ε : ℂ) * rconv Γ₁ μ f φ (x * archProj K n (Cε ε)) := by
        rw [altSum_eq_sum]
        refine Finset.sum_congr rfl fun ε _ => ?_
        rw [zero_add, hCε1 ε, zsmul_eq_mul]
        have : x * (x⁻¹ * unipOne K n r (truncInf (altPoint y ε)) * x) =
            unipOne K n r (truncInf (altPoint y ε)) * x := by group
        rw [this]
      rw [hsum]
      have hb' : ∀ w, ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (Cε ε))⁻¹ * w)‖ ≤ b₀ := by
        intro w
        refine (hc Y hYY hYR Cε hCε2 w).trans ?_
        have hprod : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ k := by
          rw [← Fin.prod_const]
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i
        calc c * ∏ i, ‖Y i‖ ≤ c' * ∏ i, ‖Y i‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Finset.prod_nonneg fun i _ => norm_nonneg _)
          _ ≤ b₀ := mul_le_mul_of_nonneg_left hprod hc'0
      have hmem : ∀ ε, Cε ε ∈ unipBall (K := K) (n := n) (k * R₁) := fun ε =>
        mem_unipBall_of_val_eq hYY hYR (hCε2 ε)
      have hsq := enorm_sum_altSign_rconv_sq_le μ f φ x h𝒞 Cε hmem hb' hm
      have hA : ENNReal.ofReal b₀ ^ 2 * μ Q * (m : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hQ.measure_lt_top.ne) (by simp)
      have hle := norm_le_of_enorm_sq_le hA (by rw [mul_assoc]; exact hsq)
      refine hle.trans (le_of_eq ?_)
      congr 1
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hb₀,
        ENNReal.toReal_natCast, Real.sqrt_mul (by positivity), Real.sqrt_mul' _ (by positivity),
        Real.sqrt_sq hb₀, measureReal_def, mul_assoc, Real.sqrt_mul ENNReal.toReal_nonneg]
  refine hfinal.trans ?_
  have hμQ : 0 ≤ μ.real Q := measureReal_nonneg
  have hm' : (m : ℝ) ≤ s.card * max Cc 0 * R ^ N :=
    hmC.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (Nat.cast_nonneg _)) (pow_nonneg (by linarith) _))
  have hsqrt : √(μ.real Q * m) ≤ √(μ.real Q * (s.card * max Cc 0)) * √(R ^ N) := by
    rw [← Real.sqrt_mul (mul_nonneg hμQ (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hm' hμQ
  calc b₀ * √(μ.real Q * m) * ‖φ‖
      ≤ b₀ * (√(μ.real Q * (s.card * max Cc 0)) * √(R ^ N)) * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hb₀) (norm_nonneg _)
    _ = c' * C₁' ^ k * √(μ.real Q * (s.card * max Cc 0)) * gain ^ k * √(R ^ N) * ‖φ‖ := by
        simp only [b₀, mul_pow]
        ring

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end
