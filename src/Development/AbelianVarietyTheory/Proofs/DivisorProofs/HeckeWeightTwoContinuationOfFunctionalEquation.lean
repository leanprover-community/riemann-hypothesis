import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyMulLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
import ReciprocityTheory.Chebotarev.EulerSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinNonconstantFourierSumSmoothHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationEqLatticeSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIsBigORpowLipschitzProductKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyFractionalIdealRealLatticeImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHilbertEisensteinWeightTwoSeries

section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add : ∀ (F : Type) [Field F] [NumberField F] (P Q : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood Q → GlobalTheory.HeckeTwo.IsGood (fun σ z => P σ z + Q σ z) := by
  first | exact @GlobalTheory.HeckeTwo.isGood_add | exact GlobalTheory.HeckeTwo.isGood_add | (intros; apply GlobalTheory.HeckeTwo.isGood_add <;> assumption)
end

section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_mul_left : ∀ (F : Type) [Field F] [NumberField F] (k : ℂ → ℂ) (P : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), DifferentiableOn ℂ k GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood (fun σ z => k σ * P σ z) := by
  first | exact @GlobalTheory.HeckeTwoMul.isGood_mul | exact GlobalTheory.HeckeTwoMul.isGood_mul | (intros; apply GlobalTheory.HeckeTwoMul.isGood_mul <;> assumption)
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem wirt_const_fun {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (d : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirt τ bar (fun _ : Φ → ℂ => d) = fun _ => 0 := by
  funext z
  simp [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirt]

theorem wirtWord_const_fun {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (d : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord ws (fun _ : Φ → ℂ => d) = fun _ => if ws = [] then d else 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord_cons, ih]
    simp only [reduceCtorEq, if_false]
    exact wirt_const_fun w.1 w.2 _

theorem isGood_const (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ)
    (ha : DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane) :
    GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) := by
  refine ⟨fun σ _ => contDiffOn_const, fun w z _ => ?_⟩
  simp only [wirtWord_const_fun]
  split_ifs
  · exact ha
  · exact differentiableOn_const 0

theorem goodConst : ∀ (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ), DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) :=
  fun F _ _ a ha => isGood_const F a ha

end GlobalTheory.HeckeTwo
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_of_sigma_only : ∀ (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ), DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) := by
  atlas_forward_decl GlobalTheory.HeckeTwo.goodConst
end

section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisensteinConstantTermPart_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (GlobalTheory.HeckeTwo.aPart 𝔞) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.aPart_differentiableOn | exact GlobalTheory.HeckeTwo.aPart_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.aPart_differentiableOn <;> assumption)
end

section
section
open NumberField Complex Filter Topology
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.ZetaPole

theorem tendsto_pow_mul (F : Type) [Field F] [NumberField F] (C C' : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ)
    (hZ' : IsPartialZeta C' Z')
    (hfe : ∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) →
      (dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s =
        (dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)) :
    ∃ L : ℂ, Tendsto (fun s => (s - 1) ^ Module.finrank ℚ F * Z s) (𝓝[≠] 1) (𝓝 L) := by
  set f := Module.finrank ℚ F
  set d : ℂ := (dF F : ℂ)
  have hd0 : d ≠ 0 := by
    simp only [d, dF, ne_eq, ofReal_eq_zero, abs_eq_zero, Int.cast_eq_zero]
    exact discr_ne_zero F
  have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) ^ f * Z s =
      (d ^ ((1 - s) / 2) / d ^ (s / 2)) * ((Complex.Gammaℝ s)⁻¹) ^ f *
        (-((1 - s) * Complex.Gammaℝ (1 - s))) ^ f * Z' (1 - s) := by
    have hb : Metric.ball (1 : ℂ) 1 ∈ 𝓝[≠] (1 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [hb, self_mem_nhdsWithin] with s hs hs1
    have hs1' : s ≠ 1 := hs1
    rw [Metric.mem_ball, dist_eq] at hs
    have hre : 0 < s.re := by
      have := abs_re_le_norm (s - 1)
      rw [sub_re, one_re] at this
      linarith [abs_le.mp (this.trans hs.le) |>.1, neg_abs_le (s.re - 1)]
    have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
    have h1 : ∀ n : ℕ, s ≠ -2 * n := by
      intro n h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h2 : ∀ n : ℕ, 1 - s ≠ -2 * n := by
      intro n h
      have hs' : s - 1 = 2 * n := by linear_combination -h
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hs1' (by simpa [sub_eq_zero] using hs')
      · rw [hs'] at hs
        have : ‖(2 * n : ℂ)‖ = 2 * n := by
          rw [show (2 * n : ℂ) = ((2 * n : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
        rw [this] at hs
        have : (1:ℝ) ≤ n := by exact_mod_cast hn
        linarith
    have e := hfe s h1 h2
    have hds : d ^ (s / 2) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; tauto
    have hZs : Z s = d ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ f * Z' (1 - s) /
        (d ^ (s / 2) * Complex.Gammaℝ s ^ f) := by
      rw [eq_div_iff (mul_ne_zero hds (pow_ne_zero _ hΓ)), ← e]; ring
    rw [hZs, show -((1 - s) * Complex.Gammaℝ (1 - s)) = (s - 1) * Complex.Gammaℝ (1 - s) by ring, mul_pow,
      inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  refine ⟨(d ^ (((1:ℂ) - 1) / 2) / d ^ ((1:ℂ) / 2)) * ((Complex.Gammaℝ 1)⁻¹) ^ f * (-2) ^ f * Z' ((1:ℂ) - 1), ?_⟩
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have hc1 : ContinuousAt (fun s : ℂ => d ^ ((1 - s) / 2) / d ^ (s / 2)) 1 := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_const_cpow hd0).comp (by fun_prop)
    · exact (continuousAt_const_cpow hd0).comp (by fun_prop)
    · rw [Ne, cpow_eq_zero_iff]; tauto
  have hc2 : ContinuousAt (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹) ^ f) 1 :=
    (Complex.differentiable_Gammaℝ_inv.continuous.pow f).continuousAt
  have hZ'0 : ContinuousAt (fun s : ℂ => Z' (1 - s)) 1 := by
    have : DifferentiableAt ℂ Z' (1 - 1) := by
      refine hZ'.1.differentiableAt (isOpen_compl_singleton.mem_nhds ?_)
      simp
    exact this.continuousAt.comp (by fun_prop)
  have hres : Tendsto (fun s : ℂ => -((1 - s) * Complex.Gammaℝ (1 - s))) (𝓝[≠] 1) (𝓝 (-2)) := by
    have hm : Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] 1) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun s : ℂ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero] at hs ⊢
        exact fun h => hs h.symm
    exact (Complex.Gammaℝ_residue_zero.comp hm).neg
  exact ((hc1.tendsto.mono_left nhdsWithin_le_nhds).mul (hc2.tendsto.mono_left nhdsWithin_le_nhds) |>.mul
    (hres.pow f)).mul (hZ'0.tendsto.mono_left nhdsWithin_le_nhds)

end GlobalTheory.ZetaPole

noncomputable section
namespace GlobalTheory.ZetaPole

theorem norm_le_idealZetaR (F : Type) [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ)
    (hZ : IsPartialZeta C Z) {x : ℝ} (hx : 1 < x) : ‖Z x‖ ≤ ReciprocityTheory.Cheb.idealZetaR F x := by
  have hs := hZ.2 x (by simpa using hx)
  set r : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} → ℝ :=
    fun J => ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℝ) ^ (-x) with hr
  have hterm : (fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
      ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-(x : ℂ))) = fun J => ((r J : ℝ) : ℂ) := by
    funext J
    rw [hr, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [hterm] at hs
  have hre := (Complex.hasSum_re hs)
  have him := (Complex.hasSum_im hs)
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  have him0 : (Z x).im = 0 := (hasSum_zero.unique him).symm
  have hnn : 0 ≤ (Z x).re := hre.nonneg fun J => by positivity
  have hZx : Z x = ((Z x).re : ℂ) := Complex.ext (by simp) (by simp [him0])
  rw [hZx, norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  refine hasSum_le_of_sum_le hre fun T => ?_
  classical
  have hinj : Function.Injective (fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} => (J.1 : Ideal (𝓞 F))) := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)
  have := ReciprocityTheory.Cheb.sum_le_idealZetaR F hx (T.image fun J => (J.1 : Ideal (𝓞 F)))
  rw [Finset.sum_image fun a _ b _ h => hinj h] at this
  exact this

theorem bdd_right (F : Type) [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ)
    (hZ : IsPartialZeta C Z) : ∃ B : ℝ, ∀ᶠ x : ℝ in 𝓝[>] 1, ‖((x : ℂ) - 1) * Z x‖ ≤ B := by
  refine ⟨dedekindZeta_residue F + 1, ?_⟩
  have ht := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  have hlt : ‖(dedekindZeta_residue F : ℂ)‖ < dedekindZeta_residue F + 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (dedekindZeta_residue_pos F)]; linarith
  filter_upwards [ht.eventually (eventually_lt_nhds hlt), self_mem_nhdsWithin] with x hx hx1
  have hx1' : 1 < x := hx1
  rw [ReciprocityTheory.Cheb.dedekindZeta_eq_idealZetaR F hx1'] at hx
  have h0 : 0 ≤ x - 1 := by linarith
  calc ‖((x : ℂ) - 1) * Z x‖ = (x - 1) * ‖Z x‖ := by
        rw [norm_mul, show ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
          Real.norm_eq_abs, abs_of_nonneg h0]
    _ ≤ (x - 1) * ReciprocityTheory.Cheb.idealZetaR F x := mul_le_mul_of_nonneg_left (norm_le_idealZetaR F C Z hZ hx1') h0
    _ ≤ ‖((x : ℂ) - 1) * ((ReciprocityTheory.Cheb.idealZetaR F x : ℝ) : ℂ)‖ := by
        rw [show ((x : ℂ) - 1) * ((ReciprocityTheory.Cheb.idealZetaR F x : ℝ) : ℂ) =
          (((x - 1) * ReciprocityTheory.Cheb.idealZetaR F x : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
        exact le_abs_self _
    _ ≤ dedekindZeta_residue F + 1 := hx.le

end GlobalTheory.ZetaPole

noncomputable section
namespace GlobalTheory.ZetaPole

theorem zeta_simple_pole : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (C C' : ClassGroup (NumberField.RingOfIntegers F)) (Z Z' : ℂ → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C' Z' →
    (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) →
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s =
        (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)) →
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ ∀ s : ℂ, s ≠ 1 → Z s = R s / (s - 1) := by
  intro F _ _ _ C C' Z Z' hZ hZ' hfe
  set f := Module.finrank ℚ F
  have hdiff : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ Z s := fun s hs =>
    hZ.1.differentiableAt (isOpen_compl_singleton.mem_nhds hs)

  obtain ⟨L, hL⟩ := tendsto_pow_mul F C C' Z Z' hZ' hfe
  set h : ℂ → ℂ := fun s => (s - 1) ^ f * Z s
  have hHd : DifferentiableOn ℂ (Function.update h 1 (limUnder (𝓝[≠] 1) h)) Set.univ := by
    refine differentiableOn_update_limUnder_of_isLittleO Filter.univ_mem ?_ ?_
    · intro s hs
      have hs1 : s ≠ 1 := hs.2
      exact (((differentiableAt_id.sub_const 1).pow f).mul (hdiff s hs1)).differentiableWithinAt
    · exact ((hL.sub_const (h 1)).norm.isBoundedUnder_le).isLittleO_sub_self_inv
  set H := Function.update h 1 (limUnder (𝓝[≠] 1) h)
  have hHdf : Differentiable ℂ H := fun s => hHd.differentiableAt Filter.univ_mem
  have hHa : AnalyticAt ℂ H 1 := hHdf.analyticAt 1
  have hHh : ∀ s, s ≠ 1 → H s = (s - 1) ^ f * Z s := fun s hs => Function.update_of_ne hs _ _

  set g : ℂ → ℂ := fun s => (s - 1) * Z s
  have hpunct : ∀ {P : ℂ → Prop}, (∀ᶠ z in 𝓝 (1:ℂ), P z) → ∀ᶠ z in 𝓝[≠] (1:ℂ), P z ∧ z ≠ 1 := fun hP =>
    (eventually_nhdsWithin_of_eventually_nhds hP).and self_mem_nhdsWithin
  have hg : ∃ M, Tendsto g (𝓝[≠] 1) (𝓝 M) := by
    by_cases hz : ∀ᶠ z in 𝓝 (1:ℂ), H z = 0
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [hpunct hz] with z ⟨hz0, hz1⟩
      have hne : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
      rw [hHh z hz1] at hz0
      have : Z z = 0 := (mul_eq_zero.mp hz0).resolve_left (pow_ne_zero _ hne)
      simp [g, this]
    · obtain ⟨n, G, hGa, hG1, hev⟩ := hHa.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
      rcases le_or_gt f (n + 1) with hfn | hfn
      · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hfn
        refine ⟨(1 - 1 : ℂ) ^ m * G 1, ?_⟩
        have hc : ContinuousAt (fun s : ℂ => (s - 1) ^ m * G s) 1 :=
          ((continuous_id.sub continuous_const).pow m).continuousAt.mul hGa.continuousAt
        refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [hpunct hev] with z ⟨hz0, hz1⟩
        have hne : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
        rw [hHh z hz1, smul_eq_mul] at hz0
        apply mul_left_cancel₀ (pow_ne_zero f hne)
        simp only [g]
        calc (z - 1) ^ f * ((z - 1) ^ m * G z) = (z - 1) ^ (n + 1) * G z := by rw [hm]; ring
          _ = (z - 1) * ((z - 1) ^ f * Z z) := by rw [hz0]; ring
          _ = (z - 1) ^ f * ((z - 1) * Z z) := by ring
      · exfalso
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hfn

        have hev2 : ∀ᶠ z in 𝓝[≠] (1:ℂ), G z = (z - 1) ^ (k + 1) * g z := by
          filter_upwards [hpunct hev] with z ⟨hz0, hz1⟩
          have hne : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
          rw [hHh z hz1, smul_eq_mul] at hz0
          apply mul_left_cancel₀ (pow_ne_zero n hne)
          simp only [g]
          calc (z - 1) ^ n * G z = (z - 1) ^ f * Z z := hz0.symm
            _ = (z - 1) ^ n * ((z - 1) ^ (k + 1) * ((z - 1) * Z z)) := by rw [hk]; ring
        have hreal : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝[≠] (1:ℂ)) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · have := (Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
            simpa using this
          · filter_upwards [self_mem_nhdsWithin] with x hx
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro h
            have : x = 1 := by exact_mod_cast h
            exact (ne_of_gt (show (1:ℝ) < x from hx)) this
        have hG : Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 (G 1)) :=
          (hGa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).comp hreal
        obtain ⟨B, hB⟩ := bdd_right F C Z hZ
        have h0 : Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have hlim : Tendsto (fun x : ℝ => |x - 1| ^ (k + 1) * B) (𝓝[>] 1) (𝓝 0) := by
            have : Tendsto (fun x : ℝ => |x - 1| ^ (k + 1) * B) (𝓝 1) (𝓝 (|1 - 1| ^ (k + 1) * B)) :=
              (((continuous_id.sub continuous_const).abs.pow (k + 1)).mul continuous_const).tendsto 1
            simpa using this.mono_left nhdsWithin_le_nhds
          refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
          filter_upwards [hB, hreal.eventually hev2] with x hx hx2
          rw [hx2, norm_mul, norm_pow, show ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
            Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (by simpa [g] using hx) (by positivity)
        exact hG1 (tendsto_nhds_unique hG h0)

  obtain ⟨M, hM⟩ := hg
  refine ⟨Function.update g 1 (limUnder (𝓝[≠] 1) g), ?_, ?_⟩
  · have hRd : DifferentiableOn ℂ (Function.update g 1 (limUnder (𝓝[≠] 1) g)) Set.univ := by
      refine differentiableOn_update_limUnder_of_isLittleO Filter.univ_mem ?_ ?_
      · intro s hs
        have hs1 : s ≠ 1 := hs.2
        exact ((differentiableAt_id.sub_const 1).mul (hdiff s hs1)).differentiableWithinAt
      · exact ((hM.sub_const (g 1)).norm.isBoundedUnder_le).isLittleO_sub_self_inv
    exact fun s => hRd.differentiableAt Filter.univ_mem
  · intro s hs
    rw [Function.update_of_ne hs]
    simp only [g]
    field_simp [sub_ne_zero.mpr hs]

end GlobalTheory.ZetaPole
end
end
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialZeta_totallyReal_at_most_simple_pole : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (C C' : ClassGroup (NumberField.RingOfIntegers F)) (Z Z' : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C' Z' → (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)) → ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ ∀ s : ℂ, s ≠ 1 → Z s = R s / (s - 1) := by
  atlas_forward_decl GlobalTheory.ZetaPole.zeta_simple_pole
end

section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn : DifferentiableOn ℂ GlobalTheory.HeckeTwo.cConst GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.cConst_differentiableOn | exact GlobalTheory.HeckeTwo.cConst_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.cConst_differentiableOn <;> assumption)
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

lemma ofReal_add_I_ne_zero (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

lemma norm_inv_ofReal_add_I_sq (t : ℝ) : ‖((t : ℂ) + I)⁻¹ ^ 2‖ = (1 + t ^ 2)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma tendsto_inv_ofReal_add_I_atTop :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)⁻¹) Filter.atTop (nhds 0) := by
  have hb : Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)) Filter.atTop (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine Filter.tendsto_atTop_mono (fun t => ?_) Filter.tendsto_abs_atTop_atTop
    have := Complex.abs_re_le_norm ((t : ℂ) + I)
    simpa using this
  exact Filter.Tendsto.comp Filter.tendsto_inv₀_cobounded hb

lemma tendsto_inv_ofReal_add_I_atBot :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)⁻¹) Filter.atBot (nhds 0) := by
  have hb : Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)) Filter.atBot (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine Filter.tendsto_atTop_mono (fun t => ?_) Filter.tendsto_abs_atBot_atTop
    have := Complex.abs_re_le_norm ((t : ℂ) + I)
    simpa using this
  exact Filter.Tendsto.comp Filter.tendsto_inv₀_cobounded hb

lemma hasDerivAt_neg_inv_ofReal_add_I (t : ℝ) :
    HasDerivAt (fun s : ℝ => -((s : ℂ) + I)⁻¹) (((t : ℂ) + I)⁻¹ ^ 2) t := by
  have h1 : HasDerivAt (fun w : ℂ => w + I) 1 (t : ℂ) := (hasDerivAt_id _).add_const I
  have h2 := (h1.inv (ofReal_add_I_ne_zero t)).neg
  have h3 := h2.comp_ofReal
  convert h3 using 1
  · funext s
    simp
  · rw [inv_pow]
    field_simp

lemma integral_inv_ofReal_add_I_sq : ∫ t : ℝ, ((t : ℂ) + I)⁻¹ ^ 2 = 0 := by
  have hint : MeasureTheory.Integrable (fun t : ℝ => ((t : ℂ) + I)⁻¹ ^ 2) := by
    refine integrable_inv_one_add_sq.mono' ?_ ?_
    · exact (((continuous_ofReal.add continuous_const).inv₀ ofReal_add_I_ne_zero).pow 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => (norm_inv_ofReal_add_I_sq t).le)
  rw [MeasureTheory.integral_of_hasDerivAt_of_tendsto hasDerivAt_neg_inv_ofReal_add_I hint
    (by simpa using tendsto_inv_ofReal_add_I_atBot.neg)
    (by simpa using tendsto_inv_ofReal_add_I_atTop.neg)]
  simp

theorem cConst_zero : cConst 0 = 0 := by
  unfold cConst hTrans phi
  simp only [mul_zero, neg_zero, Complex.cpow_zero, mul_one, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, one_mul]
  exact integral_inv_ofReal_add_I_sq

end GlobalTheory.HeckeTwo
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierConstantAtZero_zero : GlobalTheory.HeckeTwo.cConst 0 = 0 := by
  atlas_forward_decl GlobalTheory.HeckeTwo.cConst_zero
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory

theorem upperHalf_prodImPow_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), ContDiffOn ℝ ∞ (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  intro F _ _ σ
  apply contDiffOn_prod
  intro τ _
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  have hpos : 0 < (z τ).im := hz τ
  have hL : ContDiff ℝ ∞ (fun w : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => (((w τ).im : ℝ) : ℂ)) := by
    have : (fun w : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => (((w τ).im : ℝ) : ℂ)) =
        (Complex.ofRealCLM.comp (Complex.imCLM.comp (ContinuousLinearMap.proj τ))) := by
      ext w; simp
    rw [this]; exact ContinuousLinearMap.contDiff _
  have hslit : (((z τ).im : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hpos
  have hg : ContDiffAt ℂ ∞ (fun s : ℂ => s ^ (-1 - 2 * σ)) (((z τ).im : ℝ) : ℂ) :=
    (analyticAt_id.cpow analyticAt_const hslit).contDiffAt
  exact (hg.restrict_scalars ℝ).comp z hL.contDiffAt

end GlobalTheory
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlaneProduct_prod_im_rpow_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), ContDiffOn ℝ ∞ (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  atlas_forward_decl GlobalTheory.upperHalf_prodImPow_contDiffOn
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.ProdImWirt
variable {Φ : Type} [Fintype Φ]

noncomputable def mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) (z : Φ → ℂ) : ℂ :=
  c σ * Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ))

theorem hasFDerivAt_logIm (τ : Φ) {z : Φ → ℂ} (hz : (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ((Real.log (z τ).im : ℝ) : ℂ))
      (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))) z := by
  have h1 : HasFDerivAt (fun z : Φ → ℂ => (z τ).im) (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)) z :=
    (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)).hasFDerivAt
  have h2 := h1.log hz
  exact ofRealCLM.hasFDerivAt.comp z h2

theorem hasFDerivAt_expo (A : Φ → ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ∑ τ, A τ * ((Real.log (z τ).im : ℝ) : ℂ))
      (∑ τ, A τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ))))) z := by
  have := HasFDerivAt.sum (u := Finset.univ) (fun τ _ => (hasFDerivAt_logIm τ (hz τ)).const_mul (A τ))
  have e : (∑ τ, fun y : Φ → ℂ => A τ * ((Real.log (y τ).im : ℝ) : ℂ)) = fun y => ∑ τ, A τ * ((Real.log (y τ).im : ℝ) : ℂ) := by
    ext y; simp [Finset.sum_apply]
  rw [e] at this; exact this

theorem hasFDerivAt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (mono c a σ)
      (c σ • (Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ)) • ∑ τ, a σ τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))))) z :=
  ((hasFDerivAt_expo (a σ) hz).cexp).const_mul (c σ)

open Classical in
theorem wirt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, 0 < (z τ).im) (τ₀ : Φ) (b : Bool) :
    wirt τ₀ b (mono c a σ) z =
      mono (fun σ => (if b then I else -I) / 2 * c σ * a σ τ₀) (fun σ => a σ - Pi.single τ₀ 1) σ z := by
  have hz' : ∀ τ, (z τ).im ≠ 0 := fun τ => (hz τ).ne'
  rw [wirt, (hasFDerivAt_mono c a σ hz').fderiv]
  simp [mono, Pi.single_apply]
  have hy := hz τ₀
  have e1 : ∀ x, ((if x = τ₀ then (1:ℂ) else 0).im) = 0 := fun x => by split_ifs <;> simp
  have e2 : ∀ x, ((if x = τ₀ then I else 0).im) = if x = τ₀ then 1 else 0 := fun x => by split_ifs <;> simp
  simp only [e1, e2, ofReal_zero, mul_zero, Finset.sum_const_zero, zero_add, apply_ite (fun r : ℝ => (r : ℂ)), ofReal_one, ofReal_zero,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have he : ∑ x, (a σ x - if x = τ₀ then 1 else 0) * ((Real.log (z x).im : ℝ) : ℂ) =
      ∑ x, a σ x * ((Real.log (z x).im : ℝ) : ℂ) - ((Real.log (z τ₀).im : ℝ) : ℂ) := by
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [he, Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hy]
  have hy' : ((z τ₀).im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  cases b <;> simp <;> field_simp <;> ring

theorem wirtWord_mono (U : Set (Φ → ℂ)) (hU : IsOpen U) (hUpos : ∀ z ∈ U, ∀ τ, 0 < (z τ).im) (w : List (Φ × Bool)) :
    ∀ (c : ℂ → ℂ) (a : ℂ → Φ → ℂ), Differentiable ℂ c → (∀ τ, Differentiable ℂ (fun σ => a σ τ)) →
      ∃ (c' : ℂ → ℂ) (a' : ℂ → Φ → ℂ), Differentiable ℂ c' ∧ (∀ τ, Differentiable ℂ (fun σ => a' σ τ)) ∧
        ∀ σ, Set.EqOn (wirtWord w (mono c a σ)) (mono c' a' σ) U := by
  induction w with
  | nil => exact fun c a hc ha => ⟨c, a, hc, ha, fun σ z _ => rfl⟩
  | cons l w ih =>
    intro c a hc ha
    obtain ⟨c₁, a₁, hc₁, ha₁, h₁⟩ := ih c a hc ha
    classical
    refine ⟨fun σ => (if l.2 then I else -I) / 2 * c₁ σ * a₁ σ l.1, fun σ => a₁ σ - Pi.single l.1 1,
      ((differentiable_const _).mul hc₁).mul (ha₁ l.1), fun τ => ?_, fun σ z hz => ?_⟩
    · simp only [Pi.sub_apply]
      exact (ha₁ τ).sub (differentiable_const _)
    · rw [wirtWord_cons, GoodAdd.wirt_congr hU (h₁ σ) _ _ hz]
      convert wirt_mono c₁ a₁ σ (hUpos z hz) l.1 l.2

theorem mono_differentiable {c : ℂ → ℂ} {a : ℂ → Φ → ℂ} (hc : Differentiable ℂ c)
    (ha : ∀ τ, Differentiable ℂ (fun σ => a σ τ)) (z : Φ → ℂ) : Differentiable ℂ (fun σ => mono c a σ z) := by
  unfold mono
  refine hc.mul (Differentiable.cexp ?_)
  exact Differentiable.fun_sum fun τ _ => (ha τ).mul (differentiable_const _)

theorem wirtWord_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U)
    (w : List (Φ × Bool)) : Set.EqOn (wirtWord w f) (wirtWord w g) U := by
  induction w with
  | nil => exact h
  | cons l w ih => intro y hy; rw [wirtWord_cons, wirtWord_cons]; exact GoodAdd.wirt_congr hU ih _ _ hy

end GlobalTheory.HeckeTwo.ProdImWirt

theorem GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (w : List (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F × Bool)) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F → DifferentiableOn ℂ (fun σ : ℂ => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord w (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) z) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ w z hz
  have hU := GoodAdd.upperHalf_isOpen F
  obtain ⟨c', a', hc', ha', h⟩ := ProdImWirt.wirtWord_mono (upperHalf F) hU (fun z hz => hz) w (fun _ => 1)
    (fun σ _ => -1 - 2 * σ) (differentiable_const _)
    (fun _ => (differentiable_const _).sub ((differentiable_const _).mul differentiable_id))
  have hw : ∀ σ, Set.EqOn (wirtWord w (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)))
      (wirtWord w (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ)) (upperHalf F) := by
    intro σ
    have h0 : Set.EqOn (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))
        (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ) (upperHalf F) := by
      intro y hy
      simp only [ProdImWirt.mono, one_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      have hpos : 0 < (y τ).im := hy τ
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, mul_comm]
    exact ProdImWirt.wirtWord_congr hU h0 w
  refine ((ProdImWirt.mono_differentiable hc' ha' z).differentiableOn).congr fun σ _ => ?_
  rw [hw σ hz, h σ hz]
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodIm_iteratedWirtingerDerivWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (w : List (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F × Bool)) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F → DifferentiableOn ℂ (fun σ : ℂ => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord w (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) z) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  atlas_forward_decl GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

namespace BZeroGood

theorem card_emb_totReal (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) ⟨fun τ τ' h => ?_, fun φ => ?_⟩
  · ext x
    exact Complex.ofReal_injective (RingHom.congr_fun h x)
  · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x =>
      (IsTotallyReal.complexEmbedding_isReal φ).coe_embedding_apply x⟩

theorem halfPlane_mem_nhds_zero : halfPlane ∈ nhds (0 : ℂ) := by
  refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
  show (-1 / 2 : ℝ) < (0 : ℂ).re
  norm_num

theorem _root_.GlobalTheory.HeckeTwo.bZero_isGood (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (hf : 2 ≤ Module.finrank ℚ F)
    (𝔞 𝔟 : Frac F) (Zb R : ℂ → ℂ) (hR : Differentiable ℂ R) (hZ : ∀ s : ℂ, s ≠ 1 → Zb s = R s / (s - 1)) :
    IsGood (bZero Zb 𝔞 𝔟) := by
  set f := Fintype.card (Emb F) with hfdef
  have hf2 : 2 ≤ f := by rw [hfdef, card_emb_totReal F]; exact hf
  set E : ℂ → ℂ := fun σ => if σ = 0 then 0 else
    kFac F σ * (omegaFactor 𝔞 : ℂ) * ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ) * Zb (1 + 2 * σ) * cConst σ ^ f with hE
  set G : ℂ → ℂ := fun σ =>
    kFac F σ * (omegaFactor 𝔞 : ℂ) * ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ) * (R (1 + 2 * σ) / 2) *
      dslope cConst 0 σ * cConst σ ^ (f - 1) with hG
  have hEG : E = G := by
    funext σ
    simp only [hE, hG]
    split_ifs with h0
    · subst h0
      rw [GlobalTheory.T.heckePhiFourierConstantAtZero_zero, zero_pow (by omega), mul_zero]
    · rw [dslope_of_ne _ h0, slope_def_field, GlobalTheory.T.heckePhiFourierConstantAtZero_zero, hZ _ (by
          intro h; apply h0; linear_combination h / 2)]
      have hf1 : f = (f - 1) + 1 := by omega
      rw [hf1, pow_succ]
      simp only [Nat.add_sub_cancel]
      field_simp
      ring
  have hGd : DifferentiableOn ℂ G halfPlane := by
    intro σ hσ
    have hσ' : -1 - 2 * σ ≠ 0 := by
      intro h
      have : σ.re = -1 / 2 := by
        have := congrArg Complex.re h
        simp at this
        linarith
      simp only [halfPlane, Set.mem_setOf_eq] at hσ
      linarith
    have h1 : DifferentiableAt ℂ (fun σ : ℂ => ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ)) σ :=
      DifferentiableAt.const_cpow ((differentiableAt_const _).sub (differentiableAt_id.const_mul _)) (Or.inr hσ')
    have h2 : DifferentiableAt ℂ (fun σ : ℂ => R (1 + 2 * σ)) σ :=
      (hR _).comp σ ((differentiableAt_const _).add (differentiableAt_id.const_mul _))
    have h3 : DifferentiableWithinAt ℂ (dslope cConst 0) halfPlane σ :=
      ((differentiableOn_dslope halfPlane_mem_nhds_zero).2 GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn) σ hσ
    have h4 : DifferentiableWithinAt ℂ cConst halfPlane σ := GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn σ hσ
    exact ((((kFac_differentiable σ).differentiableWithinAt.mul (differentiableWithinAt_const _)).mul
      h1.differentiableWithinAt).mul (h2.differentiableWithinAt.div_const _)).mul h3 |>.mul (h4.pow _)
  have hB : bZero Zb 𝔞 𝔟 = fun σ z => E σ * ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
    funext σ z
    simp only [bZero, hE]
    split_ifs
    · simp
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      ring
  rw [hB]
  exact GlobalTheory.HeckeTwoMul.isGood_mul F E _ (hEG ▸ hGd) ⟨fun σ _ => GlobalTheory.T.upperHalfPlaneProduct_prod_im_rpow_contDiffOn F σ, fun w z hz => GlobalTheory.T.prodIm_iteratedWirtingerDerivWord_differentiableOn F w z hz⟩

end BZeroGood

end GlobalTheory.HeckeTwo
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisensteinZeroFrequencyPart_isSmoothHolomorphic : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb R : ℂ → ℂ), Differentiable ℂ R → (∀ s : ℂ, s ≠ 1 → Zb s = R s / (s - 1)) → GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bZero Zb 𝔞 𝔟) := by
  atlas_forward_decl GlobalTheory.HeckeTwo.bZero_isGood
end

section
section
noncomputable section

open Complex MeasureTheory Set
open scoped FourierTransform

namespace GlobalTheory.HeckeTwo

lemma lipschitzOneVariableKernel_two_eq_indicator {y : ℝ} (hy : 0 < y) :
    GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ 1 * Complex.exp (-(((2 * Real.pi * y : ℝ) : ℂ) * t))) := by
  funext t
  have him : ((y : ℂ) * I).im = y := by simp
  simp only [GlobalTheory.LipschitzTR.phi1, Set.indicator, Set.mem_Ioi, him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases ht : 0 < t
  · rw [if_pos ht, if_pos ht, abs_of_pos ht]
    push_cast
    congr 2
    ring_nf
    rw [I_sq]
    ring
  · rw [if_neg ht, if_neg ht]

lemma norm_inv_ofReal_add_mul_I_sq (x y : ℝ) : ‖((x : ℂ) + (y : ℂ) * I)⁻¹ ^ 2‖ = (x ^ 2 + y ^ 2)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma ofReal_add_ofReal_mul_I_ne_zero (x : ℝ) {y : ℝ} (hy : 0 < y) : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy.ne' this

theorem hTrans_sigma_zero_eq : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y =
    if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  intro ν y hy
  set g := GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) with hg
  have hw : ((y : ℂ) * I).im ≠ 0 := by simp [hy.ne']
  have hgc : Continuous g := GlobalTheory.LipschitzTR.continuous_lipschitzOneVariableKernel le_rfl hw
  have hgi : Integrable g := by
    rw [hg, lipschitzOneVariableKernel_two_eq_indicator hy, integrable_indicator_iff measurableSet_Ioi]
    exact GlobalTheory.LipschitzTR.integrableOn_pow_mul_cexp_neg 1 (by simp; positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hF : ∀ x : ℝ, 𝓕 g x = -(4 * (Real.pi : ℂ) ^ 2)⁻¹ * (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ ^ 2 := by
    intro x
    rw [hg, GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow 2 le_rfl even_two _ hw x]
    have hne := ofReal_add_ofReal_mul_I_ne_zero (-x) hy
    rw [zpow_neg, zpow_natCast]
    push_cast at hne ⊢
    have : (y : ℂ) * I - x = -(x : ℂ) + y * I := by ring
    rw [this]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hFi : Integrable (𝓕 g) := by
    have hb : Integrable (fun x : ℝ => ((4 * Real.pi ^ 2 * y ^ 2)⁻¹ : ℝ) * (1 + (x / y) ^ 2)⁻¹) :=
      (integrable_inv_one_add_sq.comp_div hy.ne').const_mul _
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    · rw [show (𝓕 g) = fun x : ℝ => -(4 * (Real.pi : ℂ) ^ 2)⁻¹ * (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ ^ 2 from funext hF]
      exact Continuous.aestronglyMeasurable
        (continuous_const.mul ((((continuous_ofReal.comp continuous_neg).add continuous_const).inv₀
          (fun x => ofReal_add_ofReal_mul_I_ne_zero (-x) hy)).pow 2))
    · rw [hF, norm_mul, norm_neg, norm_inv, norm_mul, norm_pow, norm_inv_ofReal_add_mul_I_sq]
      simp only [RCLike.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, neg_sq]
      have : y ≠ 0 := hy.ne'
      field_simp <;> ring
  have hinv : 𝓕 (𝓕⁻ g) = g := hgc.fourier_fourierInv_eq hgi hFi
  have hphi : ∀ t : ℝ, phi 0 ((t : ℂ) + (y : ℂ) * I) = -4 * (Real.pi : ℂ) ^ 2 * 𝓕⁻ g t := by
    intro t
    rw [Real.fourierInv_eq_fourier_neg, hF, neg_neg]
    unfold phi
    rw [mul_zero, Complex.cpow_zero, mul_one]
    field_simp
  have hT : hTrans 0 ν y = -4 * (Real.pi : ℂ) ^ 2 * 𝓕 (𝓕⁻ g) ν := by
    unfold hTrans
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1
    funext t
    rw [hphi t, smul_eq_mul]
    push_cast
    ring_nf
  rw [hT, hinv, hg]
  simp only [GlobalTheory.LipschitzTR.phi1]
  have him : ((y : ℂ) * I).im = y := by simp
  rw [him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases hν : 0 < ν
  · rw [if_pos hν, if_pos hν, abs_of_pos hν]
    push_cast
    ring_nf
    rw [I_sq]
    ring_nf
  · rw [if_neg hν, if_neg hν, mul_zero]

end GlobalTheory.HeckeTwo
end
end

open Complex GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y = if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  atlas_forward_decl GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq
end

section
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoSum

variable {F : Type} [Field F] [NumberField F]

theorem pow_mul_exp_neg_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (n : ℕ) :
    t ^ n * Real.exp (-(c * t)) ≤ n.factorial / c ^ n := by
  have h := Real.pow_div_factorial_le_exp (c * t) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have he := Real.exp_pos (c * t)
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ (pow_pos hc n), Real.exp_neg]
  rw [show t ^ n * (Real.exp (c * t))⁻¹ * c ^ n = (c ^ n * t ^ n) / Real.exp (c * t) by field_simp]
  rw [div_le_iff₀ he]
  linarith

theorem exists_norm_lower (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ν ∈ I, ν ≠ 0 → κ ≤ |((Algebra.norm ℚ ν : ℚ) : ℝ)| := by
  obtain ⟨d, hd, hdI⟩ := GlobalTheory.HeckeTwo.APart.exists_den I
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| := by
    simp [Algebra.norm_eq_zero_iff, hd']
  refine ⟨|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)|⁻¹, inv_pos.2 hNd, fun ν hν hν0 => ?_⟩
  obtain ⟨x, hx⟩ := hdI ν hν
  have e1 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ ν := by
    rw [Algebra.coe_norm_int, hx, map_mul]
  have hxz : (Algebra.norm ℤ x : ℤ) ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at e1
    have h1 : Algebra.norm ℚ (d : F) ≠ 0 := (Algebra.norm_ne_zero_iff).2 hd'
    have h2 : Algebra.norm ℚ ν ≠ 0 := (Algebra.norm_ne_zero_iff).2 hν0
    exact mul_ne_zero h1 h2 e1.symm
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ x : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hxz
  have e2 : ((Algebra.norm ℤ x : ℤ) : ℝ) =
      ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ ν : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  rw [e2, abs_mul] at h1
  have := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hNd).le
  rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hNd.ne', one_mul] at this

theorem norm_qPow (ξ : F) (z : Emb F → ℂ) :
    ‖qPow ξ z‖ = Real.exp (-(2 * Real.pi * ∑ τ, τ ξ * (z τ).im)) := by
  rw [qPow, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

end GlobalTheory.HeckeTwoSum

namespace GlobalTheory.HeckeTwoSum

open GlobalTheory.LipschitzTR

variable {F : Type} [Field F] [NumberField F]

theorem summable_qClass_two [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) :
    Summable (qClass 𝔞 𝔟 2 z) := by
  classical
  obtain ⟨τ₀⟩ := GlobalTheory.HeckeTwoExp.emb_nonempty (F := F)
  obtain ⟨m, hm, hmy⟩ : ∃ m : ℝ, 0 < m ∧ ∀ τ, m ≤ (z τ).im := by
    obtain ⟨τ₁, -, hτ₁⟩ := Finset.exists_min_image Finset.univ (fun τ => (z τ).im) ⟨τ₀, Finset.mem_univ _⟩
    exact ⟨_, hz τ₁, fun τ => hτ₁ τ (Finset.mem_univ _)⟩
  obtain ⟨κ, hκ, hκν⟩ := exists_norm_lower (𝔞 : FractionalIdeal (𝓞 F)⁰ F)
  have hnrm : 0 < nrm 𝔞 := lt_of_le_of_ne (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _)
    (GlobalTheory.HeckeTwoExp.nrm_ne_zero 𝔞).symm
  set N : FractionalIdeal (𝓞 F)⁰ F := (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) with hN
  haveI : DiscreteTopology (latOf N) := discrete_latOf F N
  set n : ℕ := Module.finrank ℤ (latOf N) + 1 with hn
  have hL : Summable fun v : latOf N => ‖v‖⁻¹ ^ n := ZLattice.summable_norm_pow_inv (latOf N) n (Nat.lt_succ_self _)
  set f : ℕ := Fintype.card (Emb F) with hf
  set K : ℝ := ((2 * f + n).factorial : ℝ) / (2 * Real.pi * m) ^ (2 * f + n) with hK
  set C : ℝ := K / (nrm 𝔞 * κ) with hC
  have hK0 : 0 < K := by positivity
  have hC0 : 0 < C := by positivity
  have key : ∀ ν b : F, ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ν ≠ 0 → b ≠ 0 → (∀ τ : Emb F, 0 < τ (ν * b)) →
      ‖qTerm 𝔞 2 z (ν, b)‖ ≤
        C * ((|((Algebra.norm ℚ b : ℚ) : ℝ)| ^ 2)⁻¹ * ‖remb F (ν * b)‖⁻¹ ^ n) := by
    intro ν b hν hν0 hb0 hpos
    set ξ := ν * b with hξ
    set s := ∑ τ : Emb F, τ ξ with hs_def
    set A := |((Algebra.norm ℚ ν : ℚ) : ℝ)| with hA_def
    set B := |((Algebra.norm ℚ b : ℚ) : ℝ)| with hB_def
    set w := ‖remb F ξ‖ with hw_def
    have hs : 0 < s := Finset.sum_pos (fun τ _ => hpos τ) ⟨τ₀, Finset.mem_univ _⟩
    have hA : κ ≤ A := hκν ν hν hν0
    have hA0 : 0 < A := hκ.trans_le hA
    have hB0 : 0 < B := by
      rw [hB_def, abs_pos, Rat.cast_ne_zero]; exact (Algebra.norm_ne_zero_iff).2 hb0
    have hw0 : 0 < w := by
      rw [hw_def, norm_pos_iff]
      intro h
      have := congrArg (fun v : RSp F => v τ₀) h
      have h3 : τ₀ ξ = 0 := by simpa using this
      have h2 := hpos τ₀
      linarith
    have hws : w ≤ s := by
      rw [hw_def, EuclideanSpace.norm_eq]
      refine Real.sqrt_le_iff.2 ⟨hs.le, ?_⟩
      calc ∑ τ, ‖(remb F ξ) τ‖ ^ 2 = ∑ τ : Emb F, (τ ξ) ^ 2 := by
            refine Finset.sum_congr rfl fun τ _ => ?_
            rw [remb_apply, Real.norm_eq_abs, sq_abs]
        _ ≤ (∑ τ : Emb F, τ ξ) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun τ _ => (hpos τ).le
    have hAB : A * B ≤ s ^ f := by
      have h2 := GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ξ
      rw [← Complex.ofReal_prod] at h2
      have h3 := Complex.ofReal_injective h2
      have h1 : A * B = ∏ τ : Emb F, τ ξ := by
        rw [hA_def, hB_def, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hξ, h3]
        exact Finset.prod_congr rfl fun τ _ => abs_of_pos (hpos τ)
      rw [h1, hf, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun τ _ => (hpos τ).le)
        (fun τ _ => Finset.single_le_sum (fun τ _ => (hpos τ).le) (Finset.mem_univ τ))
    set E := Real.exp (-(2 * Real.pi * ∑ τ, τ ξ * (z τ).im)) with hE
    set E' := Real.exp (-((2 * Real.pi * m) * s)) with hE'
    have hEE : E ≤ E' := by
      apply Real.exp_le_exp.2
      have : m * s ≤ ∑ τ, τ ξ * (z τ).im := by
        rw [hs_def, Finset.mul_sum]
        exact Finset.sum_le_sum fun τ _ => by nlinarith [hpos τ, hmy τ]
      nlinarith [Real.pi_pos]
    have hKs := pow_mul_exp_neg_le (c := 2 * Real.pi * m) (t := s) (by positivity) hs.le (2 * f + n)
    have hP : (A * B) ^ 2 * w ^ n ≤ s ^ (2 * f + n) := by
      rw [show s ^ (2 * f + n) = (s ^ f) ^ 2 * s ^ n by ring]
      gcongr
    have hE'K : E' * ((A * B) ^ 2 * w ^ n) ≤ K := by
      have hE'0 : 0 ≤ E' := (Real.exp_pos _).le
      calc E' * ((A * B) ^ 2 * w ^ n) ≤ E' * s ^ (2 * f + n) := mul_le_mul_of_nonneg_left hP hE'0
        _ = s ^ (2 * f + n) * E' := mul_comm _ _
        _ ≤ K := hKs
    have hnorm : ‖qTerm 𝔞 2 z (ν, b)‖ = A / nrm 𝔞 * E := by
      rw [qTerm, norm_mul, norm_qPow, Complex.norm_real, Real.norm_eq_abs, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
        abs_of_nonneg (div_nonneg (abs_nonneg _) hnrm.le)]
    have hR : C * ((B ^ 2)⁻¹ * w⁻¹ ^ n) = K / (nrm 𝔞 * κ * B ^ 2 * w ^ n) := by
      rw [hC, inv_pow]
      field_simp
    rw [hnorm, hR, le_div_iff₀ (by positivity)]
    calc A / nrm 𝔞 * E * (nrm 𝔞 * κ * B ^ 2 * w ^ n) = E * (A * κ * B ^ 2 * w ^ n) := by
          field_simp
      _ ≤ E' * (A * A * B ^ 2 * w ^ n) := by
          gcongr
      _ = E' * ((A * B) ^ 2 * w ^ n) := by ring
      _ ≤ K := hE'K
  set e := Equiv.ofBijective (GlobalTheory.HeckeTwoExp.toQ 𝔞 𝔟)
    ⟨GlobalTheory.HeckeTwoExp.toQ_injective 𝔞 𝔟, GlobalTheory.HeckeTwoExp.toQ_surjective 𝔞 𝔟⟩ with he
  let ι : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)} → latOf N :=
    fun c ν => ⟨remb F (ν.1.1 * c.out.1),
      (mem_latOf N _).2 ⟨_, FractionalIdeal.mul_mem_mul ν.1.2.1 c.out.2.1, rfl⟩⟩
  have hι : ∀ c, Function.Injective (ι c) := by
    intro c ν ν' h
    have h1 := congrArg (fun v : latOf N => (v : RSp F) τ₀) h
    simp only [ι, remb_apply] at h1
    have h2 : ν.1.1 * c.out.1 = ν'.1.1 * c.out.1 := τ₀.injective h1
    exact Subtype.ext (Subtype.ext (mul_right_cancel₀ c.out.2.2 h2))
  set Bf : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → ℝ :=
    fun c => |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| with hBf
  set G : (Σ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}) → ℝ :=
    fun p => C * ((Bf p.1 ^ 2)⁻¹ * ‖ι p.1 p.2‖⁻¹ ^ n) with hG
  have hG0 : ∀ p, 0 ≤ G p := fun p => by
    simp only [hG]; positivity
  have hbound : ∀ p, ‖qClass 𝔞 𝔟 2 z (e p)‖ ≤ G p := by
    rintro ⟨c, ν⟩
    calc ‖qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩)‖ = ‖qTerm 𝔞 2 z (ν.1.1, c.out.1)‖ :=
          congrArg norm (qClass_mk 𝔞 𝔟 2 z ⟨(ν.1.1, c.out.1), ν.1.2.1, c.out.2.1, ν.2⟩)
      _ ≤ G ⟨c, ν⟩ := key ν.1.1 c.out.1 ν.1.2.1 ν.1.2.2 c.out.2.2 ν.2
  have hGs : Summable G := by
    refine (summable_sigma_of_nonneg hG0).2 ⟨fun c => ?_, ?_⟩
    · exact ((hL.comp_injective (hι c)).mul_left ((Bf c ^ 2)⁻¹)).mul_left C
    · have hZ := GlobalTheory.HeckeTwo.APart.summable_norm_rpow (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (s := 2) one_lt_two
      refine Summable.of_nonneg_of_le (fun c => tsum_nonneg fun ν => hG0 ⟨c, ν⟩) (fun c => ?_)
        (hZ.mul_left (C * ∑' v : latOf N, ‖v‖⁻¹ ^ n))
      show ∑' ν, C * ((Bf c ^ 2)⁻¹ * ‖ι c ν‖⁻¹ ^ n) ≤ _
      rw [tsum_mul_left, tsum_mul_left, Real.rpow_neg (abs_nonneg _), Real.rpow_two]
      have hH : ∑' ν, ‖ι c ν‖⁻¹ ^ n ≤ ∑' v : latOf N, ‖v‖⁻¹ ^ n :=
        tsum_comp_le_tsum_of_inj hL (fun _ => by positivity) (hι c)
      have hB : 0 ≤ (Bf c ^ 2)⁻¹ := by positivity
      calc C * ((Bf c ^ 2)⁻¹ * ∑' ν, ‖ι c ν‖⁻¹ ^ n) ≤ C * ((Bf c ^ 2)⁻¹ * ∑' v : latOf N, ‖v‖⁻¹ ^ n) := by
            gcongr
        _ = _ := by simp only [hBf]; ring
  refine Summable.of_norm ?_
  rw [← e.summable_iff]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hGs

end GlobalTheory.HeckeTwoSum

theorem GlobalTheory.HeckeTwoSum.summable_qClass : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) :=
  fun _ _ _ _ 𝔞 𝔟 z hz => GlobalTheory.HeckeTwoSum.summable_qClass_two 𝔞 𝔟 z hz
end
end

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_hilbertEisensteinWeightTwoQSeries : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) := by
  atlas_forward_decl GlobalTheory.HeckeTwoSum.summable_qClass
end

section
section
noncomputable section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem hTrans_zero (ν y : ℝ) (hy : y ≠ 0) :
    hTrans 0 ν y = if 0 < ν * y then
      -4 * (Real.pi : ℂ) ^ 2 * ((|ν| : ℝ) : ℂ) * ((Real.exp (-(2 * Real.pi * (ν * y))) : ℝ) : ℂ) else 0 := by
  rcases hy.lt_or_gt with h | h
  · have e := hTrans_zero_neg (-ν) y
    rw [neg_neg] at e
    rw [← e, GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq _ _ (neg_pos.2 h)]
    by_cases hν : 0 < -ν
    · have h2 : 0 < ν * y := by nlinarith
      rw [if_pos hν, if_pos h2, abs_of_neg (by linarith : ν < 0),
        show -(2 * Real.pi * -ν * -y) = -(2 * Real.pi * (ν * y)) by ring]
    · have h2 : ¬ 0 < ν * y := by nlinarith
      rw [if_neg hν, if_neg h2]
  · rw [GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq _ _ h]
    by_cases hν : 0 < ν
    · have h2 : 0 < ν * y := mul_pos hν h
      rw [if_pos hν, if_pos h2, abs_of_pos hν, show 2 * Real.pi * ν * y = 2 * Real.pi * (ν * y) by ring]
    · have h2 : ¬ 0 < ν * y := by nlinarith
      rw [if_neg hν, if_neg h2]

theorem fTerm_zero [IsTotallyReal F] {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b ν : F} (hb : b ≠ 0) (hν : ν ≠ 0) :
    fTerm 0 z b ν = if ∀ τ : Emb F, 0 < τ (ν * b) then
      (-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) * ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) * qPow (ν * b) z
      else 0 := by
  have hyτ : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  unfold fTerm
  simp only [hTrans_zero _ _ (hyτ _)]
  split_ifs with hc
  · have hc' : ∀ τ : Emb F, 0 < τ ν * (τ b * (z τ).im) := fun τ => by
      have := hc τ; rw [map_mul] at this; rw [← mul_assoc]; exact mul_pos this (hz τ)
    rw [Finset.prod_congr rfl fun τ _ => by rw [if_pos (hc' τ)]]
    rw [abs_norm_eq_prod, qPow, Finset.mul_sum, Complex.exp_sum]
    rw [show ((-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) * ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ)) *
        ∏ x : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((x (ν * b) : ℂ) * z x)) =
        ∏ τ : Emb F, ((-4 * (Real.pi : ℂ) ^ 2) * ((|τ ν| : ℝ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (ν * b) : ℂ) * z τ))) by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_comm, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; congr 1
    conv_rhs => rw [← Complex.re_add_im (z τ)]
    simp only [map_mul]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * (τ ν : ℂ) * (τ b : ℂ) * ((z τ).im : ℂ)) * I_sq
  · push_neg at hc
    obtain ⟨τ, hτ⟩ := hc
    have : ¬ 0 < τ ν * (τ b * (z τ).im) := by
      rw [map_mul] at hτ; rw [← mul_assoc]; exact not_lt.2 (mul_nonpos_of_nonpos_of_nonneg hτ (hz τ).le)
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [if_neg this, mul_zero])

theorem bOne_zero_expansion [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) :
    Summable (qClass 𝔞 𝔟 2 z) ∧
      (cK F 2 : ℂ) * (kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z) / (omegaFactor 𝔞 : ℂ) ^ 2 =
        ∑' c, qClass 𝔞 𝔟 2 z c := by
  have hS := GlobalTheory.T.summable_hilbertEisensteinWeightTwoQSeries F 𝔞 𝔟 z hz
  refine ⟨hS, ?_⟩
  have hn : (nrm 𝔞 : ℂ) ≠ 0 := by exact_mod_cast nrm_ne_zero 𝔞
  have hs : ((dF F ^ ((1 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (dF_pos (F := F)) _).ne'
  have hcK : (cK F 2 : ℂ) = ((dF F ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
    unfold cK; norm_num
  have hL : (cK F 2 : ℂ) * (kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z) / (omegaFactor 𝔞 : ℂ) ^ 2 =
      (kFac F 0 / (nrm 𝔞 : ℂ)) * bOne 𝔞 𝔟 0 z := by
    rw [hcK, omegaFactor]; push_cast
    push_cast at hs
    field_simp
  rw [hL, bOne, ← tsum_mul_left, tsum_qClass_eq 𝔞 𝔟 z hS]
  refine tsum_congr fun c => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun ν => ?_
  rw [fTerm_zero hz c.out.2.2 ν.2.2]
  split_ifs with hc
  · have hk := kFac_zero_mul (F := F)
    unfold qTerm
    simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one, Complex.ofReal_div]
    linear_combination (((|(Algebra.norm ℚ ν.1 : ℝ)| : ℝ) : ℂ) / (nrm 𝔞 : ℂ) * qPow (ν.1 * c.out.1) z) * hk
  · rw [mul_zero]

theorem bOne_zero_qExpansion : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * (GlobalTheory.HeckeTwo.kFac F 0 *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * GlobalTheory.HeckeTwo.bOne 𝔞 𝔟 0 z) / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 =
      ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c :=
  fun _ _ _ _ 𝔞 𝔟 z hz => bOne_zero_expansion 𝔞 𝔟 z hz

end GlobalTheory.HeckeTwoExp
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisenstein_weight_two_qExpansion : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * (GlobalTheory.HeckeTwo.kFac F 0 * (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * GlobalTheory.HeckeTwo.bOne 𝔞 𝔟 0 z) / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 = ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c := by
  atlas_forward_decl GlobalTheory.HeckeTwoExp.bOne_zero_qExpansion
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoConst

variable {F : Type} [Field F] [NumberField F]

theorem exists_ideal (M : FractionalIdeal (𝓞 F)⁰ F) (N : Frac F) (hM : M * (N : FractionalIdeal (𝓞 F)⁰ F) = 1)
    (a : NZ M) : ∃ J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = ClassGroup.mk F N},
      ((J.1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 * N := by
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 * (N : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 := by
    rw [← hM]
    exact mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 a.2.1) _
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hs : FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 a.2.2
  have hI0 : I ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hs N.ne_zero (by rw [← hI]; simp)
  refine ⟨⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, ?_⟩, hI⟩
  have e : FractionalIdeal.mk0 F ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩ = Units.mk0 _ hs * N := by
    ext1
    rw [FractionalIdeal.coe_mk0]
    exact hI
  rw [← ClassGroup.mk_mk0 F, e, map_mul, ClassGroup.mk_eq_one_iff.2, one_mul]
  rw [FractionalIdeal.isPrincipal_iff]
  exact ⟨a.1, rfl⟩

theorem exists_equiv (M : FractionalIdeal (𝓞 F)⁰ F) (N : Frac F) (hM : M * (N : FractionalIdeal (𝓞 F)⁰ F) = 1) :
    ∃ e : Quotient (unitRel M) ≃ {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = ClassGroup.mk F N}, ∀ c,
      (((e c).1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ c.out.1 * N := by
  choose f hf using exists_ideal M N hM
  have key : ∀ a b : NZ M, (unitRel M).r a b ↔
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 := by
    intro a b
    rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
    refine exists_congr fun ε => ?_
    rw [Units.smul_def, Algebra.smul_def]
    exact eq_comm
  refine ⟨Equiv.ofBijective (fun c => f c.out) ⟨?_, ?_⟩, fun c => hf _⟩
  · intro c c' h
    have h1 := hf c.out
    simp only at h
    rw [h, hf] at h1
    have h2 := (key _ _).2 (mul_right_cancel₀ N.ne_zero h1).symm
    rw [← c.out_eq, ← c'.out_eq]
    exact Quotient.sound h2
  · rintro ⟨J, hJ⟩
    have h1 : ClassGroup.mk F (FractionalIdeal.mk0 F J * N⁻¹) = 1 := by
      rw [map_mul, map_inv, ClassGroup.mk_mk0, hJ, mul_inv_cancel]
    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at h1
    obtain ⟨a, ha⟩ := h1
    have ha0 : a ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.1 (ha ▸ Units.ne_zero _)
    have hMN : M = ((N⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_left hM
    rw [Units.val_mul, FractionalIdeal.coe_mk0, ← hMN] at ha
    have haM : a ∈ M := by
      rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← ha]
      conv_rhs => rw [← one_mul M]
      exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
    refine ⟨Quotient.mk _ ⟨a, haM, ha0⟩, ?_⟩
    have h2 : (unitRel M).r (Quotient.mk (unitRel M) ⟨a, haM, ha0⟩).out ⟨a, haM, ha0⟩ :=
      Quotient.exact (Quotient.out_eq _)
    have h3 := hf (Quotient.mk (unitRel M) ⟨a, haM, ha0⟩).out
    rw [(key _ _).1 h2] at h3
    simp only at h3
    rw [← ha, mul_assoc, hM, mul_one] at h3
    exact Subtype.ext (Subtype.ext (FractionalIdeal.coeIdeal_injective h3))

theorem card_emb [IsTotallyReal F] : Fintype.card (Emb F) = Module.finrank ℚ F := by
  have h := prod_emb (F := F) (algebraMap ℚ F 2)
  rw [Algebra.norm_algebraMap] at h
  simp only [map_ofNat, Finset.prod_const, Finset.card_univ] at h
  have h' : (2 : ℕ) ^ Fintype.card (Emb F) = 2 ^ Module.finrank ℚ F := by exact_mod_cast h
  exact Nat.pow_right_injective le_rfl h'

theorem eisTerm_zero [IsTotallyReal F] (a : F) :
    eisTerm 2 0 0 (a, 0) = ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F *
      (((|Algebra.norm ℚ a| : ℚ) : ℂ))⁻¹ ^ 2 := by
  have h1 : ∏ τ, latPt (0 : Emb F → ℂ) (a, 0) τ =
      (2 * (Real.pi : ℂ) * I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
    rw [← prod_emb, ← card_emb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [latPt]
  have h2 : (((|Algebra.norm ℚ a| : ℚ) : ℂ))⁻¹ ^ 2 = ((Algebra.norm ℚ a : ℚ) : ℂ)⁻¹ ^ 2 := by
    rw [inv_pow, inv_pow, ← Rat.cast_pow, sq_abs, Rat.cast_pow]
  unfold eisTerm
  rw [h1, h2, mul_zero, cpow_zero, mul_one, mul_inv, mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm 2 (Module.finrank ℚ F)]

theorem aPart_zero [IsTotallyReal F] (𝔞 : Frac F) (C : ClassGroup (𝓞 F)) (D : (Ideal (𝓞 F))⁰) (Za : ℂ → ℂ)
    (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F)) (hC : C * (ClassGroup.mk F 𝔞)⁻¹ = ClassGroup.mk0 D)
    (hZ : IsPartialZeta C Za) :
    aPart 𝔞 0 = ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F * ((dF F : ℂ) * (nrm 𝔞 : ℂ)) ^ 2 * Za 2 := by
  set N : Frac F := FractionalIdeal.mk0 F D * 𝔞 with hN
  have hCN : C = ClassGroup.mk F N := by
    rw [hN, map_mul, ClassGroup.mk_mk0, ← hC, inv_mul_cancel_right]
  have hM : latM 𝔞 * (N : FractionalIdeal (𝓞 F)⁰ F) = 1 := by
    have := (FractionalIdeal.mk0 F D).ne_zero
    rw [FractionalIdeal.coe_mk0] at this
    rw [latM, hN, ← hD, Units.val_mul, FractionalIdeal.coe_mk0, Units.val_inv_eq_inv_val, ← mul_inv,
      inv_mul_cancel₀ (mul_ne_zero this 𝔞.ne_zero)]
  have hnN : ((FractionalIdeal.absNorm (N : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℂ) = (dF F : ℂ) * (nrm 𝔞 : ℂ) := by
    rw [hN, Units.val_mul, FractionalIdeal.coe_mk0, map_mul, FractionalIdeal.coeIdeal_absNorm, hD,
      absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, dF, nrm, ← Int.cast_abs,
      Rat.cast_mul, Rat.cast_intCast, ofReal_intCast, ofReal_ratCast]
  have hn0 : (dF F : ℂ) * (nrm 𝔞 : ℂ) ≠ 0 := by
    rw [← hnN]
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 N.ne_zero)
  subst hCN
  obtain ⟨e, he⟩ := exists_equiv _ N hM
  have hs := (e.hasSum_iff.2 (hZ.2 2 (by norm_num))).mul_left
    (((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F * ((dF F : ℂ) * (nrm 𝔞 : ℂ)) ^ 2)
  rw [← hs.tsum_eq, aPart]
  refine tsum_congr fun c => ?_
  have h1 := congrArg (fun I => ((FractionalIdeal.absNorm I : ℚ) : ℂ)) (he c)
  simp only [map_mul, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, hnN,
    Rat.cast_natCast] at h1
  rw [eisTerm_zero, Function.comp_apply, h1, cpow_neg, cpow_two]
  generalize (dF F : ℂ) * (nrm 𝔞 : ℂ) = x at hn0 ⊢
  generalize ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F = y
  rw [mul_pow, mul_inv, inv_pow, mul_assoc, mul_left_comm (x ^ 2), mul_inv_cancel₀ (pow_ne_zero 2 hn0), mul_one]

theorem gammaR_two : Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
  rw [Gammaℝ_def, show (2 : ℂ) / 2 = 1 by norm_num, show -(2 : ℂ) / 2 = -1 by norm_num, Complex.Gamma_one, cpow_neg_one,
    mul_one]

theorem gammaR_neg_one : Gammaℝ (-1) = -2 * (Real.pi : ℂ) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := Gammaℝ_add_two (s := -1) (by norm_num)
  rw [show (-1 : ℂ) + 2 = 1 by norm_num, Gammaℝ_one] at h
  field_simp at h
  linear_combination h

theorem constant_term : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (C : ClassGroup (NumberField.RingOfIntegers F)) (D : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F))) (Za Za' : ℂ → ℂ), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) → C * (ClassGroup.mk F 𝔞)⁻¹ = ClassGroup.mk0 D → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Za → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Za' → (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Za s = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Za' (1 - s)) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * GlobalTheory.HeckeTwo.aPart 𝔞 0 / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Za' (1 - ((2 : ℕ) : ℂ)) := by
  intro F _ _ _ 𝔞 C D Za Za' hD hC hZ _ hfe
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfe2 := hfe 2 (fun n h => by
      have h' : (2 : ℤ) = -2 * n := by exact_mod_cast h
      omega) (fun n h => by
      have h' : (1 - 2 : ℤ) = -2 * n := by exact_mod_cast h
      omega)
  have hd : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hn : (nrm 𝔞 : ℂ) ≠ 0 := by
    rw [nrm]
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 𝔞.ne_zero)
  set r : ℝ := dF F ^ ((1 : ℝ) / 2) with hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hd _).ne'
  have hrr : (dF F : ℂ) = (r : ℂ) ^ 2 := by
    have : dF F = r ^ 2 := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]; norm_num
    exact_mod_cast this
  have hc : cK F 2 = r := by
    rw [cK, hr]; norm_num
  have hneg : (dF F : ℂ) ^ ((-1 : ℂ) / 2) = (r : ℂ)⁻¹ := by
    rw [hr, ofReal_cpow hd.le, ← cpow_neg]
    congr 1
    push_cast; ring
  rw [show (1 : ℂ) - 2 = -1 by norm_num, show (2 : ℂ) / 2 = 1 by norm_num, cpow_one, hneg, gammaR_two,
    gammaR_neg_one] at hfe2
  rw [show (1 : ℂ) - ((2 : ℕ) : ℂ) = -1 by norm_num, aPart_zero 𝔞 C D Za hD hC hZ, hc, omegaFactor, ← hr]
  have hI : (2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 = 2⁻¹ * (Real.pi : ℂ)⁻¹ * (-2 * (Real.pi : ℂ))⁻¹ := by
    rw [inv_pow, mul_pow, I_sq]; field_simp
  have hg : (-2 * (Real.pi : ℂ)) ^ Module.finrank ℚ F ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) hπ)
  rw [hI, mul_pow, mul_pow, inv_pow (-2 * (Real.pi : ℂ)), hrr]
  rw [hrr] at hfe2
  generalize (-2 * (Real.pi : ℂ)) ^ Module.finrank ℚ F = g at hg hfe2
  generalize ((Real.pi : ℂ)⁻¹) ^ Module.finrank ℚ F = p at hfe2
  generalize ((2 : ℂ)⁻¹) ^ Module.finrank ℚ F = t
  push_cast
  field_simp at hfe2 ⊢
  linear_combination t * hfe2

end GlobalTheory.HeckeTwoConst
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwo_constantTerm_eq_partialZeta_neg_one : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (C : ClassGroup (NumberField.RingOfIntegers F)) (D : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F))) (Za Za' : ℂ → ℂ), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) → C * (ClassGroup.mk F 𝔞)⁻¹ = ClassGroup.mk0 D → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Za → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Za' → (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Za s = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Za' (1 - s)) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * GlobalTheory.HeckeTwo.aPart 𝔞 0 / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Za' (1 - ((2 : ℕ) : ℂ)) := by
  atlas_forward_decl GlobalTheory.HeckeTwoConst.constant_term
end

section
section
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe : GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo := by
  intro hFE F _ _ _ hf 𝔞 𝔟
  have hD0 : (differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) ∈ (Ideal (𝓞 F))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  let D : (Ideal (𝓞 F))⁰ := ⟨_, hD0⟩
  obtain ⟨Zb, Zb', hZb, hZb', hFEb⟩ := hFE F (ClassGroup.mk F 𝔟)⁻¹ (ClassGroup.mk0 D * ClassGroup.mk F 𝔟) D rfl
    (by rw [mul_comm, mul_inv_cancel_right])
  obtain ⟨R, hR, hZR⟩ := GlobalTheory.T.partialZeta_totallyReal_at_most_simple_pole F _ _ Zb Zb' hZb hZb' hFEb
  obtain ⟨Za, Za', hZa, hZa', hFEa⟩ := hFE F (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) (ClassGroup.mk F 𝔞)⁻¹ D rfl
    (mul_inv_cancel_right _ _)
  have hgood : IsGood (gFun Zb 𝔞 𝔟) :=
    GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add F _ _ (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add F _ _ (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_of_sigma_only F _ (GlobalTheory.T.heckeEisensteinConstantTermPart_differentiableOn F 𝔞)) (GlobalTheory.T.heckeEisensteinZeroFrequencyPart_isSmoothHolomorphic F hf 𝔞 𝔟 Zb R hR hZR))
      (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_mul_left F _ _ ((kFac_differentiable.mul_const _).differentiableOn) (GlobalTheory.T.heckeEisensteinNonconstantFourierSum_smoothHolomorphic F 𝔞 𝔟))
  have hdF : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hcK : (cK F 2 : ℂ) ≠ 0 := by
    have : 0 < cK F 2 := by unfold cK; positivity
    exact_mod_cast this.ne'
  have hω : (omegaFactor 𝔞 : ℂ) ≠ 0 := by
    have hn : 0 < nrm 𝔞 := by
      unfold nrm
      have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
      have h3 := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) h2.symm
      exact_mod_cast h3
    have : 0 < omegaFactor 𝔞 := by unfold omegaFactor; positivity
    exact_mod_cast this.ne'
  have hG0 : ∀ z, gFun Zb 𝔞 𝔟 0 z = aPart 𝔞 0 + kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z := by
    intro z; simp [gFun, bZero]
  have hB : ∀ z ∈ upperHalf F, kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z =
      (∑' c, qClass 𝔞 𝔟 2 z c) * (omegaFactor 𝔞 : ℂ) ^ 2 / (cK F 2 : ℂ) := by
    intro z hz
    rw [← (GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).2]
    field_simp
  refine ⟨gFun Zb 𝔞 𝔟, ⟨fun σ hσ z hz => GlobalTheory.T.heckeWeightTwoContinuation_eq_latticeSeries F 𝔞 𝔟 Zb hZb σ hσ z hz, hgood.1, hgood.2⟩, ?_, ?_⟩
  · refine DifferentiableOn.congr (f := fun z => aPart 𝔞 0 + (∑' c, qClass 𝔞 𝔟 2 z c) * ((omegaFactor 𝔞 : ℂ) ^ 2 / (cK F 2 : ℂ)))
      ?_ fun z hz => by rw [hG0, hB z hz, mul_div_assoc]
    apply DifferentiableOn.const_add
    apply DifferentiableOn.mul_const
    exact GlobalTheory.T.differentiableOn_hilbertEisensteinWeightTwoSeries F 𝔞 𝔟
  · refine ⟨Za', hZa', fun z hz => ⟨(GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).1, ?_⟩⟩
    rw [hG0, mul_add, add_div, GlobalTheory.T.heckeWeightTwo_constantTerm_eq_partialZeta_neg_one F 𝔞 _ D Za Za' rfl (mul_inv_cancel_right _ _) hZa hZa' hFEa,
      (GlobalTheory.T.heckeEisenstein_weight_two_qExpansion F 𝔞 𝔟 z hz).2]
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo := by
  atlas_forward_decl GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe
end
