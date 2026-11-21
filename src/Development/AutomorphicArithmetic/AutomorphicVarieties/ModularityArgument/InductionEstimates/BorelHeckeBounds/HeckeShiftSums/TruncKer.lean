import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.UnipMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.OmMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.MainBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.ContinuousLeviUnipotentPath
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PairFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TruncEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SgBasics
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpqMinor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.BlkCont
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.NormLeOfSq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.HsOfKer

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.HeckeShiftDescent

private theorem mk_shift {G : Type*} [Group G] (P : Subgroup G) (a b : G) :
    (Quotient.mk (QuotientGroup.rightRel P) ((Quotient.mk (QuotientGroup.rightRel P) a).out * b)) =
      Quotient.mk (QuotientGroup.rightRel P) (a * b) := by
  have h : (QuotientGroup.rightRel P) ((Quotient.mk (QuotientGroup.rightRel P) a).out) a :=
    Quotient.mk_out (s := QuotientGroup.rightRel P) a
  refine Quotient.sound ?_
  change (QuotientGroup.rightRel P) _ _
  rw [QuotientGroup.rightRel_apply] at h ⊢
  simpa [mul_assoc] using h

private theorem shift_bij {G : Type*} [Group G] (P : Subgroup G) (b : G) :
    Function.Bijective fun q : Quotient (QuotientGroup.rightRel P) =>
      Quotient.mk (QuotientGroup.rightRel P) (q.out * b) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun q => Quotient.mk (QuotientGroup.rightRel P) (q.out * b⁻¹), fun q => ?_, fun q => ?_⟩
  · simp only [mk_shift, mul_inv_cancel_right, Quotient.out_eq]
  · simp only [mk_shift, inv_mul_cancel_right, Quotient.out_eq]

variable {K : Type} [Field K] [NumberField K]

private theorem sum_shift {M : Type*} [AddCommMonoid M] (F : G1 K (2 + 2) → M)
    (hP : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) (γ : G1 K (2 + 2)) (hγ : γ ∈ Gam K (2 + 2))
    (g : G1 K (2 + 2)) :
    ∑ᶠ q : Cos K, F ((q.out : G1 K (2 + 2)) * (γ * g)) = ∑ᶠ q : Cos K, F ((q.out : G1 K (2 + 2)) * g) := by
  have hout : ∀ (c : Gam K (2 + 2)) (g : G1 K (2 + 2)),
      F ((((Quotient.mk _ c : Cos K).out : Gam K (2 + 2)) : G1 K (2 + 2)) * g) = F (c * g) := fun c g => by
    obtain ⟨δ, hδ, h⟩ := (pkLaws (K := K)).2.2.2 c
    rw [h, mul_assoc, hP δ hδ]
  refine finsum_eq_of_bijective _ (shift_bij (ParΓ K 2 2) ⟨γ, hγ⟩) fun q => ?_
  rw [hout, Subgroup.coe_mul, mul_assoc]

private theorem desc_cont {Y : Type*} [TopologicalSpace Y] (f : G1 K (2 + 2) → Y) (hc : Continuous f)
    (hi : ∀ γ ∈ Gam K (2 + 2), ∀ x, f (γ * x) = f x) :
    Continuous fun y : RightCosetSpace (Gam K (2 + 2)) => f (Quotient.out y) := by
  rw [(isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.continuous_iff]
  have : (fun y : RightCosetSpace (Gam K (2 + 2)) => f (Quotient.out y)) ∘ mk (Gam K (2 + 2)) = f := funext fun g => by
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Gam K (2 + 2)) (g := (mk (Gam K (2 + 2)) g).out) (h := g)).1 (Quotient.out_eq _)
    change f _ = _
    rw [← hγ]
    exact hi γ γ.2 g
  rwa [this]

private theorem desc_sm {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    (f : G1 K (2 + 2) → Y) (hc : Continuous f) (hi : ∀ γ ∈ Gam K (2 + 2), ∀ x, f (γ * x) = f x) :
    StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => f (Quotient.out y) := by
  haveI : SecondCountableTopology (RightCosetSpace (Gam K (2 + 2))) :=
    (isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.secondCountableTopology
      (isOpenQuotientMap_mk (Gam K (2 + 2))).isOpenMap
  exact (desc_cont f hc hi).stronglyMeasurable

private noncomputable def ramp (T : ℝ) (n : ℕ) (h : ℝ) : ℝ := max 0 (min 1 (((n : ℝ) + 1) * (h - T)))

private theorem ramp_cont (T : ℝ) (n : ℕ) : Continuous (ramp T n) := by
  unfold ramp
  fun_prop

private theorem ramp_zero {T h : ℝ} (n : ℕ) (hh : h ≤ T) : ramp T n h = 0 := by
  have : ((n : ℝ) + 1) * (h - T) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 hh)
  exact max_eq_left ((min_le_right _ _).trans this)

private theorem ramp_lim (T h : ℝ) :
    Tendsto (fun n : ℕ => ((ramp T n h : ℝ) : ℂ)) atTop (𝓝 (if T < h then 1 else 0)) := by
  split_ifs with hh
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (h - T))
    have hp : 0 < h - T := sub_pos.2 hh
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : 1 ≤ ((n : ℝ) + 1) * (h - T) := by
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_lt_iff₀ hp] at hN
      nlinarith
    have : ramp T n h = 1 := by
      unfold ramp
      rw [min_eq_left h1]
      exact max_eq_right zero_le_one
    rw [this]
    simp
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [ramp_zero n (not_lt.1 hh)]
    simp

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.HeckeShiftDescent

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.HeckeShiftDescent in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.kT :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (a : CC K (2 + 2)) (T : ℝ), ∃ kk : G1 K (2 + 2) → L2 μ,
      (∀ x φ, ⟪kk x, φ⟫_ℂ = lam T (rc μ a φ) x) ∧ (∀ γ ∈ Gam K (2 + 2), ∀ x, kk (γ * x) = kk x) ∧ (∀ x, Om T x → kk x = kv μ a x) ∧
      StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => kk (Quotient.out y) := by
  intro K _ _ μ _ a T
  obtain ⟨kc, hkc, hin⟩ := (ctKv μ a).1 2
  have hlaw := (ctKv μ a).2
  have hH := hpSpec (K := K)
  have hkP : ∀ γ ∈ PK K, ∀ z, kc (γ * z) = kc z := fun γ hγ z =>
    ext_inner_right ℂ fun φ => by rw [hin, hin, (hlaw φ).2.2.2.1 γ hγ z]

  let A : (ℝ → ℂ) → G1 K (2 + 2) → L2 μ := fun w x =>
    kv μ a x - ∑ᶠ q : Cos K, w (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x)
  have hAinv : ∀ w, ∀ γ ∈ Gam K (2 + 2), ∀ x, A w (γ * x) = A w x := fun w γ hγ x => by
    have h1 := (ropAe K (2 + 2) μ a).2 γ hγ x
    have h2 := sum_shift (K := K) (fun g => w (HH g) • kc g)
      (fun δ hδ g => by simp only [hkP δ hδ g, hH.2.2.1 δ hδ g]) γ hγ x
    simp only [A, h1, h2]
  let ind : ℝ → ℂ := fun h => if T < h then 1 else 0

  have hfin : ∀ x : G1 K (2 + 2), {q : Cos K | T ≤ HH ((q.out : G1 K (2 + 2)) * x)}.Finite := fun x =>
    (locFin {x} T isCompact_singleton).subset fun q hq => ⟨x, rfl, hq⟩
  have hsupp : ∀ (w : ℝ → ℂ), (∀ h, h < T → w h = 0) → ∀ x : G1 K (2 + 2),
      (Function.support fun q : Cos K => w (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x)) ⊆
        {q : Cos K | T ≤ HH ((q.out : G1 K (2 + 2)) * x)} := fun w hw x q hq => by
    by_contra hlt
    exact hq (by beta_reduce; rw [hw _ (not_le.1 hlt), zero_smul])
  have hind : ∀ h, h < T → ind h = 0 := fun h hh => if_neg (not_lt.2 hh.le)
  have hrz : ∀ n : ℕ, ∀ h, h < T → ((ramp T n h : ℝ) : ℂ) = 0 := fun n h hh => by
    rw [ramp_zero n hh.le]
    simp
  refine ⟨A ind, fun x φ => ?_, hAinv ind, fun x hx => ?_, ?_⟩
  · let ip : L2 μ →+ ℂ :=
      { toFun := fun v => ⟪v, φ⟫_ℂ, map_zero' := inner_zero_left _, map_add' := fun u v => inner_add_left _ _ _ }
    have hsum : ⟪∑ᶠ q : Cos K, ind (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x), φ⟫_ℂ =
        ∑ᶠ q : Cos K, ⟪ind (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x), φ⟫_ℂ :=
      ip.map_finsum ((hfin x).subset (hsupp ind hind x))
    simp only [A, inner_sub_left, inner_kv, hsum, lam, th, hi]
    congr 1
    refine finsum_congr fun q => ?_
    rw [inner_smul_left, hin]
    by_cases h : T < HH ((q.out : G1 K (2 + 2)) * x)
    · simp [ind, h]
    · simp [ind, h]
  · have : ∀ q : Cos K, ind (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x) = 0 := fun q => by
      have : ind (HH ((q.out : G1 K (2 + 2)) * x)) = 0 := if_neg (not_lt.2 (hx q))
      rw [this, zero_smul]
    simp only [A, this, finsum_zero, sub_zero]
  ·
    have hcont : ∀ n : ℕ, Continuous (A fun h => ((ramp T n h : ℝ) : ℂ)) := fun n => by
      refine (kvCont K (2 + 2) μ a).sub (continuous_finsum (fun q => ?_) fun x => ?_)
      · have hm : Continuous fun x : G1 K (2 + 2) => (q.out : G1 K (2 + 2)) * x :=
          continuous_const.mul continuous_id
        exact (Complex.continuous_ofReal.comp ((ramp_cont T n).comp (hH.2.2.2.1.comp hm))).smul (hkc.comp hm)
      · obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
        refine ⟨C, hx, (locFin C T hC).subset fun q ⟨g, hg, hgC⟩ => ⟨g, hgC, ?_⟩⟩
        exact hsupp _ (hrz n) g hg
    have hdesc : ∀ n : ℕ, StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) =>
        A (fun h => ((ramp T n h : ℝ) : ℂ)) (Quotient.out y) := fun n =>
      desc_sm (A fun h => ((ramp T n h : ℝ) : ℂ)) (hcont n) (hAinv fun h => ((ramp T n h : ℝ) : ℂ))
    refine stronglyMeasurable_of_tendsto atTop hdesc (tendsto_pi_nhds.2 fun y => ?_)
    set x : G1 K (2 + 2) := Quotient.out y
    have e : ∀ w : ℝ → ℂ, (∀ h, h < T → w h = 0) →
        A w x = kv μ a x - ∑ q ∈ (hfin x).toFinset, w (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x) := fun w hw => by
      simp only [A]
      rw [finsum_eq_sum_of_support_subset (s := (hfin x).toFinset) _ (by rw [Set.Finite.coe_toFinset]; exact hsupp w hw x)]
    simp only [e _ (hrz _), e ind hind]
    refine tendsto_const_nhds.sub (tendsto_finset_sum _ fun q _ => ?_)
    exact (ramp_lim T _).smul_const _
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private def chi (T : ℝ) (n : ℕ) (x : ℝ) : ℝ := max 0 (min (min 1 ((n + 1) * (x - T))) (T + n + 2 - x))

private theorem chi_cont (T : ℝ) (n : ℕ) : Continuous (chi T n) := by
  unfold chi
  fun_prop

private theorem chi_low (T : ℝ) (n : ℕ) {x : ℝ} (h : x ≤ T) : chi T n x = 0 := by
  unfold chi
  refine max_eq_left ?_
  have : ((n : ℝ) + 1) * (x - T) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  exact (min_le_left _ _).trans ((min_le_right _ _).trans this)

private theorem chi_high (T : ℝ) (n : ℕ) {x : ℝ} (h : T + n + 2 ≤ x) : chi T n x = 0 := by
  unfold chi
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

private theorem chi_nonneg (T : ℝ) (n : ℕ) (x : ℝ) : 0 ≤ chi T n x := le_max_left _ _

private theorem chi_le (T : ℝ) (n : ℕ) (x : ℝ) : chi T n x ≤ 1 :=
  max_le zero_le_one ((min_le_left _ _).trans (min_le_left _ _))

private theorem chi_supp (T : ℝ) (n : ℕ) : HasCompactSupport (chi T n) :=
  HasCompactSupport.intro (isCompact_Icc (a := T) (b := T + n + 2)) fun x hx => by
    rcases le_or_gt x T with h | h
    · exact chi_low T n h
    · exact chi_high T n (by
        by_contra h'
        exact hx ⟨h.le, (not_le.1 h').le⟩)

private theorem chi_one (T : ℝ) {x : ℝ} (h : T < x) : ∀ᶠ n : ℕ in atTop, chi T n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (1 / (x - T)) (x - T))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hp : 0 < x - T := sub_pos.2 h
  have hn' : (N : ℝ) ≤ n := Nat.cast_le.2 hn
  have h1 : 1 / (x - T) ≤ n := ((le_max_left _ _).trans hN).trans hn'
  have h2 : x - T ≤ n := ((le_max_right _ _).trans hN).trans hn'
  have h3 : 1 ≤ ((n : ℝ) + 1) * (x - T) := by
    have := (div_le_iff₀ hp).1 h1
    nlinarith
  unfold chi
  rw [min_eq_left h3, min_eq_left (by linarith)]
  exact max_eq_right zero_le_one

private theorem sum_ae {α ι E : Type*} {m : MeasurableSpace α} {ν : Measure α} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → Lp E 2 ν) :
    ∀ᵐ x ∂ν, ((∑ i ∈ s, f i : Lp E 2 ν) : α → E) x = ∑ i ∈ s, (f i : α → E) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero E 2 ν] with x hx
    rw [Finset.sum_empty, hx]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

private theorem eu_sum {d : ℕ} (v : Eu d) : ∑ i, v i • (EuclideanSpace.single i (1 : ℂ) : Eu d) = v := by
  have := (EuclideanSpace.basisFun (Fin d) ℂ).sum_repr v
  simpa using this

private theorem ae_down {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (w : L2 μ)
    (E : Set (RightCosetSpace (Gam K (2 + 2)))) (hE : MeasurableSet E)
    (h : ∀ᵐ y ∂μ, mk (Gam K (2 + 2)) y ∈ E →
      (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = 0) :
    ∀ᵐ p ∂quotientMeasure (Gam K (2 + 2)) μ, p ∈ E → (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) p = 0 := by
  have hm : MeasurableSet (E ∩ {p | (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) p ≠ 0}) :=
    hE.inter ((Lp.stronglyMeasurable w).measurable (measurableSet_singleton 0).compl)
  have h0 : ∫⁻ p, (E ∩ {p | (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) p ≠ 0}).indicator 1 p
      ∂quotientMeasure (Gam K (2 + 2)) μ = 0 := by
    rw [lintegral_quotientMeasure]
    refine (lintegral_congr_ae (g := 0) (ae_restrict_of_ae ?_)).trans (by simp)
    filter_upwards [h] with y hy
    exact indicator_of_notMem (fun hA => hA.2 (hy hA.1)) _
  rw [lintegral_indicator_one hm] at h0
  exact ae_iff.2 (measure_mono_null (fun p hp => _root_.not_imp.1 hp) h0)

private theorem first {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d)
    (T : ℝ) (c : L (Eu d)) (hc : ∀ᵐ x : ℝ, x ≤ T → c x = 0) :
    ∀ᵐ y ∂μ, Om T y → (A.J c : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = 0 := by
  let E : Set (RightCosetSpace (Gam K (2 + 2))) := {p | Om T (Quotient.out p : G1 K (2 + 2))}
  have hEm : MeasurableSet E := (omMeas T).2.2
  have hmk : ∀ y : G1 K (2 + 2), mk (Gam K (2 + 2)) y ∈ E ↔ Om T y := fun y => by
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk (Gam K (2 + 2)) y))
    change Om T (Quotient.out (RightCosetSpace.mk (Gam K (2 + 2)) y)) ↔ Om T y
    rw [← hγ]
    exact (omMeas T).1 _ γ.2 y
  let R := LpToLpRestrictCLM (RightCosetSpace (Gam K (2 + 2))) ℂ ℂ (quotientMeasure (Gam K (2 + 2)) μ) 2 E
  have hR : ∀ w : L2 μ, R w = 0 ↔ ∀ᵐ p ∂quotientMeasure (Gam K (2 + 2)) μ, p ∈ E →
      (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) p = 0 := fun w => by
    rw [Lp.eq_zero_iff_ae_eq_zero, ← ae_restrict_iff' hEm]
    constructor
    · intro h
      filter_upwards [h, LpToLpRestrictCLM_coeFn ℂ E w] with p h1 h2
      rw [← h2, h1]
      rfl
    · intro h
      filter_upwards [h, LpToLpRestrictCLM_coeFn ℂ E w] with p h1 h2
      rw [h2, h1]
      rfl
  let Φ := R.comp A.J.toContinuousLinearMap
  let Sp : Submodule ℂ (L (Eu d)) := LinearMap.ker Φ.toLinearMap
  have hcl : IsClosed (Sp : Set (L (Eu d))) := by
    have : (Sp : Set (L (Eu d))) = {x | Φ x = 0} := by
      ext x
      simp [Sp]
    rw [this]
    exact isClosed_eq Φ.continuous continuous_const
  have hsub : Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d), Continuous β ∧ HasCompactSupport β ∧
      (∀ x, x ≤ T → β x = 0) ∧ ∀ᵐ x : ℝ, u x = β x • v} ≤ Sp := by
    refine Submodule.span_le.2 ?_
    rintro g ⟨β, v, h1, h2, h3, h4⟩
    refine (hR (A.J g)).2 (ae_down μ _ E hEm ?_)
    filter_upwards [A.spec β v g h1 h2 h4] with y hy hyE
    rw [hy]
    unfold theta
    refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
    rw [h3 _ ((hmk y).1 hyE q), zero_mul, zero_mul]
  have hin := closure_mono hsub ((denseCc d).2.2 T c hc)
  rw [hcl.closure_eq] at hin
  have hz : R (A.J c) = 0 := hin
  filter_upwards [(quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae ((hR _).1 hz)] with y hy hO
  exact hy ((hmk y).2 hO)

private theorem th_chi {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d)
    (T : ℝ) (U : ℝ → Eu d) (χ : ℝ → ℝ) (h0 : ∀ x ≤ T, χ x = 0) (y : G1 K (2 + 2)) :
    ∑ i, theta (fun x => (χ x : ℂ) * U x i) (A.sec (EuclideanSpace.single i (1 : ℂ))) y =
      th (fun z => (χ (HH z) : ℂ) * secF A.sec U z) y := by
  have fin : ∀ i : Fin d, (Function.support fun q : Cos K =>
      bf (fun x => (χ x : ℂ) * U x i) (A.sec (EuclideanSpace.single i (1 : ℂ))) ((q.out : G1 K (2 + 2)) * y)).Finite := fun i => by
    refine (locFin {y} T isCompact_singleton).subset fun q hq => ⟨y, rfl, ?_⟩
    by_contra hlt
    apply hq
    have e : χ (HP 2 2 ((q.out : G1 K (2 + 2)) * y)) = 0 := h0 _ (not_le.1 hlt).le
    simp only [bf, e]
    simp
  simp only [theta_eq]
  unfold th
  rw [← finsum_sum_comm _ _ fun i _ => fin i]
  refine finsum_congr fun q => ?_
  generalize ((q.out : G1 K (2 + 2)) * y) = z
  have hs : A.sec (U (HH z)) z = ∑ i, U (HH z) i * A.sec (EuclideanSpace.single i (1 : ℂ)) z := by
    conv_lhs => rw [← eu_sum (U (HH z))]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
  have ex : ((((2 + 2 : ℕ) : ℝ) / 2 * HP 2 2 z : ℝ) : ℂ) = 2 * (HH z : ℂ) := by
    push_cast
    ring
  simp only [bf, secF, ex, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem rep_chi {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d)
    (T : ℝ) (U : ℝ → Eu d) (hU : Continuous U) (χ : ℝ → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (h0 : ∀ x ≤ T, χ x = 0) :
    ∃ w : L (Eu d), (∀ᵐ x : ℝ, w x = (χ x : ℂ) • U x) ∧
      Reps μ (A.J w) (th fun z => (χ (HH z) : ℂ) * secF A.sec U z) := by
  have hβ : ∀ i : Fin d, Continuous fun x => (χ x : ℂ) * U x i := fun i =>
    (Complex.continuous_ofReal.comp hχ).mul ((EuclideanSpace.proj i : Eu d →L[ℂ] ℂ).continuous.comp hU)
  have hβc : ∀ i : Fin d, HasCompactSupport fun x => (χ x : ℂ) * U x i := fun i =>
    (hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_right
  have hex := fun i => (denseCc d).2.1 _ (EuclideanSpace.single i (1 : ℂ)) (hβ i) (hβc i)
  choose u hu using hex
  refine ⟨∑ i, u i, ?_, ?_⟩
  · filter_upwards [sum_ae Finset.univ u, ae_all_iff.2 hu] with x h1 h2
    rw [h1, Finset.sum_congr rfl fun i _ => h2 i]
    simp only [mul_smul, ← Finset.smul_sum, eu_sum]
  · have h2 := ae_all_iff.2 fun i => A.spec _ _ (u i) (hβ i) (hβc i) (hu i)
    have h3 := (quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae (sum_ae Finset.univ fun i => A.J (u i))
    unfold Reps
    filter_upwards [h2, h3] with y a b
    rw [map_sum, b, Finset.sum_congr rfl fun i _ => a i]
    exact th_chi μ A T U χ h0 y

private theorem th_lim {K : Type} [Field K] [NumberField K] (T : ℝ) (G : G1 K (2 + 2) → ℂ) (y : G1 K (2 + 2)) :
    ∀ᶠ n : ℕ in atTop, th (fun z => (chi T n (HH z) : ℂ) * G z) y = th (hi T G) y := by
  have h1 := (Filter.eventually_all_finite (l := (atTop : Filter ℕ)) (locFin {y} T isCompact_singleton)
    (p := fun q n => (chi T n (HH ((q.out : G1 K (2 + 2)) * y)) : ℂ) * G ((q.out : G1 K (2 + 2)) * y) =
      hi T G ((q.out : G1 K (2 + 2)) * y))).2 fun q _ => by
    by_cases h : T < HH ((q.out : G1 K (2 + 2)) * y)
    · filter_upwards [chi_one T h] with n hn
      rw [hn, hi, indicator_of_mem (show _ ∈ {z | T < HH z} from h)]
      simp
    · refine Eventually.of_forall fun n => ?_
      rw [chi_low T n (not_lt.1 h), hi, indicator_of_notMem (show _ ∉ {z | T < HH z} from h)]
      simp
  filter_upwards [h1] with n hn
  unfold th
  refine finsum_congr fun q => ?_
  by_cases hq : T ≤ HH ((q.out : G1 K (2 + 2)) * y)
  · exact hn q ⟨y, rfl, hq⟩
  · have h' : ¬ T < HH ((q.out : G1 K (2 + 2)) * y) := fun h => hq h.le
    beta_reduce
    rw [chi_low T n (not_lt.1 h'), hi, indicator_of_notMem (show _ ∉ {z | T < HH z} from h')]
    simp

private theorem nsq {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (u : L V) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner u u)]
  simp only [inner_self_eq_norm_sq]

private theorem cut_lim {d : ℕ} (T : ℝ) (u c : L (Eu d)) (w : ℕ → L (Eu d))
    (hc : ∀ᵐ x : ℝ, c x = (Ioi T).indicator u x) (hw : ∀ n, ∀ᵐ x : ℝ, w n x = (chi T n x : ℂ) • u x) :
    Tendsto w atTop (𝓝 c) := by
  have hall := ae_all_iff.2 hw
  have hae : ∀ n, ∀ᵐ x : ℝ, ‖(w n - c : L (Eu d)) x‖ ^ 2 ≤ ‖u x‖ ^ 2 := fun n => by
    filter_upwards [Lp.coeFn_sub (w n) c, hc, hw n] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    by_cases h : T < x
    · rw [indicator_of_mem (show x ∈ Ioi T from h)]
      have e : ((chi T n x : ℂ) • u x - u x) = ((chi T n x - 1 : ℝ) : ℂ) • u x := by
        push_cast
        rw [sub_smul, one_smul]
      rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [abs_le]
      constructor <;> linarith [chi_nonneg T n x, chi_le T n x]
    · rw [indicator_of_notMem (show x ∉ Ioi T from h), chi_low T n (not_lt.1 h)]
      simp
  have hlim : ∀ᵐ x : ℝ, Tendsto (fun n => ‖(w n - c : L (Eu d)) x‖ ^ 2) atTop (𝓝 0) := by
    have hsub := ae_all_iff.2 fun n => Lp.coeFn_sub (w n) c
    filter_upwards [hsub, hc, hall] with x h1 h2 h3
    refine tendsto_const_nhds.congr' ?_
    by_cases h : T < x
    · filter_upwards [chi_one T h] with n hn
      beta_reduce
      rw [h1 n, Pi.sub_apply, h2, h3 n, hn, indicator_of_mem (show x ∈ Ioi T from h)]
      simp
    · refine Eventually.of_forall fun n => ?_
      beta_reduce
      rw [h1 n, Pi.sub_apply, h2, h3 n, indicator_of_notMem (show x ∉ Ioi T from h), chi_low T n (not_lt.1 h)]
      simp
  have hi2 : Integrable fun x => ‖u x‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have h1 := tendsto_integral_of_dominated_convergence (F := fun n x => ‖(w n - c : L (Eu d)) x‖ ^ 2) (f := fun _ => 0)
    (fun x => ‖u x‖ ^ 2) (fun n => (Lp.aestronglyMeasurable (w n - c)).norm.pow 2) hi2
    (fun n => by
      filter_upwards [hae n] with x hx
      rwa [Real.norm_of_nonneg (sq_nonneg _)]) hlim
  have h3 : (fun n => ∫ x, ‖(w n - c : L (Eu d)) x‖ ^ 2) = fun n => ‖w n - c‖ ^ 2 := funext fun n => (nsq _).symm
  rw [h3, integral_zero] at h1
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
  rw [Real.sqrt_zero] at h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact h2.congr fun n => by
    rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cutRep :
    ForAllC fun K _ _ μ _ _ _ _ _ _ d _ A _ => ∀ (T : ℝ) (u : L (Eu d)), (∀ᵐ y ∂μ, Om T y → (A.J (cut (Eu d) (Ioi T) u) : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = 0) ∧
      ∀ U : ℝ → Eu d, Continuous U → (∀ᵐ s : ℝ, u s = U s) → Reps μ (A.J (cut (Eu d) (Ioi T) u)) (th (hi T (secF A.sec U))) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' T u
  have hc := cutSpec (V := Eu d) (Ioi T) measurableSet_Ioi u
  refine ⟨first μ A T _ ?_, fun U hU hu => ?_⟩
  · filter_upwards [hc] with x hx h
    rw [hx]
    exact indicator_of_notMem (fun h' : x ∈ Ioi T => not_lt.2 h h') _
  have hex := fun n : ℕ => rep_chi μ A T U hU (chi T n) (chi_cont T n) (chi_supp T n) fun x hx => chi_low T n hx
  choose w hw hr using hex
  have hlim : Tendsto w atTop (𝓝 (cut (Eu d) (Ioi T) u)) := cut_lim T u _ w hc fun n => by
    filter_upwards [hw n, hu] with x h1 h2
    rw [h1, h2]
  have hJ : Tendsto (fun n => A.J (w n)) atTop (𝓝 (A.J (cut (Eu d) (Ioi T) u))) :=
    (A.J.continuous.tendsto _).comp hlim
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hJ).exists_seq_tendsto_ae
  have h1 := (quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae hae
  have h2 := ae_all_iff.2 hr
  unfold Reps
  filter_upwards [h1, h2] with y a b
  refine tendsto_nhds_unique a (tendsto_const_nhds.congr' ?_)
  filter_upwards [hns.tendsto_atTop.eventually (th_lim T (secF A.sec U) y)] with i hi'
  rw [b (ns i), hi']
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem fix_of {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (J : V →L[ℂ] H) (P : H →L[ℂ] H)
    (h1 : IsSelfAdjoint P) (h2 : P ∘L P = P) (h3 : ∀ h, P h = 0 → ∀ u, ⟪J u, h⟫_ℂ = 0) :
    (∀ u, P (J u) = J u) ∧ ∀ h, ContinuousLinearMap.adjoint J (P h) = ContinuousLinearMap.adjoint J h := by
  have a : ∀ u, P (J u) = J u := fun u => by
    have k : P (J u - P (J u)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact (DFunLike.congr_fun h2 (J u)).symm
    have e : ⟪J u - P (J u), J u - P (J u)⟫_ℂ = 0 := by
      rw [inner_sub_left, h3 _ k, h1.isSymmetric.apply_clm, k, inner_zero_right, sub_zero]
    exact (sub_eq_zero.1 (inner_self_eq_zero.1 e)).symm
  refine ⟨a, fun h => ext_inner_left ℂ fun u => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ← h1.isSymmetric.apply_clm, a]

private theorem cut_van {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (T : ℝ) (u : L V) : ∀ᵐ x : ℝ, x ≤ T → cut V (Ioi T) u x = 0 := by
  have c := cutLaws (V := V) (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi
  have e : cut V (Ioi T) (cut V (Ioi T) u) = cut V (Ioi T) u := by
    have := DFunLike.congr_fun c.1 u
    rwa [inter_self] at this
  filter_upwards [(c.2.2.2.2.2.2.2.1 _).1 e] with x hx h
  exact hx (not_lt.2 h)

private theorem th_hi_add {K : Type} [Field K] [NumberField K] (T : ℝ) (F F₁ F₂ : G1 K (2 + 2) → ℂ)
    (h : ∀ z, F z = F₁ z + F₂ z) (x : G1 K (2 + 2)) : th (hi T F) x = th (hi T F₁) x + th (hi T F₂) x := by
  have fin : ∀ G : G1 K (2 + 2) → ℂ,
      (Function.support fun q : Cos K => hi T G ((q.out : G1 K (2 + 2)) * x)).Finite := fun G => by
    refine (locFin {x} T isCompact_singleton).subset fun q hq => ⟨x, rfl, ?_⟩
    have h1 : ((q.out : G1 K (2 + 2)) * x) ∈ {z : G1 K (2 + 2) | T < HH z} :=
      Set.mem_of_indicator_ne_zero (f := G) hq
    exact le_of_lt h1
  unfold th
  rw [← finsum_add_distrib (fin F₁) (fin F₂)]
  refine finsum_congr fun q => ?_
  have : F = F₁ + F₂ := funext h
  subst this
  unfold hi
  rw [Set.indicator_add']
  rfl

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.lamRep :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ (P Λ : L2 μ →L[ℂ] L2 μ) (T : ℝ), IsOrthogonalProjectionTwoLines A.J A'.J P → 0 ≤ T → IsTrunc A.J A'.J T Λ →
      Λ ∘L P = P ∘L Λ ∧ (∀ w : L2 μ, ∀ᵐ y ∂μ, Om T y → (Λ w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) =
        (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y)) ∧
      ∀ a : CC K (2 + 2), D.Hecke a → ∀ φ, P φ = φ → Reps μ (Λ (Rop μ a φ)) (lam T (rc μ a φ)) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' P Λ T hP hT hΛ
  have hp' : Pair μ₂ τ₂ τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  have hc := (pairFacts K μ μ₂ τ₁ τ₂ hp D d d' A A').2
  have ho : ∀ u v, ⟪A.J (cut (Eu d) (Ioi T) u), A'.J (cut (Eu d') (Ioi T) v)⟫_ℂ = 0 := fun u v => by
    refine hc T _ _ (cut_van T u) ?_
    filter_upwards [cut_van T v] with x hx h
    exact hx (by linarith)
  have hL := (truncEq A.J A'.J T Λ ho).1 hΛ
  have hv : ∀ w, Λ w = w - A.J (cut (Eu d) (Ioi T) (Jd A.J w)) - A'.J (cut (Eu d') (Ioi T) (Jd A'.J w)) := fun w => by
    rw [hL]; rfl
  have hae : ∀ w : L2 μ, ∀ᵐ y ∂μ, (Λ w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) =
      (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) -
      (A.J (cut (Eu d) (Ioi T) (Jd A.J w)) : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) -
      (A'.J (cut (Eu d') (Ioi T) (Jd A'.J w)) : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) := fun w => by
    rw [hv w]
    filter_upwards [(quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae (Lp.coeFn_sub
        (w - A.J (cut (Eu d) (Ioi T) (Jd A.J w))) (A'.J (cut (Eu d') (Ioi T) (Jd A'.J w)))),
      (quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae (Lp.coeFn_sub w (A.J (cut (Eu d) (Ioi T) (Jd A.J w))))] with y e1 e2
    rw [e1, Pi.sub_apply, e2, Pi.sub_apply]
  obtain ⟨f1, g1⟩ := fix_of A.J.toContinuousLinearMap P hP.1 hP.2.1 fun h hh => ((hP.2.2 h).1 hh).1
  obtain ⟨f2, g2⟩ := fix_of A'.J.toContinuousLinearMap P hP.1 hP.2.1 fun h hh => ((hP.2.2 h).1 hh).2
  have c1 := cutRep K μ μ₂ τ₁ τ₂ hp D d d' A A' T
  have c2 := cutRep K μ μ₂ τ₂ τ₁ hp' D d' d A' A T
  refine ⟨ContinuousLinearMap.ext fun h => ?_, fun w => ?_, fun a ha φ hφ => ?_⟩
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hv, hv, map_sub, map_sub]
    have a1 := f1 (cut (Eu d) (Ioi T) (Jd A.J h))
    have a2 := f2 (cut (Eu d') (Ioi T) (Jd A'.J h))
    have b1 : Jd A.J (P h) = Jd A.J h := g1 h
    have b2 : Jd A'.J (P h) = Jd A'.J h := g2 h
    rw [LinearIsometry.coe_toContinuousLinearMap] at a1 a2
    rw [a1, a2, b1, b2]
  · filter_upwards [hae w, (c1 (Jd A.J w)).1, (c2 (Jd A'.J w)).1] with y e e1 e2 hy
    rw [e, e1 hy, e2 hy, sub_zero, sub_zero]
  · obtain ⟨C, hC⟩ := ctRep K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP ha
    obtain ⟨U, U', hU, hU', -, r1, r2, hct⟩ := hC φ hφ
    filter_upwards [hae (Rop μ a φ), (c1 _).2 U hU r1, (c2 _).2 U' hU' r2, ((ctKv μ a).2 φ).2.1] with y e e1 e2 e3
    rw [e, e1, e2, e3, lam, th_hi_add T _ _ _ hct, sub_sub]
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem omBd_real (a : Fin (2 + 2) → ℝ) (s C T : ℝ) (hs : 0 ≤ s) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (h0 : a 1 ≤ a 0 + s) (h1 : a 2 ≤ a 1 + s) (h2 : a 3 ≤ a 2 + s) (h3 : a 0 + a 1 ≤ T + C)
    (h4 : -C ≤ a 0 + a 1 + (a 2 + a 3)) (i j : Fin (2 + 2)) : a i - a j ≤ 4 * T + 20 * (C + s) := by
  have key : ∀ i : Fin (2 + 2), a i ≤ 2 * T + 10 * (C + s) ∧ -(2 * T + 10 * (C + s)) ≤ a i := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl <;> constructor <;> linarith
  linarith [(key i).1, (key j).2]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.omBd :
    ∀ {K : Type} [Field K] [NumberField K], ∃ (C c : ℝ) (N : ℕ), 0 < c ∧ 0 ≤ C ∧ ∀ (T : ℝ) (x : G1 K (2 + 2)), 0 ≤ T → (Om T x → qht x ≤ C * Real.exp (N * T)) ∧ (¬ Om T x → Real.exp (c * T - C) ≤ qht x) := by
  intro K _ _
  obtain ⟨ω, t, hred⟩ := redEx (K := K)
  obtain ⟨C, c, hC, hsg⟩ := sgBasics ω hred.bor
  obtain ⟨c', C', hc', hq⟩ := hpQht (K := K)
  obtain ⟨hq1, hqinv, -⟩ := qhtBasic K (2 + 2)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  set s : ℝ := |Real.log t| with hsdef
  have hs : 0 ≤ s := abs_nonneg _
  set A : ℝ := C * Real.exp (c * (20 * (C + s))) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A + |C' / c'|, c'⁻¹, 4 * c, inv_pos.2 hc', by positivity, fun T x hT => ⟨fun hom => ?_, fun hom => ?_⟩⟩
  · obtain ⟨γ, hγ, ρ, hS, hF⟩ := hred.full x
    obtain ⟨h1, h2, h3⟩ := hsg ρ _ hS
    obtain ⟨hρ, -⟩ := hS
    have hH : HH (γ * x) ≤ T := by
      obtain ⟨δ, hδ, e⟩ := (pkLaws (K := K)).2.2.2 ⟨γ, hγ⟩
      have h := hom (Quotient.mk _ ⟨γ, hγ⟩)
      unfold qx at h
      rw [e, mul_assoc, (hpSpec (K := K)).2.2.1 δ hδ] at h
      exact h
    have hd : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
    have hL : Real.log (ρ 0 * ρ 1) ≤ T + C := by
      have h4 := (abs_le.1 h1).1
      rcases le_total 0 (Real.log (ρ 0 * ρ 1)) with h | h
      · nlinarith
      · linarith
    have hstep : ∀ i j : Fin (2 + 2), (j : ℕ) = i + 1 → Real.log (ρ j) ≤ Real.log (ρ i) + s := by
      intro i j hij
      have h := Real.log_le_log (mul_pos hred.pos (hρ j)) (hF i j hij)
      rw [Real.log_mul hred.pos.ne' (hρ j).ne'] at h
      linarith [neg_abs_le (Real.log t)]
    rw [Real.log_mul (mul_pos (hρ 0) (hρ 1)).ne' (mul_pos (hρ 2) (hρ 3)).ne', Real.log_mul (hρ 0).ne' (hρ 1).ne',
      Real.log_mul (hρ 2).ne' (hρ 3).ne'] at h2
    rw [Real.log_mul (hρ 0).ne' (hρ 1).ne'] at hL
    have hR := omBd_real (fun i => Real.log (ρ i)) s C T hs hC0 hT (hstep 0 1 rfl) (hstep 1 2 rfl) (hstep 2 3 rfl) hL
      (abs_le.1 h2).1
    have h5 := h3 (Real.exp (4 * T + 20 * (C + s))) (Real.one_le_exp (by positivity)) fun i j => by
      rw [← Real.exp_log (div_pos (hρ i) (hρ j)), Real.log_div (hρ i).ne' (hρ j).ne']
      exact Real.exp_le_exp.2 (hR i j)
    have h6 : qht x ≤ AutomorphicForm.height ((γ * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) :=
      ciInf_le (f := fun δ : Gam K (2 + 2) =>
        AutomorphicForm.height (((δ : G1 K (2 + 2)) * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)))
        ⟨0, by rintro _ ⟨δ, rfl⟩; exact (height_pos _).le⟩ ⟨γ, hγ⟩
    have h7 : C * Real.exp (4 * T + 20 * (C + s)) ^ c = A * Real.exp (((4 * c : ℕ) : ℝ) * T) := by
      rw [hA, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2
      push_cast
      ring
    refine h6.trans (h5.trans ?_)
    rw [h7]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) (Real.exp_pos _).le
  · unfold Om at hom
    push Not at hom
    obtain ⟨q, hq'⟩ := hom
    have h1 := hq (qx q x)
    have h2 : qht (qx q x) = qht x := hqinv _ (q.out : Gam K (2 + 2)).2 x
    rw [h2] at h1
    rw [← Real.le_log_iff_exp_le (zero_lt_one.trans_le (hq1 x))]
    have h3 : (T - C') / c' ≤ Real.log (qht x) := by
      rw [div_le_iff₀ hc']
      linarith
    rw [sub_div, div_eq_inv_mul T] at h3
    linarith [le_abs_self (C' / c')]
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem sfinite_of_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] : SFinite ν := inferInstance

private theorem le_of_sq_le {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) (h : t ^ 2 ≤ B * t) : t ≤ B := by
  rcases ht.eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · exact le_of_mul_le_mul_right (by nlinarith) h0

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.truncKer :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ (a : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → IsLeftSmooth a → D.Hecke a →
      ∃ kk : ℝ → G1 K (2 + 2) → L2 μ, (∀ T, ∀ γ ∈ Gam K (2 + 2), ∀ x, kk T (γ * x) = kk T x) ∧ (∀ T x, Om T x → kk T x = P (kv μ a x)) ∧
        (∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ T x, 0 ≤ T → ¬ Om T x → ‖kk T x‖ ≤ C * (qht x ^ N')⁻¹) ∧
        (∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ T x, 0 ≤ T → ‖kk T x‖ ≤ C * qht x ^ N) ∧
        ∀ T Λ, 0 ≤ T → IsTrunc A.J A'.J T Λ → (∃ B : ℝ, ∀ x, ‖kk T x‖ ≤ B) ∧
          StronglyMeasurable (fun y : RightCosetSpace (Gam K (2 + 2)) => kk T (Quotient.out y)) ∧ IsHilbertSchmidt (Λ ∘L Rop μ a ∘L P) ∧
          ∀ φ, ((Λ ∘L Rop μ a ∘L P) φ : RightCosetSpace (Gam K (2 + 2)) → ℂ) =ᵐ[quotientMeasure (Gam K (2 + 2)) μ] fun y => ⟪kk T (Quotient.out y), φ⟫_ℂ := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' a P hP ha hD
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := 2 + 2) μ
  haveI hsf : SFinite (quotientMeasure (Gam K (2 + 2)) μ) := sfinite_of_finite _
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI : SecondCountableTopology (RightCosetSpace (Gam K (2 + 2))) :=
    (isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.secondCountableTopology
      (isOpenQuotientMap_mk (Gam K (2 + 2))).isOpenMap
  haveI : MeasurableSpace.CountablyGenerated (RightCosetSpace (Gam K (2 + 2))) := BorelSpace.countablyGenerated
  haveI : IsSeparable (quotientMeasure (Gam K (2 + 2)) μ) := isSeparable_of_sigmaFinite _
  haveI : SecondCountableTopology (Lp ℂ 2 (quotientMeasure (Gam K (2 + 2)) μ)) := Lp.SecondCountableTopology
  haveI : TopologicalSpace.SeparableSpace (Lp ℂ 2 (quotientMeasure (Gam K (2 + 2)) μ)) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  choose k hk hkγ hkO hkm using fun T => UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.kT μ a T
  have hsa : ∀ u w : L2 μ, ⟪P u, w⟫_ℂ = ⟪u, P w⟫_ℂ := fun u w => hP.1.isSymmetric u w
  have hPP : ∀ u : L2 μ, P (P u) = P u := fun u => DFunLike.congr_fun hP.2.1 u
  have hsq : ∀ u : L2 μ, ‖P u‖ ^ 2 = ‖⟪u, P u⟫_ℂ‖ := by
    intro u
    have h : ⟪u, P u⟫_ℂ = ⟪P u, P u⟫_ℂ := by rw [hsa, hPP]
    rw [h, inner_self_eq_norm_sq_to_K]
    simp
  have hPn : ∀ u : L2 μ, ‖P u‖ ≤ ‖u‖ := fun u =>
    le_of_sq_le (norm_nonneg _) (norm_nonneg _) ((hsq u).trans_le (norm_inner_le_norm _ _))
  obtain ⟨q1, -, -⟩ := qhtBasic K (2 + 2)
  have q0 : ∀ x : G1 K (2 + 2), 0 ≤ qht x := fun x => zero_le_one.trans (q1 x)
  have hfar : ∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ T x, 0 ≤ T → ¬ Om T x → ‖P (k T x)‖ ≤ C * (qht x ^ N')⁻¹ := by
    intro N'
    obtain ⟨C, hC, h⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.mainBd K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP ha hD N'
    refine ⟨C, hC, fun T x hT hx => ?_⟩
    refine le_of_sq_le (norm_nonneg _) (mul_nonneg hC (inv_nonneg.2 (pow_nonneg (q0 x) _))) ?_
    rw [hsq, hk]
    exact h T x _ hT (hPP _) hx
  obtain ⟨C₁, N₁, hC₁, b₁⟩ := (kvBd K (2 + 2) μ a).1 (UpperTheory.ConvolutionTheory.C.polyBdAll K (2 + 2) μ a)
  obtain ⟨C₂, hC₂, b₂⟩ := hfar 0
  have hnear : ∀ T x, Om T x → ‖P (k T x)‖ ≤ C₁ * qht x ^ N₁ := fun T x hx => by
    rw [hkO T x hx]; exact (hPn _).trans (b₁ x)
  have hfar0 : ∀ T x, 0 ≤ T → ¬ Om T x → ‖P (k T x)‖ ≤ C₂ := fun T x hT hx => by simpa using b₂ T x hT hx
  refine ⟨fun T x => P (k T x), fun T γ hγ x => by simp only [hkγ T γ hγ x], fun T x hx => by simp only [hkO T x hx], hfar,
    ⟨C₁ + C₂, N₁, add_nonneg hC₁ hC₂, fun T x hT => ?_⟩, fun T Λ hT hΛ => ?_⟩
  · have h1 : 1 ≤ qht x ^ N₁ := one_le_pow₀ (q1 x)
    by_cases hx : Om T x
    · exact (hnear T x hx).trans (by nlinarith)
    · exact (hfar0 T x hT hx).trans (by nlinarith)
  · obtain ⟨C, c, N, -, hC, hb⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.omBd (K := K)
    have hB : ∀ x, ‖P (k T x)‖ ≤ C₁ * (C * Real.exp (N * T)) ^ N₁ + C₂ := by
      intro x
      by_cases hx : Om T x
      · refine (hnear T x hx).trans (le_add_of_le_of_nonneg ?_ hC₂)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (q0 x) ((hb T x hT).1 hx) _) hC₁
      · exact (hfar0 T x hT hx).trans (le_add_of_nonneg_left (by positivity))
    have hm : StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => P (k T (Quotient.out y)) :=
      P.continuous.comp_stronglyMeasurable (hkm T)
    have hae : ∀ φ, ((Λ ∘L Rop μ a ∘L P) φ : RightCosetSpace (Gam K (2 + 2)) → ℂ) =ᵐ[quotientMeasure (Gam K (2 + 2)) μ]
        fun y => ⟪P (k T (Quotient.out y)), φ⟫_ℂ := by
      intro φ
      have hr := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.lamRep K μ μ₂ τ₁ τ₂ hp D d d' A A' P Λ T hP hT hΛ).2.2 a hD (P φ) (hPP φ)
      have hm2 : ∀ᵐ y ∂(Measure.map (mk (Gam K (2 + 2))) (μ.restrict (fundamentalDomain (Gam K (2 + 2))))),
          ((Λ ∘L Rop μ a ∘L P) φ : RightCosetSpace (Gam K (2 + 2)) → ℂ) y = ⟪P (k T (Quotient.out y)), φ⟫_ℂ := by
        refine (ae_map_iff (measurable_mk (Gam K (2 + 2))).aemeasurable
          (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
            (hm.inner stronglyMeasurable_const).measurable)).2 ?_
        refine ae_restrict_of_ae (Filter.Eventually.mono hr fun y hy => ?_)
        obtain ⟨γ, hγ⟩ := GroundTheory.Automorphic.RightCosetSpace.mk_eq_mk_iff.1
          (show mk (Gam K (2 + 2)) (Quotient.out (mk (Gam K (2 + 2)) y)) = mk (Gam K (2 + 2)) y from Quotient.out_eq _)
        have e : k T (Quotient.out (mk (Gam K (2 + 2)) y)) = k T y := by
          rw [← hγ]; exact hkγ T _ γ.2 y
        rw [e, hsa, hk]
        exact hy
      rwa [map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K (2 + 2)) μ)] at hm2
    exact ⟨⟨_, hB⟩, hm, hsOfKer (quotientMeasure (Gam K (2 + 2)) μ) _ _ (MemLp.of_bound hm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun y => hB _)) hae, hae⟩
end
