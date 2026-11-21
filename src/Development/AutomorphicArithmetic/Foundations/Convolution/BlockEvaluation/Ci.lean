import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.ExpForm
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PowSym
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.KillEx
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.HomogMonomial
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpecAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebBd
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OpBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.CommProj
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PowLeExpEventually
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Degree
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.SideEst
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TotalDegreeAevalLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvExSub
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TwInt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SmoothDecay
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClass
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspTrBand

section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

section SlopeTestRemainingChoices

open scoped InnerProductSpace

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] : prj E = E.starProjection := by
  have h : E.topologicalClosure = E := E.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  unfold prj
  congr 1

private theorem prj_mem_iff {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v = v ↔ v ∈ V := by
  unfold prj
  rw [Submodule.starProjection_eq_self_iff, hV.submodule_topologicalClosure_eq]

private noncomputable def cprs (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) : Module.End ℂ E :=
  (E.orthogonalProjection : H →ₗ[ℂ] E) ∘ₗ (T : H →ₗ[ℂ] H) ∘ₗ E.subtype

private theorem cprs_coe (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) (v : E) :
    (cprs E T v : H) = E.starProjection (T v) := rfl

private theorem trOn_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) :
    trOn E T = LinearMap.trace ℂ E (cprs E T) := by
  let b := stdOrthonormalBasis ℂ E
  rw [LinearMap.trace_eq_sum_inner _ b, trOn, prj_eq, GroundTheory.Automorphic.trace]
  set S : H →L[ℂ] H := T ∘L E.starProjection with hS
  refine HasSum.tsum_eq ?_
  have h := hasSum_sum (s := Finset.univ) fun k _ =>
    (GroundTheory.Automorphic.stdHilbertBasis ℂ H).hasSum_inner_mul_inner (ContinuousLinearMap.adjoint S (b k : H)) (b k : H)
  convert h using 1
  · rfl
  · funext i
    rw [ContinuousLinearMap.comp_apply, b.starProjection_eq_sum_rankOne]
    simp only [ContinuousLinearMap.sum_apply, inner_sum, InnerProductSpace.rankOne_apply, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, Submodule.coe_inner, cprs_coe, hS, ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.2 (b k).2, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (b k).2]

private theorem comm_proj (E : Submodule ℂ H) [FiniteDimensional ℂ E] (U : H →L[ℂ] H) (h : ∀ v ∈ E, U v ∈ E)
    (h' : ∀ v ∈ E, ContinuousLinearMap.adjoint U v ∈ E) (v : H) :
    E.starProjection (U v) = U (E.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h _ (E.starProjection_apply_mem v)) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact E.starProjection_inner_eq_zero v _ (h' w hw)

private theorem cprs_mul_right (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T U : H →L[ℂ] H) (h : ∀ v ∈ E, U v ∈ E) :
    cprs E T * cprs E U = cprs E (T * U) := by
  ext v
  rw [Module.End.mul_apply, cprs_coe, cprs_coe, cprs_coe, Submodule.starProjection_eq_self_iff.2 (h _ v.2)]
  rfl

private theorem cprs_mul_left (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T U : H →L[ℂ] H)
    (h : ∀ v, E.starProjection (U v) = U (E.starProjection v)) :
    cprs E U * cprs E T = cprs E (U * T) := by
  ext v
  rw [Module.End.mul_apply, cprs_coe, cprs_coe, cprs_coe, ContinuousLinearMap.mul_apply, h, h,
    Submodule.starProjection_eq_self_iff.2 (E.starProjection_apply_mem _)]

private theorem mem_eig {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (A U : H →L[ℂ] H) (x : ℝ)
    (h1 : Commute U (prj V)) (h2 : Commute U A) : ∀ v ∈ eigIn V A x, U v ∈ eigIn V A x := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [← prj_mem_iff hV] at hv1 ⊢
    have := congrArg (fun L : H →L[ℂ] H => L v) h1.eq
    simp only [ContinuousLinearMap.mul_apply, hv1] at this
    exact this.symm
  · rw [Module.End.mem_eigenspace_iff] at hv2 ⊢
    have := congrArg (fun L : H →L[ℂ] H => L v) h2.eq
    simp only [ContinuousLinearMap.mul_apply] at this
    simp only [ContinuousLinearMap.coe_coe] at hv2 ⊢
    rw [← this, hv2, map_smul]

private theorem abs_form (hE : ExpForm) (l : ℕ) (hl : 0 < l) (V : Submodule ℂ H) (hV : IsClosed (V : Set H))
    (A T : H →L[ℂ] H) (hA : 0 ≤ A) (x : ℝ) [FiniteDimensional ℂ (eigIn V A x)] (U : ZMod l → H →L[ℂ] H)
    (h1 : ∀ i, Commute (U i) (prj V)) (h2 : ∀ i, Commute (U i) A) (h3 : ∀ i k, Commute (U i) (U k))
    (h4 : ∀ i, T * U i = U (i + 1) * T) :
    ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop,
      trOn (eigIn V A x) ((U 0 ^ j) ∘L T) = ∑ ζ ∈ s, c ζ * ζ ^ j := by
  have hAs : IsSelfAdjoint A := GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA
  have hPs : IsSelfAdjoint (prj V) := isSelfAdjoint_starProjection _
  have hm : ∀ i, ∀ v ∈ eigIn V A x, U i v ∈ eigIn V A x := fun i => mem_eig hV A _ x (h1 i) (h2 i)
  have hm' : ∀ i, ∀ v ∈ eigIn V A x, ContinuousLinearMap.adjoint (U i) v ∈ eigIn V A x := fun i => by
    refine mem_eig hV A _ x ?_ ?_
    · have := (h1 i).star_star
      rwa [hPs.star_eq] at this
    · have := (h2 i).star_star
      rwa [hAs.star_eq] at this
  have hc := fun i => comm_proj _ (U i) (hm i) (hm' i)
  obtain ⟨s, c, hs, h⟩ := hE (eigIn V A x) l hl (fun i => cprs _ (U i)) (cprs _ T)
    (fun i k => by
      show _ * _ = _ * _
      rw [cprs_mul_right _ _ _ (hm k), cprs_mul_right _ _ _ (hm i), (h3 i k).eq])
    (fun i => by rw [cprs_mul_right _ _ _ (hm i), cprs_mul_left _ _ _ (hc (i + 1)), h4])
  refine ⟨s, c, hs, (eventually_ge_atTop (Module.finrank ℂ (eigIn V A x))).mono fun j hj => ?_⟩
  rw [← h j hj, trOn_eq]
  congr 1
  clear hj
  induction j with
  | zero => rw [pow_zero, pow_zero, one_mul]; rfl
  | succ j ih => rw [pow_succ', pow_succ', mul_assoc, ← ih, cprs_mul_left _ _ _ (hc 0)]; rfl

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Ci.trExp :
    ExpForm → TrExp := by
  intro hE K _ _ n l hl μ _ θ 𝔰 V x hA hV hfin
  exact abs_form hE l hl V hV.closed _ _ hA x 𝔰.Uq (fun i => 𝔰.Uq_inner i V hV.closed hV.inv) 𝔰.Uq_amp 𝔰.Uq_comm
    𝔰.Uq_perm
end

section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

private theorem prj_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) {v : H} (hv : v ∈ W) : prj W v = v := by
  unfold prj
  exact Submodule.starProjection_eq_self_iff.2 (W.le_topologicalClosure hv)

private theorem fixF_anti {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    {U U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (h : U' ≤ U) : fixF μ U ≤ fixF μ U' := by
  unfold fixF
  exact biInf_mono fun u hu => h hu

private theorem eig_fix {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) : v ∈ V ∧ 𝔞.A v = (x : ℂ) • v ∧ v ∈ fixF μ 𝔞.U := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
  have h3 : 𝔞.A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 h2
  refine ⟨h1, h3, ?_⟩
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h4 := hA v
  rw [h3] at h4
  exact (Submodule.smul_mem_iff _ hx').1 h4

private theorem poly_ind {H σ ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ev : MvPolynomial σ (MvPolynomial ι ℂ) →+* (H →L[ℂ] H)) (f : MvPolynomial σ (MvPolynomial ι ℂ) →+* ℂ)
    (v : H) (s : Set σ) (h0 : ∀ c : ℂ, ev (C (C c)) v = f (C (C c)) • v)
    (h1 : ∀ i, ev (C (X i)) v = f (C (X i)) • v) (h2 : ∀ y ∈ s, ev (X y) v = f (X y) • v)
    (P : MvPolynomial σ (MvPolynomial ι ℂ)) (hP : ∀ y ∈ P.vars, y ∈ s) : ev P v = f P • v := by
  have hadd : ∀ P Q, ev P v = f P • v → ev Q v = f Q • v → ev (P + Q) v = f (P + Q) • v := by
    intro P Q hP hQ
    rw [map_add, map_add, ContinuousLinearMap.add_apply, hP, hQ, add_smul]
  have hmul : ∀ P Q, ev P v = f P • v → ev Q v = f Q • v → ev (P * Q) v = f (P * Q) • v := by
    intro P Q hP hQ
    rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hQ, map_smul, hP, smul_smul, mul_comm]
  have hC : ∀ c : MvPolynomial ι ℂ, ev (C c) v = f (C c) • v := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add p q hp hq => rw [C_add]; exact hadd _ _ hp hq
    | mul_X p i hp => rw [C_mul]; exact hmul _ _ hp (h1 i)
  have hm : P ∈ supported (MvPolynomial ι ℂ) s := mem_supported.2 fun y hy => hP y hy
  clear hP
  rw [supported_eq_adjoin_X] at hm
  induction hm using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact h2 y hy
  | algebraMap r => exact hC r
  | add p q _ _ hp hq => exact hadd _ _ hp hq
  | mul p q _ _ hp hq => exact hmul _ _ hp hq

private theorem eig_fixL {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) {w : Pl K} (hw : w ∉ 𝔞.S) :
    v ∈ V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) := by
  obtain ⟨h1, -, h2⟩ := eig_fix 𝔞 hA hx hv
  rw [Submodule.mem_inf, fixL]
  exact ⟨h1, fixF_anti μ (𝔞.max w hw) h2⟩

private theorem val_CC {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (c : ℂ) : val (n := n) x Λ t (C (C c)) = c := by simp [val]

private theorem val_none {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) : val (n := n) x Λ t (C (X none)) = x := by simp [val]

private theorem val_some {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (y : Ix K n) :
    val (n := n) x Λ t (C (X (some y))) = x * (Λ y.1).esymm (y.2 + 1) := by simp [val]

private theorem val_X {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (w : Pl K) (i : Fin n) :
    val (n := n) x Λ t (X (w, i)) = (t w).esymm (i + 1) := by simp [val, hval]

private theorem ev_val {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x)
    {ev : PR K n →+* (LL μ →L[ℂ] LL μ)} (hev : 𝔞.IsEv ev) {Λ : (K →+* ℂ) → Multiset ℂ} {t : Pl K → Multiset ℂ}
    (h : At μ 𝔞.S V Λ t) (P : PR K n) (hPv : ∀ y ∈ P.vars, y.1 ∉ 𝔞.S) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) : ev P v = val x Λ t P • v := by
  obtain ⟨hvV, hAv, hvU⟩ := eig_fix 𝔞 hA hx hv
  obtain ⟨hI, hS⟩ := h
  have hO : Oinf μ 𝔞.ν 𝔞.a₀ v = (x : ℂ) • v := by
    rw [← hAv, Amp.A, ContinuousLinearMap.comp_apply, prj_self _ hvU]
  refine poly_ind ev (val x Λ t) v {y | y.1 ∉ 𝔞.S} (fun c => ?_) (fun o => ?_) (fun y hy => ?_) P hPv
  · rw [hev.const, val_CC, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  · cases o with
    | none => rw [hev.amp, hAv, val_none]
    | some y =>
      obtain ⟨-, h1⟩ := hI y.1
      rw [hev.cen, Amp.Z, ContinuousLinearMap.comp_apply, prj_self _ hvU,
        h1 𝔞.ν 𝔞.a₀ 𝔞.smooth y.2 v hvV, hO, smul_smul, mul_comm, val_some]
  · obtain ⟨w, i⟩ := y
    obtain ⟨-, -, h1⟩ := hS w hy
    rw [hev.hecke w hy i, h1 i v (eig_fixL 𝔞 hA hx hv hy), val_X]

theorem UpperTheory.ConvolutionTheory.Ci.evVal :
    EvEx → ParEx → EvVal := by
  intro hE hP K _ _ _ n hn μ _ 𝔞 V x hx hV
  obtain ⟨-, -, hA, -⟩ := hE K n hn μ 𝔞
  obtain ⟨p1, p2, -⟩ := hP K n hn μ V hV
  refine ⟨fun hne => ?_, fun Λ t Λ' t' h h' => ?_, fun ev hev Λ t h P hPv v hv => ev_val 𝔞 hA hx hev h P hPv hv⟩
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hB : ∀ w, ∃ B, w ∉ 𝔞.S → SSat μ V w B := by
      intro w
      by_cases hw : w ∈ 𝔞.S
      · exact ⟨0, fun h => absurd hw h⟩
      · obtain ⟨B, hB⟩ := (p2 w ((Submodule.ne_bot_iff _).2 ⟨v, eig_fixL 𝔞 hA hx hv hw, hv0⟩)).exists
        exact ⟨B, fun _ => hB⟩
    choose t ht using hB
    choose Λ hΛ using fun τ => (p1 τ).exists
    exact ⟨Λ, t, And.intro hΛ ht⟩
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨h1', h2'⟩ := h'
    refine ⟨funext fun τ => ?_, fun w hw => ?_⟩
    · obtain ⟨m, -, hm⟩ := p1 τ
      beta_reduce at hm
      rw [hm (Λ τ) (h1 τ), hm (Λ' τ) (h1' τ)]
    · have h3 := h2 w hw
      obtain ⟨-, h4, -⟩ := h2 w hw
      obtain ⟨m, -, hm⟩ := p2 w h4
      beta_reduce at hm
      rw [hm (t w) h3, hm (t' w) (h2' w hw)]
end

section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

private theorem eval_powE {n : ℕ} (f : ℕ) (i : Fin n) (s : Multiset ℂ) (hs : s.card = n) :
    eval (fun j : Fin n => s.esymm (j + 1)) (powE f i) = (s.map (· ^ f)).esymm (i + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin n → ℂ, s = Finset.univ.val.map a := by
    induction s using Quotient.inductionOn with
    | h l =>
      have hl : l.length = n := by simpa using hs
      subst hl
      refine ⟨l.get, ?_⟩
      rw [Fin.univ_val_map, List.ofFn_get]
      rfl
  have h1 : aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) (powE f i)
      = expand f (esymm (Fin n) ℂ (i + 1)) := by
    rw [← esymmAlgHom_apply]
    have := congrArg Subtype.val
      ((esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
        ⟨expand f (esymm (Fin n) ℂ (i + 1)), fun w => by rw [rename_expand, esymm_isSymmetric]⟩)
    exact this
  have h2 := congrArg (aeval a) h1
  rw [← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply] at h2
  have h3 : (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).comp (expand f) = aeval fun r => a r ^ f := by
    apply MvPolynomial.algHom_ext
    intro r
    simp
  rw [h3] at h2
  simp only [aeval_esymm_eq_multiset_esymm] at h2
  rw [Multiset.map_map, ← coe_aeval_eq_eval]
  exact h2

theorem UpperTheory.ConvolutionTheory.Ci.valBc :
    ValBc := by
  classical
  intro F E _ _ _ _ _ n x Λ t P hP
  refine ⟨?_, ?_, ?_⟩
  · rw [← RingHom.comp_apply]
    refine hom_congr_vars (p₁ := P) (p₂ := P) ?_ ?_ rfl
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [val, bcPR]
      · rintro (_ | y)
        · simp [val, bcPR]
        · simp [val, bcPR, bcInf]
    · intro y hy _
      have h := eval_powE (resDeg F y.1) y.2 _ (hP y hy)
      simp only [val, bcPR, RingHom.comp_apply, eval₂Hom_X', coe_eval₂Hom, eval₂_map, eval₂_rename, eval₂_X]
      rw [hval, bcSat, ← h]
      have hc : ((eval fun o : Option (Ix F n) => o.elim (x : ℂ) fun y => x * (Λ y.1).esymm (y.2 + 1)).comp C)
          = RingHom.id ℂ := by
        ext c
        simp
      rw [hc]
      rfl
  · intro y hy
    have h : bcPR F P = bind₁ (fun x : Pl E × Fin n =>
        (map C (rename (fun i => (x.1.under (𝓞 F), i)) (powE (resDeg F x.1) x.2)) : PR F n))
        (map (rename (Option.map fun x : Ix E n => (x.1.comp (algebraMap F E), x.2))).toRingHom P) := by
      rw [bind₁, aeval_def, eval₂_map]
      rfl
    rw [h] at hy
    obtain ⟨y', hy', hy2⟩ := mem_vars_bind₁ _ _ hy
    refine ⟨y', vars_map _ _ hy', ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_vars_rename _ _ (vars_map _ _ hy2)
    rfl
  · intro η m
    simp only [chebP, bcPR, eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Polynomial.aeval_algHom_apply]
    simp
end

section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

private theorem exists_esymm_ne {s t : Multiset ℂ} {n : ℕ} (hs : s.card = n) (ht : t.card = n) (h : s ≠ t) :
    ∃ k : Fin n, s.esymm (k + 1) ≠ t.esymm (k + 1) := by
  by_contra hc
  push Not at hc
  apply h
  have hp : (s.map fun a => Polynomial.X - Polynomial.C a).prod = (t.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hs, ht]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n + 1 := Finset.mem_range.mp hj
    have : s.esymm j = t.esymm j := by
      rcases j with _ | j
      · simp [Multiset.esymm]
      · exact hc ⟨j, by omega⟩
    rw [this]
  rw [← Polynomial.roots_multiset_prod_X_sub_C s, hp, Polynomial.roots_multiset_prod_X_sub_C]

private theorem one_factor (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Set (Pl K))
    (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) (Λ' : (K →+* ℂ) → Multiset ℂ) (t' : Pl K → Multiset ℂ)
    (h1 : ∀ τ, (Λ τ).card = n) (h2 : ∀ w ∉ S, (t w).card = n) (h3 : ∀ τ, (Λ' τ).card = n)
    (h4 : ∀ w ∉ S, (t' w).card = n) (h : ¬ (Λ = Λ' ∧ ∀ w ∉ S, t w = t' w)) :
    ∃ P : PR K n, (∀ y ∈ P.vars, y.1 ∉ S) ∧ (∀ x : ℝ, x ≠ 0 → val x Λ t P ≠ 0) ∧ ∀ x : ℝ, val x Λ' t' P = 0 := by
  classical
  by_cases hΛ : Λ = Λ'
  · have : ∃ w, w ∉ S ∧ t w ≠ t' w := by
      by_contra hc
      push Not at hc
      exact h ⟨hΛ, hc⟩
    obtain ⟨w, hw, hne⟩ := this
    obtain ⟨k, hk⟩ := exists_esymm_ne (h2 w hw) (h4 w hw) hne
    refine ⟨X (w, k) - C (C ((t' w).esymm (k + 1))), ?_, ?_, ?_⟩
    · intro y hy
      have := vars_sub_subset _ hy
      rw [vars_C, vars_X, Finset.union_empty, Finset.mem_singleton] at this
      rw [this]; exact hw
    · intro x _
      simpa [val, hval, sub_eq_zero] using hk
    · intro x
      simp [val, hval]
  · obtain ⟨τ, hne⟩ := Function.ne_iff.mp hΛ
    obtain ⟨k, hk⟩ := exists_esymm_ne (h1 τ) (h3 τ) hne
    refine ⟨C (X (some (τ, k)) - C ((Λ' τ).esymm (k + 1)) * X none), ?_, ?_, ?_⟩
    · intro y hy
      rw [vars_C] at hy
      exact absurd hy (Finset.notMem_empty _)
    · intro x hx
      have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      have e : val x Λ t (C (X (some (τ, k)) - C ((Λ' τ).esymm (k + 1)) * X none) : PR K n) =
          x * ((Λ τ).esymm (k + 1) - (Λ' τ).esymm (k + 1)) := by
        rw [val, eval₂Hom_C]
        simp
        ring
      rw [e]
      exact mul_ne_zero hx' (sub_ne_zero.mpr hk)
    · intro x
      rw [val, eval₂Hom_C]
      simp
      ring

theorem UpperTheory.ConvolutionTheory.Ci.sepPoly :
    SepPoly := by
  classical
  intro K _ _ n S Λ t I _ Λ' t' h1 h2 h3 h4 h
  choose P hP1 hP2 hP3 using fun i => one_factor K n S Λ t (Λ' i) (t' i) h1 h2 (h3 i) (h4 i) (h i)
  set Q : PR K n := ∏ i, P i with hQ
  refine ⟨Q, Q.vars.image Prod.fst, max Q.totalDegree (Q.support.sup fun β => (Q.coeff β).totalDegree), ?_,
    ⟨?_, le_max_left _ _, ?_⟩, ?_, ?_⟩
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (vars_prod P hy)
    exact hP1 i y hi
  · intro y hy
    exact Finset.mem_image_of_mem _ hy
  · intro β
    by_cases hβ : β ∈ Q.support
    · exact le_max_of_le_right (Finset.le_sup (f := fun β => (Q.coeff β).totalDegree) hβ)
    · rw [notMem_support_iff.mp hβ, totalDegree_zero]
      exact Nat.zero_le _
  · intro x hx
    rw [hQ, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hP2 i x hx
  · intro i x
    rw [hQ, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hP3 i x)
end

section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

section SlopeTestRemainingChoices

open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem cheb_cont (η : ℝ) (m : ℕ) : Continuous (cheb η m) := by
  unfold cheb
  exact (Polynomial.continuous _).comp (by fun_prop)

private theorem ev_cheb {K : Type} [Field K] [NumberField K] {n : ℕ} (ψ : PR K n →+* (H →L[ℂ] H))
    (hc : ∀ c : ℂ, ψ (C (C c)) = c • 1) (A : H →L[ℂ] H) (hA : ψ (C (X none)) = A) (hsa : IsSelfAdjoint A)
    (η : ℝ) (m : ℕ) : ψ (chebP η m) = fcalc (cheb η m) A := by
  have e1 : fcalc (fun x : ℝ => 2 * x / η - 1) A = ((2 / η : ℝ) : ℂ) • A - 1 := by
    unfold fcalc
    have : (fun x : ℝ => 2 * x / η - 1) = fun x : ℝ => (2 / η) • x - 1 := by
      funext x; simp only [smul_eq_mul]; ring
    rw [this, cfc_sub _ _ A, cfc_smul (2 / η) (fun x : ℝ => x) A, cfc_id' ℝ A, cfc_const_one ℝ A]
    rfl
  have e2 : fcalc (cheb η m) A =
      Polynomial.aeval (((2 / η : ℝ) : ℂ) • A - 1) (Polynomial.Chebyshev.T ℝ m) := by
    rw [← e1]
    unfold fcalc
    rw [← cfc_polynomial (R := ℝ) (Polynomial.Chebyshev.T ℝ m) (cfc (fun x : ℝ => 2 * x / η - 1) A),
      ← cfc_comp' (fun y => (Polynomial.Chebyshev.T ℝ m).eval y) (fun x : ℝ => 2 * x / η - 1) A]
    rfl
  let φ : MvPolynomial (Option (Ix K n)) ℂ →ₐ[ℤ] (H →L[ℂ] H) := (ψ.comp C).toIntAlgHom
  have e3 : ψ (chebP η m) = φ (Polynomial.aeval (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ)
      (Polynomial.Chebyshev.T ℤ m)) := by
    unfold chebP
    rw [← Polynomial.Chebyshev.map_T (algebraMap ℤ ℂ), Polynomial.aeval_map_algebraMap]
    rfl
  have e4 : φ (C ((2 / η : ℝ) : ℂ) * X none - 1) = ((2 / η : ℝ) : ℂ) • A - 1 := by
    rw [map_sub, map_mul, map_one]
    show ψ (C (C _)) * ψ (C (X none)) - 1 = _
    rw [hc, hA, smul_mul_assoc, one_mul]
  rw [e3, ← Polynomial.aeval_algHom_apply, e4, e2, ← Polynomial.Chebyshev.map_T (algebraMap ℤ ℝ),
    Polynomial.aeval_map_algebraMap]

private theorem fcalc_norm_le (A : H →L[ℂ] H) (h0 : 0 ≤ A) (h1 : ‖A‖ ≤ 1) (φ : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ c) : ‖fcalc φ A‖ ≤ c := by
  unfold fcalc
  refine norm_cfc_le hc fun x hx => h x ⟨spectrum_nonneg_of_nonneg h0 hx, ?_⟩
  rcases subsingleton_or_nontrivial (H →L[ℂ] H) with hs | hs
  · simp [spectrum.of_subsingleton] at hx
  · exact (le_abs_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans h1)

private theorem off_est (A Q W P : H →L[ℂ] H) (h0 : 0 ≤ A) (h1 : ‖A‖ ≤ 1) (hQ : Commute A Q) (hW : Commute W P)
    (hP : ‖1 - P‖ ≤ 1) (η c : ℝ) (hc : 0 ≤ c) (t χ : ℝ → ℝ) (ht : Continuous t) (hχ : Continuous χ)
    (ht1 : ∀ x ∈ Set.Icc 0 η, |t x| ≤ 1) (ht2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |t x| ≤ c)
    (hχ1 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ2 : ∀ x ≥ η, χ x = 1) :
    ‖fcalc t A * Q * W * (1 - P)‖ ≤ ‖W‖ * (‖Q‖ + c * ‖Q * (fcalc χ A * (1 - P))‖) := by
  have hsa : IsSelfAdjoint A := isSelfAdjoint_of_nonneg h0
  have hcm : Commute (fcalc χ A) Q := hQ.cfc_real χ
  have e1 : fcalc t A = fcalc (fun x => t x * (1 - χ x)) A + fcalc t A * fcalc χ A := by
    unfold fcalc
    rw [← cfc_mul t χ A, ← cfc_add A _ _]
    congr 1
    funext x; ring
  have n1 : ‖fcalc (fun x => t x * (1 - χ x)) A‖ ≤ 1 := by
    refine fcalc_norm_le A h0 h1 _ 1 zero_le_one fun x hx => ?_
    rcases le_total x η with h | h
    · rw [abs_mul]
      have : |1 - χ x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hχ1 x]
      exact mul_le_one₀ (ht1 x ⟨hx.1, h⟩) (abs_nonneg _) this
    · simp [hχ2 x h]
  have n2 := fcalc_norm_le A h0 h1 t c hc ht2
  have hW' : W * (1 - P) = (1 - P) * W := ((Commute.one_right W).sub_right hW).eq
  have e2 : fcalc t A * Q * W * (1 - P) =
      (fcalc (fun x => t x * (1 - χ x)) A * (Q * (1 - P)) + fcalc t A * (Q * (fcalc χ A * (1 - P)))) * W := by
    rw [mul_assoc _ W, hW', ← mul_assoc]
    congr 1
    conv_lhs => rw [e1]
    rw [add_mul, add_mul, mul_assoc (fcalc t A), hcm.eq]
    simp only [mul_assoc]
  rw [e2, mul_comm ‖W‖]
  refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _))
  · calc _ ≤ 1 * (‖Q‖ * 1) := (norm_mul_le _ _).trans
          (mul_le_mul n1 ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hP (norm_nonneg _))) (norm_nonneg _) zero_le_one)
      _ = ‖Q‖ := by ring
  · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right n2 (norm_nonneg _))

omit [CompleteSpace H] in
private theorem norm_pow_le_clm (U : H →L[ℂ] H) (j : ℕ) : ‖U ^ j‖ ≤ ‖U‖ ^ j := by
  rcases j with _ | j
  · rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' U j.succ_pos

private theorem prj_facts (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) :
    (∀ v, prj V v ∈ V) ∧ (∀ v ∈ V, prj V v = v) ∧ IsSelfAdjoint (prj V) := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V := fun v => by rw [hc]
  exact ⟨fun v => (hm _).1 (Submodule.starProjection_apply_mem _ v),
    fun v hv => Submodule.starProjection_eq_self_iff.2 ((hm _).2 hv), isSelfAdjoint_starProjection _⟩

private theorem pres_of_comm (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H)
    (h : T * prj V = prj V * T) : ∀ v ∈ V, T v ∈ V := by
  intro v hv
  obtain ⟨a1, a2, -⟩ := prj_facts V hV
  have := congrArg (fun S : H →L[ℂ] H => S v) h
  simp only [ContinuousLinearMap.mul_apply, a2 v hv] at this
  rw [this]; exact a1 _

private theorem eig_pres (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (A T : H →L[ℂ] H) (x : ℝ)
    (h : Commute T (prj V)) (hA : Commute T A) : ∀ v ∈ eigIn V A x, T v ∈ eigIn V A x := by
  intro v hv
  refine ⟨pres_of_comm V hV T h.eq v hv.1, ?_⟩
  have h2 : A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv.2
  refine Module.End.mem_eigenspace_iff.2 ?_
  have := congrArg (fun S : H →L[ℂ] H => S v) hA.eq
  simp only [ContinuousLinearMap.mul_apply, h2, map_smul] at this
  exact this.symm

private theorem trOn_scalar (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (A Q B : H →L[ℂ] H) (x : ℝ) (a : ℂ)
    (hsa : IsSelfAdjoint A) (hAV : Commute A (prj V)) (hQV : Commute Q (prj V)) (hQA : Commute Q A)
    [FiniteDimensional ℂ (eigIn V A x)] (hQ : ∀ v ∈ eigIn V A x, Q v = a • v) :
    trOn (eigIn V A x) (A * Q * B) = x * a * trOn (eigIn V A x) B := by
  have hE : IsClosed (eigIn V A x : Set H) := (eigIn V A x).closed_of_finiteDimensional
  obtain ⟨a1, a2, a3⟩ := prj_facts _ hE
  obtain ⟨-, -, b3⟩ := prj_facts _ hV
  have hc : (eigIn V A x).topologicalClosure = eigIn V A x := hE.submodule_topologicalClosure_eq
  have hT1 : Commute (A * Q) (prj V) := hAV.mul_left hQV
  have hT2 : Commute (A * Q) A := (Commute.refl A).mul_left hQA
  have hcomm : (A * Q) ∘L prj (eigIn V A x) = prj (eigIn V A x) ∘L (A * Q) := by
    refine K.commProj _ _ ?_ ?_
    · rw [hc]; exact eig_pres V hV A _ x hT1 hT2
    · rw [hc]
      refine eig_pres V hV A _ x ?_ ?_
      · have := hT1.star_star
        rwa [b3.star_eq] at this
      · have := hT2.star_star
        rwa [hsa.star_eq] at this
  have e : prj (eigIn V A x) ∘L (A * Q * B) ∘L prj (eigIn V A x) =
      ((x : ℂ) * a) • (prj (eigIn V A x) ∘L B ∘L prj (eigIn V A x)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h1 := congrArg (fun S : H →L[ℂ] H => S (B (prj (eigIn V A x) v))) hcomm
    have hm := a1 (B (prj (eigIn V A x) v))
    have h2 : A (prj (eigIn V A x) (B (prj (eigIn V A x) v))) = (x : ℂ) • _ := Module.End.mem_eigenspace_iff.1 hm.2
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply] at h1 ⊢
    rw [← h1, hQ _ hm, map_smul, h2, smul_smul, mul_comm]
  unfold trOn
  rw [e]
  unfold trace
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right]
  exact tsum_mul_left

private theorem final_arith (C τ u q r k zN zN' x y : ℝ) (hτ : 0 ≤ τ) (hu : 0 ≤ u) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hk : 0 ≤ k) (hz : 1 ≤ zN) (hz' : 0 ≤ zN') (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ u * (q + k * r)) (hy : y ≤ k * q * u) :
    C * zN * x + C * zN' * y + 1 * (q * u * τ) ≤ (|C| + τ) * u * (zN * (q + k * r) + k * zN' * q) := by
  have hz0 : 0 ≤ zN := zero_le_one.trans hz
  have h1 : C * zN * x ≤ |C| * zN * (u * (q + k * r)) := by
    have := le_abs_self C
    gcongr
  have h2 : C * zN' * y ≤ |C| * zN' * (k * q * u) := by
    have := le_abs_self C
    gcongr
  have h3 : q ≤ zN * (q + k * r) + k * zN' * q := by
    have a : 0 ≤ k * r := by positivity
    have b : 0 ≤ k * zN' * q := by positivity
    nlinarith
  have h4 : τ * u * q ≤ τ * u * (zN * (q + k * r) + k * zN' * q) := by gcongr
  nlinarith

end SlopeTestRemainingChoices

set_option maxHeartbeats 1600000 in
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core in
theorem UpperTheory.ConvolutionTheory.Ci.oneSide :
    K.Kern2 → PolyBdAll → SmoothDecay → DecayTraceClass → CuspTrBand → CuspidalMultiplicityOneTotallyComplex → EvEx → OneSide := by
  intro hK hPB hSD hDT hCB hMO hEv K _ _ _ n l hn μ _ θ 𝔰 ev hev hin
  obtain ⟨h0, h1, -, -⟩ := hEv K n hn μ 𝔰.toAmp
  have da := hSD K n μ 𝔰.a 𝔰.a_smooth
  have dg := hSD K n μ _ 𝔰.g_smooth
  obtain ⟨N, hN⟩ := hK K n μ θ 𝔰.a 𝔰.g (hPB K n μ _) da (hPB K n μ _) dg
  refine ⟨N, fun η hη hη1 χ hχ hχ1 hχ2 => ?_⟩
  have hsa : IsSelfAdjoint 𝔰.toAmp.A := isSelfAdjoint_of_nonneg h0
  have hPc : prj (cuspidalL2 μ) = Pc μ := by
    unfold prj Pc
    congr 1
    exact (isClosed_cuspidalL2 μ).submodule_topologicalClosure_eq
  have hcP : ∀ T, Inner μ T → Commute T (Pc μ) := fun T hT => by
    rw [← hPc]; exact hT _ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ)
  have hcV : ∀ T, Inner μ T → ∀ V, IsSummand μ V → Commute T (prj V) := fun T hT V hV => hT _ hV.closed hV.inv
  have hAin : Inner μ 𝔰.toAmp.A := hev.amp ▸ hin _
  have hQA : ∀ Q, Commute (ev Q) 𝔰.toAmp.A := fun Q => hev.amp ▸ (Commute.all Q _).map ev
  have hcomp : IsCompactOperator (𝔰.toAmp.A ∘L Pc μ) := by
    rw [← hPc, ← 𝔰.a_op]; exact (opBasics K n μ 𝔰.a).2.2
  obtain ⟨s, hs1, hs2, hs3⟩ := hCB K n μ θ (hMO K n μ) 𝔰.toAmp.A h0
    (fun V hV => pres_of_comm V hV.closed _ (hcV _ hAin V hV).eq) hcomp η hη
  refine ⟨s, hs1, hs2, fun N' => ?_⟩
  obtain ⟨C₀, hC⟩ := hN N'
  have htc : IsTraceClass (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ) := by
    have := hDT K n μ 𝔰.a 𝔰.g 1 da dg (Commute.one_left (Pc μ)).eq
    rw [𝔰.a_op] at this
    exact this
  refine ⟨|C₀| + (traceNorm (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ)).toReal, fun Q a ha m j Z f hZ hf => ?_⟩
  obtain ⟨hb1, hb2, -⟩ := FX.cheb_bound η m hη hη1
  have hk : 0 ≤ (4 / η) ^ m := by positivity
  have hch : ev (chebP η m * Q) = fcalc (cheb η m) 𝔰.toAmp.A * ev Q := by
    rw [map_mul, ev_cheb ev hev.const _ hev.amp hsa]
  have hUP : Commute (𝔰.Uq 0 ^ j) (Pc μ) := (hcP _ (𝔰.Uq_inner 0)).pow_left j
  have hUA : Commute (𝔰.Uq 0 ^ j) 𝔰.toAmp.A := (𝔰.Uq_amp 0).pow_left j
  have hMP : Commute (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) (Pc μ) := (hcP _ (hin _)).mul_left hUP
  have k1 := hC f (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) Z hZ hMP.eq (by rw [𝔰.a_op]; exact hf.1) hf.2
  have hP : ‖1 - Pc μ‖ ≤ 1 := by
    have : 1 - Pc μ = (cuspidalL2 μ)ᗮ.starProjection := by
      unfold Pc
      rw [Submodule.starProjection_orthogonal]; rfl
    rw [this]
    exact Submodule.starProjection_norm_le _
  have hu := norm_pow_le_clm (𝔰.Uq 0) j
  have k2 := off_est 𝔰.toAmp.A (ev Q) (𝔰.Uq 0 ^ j) (Pc μ) h0 h1 (hQA Q).symm hUP hP η _ hk (cheb η m) χ (cheb_cont η m) hχ
    hb1 hb2 hχ1 hχ2
  have k2' := k2.trans (mul_le_mul_of_nonneg_right hu (by positivity))
  rw [← hch] at k2'
  have k3 : ‖ev (chebP η m * Q) * 𝔰.Uq 0 ^ j‖ ≤ (4 / η) ^ m * ‖ev Q‖ * ‖𝔰.Uq 0‖ ^ j := by
    rw [hch]
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans ?_) hu (norm_nonneg _) (by positivity))
    exact mul_le_mul_of_nonneg_right (fcalc_norm_le _ h0 h1 _ _ hk hb2) (norm_nonneg _)
  have eT : Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ =
      (ev Q * 𝔰.Uq 0 ^ j) * (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ) := by
    have c1 : Commute (ev Q * 𝔰.Uq 0 ^ j) (Pc μ * 𝔰.toAmp.A) :=
      ((hcP _ (hin Q)).mul_left hUP).mul_right ((hQA Q).mul_left hUA)
    calc _ = (Pc μ * 𝔰.toAmp.A) * (ev Q * 𝔰.Uq 0 ^ j) * (Rop μ 𝔰.g * Pc μ) := by simp only [mul_assoc]
      _ = _ := by rw [← c1.eq]; simp only [mul_assoc]
  have hTt : IsTraceClass (Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ) := by
    rw [eT]; exact htc.comp_left _
  have hTn : (traceNorm (Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ)).toReal ≤
      ‖ev Q‖ * ‖𝔰.Uq 0‖ ^ j * (traceNorm (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ)).toReal := by
    rw [eT]
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top htc.ne) (traceNorm_comp_left_le _ _)).trans ?_
    rw [ENNReal.toReal_mul, toReal_enorm]
    exact mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _)))
      ENNReal.toReal_nonneg
  have k4 := hs3 (cheb η m) 1 (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) (cheb_cont η m) zero_le_one hb1
    (fun V hV v hv => pres_of_comm V hV.closed (𝔰.toAmp.A * ev Q * 𝔰.Uq 0 ^ j)
      (((hcV _ hAin V hV).mul_left (hcV _ (hin Q) V hV)).mul_left ((hcV _ (𝔰.Uq_inner 0) V hV).pow_left j)).eq _
      ((opBasics K n μ 𝔰.g).1 V hV v hv)) hTt
  have e1 : cuspTr μ θ f = trace (Pc μ ∘L fcalc (cheb η m) 𝔰.toAmp.A ∘L
      (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) ∘L θ.U ∘L Pc μ) := by
    have c : Commute (fcalc (cheb η m) 𝔰.toAmp.A) 𝔰.toAmp.A := (Commute.refl _).cfc_real _
    unfold cuspTr
    rw [hf.1, hch]
    simp only [← ContinuousLinearMap.mul_def, mul_assoc]
    rw [← mul_assoc 𝔰.toAmp.A, ← c.eq, mul_assoc]
  have e2 : ∑ p ∈ s, (cheb η m p.1 : ℂ) * (p.1 * a p *
      trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) =
      ∑ p ∈ s, (cheb η m p.1 : ℂ) * trOn (eigIn p.2 𝔰.toAmp.A p.1)
        ((𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) ∘L θ.U) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hV := ((hs1 p).1 hp).2.1
    haveI := hs2 p hp
    rw [← trOn_scalar p.2 hV.closed 𝔰.toAmp.A (ev Q) _ p.1 (a p) hsa (hcV _ hAin _ hV) (hcV _ (hin Q) _ hV) (hQA Q) (ha p hp)]
    rfl
  rw [e2]
  rw [← e1] at k4
  refine (norm_sub_le_norm_sub_add_norm_sub _ (cuspTr μ θ f) _).trans
    ((add_le_add k1 (k4.trans (mul_le_mul_of_nonneg_left hTn zero_le_one))).trans ?_)
  exact final_arith _ _ _ _ _ _ _ _ _ _ ENNReal.toReal_nonneg (by positivity) (norm_nonneg _) (norm_nonneg _) hk
    (one_le_pow₀ hZ) (by have := zero_le_one.trans hZ; positivity) (norm_nonneg _) (norm_nonneg _) k2' k3
end

section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private lemma abs_d_atTop (d : ℕ → ℕ)
    (hfac : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) :
    Tendsto d atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [hfac 1, eventually_ge_atTop M.factorial] with j hj hM
  by_contra hlt
  have h1 : (d j).factorial ≤ M.factorial := Nat.factorial_le (not_le.1 hlt).le
  have h2 : ((d j).factorial : ℝ) ≤ j := by exact_mod_cast h1.trans hM
  have h3 := Real.add_one_le_exp (j : ℝ)
  rw [one_mul] at hj
  linarith

private lemma abs_sum_eq {T : Type} [DecidableEq ℝ] (s : Finset T) (a : T → ℝ) (A : Finset ℝ)
    (Z : Finset ℂ) (hA : ∀ i ∈ s, a i ∈ A) (v : T → ℂ) (C : T → ℂ → ℂ) (t : T → ℂ)
    (f g : ℝ → ℂ) (n : ℕ) (ht : ∀ i ∈ s, t i = ∑ ζ ∈ Z, C i ζ * ζ ^ n) :
    ∑ q ∈ A ×ˢ Z, (∑ i ∈ s with a i = q.1, v i * C i q.2) * f q.1 * g q.1 * q.2 ^ n =
      ∑ i ∈ s, v i * f (a i) * g (a i) * t i := by
  rw [Finset.sum_product, ← Finset.sum_fiberwise_of_maps_to hA]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  rw [ht i hi1, hi2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  ring

theorem UpperTheory.ConvolutionTheory.Ci.abs :
    ∀ (T : Type) (a : T → ℝ) (τ : T → ℕ → ℂ) (act good : T → Prop) (x : ℝ), 0 < x → x ≤ 1 → ∀ (p : ℕ), 0 < p → ∀ (c₁ : ℝ) (d : ℕ → ℕ),
      Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) → (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
      (∀ i, act i → 0 < a i → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τ i j = ∑ ζ ∈ s, c ζ * ζ ^ j) →
      (∀ η : ℝ, 0 < η → η < x → ∃ (s : Finset T) (u : T → ℕ → ℂ) (u' : T → ℂ) (k : ℂ), k ≠ 0 ∧ (∀ i, i ∈ s ↔ η < a i ∧ act i) ∧
        (∀ i ∈ s, Tendsto (u i) atTop (𝓝 (u' i))) ∧ (∀ i ∈ s, good i → a i = x → u' i = k) ∧ (∀ i ∈ s, ¬ good i → u' i = 0) ∧
        ∀ (N : ℝ) (s₀ : ℕ), ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀,
          ‖∑ i ∈ s, u i (d j) * (a i : ℂ) ^ d j * (cheb η (j / p + m) (a i) : ℂ) * τ i (j + m')‖ ≤
            K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
      {i | act i ∧ good i ∧ a i = x}.Finite ∧ ∀ᶠ j : ℕ in atTop, ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0 := by
  intro T a τ act good x hx hx1 p hp c₁ d hd hfac hτ H
  classical
  have hdt := abs_d_atTop d hfac
  have hτ' : ∀ i, ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ (act i → 0 < a i →
      ∀ᶠ j : ℕ in atTop, ∀ Z : Finset ℂ, s ⊆ Z → τ i j = ∑ ζ ∈ Z, c ζ * ζ ^ j) := by
    intro i
    by_cases h : act i ∧ 0 < a i
    · obtain ⟨s, c, h0, hc⟩ := hτ i h.1 h.2
      refine ⟨s, fun ζ => if ζ ∈ s then c ζ else 0, h0, fun _ _ => ?_⟩
      filter_upwards [hc] with j hj Z hZ
      rw [hj, ← Finset.sum_subset hZ]
      · exact Finset.sum_congr rfl fun ζ hζ => by simp [hζ]
      · intro ζ _ hζ; simp [hζ]
    · exact ⟨∅, 0, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose S C hS0 hSC using hτ'
  have hF : {i | act i ∧ good i ∧ a i = x}.Finite := by
    obtain ⟨s, -, -, -, -, hs, -⟩ := H (x / 2) (by linarith) (by linarith)
    refine s.finite_toSet.subset fun i hi => ?_
    exact (hs i).2 ⟨by rw [hi.2.2]; linarith, hi.1⟩
  refine ⟨hF, ?_⟩
  have key : ∀ ζ₀ : ℂ, ζ₀ ≠ 0 → ∑ i ∈ hF.toFinset, C i ζ₀ = 0 := by
    intro ζ₀ hζ₀
    obtain ⟨η, hη, hηx, hE⟩ :=
      UpperTheory.ConvolutionTheory.FX.exponents2 d hd hfac p hp c₁ (-Real.log ‖ζ₀‖) x hx hx1
    obtain ⟨N, hE⟩ := hE η hη le_rfl
    obtain ⟨s, u, u', k, hk, hs, hu, hg, hng, hb⟩ := H η hη hηx
    set A : Finset ℝ := insert x (s.image a) with hA
    set Z : Finset ℂ := insert ζ₀ (s.biUnion S) with hZ
    have hAη : ∀ α ∈ A, η < α := by
      intro α hα
      rcases Finset.mem_insert.1 hα with rfl | hα
      · exact hηx
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hα
        exact ((hs i).1 hi).1
    have hZ0 : ∀ ζ ∈ Z, ζ ≠ 0 := by
      intro ζ hζ
      rcases Finset.mem_insert.1 hζ with rfl | hζ
      · exact hζ₀
      · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hζ
        rintro rfl
        exact hS0 i hi
    have hev : ∀ᶠ j : ℕ in atTop, ∀ i ∈ s, τ i j = ∑ ζ ∈ Z, C i ζ * ζ ^ j := by
      refine (Filter.eventually_all_finset s).2 fun i hi => ?_
      filter_upwards [hSC i ((hs i).1 hi).2 (hη.trans ((hs i).1 hi).1)] with j hj
      exact hj Z ((Finset.subset_biUnion_of_mem S hi).trans (Finset.subset_insert _ _))
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
    have hmem : (x, ζ₀) ∈ A ×ˢ Z :=
      Finset.mem_product.2 ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
    have main := hE (A ×ˢ Z : Finset (ℝ × ℂ)) (fun q => q.1.1) (fun q => q.1.2)
      (fun q => hAη _ (Finset.mem_product.1 q.2).1) (fun q => hZ0 _ (Finset.mem_product.1 q.2).2)
      (fun q q' h => Subtype.ext h)
      (fun j q => ∑ i ∈ s with a i = q.1.1, u i (d j) * C i q.1.2)
      (fun q => ∑ i ∈ s with a i = q.1.1, u' i * C i q.1.2)
      (fun q => tendsto_finset_sum _ fun i hi =>
        ((hu i (Finset.mem_filter.1 hi).1).comp hdt).mul_const _)
      (fun s₀ => by
        obtain ⟨K, hK⟩ := hb N s₀
        refine ⟨K, ?_⟩
        filter_upwards [hK, eventually_ge_atTop J] with j hj hjJ m hm m' hm'
        have e := abs_sum_eq s a A Z
          (fun i hi => Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hi))
          (fun i => u i (d j)) C (fun i => τ i (j + m')) (fun α => (α : ℂ) ^ d j)
          (fun α => (cheb η (j / p + m) α : ℂ)) (j + m') (hJ (j + m') (by omega))
        rw [← Finset.sum_coe_sort] at e
        exact (congrArg norm e).trans_le (hj m hm m' hm'))
      ⟨(x, ζ₀), hmem⟩ le_rfl
      (by simp only [neg_neg]; rw [Real.exp_log (norm_pos_iff.2 hζ₀)])
    have e : ∑ i ∈ s with a i = x, u' i * C i ζ₀ = k * ∑ i ∈ hF.toFinset, C i ζ₀ := by
      rw [Finset.mul_sum]
      symm
      refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
      · intro i hi
        have hi := hF.mem_toFinset.1 hi
        exact Finset.mem_filter.2 ⟨(hs i).2 ⟨by rw [hi.2.2]; exact hηx, hi.1⟩, hi.2.2⟩
      · intro i hi
        obtain ⟨hi1, hi2⟩ := Finset.mem_sdiff.1 hi
        obtain ⟨hi3, hi4⟩ := Finset.mem_filter.1 hi1
        rw [hng i hi3 fun h => hi2 (hF.mem_toFinset.2 ⟨((hs i).1 hi3).2, h, hi4⟩), zero_mul]
      · intro i hi
        have hi := hF.mem_toFinset.1 hi
        rw [hg i ((hs i).2 ⟨by rw [hi.2.2]; exact hηx, hi.1⟩) hi.2.1 hi.2.2]
    exact (mul_eq_zero.1 (e.symm.trans main)).resolve_left hk
  have hev : ∀ᶠ j : ℕ in atTop, ∀ i ∈ hF.toFinset,
      τ i j = ∑ ζ ∈ hF.toFinset.biUnion S, C i ζ * ζ ^ j := by
    refine (Filter.eventually_all_finset _).2 fun i hi => ?_
    have hi' := hF.mem_toFinset.1 hi
    filter_upwards [hSC i hi'.1 (by rw [hi'.2.2]; exact hx)] with j hj
    exact hj _ (Finset.subset_biUnion_of_mem S hi)
  filter_upwards [hev] with j hj
  refine (finsum_mem_eq_finite_toFinset_sum (fun i => τ i j) hF).trans ?_
  rw [Finset.sum_congr rfl hj, Finset.sum_comm]
  refine Finset.sum_eq_zero fun ζ hζ => ?_
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hζ
  rw [← Finset.sum_mul, key ζ (by rintro rfl; exact hS0 i hi), zero_mul]
end

section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private theorem UpperTheory.ConvolutionTheory.Ci.finSplit {A B : Type} (x : ℝ) (PE : A → Prop) (PF : B → Prop)
    (Q : (ℝ × A) ⊕ (ℝ × B) → Prop) (hE : ∀ y, Q (Sum.inl y) ↔ y.1 = x ∧ PE y.2)
    (hF : ∀ y, Q (Sum.inr y) ↔ y.1 = x ∧ PF y.2) (hfin : {i | Q i}.Finite) (τ : (ℝ × A) ⊕ (ℝ × B) → ℂ) :
    {V | PF V}.Finite ∧ ∑ᶠ i ∈ {i | Q i}, τ i =
      (∑ᶠ V ∈ {V | PE V}, τ (Sum.inl (x, V))) + ∑ᶠ V ∈ {V | PF V}, τ (Sum.inr (x, V)) := by
  have iE : Function.Injective fun V : A => (Sum.inl (x, V) : (ℝ × A) ⊕ (ℝ × B)) := fun V W h => by simpa using h
  have iF : Function.Injective fun V : B => (Sum.inr (x, V) : (ℝ × A) ⊕ (ℝ × B)) := fun V W h => by simpa using h
  have hS : {i | Q i} = (fun V : A => (Sum.inl (x, V) : (ℝ × A) ⊕ (ℝ × B))) '' {V | PE V} ∪
      (fun V : B => (Sum.inr (x, V) : (ℝ × A) ⊕ (ℝ × B))) '' {V | PF V} := by
    ext i
    rcases i with ⟨a, V⟩ | ⟨a, V⟩
    · simp only [Set.mem_setOf_eq, hE, Set.mem_union, Set.mem_image]
      constructor
      · rintro ⟨rfl, h⟩; exact Or.inl ⟨V, h, rfl⟩
      · rintro (⟨W, h, e⟩ | ⟨W, h, e⟩)
        · cases e; exact ⟨rfl, h⟩
        · cases e
    · simp only [Set.mem_setOf_eq, hF, Set.mem_union, Set.mem_image]
      constructor
      · rintro ⟨rfl, h⟩; exact Or.inr ⟨V, h, rfl⟩
      · rintro (⟨W, h, e⟩ | ⟨W, h, e⟩)
        · cases e
        · cases e; exact ⟨rfl, h⟩
  rw [hS] at hfin ⊢
  rw [Set.finite_union] at hfin
  refine ⟨Set.Finite.of_finite_image hfin.2 iF.injOn, ?_⟩
  rw [finsum_mem_union _ hfin.1 hfin.2, finsum_mem_image iE.injOn, finsum_mem_image iF.injOn]
  rw [Set.disjoint_left]
  rintro _ ⟨V, -, rfl⟩ ⟨W, -, e⟩
  cases e

private theorem UpperTheory.ConvolutionTheory.Ci.abs2 {A B : Type} (τE : ℝ × A → ℕ → ℂ) (τF : ℝ × B → ℕ → ℂ) (actE : ℝ × A → Prop)
    (actF : ℝ × B → Prop) (gE : A → Prop) (gF : B → Prop) (c : ℂ) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (p : ℕ) (hp : 0 < p)
    (cE cF : ℝ) (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0))
    (hd' : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial)
    (eE : ∀ i, actE i → 0 < i.1 → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τE i j = ∑ ζ ∈ s, c ζ * ζ ^ j)
    (eF : ∀ i, actF i → 0 < i.1 → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τF i j = ∑ ζ ∈ s, c ζ * ζ ^ j)
    (main : ∀ η : ℝ, 0 < η → η < x → ∃ (sE : Finset (ℝ × A)) (sF : Finset (ℝ × B)) (uE : ℝ × A → ℕ → ℂ)
      (uF : ℝ × B → ℕ → ℂ) (w : ℝ → ℂ), w x ≠ 0 ∧ (∀ y, y ∈ sE ↔ η < y.1 ∧ actE y) ∧ (∀ y, y ∈ sF ↔ η < y.1 ∧ actF y) ∧
      (∀ y ∈ sE, (gE y.2 → Tendsto (uE y) atTop (𝓝 (w y.1))) ∧ (¬ gE y.2 → Tendsto (uE y) atTop (𝓝 0))) ∧
      (∀ y ∈ sF, (gF y.2 → Tendsto (uF y) atTop (𝓝 (w y.1))) ∧ (¬ gF y.2 → Tendsto (uF y) atTop (𝓝 0))) ∧
      ∀ (N : ℝ) (s₀ : ℕ), ∃ ME MF : ℝ, 0 ≤ ME ∧ 0 ≤ MF ∧ ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀, ∃ z : ℂ,
        ‖c * z - ∑ y ∈ sE, uE y (d j) * (y.1 : ℂ) ^ d j * (cheb η (j / p + m) y.1 : ℂ) * τE y (j + m')‖ ≤
          ME ^ (d j + 1) * (Real.exp (cE * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j)) ∧
        ‖z - ∑ y ∈ sF, uF y (d j) * (y.1 : ℂ) ^ d j * (cheb η (j / p + m) y.1 : ℂ) * τF y (j + m')‖ ≤
          MF ^ (d j + 1) * (Real.exp (cF * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) :
    ∀ᶠ j : ℕ in atTop, ∑ᶠ V ∈ {V | actE (x, V) ∧ gE V}, τE (x, V) j = c * ∑ᶠ V ∈ {V | actF (x, V) ∧ gF V}, τF (x, V) j := by
  classical
  have key := UpperTheory.ConvolutionTheory.Ci.abs ((ℝ × A) ⊕ (ℝ × B)) (Sum.elim Prod.fst Prod.fst) (Sum.elim τE fun y j => -c * τF y j)
    (Sum.elim actE actF) (Sum.elim (fun y => gE y.2) fun y => gF y.2) x hx hx1 p hp (max cE cF) d hd hd' ?_ ?_
  · obtain ⟨hfin, hev⟩ := key
    filter_upwards [hev] with j hj
    obtain ⟨hF, hs⟩ := UpperTheory.ConvolutionTheory.Ci.finSplit x (fun V => actE (x, V) ∧ gE V) (fun V => actF (x, V) ∧ gF V) _
      (by rintro ⟨a, V⟩; simp only [Sum.elim_inl]; constructor
          · rintro ⟨h1, h2, rfl⟩; exact ⟨rfl, h1, h2⟩
          · rintro ⟨rfl, h1, h2⟩; exact ⟨h1, h2, rfl⟩)
      (by rintro ⟨a, V⟩; simp only [Sum.elim_inr]; constructor
          · rintro ⟨h1, h2, rfl⟩; exact ⟨rfl, h1, h2⟩
          · rintro ⟨rfl, h1, h2⟩; exact ⟨h1, h2, rfl⟩) hfin (fun i => Sum.elim τE (fun y j => -c * τF y j) i j)
    replace hj := hs.symm.trans hj
    simp only [Sum.elim_inl, Sum.elim_inr] at hj
    change ∑ᶠ V ∈ {V | actE (x, V) ∧ gE V}, τE (x, V) j = c * ∑ᶠ V ∈ {V | actF (x, V) ∧ gF V}, τF (x, V) j
    rw [finsum_mem_eq_finite_toFinset_sum _ hF] at hj ⊢
    rw [← Finset.mul_sum] at hj
    linear_combination hj
  · rintro (y | y) h1 h2
    · exact eE y h1 h2
    · obtain ⟨s, e, h0, h⟩ := eF y h1 h2
      refine ⟨s, fun ζ => -c * e ζ, h0, ?_⟩
      filter_upwards [h] with j hj
      simp only [Sum.elim_inr, hj, Finset.mul_sum, mul_assoc]
  · intro η h0 h1
    obtain ⟨sE, sF, uE, uF, w, hw, hsE, hsF, huE, huF, hb⟩ := main η h0 h1
    refine ⟨sE.disjSum sF, Sum.elim uE uF,
      Sum.elim (fun y => if gE y.2 then w y.1 else 0) fun y => if gF y.2 then w y.1 else 0, w x, hw, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (y | y)
      · simpa using hsE y
      · simpa using hsF y
    · rintro (y | y) hy
      · have := huE y (by simpa using hy)
        by_cases hg : gE y.2
        · simpa [hg] using this.1 hg
        · simpa [hg] using this.2 hg
      · have := huF y (by simpa using hy)
        by_cases hg : gF y.2
        · simpa [hg] using this.1 hg
        · simpa [hg] using this.2 hg
    · rintro (y | y) - hg ha
      · simp only [Sum.elim_inl] at hg ha ⊢
        rw [if_pos hg, ha]
      · simp only [Sum.elim_inr] at hg ha ⊢
        rw [if_pos hg, ha]
    · rintro (y | y) - hg
      · simp only [Sum.elim_inl] at hg ⊢
        rw [if_neg hg]
      · simp only [Sum.elim_inr] at hg ⊢
        rw [if_neg hg]
    · intro N s₀
      obtain ⟨ME, MF, hME, hMF, hev⟩ := hb N s₀
      refine ⟨ME + (1 + ‖c‖) * MF, ?_⟩
      filter_upwards [hev] with j hj m hm m' hm'
      obtain ⟨z, h2, h3⟩ := hj m hm m' hm'
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr]
      set SE := ∑ y ∈ sE, uE y (d j) * (y.1 : ℂ) ^ d j * (cheb η (j / p + m) y.1 : ℂ) * τE y (j + m') with hSE
      set SF := ∑ y ∈ sF, uF y (d j) * (y.1 : ℂ) ^ d j * (cheb η (j / p + m) y.1 : ℂ) * τF y (j + m') with hSF
      have e1 : ∑ y ∈ sF, uF y (d j) * (y.1 : ℂ) ^ d j * (cheb η (j / p + m) y.1 : ℂ) * (-c * τF y (j + m')) = -c * SF := by
        rw [hSF, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [e1]
      set Er := Real.exp (max cE cF * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j)
        with hEr
      have mono : ∀ e : ℝ, e ≤ max cE cF →
          Real.exp (e * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j) ≤ Er := by
        intro e he
        rw [hEr]
        gcongr
      have hEr0 : 0 ≤ Er := by rw [hEr]; positivity
      have h4 : ‖c * z - SE‖ ≤ ME ^ (d j + 1) * Er :=
        h2.trans (mul_le_mul_of_nonneg_left (mono _ (le_max_left _ _)) (by positivity))
      have h5 : ‖z - SF‖ ≤ MF ^ (d j + 1) * Er :=
        h3.trans (mul_le_mul_of_nonneg_left (mono _ (le_max_right _ _)) (by positivity))
      have h6 : ‖c‖ ≤ (1 + ‖c‖) ^ (d j + 1) :=
        (le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ (le_add_of_nonneg_right (norm_nonneg _)) (by omega))
      have e2 : SE + -c * SF = c * (z - SF) - (c * z - SE) := by ring
      rw [e2]
      calc _ ≤ ‖c * (z - SF)‖ + ‖c * z - SE‖ := norm_sub_le _ _
        _ ≤ (1 + ‖c‖) ^ (d j + 1) * (MF ^ (d j + 1) * Er) + ME ^ (d j + 1) * Er := by
          rw [norm_mul]; gcongr
        _ = (ME ^ (d j + 1) + ((1 + ‖c‖) * MF) ^ (d j + 1)) * Er := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_add_pow_le hME (by positivity) (by omega)) hEr0

private theorem UpperTheory.ConvolutionTheory.Ci.chiEx (η : ℝ) (hη : 0 < η) : ∃ χ : ℝ → ℝ, Continuous χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
    (∀ x ≥ η, χ x = 1) ∧ ∀ x ≤ η / 2, χ x = 0 := by
  refine ⟨fun x => max 0 (min 1 (2 * x / η - 1)), by fun_prop, fun x => ⟨le_max_left _ _, ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · exact max_le zero_le_one (min_le_left _ _)
  · have : 2 ≤ 2 * x / η := by rw [le_div_iff₀ hη]; linarith
    show max 0 (min 1 (2 * x / η - 1)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  · have : 2 * x / η ≤ 1 := by rw [div_le_iff₀ hη]; linarith
    exact max_eq_left ((min_le_right _ _).trans (by linarith))

private theorem UpperTheory.ConvolutionTheory.Ci.degEv (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0)) (p : ℕ) (hp : 0 < p)
    (e : ℕ) : ∀ᶠ j : ℕ in atTop, j / (2 * p) + d j + e ≤ j / p := by
  have h1 := hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * p) by positivity))
  filter_upwards [h1, eventually_ge_atTop (4 * p * e + 1)] with j hj hj'
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  rw [div_lt_div_iff₀ hj0 (by positivity), one_mul] at hj
  have h2 : d j * (4 * p) < j := by exact_mod_cast hj
  have h3 := Nat.div_mul_le_self j (2 * p)
  rw [Nat.le_div_iff_mul_le hp]
  nlinarith

private theorem UpperTheory.ConvolutionTheory.Ci.trOn_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) : trOn ⊥ T = 0 := by
  have : prj (⊥ : Submodule ℂ H) = 0 := by
    ext v
    have h := Submodule.starProjection_apply_mem (⊥ : Submodule ℂ H).topologicalClosure v
    have hb : (⊥ : Submodule ℂ H).topologicalClosure = ⊥ := IsClosed.submodule_topologicalClosure_eq (by simp)
    have h2 : ∀ z : H, z ∈ (⊥ : Submodule ℂ H).topologicalClosure → z = 0 := fun z hz => by rwa [hb, Submodule.mem_bot] at hz
    exact h2 _ h
  rw [trOn, this]
  simp [trace]

private theorem UpperTheory.ConvolutionTheory.Ci.eig_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) (x : ℝ) (hx : 1 < x) : eigIn V A x = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨-, hv⟩
  have h : A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv
  have h1 := A.le_opNorm v
  rw [h, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h1
  have h2 : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v, norm_nonneg A]
  exact norm_le_zero_iff.1 h2

private theorem UpperTheory.ConvolutionTheory.Ci.ptCard {K : Type} [Field K] [NumberField K] {n : ℕ} (b : Datum K n) (S : Set (Pl K)) (Λ) (t)
    (h : b.Pt S Λ t) : ∀ w ∉ S, (t w).card = n := by
  obtain ⟨lam, m, B, h1, -, h3⟩ := h
  intro w hw
  rw [h3 w hw, Multiset.card_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) b.sum
  rw [Multiset.card_map]
  exact ((h1 i).2 w hw).1

private theorem UpperTheory.ConvolutionTheory.Ci.valCongr {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ) (t t' : Pl K → Multiset ℂ)
    (S : Set (Pl K)) (h : ∀ w ∉ S, t w = t' w) (P : PR K n) (hP : ∀ y ∈ P.vars, y.1 ∉ S) : val x Λ t P = val x Λ t' P :=
  eval₂Hom_congr' rfl (fun y hy _ => by rw [hval, hval, h _ (hP y hy)]) rfl

private theorem UpperTheory.ConvolutionTheory.Ci.valC {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ) (t : Pl K → Multiset ℂ)
    (γ : MvPolynomial (Pl K × Fin n) ℂ) : val x Λ t (map C γ : PR K n) = eval (hval t) γ := by
  rw [val, coe_eval₂Hom, eval₂_map]
  change _ = eval₂ (RingHom.id ℂ) _ _
  congr 1
  ext c
  simp

set_option maxHeartbeats 1600000 in
theorem UpperTheory.ConvolutionTheory.Ci.ciOf :
    TrExp → EvVal → ValBc → KillEx → KfBc → TruncSpec → SepPoly → OneSide → EvEx → Kill → CI := by
  classical
  intro hT hV hB hKE hKB hTS hSP hOS hEv hKl F E _ _ _ _ _ _ _ n l hn hl μE _ μF _ θ 𝔢 𝔣 c hG Λ t hΛ ht hoff x hx
  obtain ⟨hS, p, C₀, hp, hG⟩ := hG
  obtain ⟨e0, e1, -, evE, hevE, hinE⟩ := hEv E n hn μE 𝔢.toAmp
  obtain ⟨f0, f1, -, evF, hevF, hinF⟩ := hEv F n hn μF 𝔣.toAmp
  rcases lt_or_ge 1 x with hx1 | hx1
  · refine Eventually.of_forall fun j => ?_
    simp only [Side.tr, eig_bot _ _ e1 x hx1, eig_bot _ _ f1 x hx1, trOn_bot, finsum_zero, mul_zero]
  have bE := bdLem E n
  have msE := (bE ∅ ∅ 0 0 0 0 0 0).2.2.2
  have msF := (bdLem F n ∅ ∅ 0 0 0 0 0 0).2.2.2
  obtain ⟨L, rfl⟩ := msE Λ hΛ
  obtain ⟨cE, hsE⟩ := sideEst hOS hV hTS E n l hn μE θ 𝔢 evE hevE hinE C₀
  obtain ⟨cF, hsF⟩ := sideEst hOS hV hTS F n l hn μF (Twist.id μF) 𝔣 evF hevF hinF C₀
  obtain ⟨d, hd, hd'⟩ := FX.degree
  have key := abs2
    (fun (y : ℝ × Submodule ℂ (LL μE)) j => trOn (eigIn y.2 𝔢.toAmp.A y.1) ((𝔢.Uq 0 ^ j) ∘L Rop μE 𝔢.g ∘L θ.U))
    (fun (y : ℝ × Submodule ℂ (LL μF)) j => trOn (eigIn y.2 𝔣.toAmp.A y.1) ((𝔣.Uq 0 ^ j) ∘L Rop μF 𝔣.g ∘L (Twist.id μF).U))
    (fun y => IsSummand μE y.2 ∧ y.2.map (θ.U : LL μE →ₗ[ℂ] LL μE) = y.2 ∧ eigIn y.2 𝔢.toAmp.A y.1 ≠ ⊥)
    (fun y => IsSummand μF y.2 ∧ y.2.map ((Twist.id μF).U : LL μF →ₗ[ℂ] LL μF) = y.2 ∧ eigIn y.2 𝔣.toAmp.A y.1 ≠ ⊥)
    (fun V => At μE 𝔢.S V (msOf L) t)
    (fun V => ∃ Λ' t', At μF 𝔣.S V Λ' t' ∧ msOf L = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, t w = bcSat t' w)
    c x hx hx1 (2 * p) (by omega) cE cF d hd hd' ?_ ?_ ?_
  · filter_upwards [key] with j hj
    unfold Side.tr
    convert hj using 1
    · refine finsum_mem_inter_support_eq' _ _ _ fun V hV0 => ?_
      have : eigIn V 𝔢.toAmp.A x ≠ ⊥ := fun h => hV0 (by simp only [h, trOn_bot])
      exact ⟨fun h => ⟨⟨h.1, h.2.1, this⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2.1, h.2⟩⟩
    · congr 1
      refine finsum_mem_inter_support_eq' _ _ _ fun V hV0 => ?_
      have : eigIn V 𝔣.toAmp.A x ≠ ⊥ := fun h => hV0 (by simp only [h, trOn_bot])
      exact ⟨fun h => ⟨⟨h.1, h.2.1, this⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2.1, h.2⟩⟩
  · intro y hy h0
    have hη : 0 < min (y.1 / 2) 1 := lt_min (by linarith) one_pos
    obtain ⟨χ, c1, c2, c3, -⟩ := chiEx _ hη
    obtain ⟨s, s1, s2, -⟩ := hsE _ hη (min_le_right _ _) χ c1 c2 c3
    exact hT E n l hl μE θ 𝔢 y.2 y.1 e0 hy.1 (s2 y ((s1 y).2 ⟨(min_le_left _ _).trans_lt (by linarith), hy⟩))
  · intro y hy h0
    have hη : 0 < min (y.1 / 2) 1 := lt_min (by linarith) one_pos
    obtain ⟨χ, c1, c2, c3, -⟩ := chiEx _ hη
    obtain ⟨s, s1, s2, -⟩ := hsF _ hη (min_le_right _ _) χ c1 c2 c3
    exact hT F n l hl μF _ 𝔣 y.2 y.1 f0 hy.1 (s2 y ((s1 y).2 ⟨(min_le_left _ _).trans_lt (by linarith), hy⟩))
  intro η h0 h1
  obtain ⟨χ, c1, c2, c3, c4⟩ := chiEx η h0
  have c5 : ∀ x, |χ x| ≤ 1 := fun x => by rw [abs_of_nonneg (c2 x).1]; exact (c2 x).2
  obtain ⟨sE, conjLinearRankOne, -, sE3⟩ := hsE η h0 (h1.le.trans hx1) χ c1 c2 c3
  obtain ⟨sF, sF1, -, sF3⟩ := hsF η h0 (h1.le.trans hx1) χ c1 c2 c3
  obtain ⟨B, _, b, hb, hk⟩ := hKl E n hn μE 𝔢.toAmp η h0
  obtain ⟨B', _, b', hb', hk'⟩ := hKl F n hn μF 𝔣.toAmp η h0
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, hΦ2⟩ := hKE F E n 𝔢.S 𝔣.S hS B B' b b' hb hb' L t (fun w hw => (ht w hw).1) hoff
  obtain ⟨⟨G, hGen⟩, hTG⟩ := hTS E n 𝔢.S Φ hΦ
  obtain ⟨⟨κ₁, D₁, hκ₁, hBd⟩, hlim, -⟩ := hTG G hGen
  obtain ⟨Φ', G', hΦ', hGen', htr, hev'⟩ := hKB F E n 𝔢.S 𝔣.S hS Φ G hΦ hGen
  have hkill' : ∀ i, Kills 𝔣.S Φ' (b' i) := fun i L' t' hpt => by
    rw [hev' L' t' (ptCard _ _ _ _ hpt)]
    exact hΦ2 i L' t' hpt
  have pE : ∀ y : sE, ∃ Λ t, At μE 𝔢.S y.1.2 Λ t := fun y =>
    have h := (conjLinearRankOne y).1 y.2
    (hV E n hn μE 𝔢.toAmp y.1.2 y.1.1 (h0.trans h.1) h.2.1).1 h.2.2.2
  have pF : ∀ y : sF, ∃ Λ t, At μF 𝔣.S y.1.2 Λ t := fun y =>
    have h := (sF1 y).1 y.2
    (hV F n hn μF 𝔣.toAmp y.1.2 y.1.1 (h0.trans h.1) h.2.1).1 h.2.2.2
  choose ΛE tE hE using pE
  choose ΛF tF hF using pF
  obtain ⟨P₀, κ₂, D₂, hκ₂, hP₀, hP1, hP2⟩ := hSP E n 𝔢.S (msOf L) t
    ({y : sE // ¬ At μE 𝔢.S y.1.2 (msOf L) t} ⊕
      {y : sF // ¬ ∃ Λ' t', At μF 𝔣.S y.1.2 Λ' t' ∧ msOf L = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, t w = bcSat t' w})
    (Sum.elim (fun y => ΛE y.1) fun y => bcInf (ΛF y.1)) (Sum.elim (fun y => tE y.1) fun y => bcSat (tF y.1))
    hΛ (fun w hw => (ht w hw).1)
    (by rintro (y | y) τ
        · exact ((hE y.1).1 τ).1
        · exact ((hF y.1).1 _).1)
    (by rintro (y | y) w hw
        · exact ((hE y.1).2 w hw).1
        · exact (Multiset.card_map _ _).trans ((hF y.1).2 _ (mt (hS w).2 hw)).1)
    (by rintro (y | y) ⟨a1, a2⟩
        · refine y.2 ⟨fun τ => ?_, fun w hw => ?_⟩
          · exact (congrArg (SInf μE y.1.1.2 τ) (congrFun a1 τ)).mpr ((hE y.1).1 τ)
          · exact (congrArg (SSat μE y.1.1.2 w) (a2 w hw)).mpr ((hE y.1).2 w hw)
        · exact y.2 ⟨_, _, hF y.1, a1, a2⟩)
  have hκ : ∀ w ∈ κ₁ ∪ κ₂, w ∉ 𝔢.S := fun w hw => (Finset.mem_union.1 hw).elim (hκ₁ w) (hκ₂ w)
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hG (κ₁ ∪ κ₂) hκ t (fun w hw => ht w (hκ w hw)) (D₁ + D₂)
  have hPv : ∀ y ∈ (map C γ * P₀ : PR E n).vars, y.1 ∉ 𝔢.S := fun y hy => by
    rcases Finset.mem_union.1 (vars_mul _ _ hy) with h | h
    · exact hκ _ (hγ1 y (vars_map _ _ h))
    · exact hκ₂ _ (hP₀.1 y h)
  have hB0 := hB F E n 0 (fun _ => 0) (fun _ => Multiset.replicate n 0) (map C γ * P₀) (fun _ _ => Multiset.card_replicate _ _)
  have hPv' : ∀ y ∈ (bcPR F (map C γ * P₀ : PR E n)).vars, y.1 ∉ 𝔣.S := fun y hy => by
    obtain ⟨y', h1, h2⟩ := hB0.2.1 y hy
    rw [h2]
    exact mt (hS _).2 (hPv y' h1)
  obtain ⟨uE, uE1, uE2⟩ := sE3 Φ G hΦ hGen (hk evE hevE χ c1 c4 c5 Φ G hΦ hΦ1 hGen) _ hPv
  obtain ⟨uF, uF1, uF2⟩ := sF3 Φ' G' hΦ' hGen' (hk' evF hevF χ c1 c4 c5 Φ' G' hΦ' hkill' hGen') _ hPv'
  have vF : ∀ (V : Submodule ℂ (LL μF)) (a : ℝ) Λ' t', At μF 𝔣.S V Λ' t' →
      val a Λ' t' (bcPR F (map C γ * P₀ : PR E n)) = val a (bcInf Λ') (bcSat t') (map C γ * P₀ : PR E n) :=
    fun V a Λ' t' h => (hB F E n a Λ' t' _ fun y hy => (h.2 _ (mt (hS _).2 (hPv y hy))).1).1
  refine ⟨sE, sF, uE, uF, fun a => a * val a (msOf L) t (map C γ * P₀ : PR E n) * evK L (hval t) Φ, ?_, conjLinearRankOne, sF1, ?_, ?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero (by exact_mod_cast hx.ne') ?_) hΦ0
    rw [map_mul, valC]
    exact mul_ne_zero hγ2 (hP1 x hx.ne')
  · refine fun y hy => ⟨fun hg => uE1 y hy L t hg, fun hg => ?_⟩
    obtain ⟨L', hL'⟩ := msE (ΛE ⟨y, hy⟩) fun τ => ((hE _).1 τ).1
    have := uE1 y hy L' (tE ⟨y, hy⟩) (hL' ▸ hE ⟨y, hy⟩)
    have z : val y.1 (ΛE ⟨y, hy⟩) (tE ⟨y, hy⟩) P₀ = 0 := hP2 (Sum.inl ⟨⟨y, hy⟩, hg⟩) y.1
    rwa [hL', map_mul, z, mul_zero, mul_zero, zero_mul] at this
  · refine fun y hy => ⟨fun hg => ?_, fun hg => ?_⟩
    · obtain ⟨Λ', t', a1, a2, a3⟩ := hg
      obtain ⟨L', rfl⟩ := msF Λ' fun τ => (a1.1 τ).1
      have := uF1 y hy L' t' a1
      rw [vF _ _ _ _ a1, hev' L' t' (fun v hv => (a1.2 v hv).1), ← a2, ← valCongr y.1 _ t _ 𝔢.S a3 _ hPv] at this
      have e : evK (fun y : Ix E n => L' (y.1.comp (algebraMap F E), y.2)) (hval (bcSat t')) Φ = evK L (hval t) Φ := by
        obtain ⟨u, u1, u2⟩ := hlim L t
        obtain ⟨u', u1', u2'⟩ := hlim (fun y : Ix E n => L' (y.1.comp (algebraMap F E), y.2)) (bcSat t')
        have : u' = u := funext fun k => by
          have b1 := u2 1 k
          have b2 := u2' 1 k
          have b3 : msOf (fun y : Ix E n => L' (y.1.comp (algebraMap F E), y.2)) = msOf L := a2.symm
          rw [b3, ← valCongr 1 _ t _ 𝔢.S a3 _ (fun y hy => hκ₁ _ ((hBd k).1 y hy)), b1] at b2
          simpa using b2.symm
        rw [this] at u1'
        exact tendsto_nhds_unique u1' u1
      rwa [e] at this
    · obtain ⟨L', hL'⟩ := msF (ΛF ⟨y, hy⟩) fun τ => ((hF _).1 τ).1
      have := uF1 y hy L' (tF ⟨y, hy⟩) (hL' ▸ hF ⟨y, hy⟩)
      have z : val y.1 (bcInf (ΛF ⟨y, hy⟩)) (bcSat (tF ⟨y, hy⟩)) P₀ = 0 := hP2 (Sum.inr ⟨⟨y, hy⟩, hg⟩) y.1
      rwa [hL', vF _ _ _ _ (hF ⟨y, hy⟩), map_mul, z, mul_zero, mul_zero, zero_mul] at this
  · intro N s₀
    obtain ⟨ME, hME, bdE⟩ := uE2 (2 * p) N s₀
    obtain ⟨MF, hMF, bdF⟩ := uF2 (2 * p) N s₀
    refine ⟨ME, MF, hME, hMF, ?_⟩
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hγ3 evE evF hevE hevF)
    filter_upwards [degEv d hd p hp (s₀ + D₂), eventually_ge_atTop j₀] with j hj hj' m hm m' hm'
    have r1 := (bE κ₁ κ₂ D₁ D₂ (d j) D₂ _ _).1 (hBd (d j)) hP₀
    have r2 := (bE (κ₁ ∪ κ₂) (κ₁ ∪ κ₂) 0 (D₁ + D₂) (j / (2 * p) + m) (d j + D₂) _ _).1
      ((bE (κ₁ ∪ κ₂) ∅ 0 0 0 0 0 0).2.1 η _) r1
    rw [Finset.union_idempotent, zero_add] at r2
    have hdiv : j / p ≤ (j + m') / p := Nat.div_le_div_right (Nat.le_add_right _ _)
    obtain ⟨fE, fF, g1, g2, g3⟩ := hj₀ (j + m') (by omega) _ r2.1 r2.2.1 (fun β => (r2.2.2 β).trans (by omega))
    have q1 : (map C γ * (chebP η (j / (2 * p) + m) * (trunc (d j) G * P₀)) : PR E n) =
        chebP η (j / (2 * p) + m) * (trunc (d j) G * (map C γ * P₀)) := by ring
    rw [q1] at g1 g2
    rw [map_mul (bcPR F), hB0.2.2, map_mul (bcPR F), ← htr] at g2
    refine ⟨twInt (Twist.id μF) fF, ?_, bdF j (d j) m hm m' hm' fF g2⟩
    rw [← g3]
    exact bdE j (d j) m hm m' hm' fE g1
end

section
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.Ci in

theorem UpperTheory.ConvolutionTheory.ci : UpperTheory.ConvolutionTheory.CI :=
  ciOf (trExp expForm) (evVal evEx Dp.parEx) valBc (killEx Dp.parEx) kfBc truncSpec sepPoly
    (oneSide K.kern2 C.polyBdAll C.smoothDecay C.decayTraceClass C.cuspTrBand Dp.multiplicity_one_cuspidal_spectrum_normOneGL evEx) evEx kill
end
