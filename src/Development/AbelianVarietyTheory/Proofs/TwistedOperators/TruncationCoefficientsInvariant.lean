import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaDecompositionAdelicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyUnipotentInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsAUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviMonotoneInParabolicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicDeterminantMultiplicative
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviMonotoneInParabolic

section
section
open MeasureTheory GlobalTheory.Chamber Filter Topology

noncomputable section

namespace GlobalTheory.Chamber

theorem sumM_expFam_shift {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (X Y : Finset (SV k) → A0 k) (h : A0 k)
    (hY : ∀ P ∈ parP 𝔞 Q, Y P = X P + pr P h) (l : A0 k) :
    sumM 𝔞 Q (expFam Y) l = eL l (𝔞.starProjection h) * sumM 𝔞 Q (expFam X) l := by
  unfold sumM
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hP' := (mem_parP.1 hP).2.1
  have e : pr P h = 𝔞.starProjection h := by subst hP'; rfl
  simp only [expFam, hY P hP, e, eL, inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem cM_expFam_shift_zero : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅,
    ∀ X Y : Finset (SV k) → A0 k, IsOrth 𝔞 X → ∀ h : A0 k, (∀ P ∈ parP 𝔞 Q, Y P = X P + pr P h) →
      cM 𝔞 Q (expFam Y) 0 = cM 𝔞 Q (expFam X) 0 := by
  intro hFS k 𝔞 hL Q hQ X Y hX h hY
  have hc := (hFS k 𝔞 hL (expFam X) hX.isGMFam Q hQ).1
  have t1 : Tendsto (sumM 𝔞 Q (expFam X)) (𝓝[generic k] 0) (𝓝 (cM 𝔞 Q (expFam X) 0)) :=
    ((hc.1.continuous.tendsto 0).mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun l hl => hc.2 hl)
  have hg : Continuous fun l : A0 k => eL l (𝔞.starProjection h) := by
    unfold eL; fun_prop
  have t2 : Tendsto (fun l : A0 k => eL l (𝔞.starProjection h)) (𝓝[generic k] 0) (𝓝 1) := by
    have := (hg.tendsto 0).mono_left (nhdsWithin_le_nhds (s := generic k))
    simpa [eL] using this
  have t3 := t2.mul t1
  rw [one_mul] at t3
  unfold cM
  refine extendFrom_eq (dense_generic 0) ?_
  have e : sumM 𝔞 Q (expFam Y) = fun l => eL l (𝔞.starProjection h) * sumM 𝔞 Q (expFam X) l :=
    funext (sumM_expFam_shift 𝔞 Q X Y h hY)
  rw [e]
  exact t3

end GlobalTheory.Chamber
end
end

open MeasureTheory GlobalTheory.Chamber
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chamber_coefficient_translation : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅, ∀ X Y : Finset (SV k) → A0 k, IsOrth 𝔞 X → ∀ h : A0 k, (∀ P ∈ parP 𝔞 Q, Y P = X P + pr P h) → cM 𝔞 Q (expFam Y) 0 = cM 𝔞 Q (expFam X) 0 := by
  atlas_forward_decl GlobalTheory.Chamber.cM_expFam_shift_zero
end

section
section
noncomputable section

open MeasureTheory GlobalTheory.Chamber Finset
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FamCont

theorem deriv_pow_succ_mul {g : ℝ → ℂ} (hg : Differentiable ℝ g) (m : ℕ) :
    deriv (fun t : ℝ => (t : ℂ) ^ (m + 1) * g t) =
      fun t : ℝ => (t : ℂ) ^ m * (((m : ℂ) + 1) * g t + (t : ℂ) * deriv g t) := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (t : ℂ) ^ m) t := by
    simpa using (hasDerivAt_pow (m + 1) (t : ℂ)).comp_ofReal
  have h3 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (m + 1) * g t)
      (((m + 1 : ℕ) : ℂ) * (t : ℂ) ^ m * g t + (t : ℂ) ^ (m + 1) * deriv g t) t := h1.mul (hg t).hasDerivAt
  rw [h3.deriv]
  push_cast; ring

theorem contDiff_linear_deriv_combination {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (a : ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => a * g t + (t : ℂ) * deriv g t) := by
  have hd := (contDiff_infty_iff_deriv.1 hg).2
  exact (contDiff_const.mul hg).add (Complex.ofRealCLM.contDiff.mul hd)

theorem iteratedDeriv_pow_mul (n : ℕ) : ∀ g : ℝ → ℂ, ContDiff ℝ ∞ g →
    iteratedDeriv n (fun t : ℝ => (t : ℂ) ^ n * g t) 0 = n.factorial * g 0 := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [iteratedDeriv_succ', deriv_pow_succ_mul (hg.differentiable (by simp)), ih _ (contDiff_linear_deriv_combination hg _)]
    simp [Nat.factorial_succ]
    ring

theorem iteratedDeriv_sum_exp {ι : Type} (s : Finset ι) (e c : ι → ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => ∑ i ∈ s, e i * Complex.exp (c i * t)) =
      fun t : ℝ => ∑ i ∈ s, e i * c i ^ n * Complex.exp (c i * (t : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h : ∀ i ∈ s, HasDerivAt (fun t : ℝ => e i * c i ^ n * Complex.exp (c i * t))
        (e i * c i ^ (n + 1) * Complex.exp (c i * t)) t := fun i _ => by
      have h1 : HasDerivAt (fun t : ℝ => c i * (t : ℂ)) (c i) t := by
        simpa using ((hasDerivAt_id (t : ℂ)).const_mul (c i)).comp_ofReal
      have h2 : HasDerivAt (fun t : ℝ => e i * c i ^ n * Complex.exp (c i * t))
          (e i * c i ^ n * (Complex.exp (c i * t) * c i)) t := h1.cexp.const_mul (e i * c i ^ n)
      exact h2.congr_deriv (by ring)
    have hs := HasDerivAt.sum h
    rw [Finset.sum_fn] at hs
    exact hs.deriv

theorem card_eq_finrank {k : ℕ} {P : Finset (SV k)} (h : IsPar P) : Module.finrank ℝ (aP P) = P.card := by
  have li : LinearIndependent ℝ (fun u : (P : Set (SV k)) => vec (k := k) u) := by
    rw [linearIndependent_iff_notMem_span]
    rintro ⟨u, hu⟩
    have h' := h.vec_notMem hu
    convert h' using 3
    rw [aP]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and, Subtype.exists,
      Finset.mem_coe, Finset.mem_erase, Subtype.mk.injEq]
    constructor
    · rintro ⟨a, ha, hne, rfl⟩; exact ⟨a, ⟨hne, ha⟩, rfl⟩
    · rintro ⟨a, ⟨hne, ha⟩, rfl⟩; exact ⟨a, ha, hne, rfl⟩
  have := finrank_span_eq_card li
  rw [aP, Set.image_eq_range, this]
  convert Fintype.card_coe P
  simp

theorem isGMFam_expFam {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (hX : IsOrth 𝔞 X) :
    IsGMFam 𝔞 (expFam X) := by
  intro P hP
  refine ⟨?_, fun R hR l => ?_⟩
  · unfold expFam eL
    exact Complex.contDiff_exp.comp (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)))
  · simp only [expFam, eL]
    rw [hX P hP R hR, pr, Submodule.inner_starProjection_left_eq_right]

theorem smul_mem_generic {k : ℕ} {l : A0 k} (hl : l ∈ generic k) {t : ℝ} (ht : t ≠ 0) : t • l ∈ generic k := by
  intro P hP R hR u hu
  rw [real_inner_smul_left]
  exact mul_ne_zero ht (hl P hP R hR u hu)

theorem card_sdiff_of_mem_parP {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} {Q P : Finset (SV k)} (hP : P ∈ parP 𝔞 Q) :
    (P \ Q).card = Module.finrank ℝ 𝔞 - Q.card := by
  obtain ⟨hP1, hP2, hP3⟩ := mem_parP.1 hP
  rw [card_sdiff_of_subset hP3, ← card_eq_finrank hP1, hP2]

theorem eps_smul {k : ℕ} (P Q : Finset (SV k)) (l : A0 k) (t : ℝ) :
    eps P Q (t • l) = ((t : ℂ) ^ (P \ Q).card)⁻¹ * eps P Q l := by
  have e1 : ∀ a : ℂ, (Complex.I * ((t : ℂ) * a))⁻¹ = (t : ℂ)⁻¹ * (Complex.I * a)⁻¹ := fun a => by
    rw [mul_left_comm, mul_inv]
  simp only [eps, epsOf, real_inner_smul_left, Complex.ofReal_mul]
  simp_rw [e1, prod_mul_distrib, prod_const, inv_pow]
  ring

theorem cM_expFam_zero (hFS : FamilySmooth) {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} (h𝔞 : IsLevi 𝔞) {Q : Finset (SV k)}
    (hQ : Q ∈ parF 𝔞 ∅) {X : Finset (SV k) → A0 k} (hX : IsOrth 𝔞 X) {l₀ : A0 k} (hl₀ : l₀ ∈ generic k) :
    cM 𝔞 Q (expFam X) 0 = (∑ P ∈ parP 𝔞 Q, eps P Q l₀ *
      (Complex.I * (⟪l₀, X P⟫_ℝ : ℂ)) ^ (Module.finrank ℝ 𝔞 - Q.card)) / (Module.finrank ℝ 𝔞 - Q.card).factorial := by
  set n := Module.finrank ℝ 𝔞 - Q.card
  obtain ⟨⟨hsm, heq⟩, -⟩ := hFS k 𝔞 h𝔞 _ (isGMFam_expFam hX) Q hQ
  set f : ℝ → ℂ := fun t => cM 𝔞 Q (expFam X) (t • l₀) with hfdef
  have hf : ContDiff ℝ ∞ f := hsm.comp (contDiff_id.smul contDiff_const)
  have hfun : (fun t : ℝ => (t : ℂ) ^ n * f t) = fun t : ℝ => ∑ P ∈ parP 𝔞 Q,
      eps P Q l₀ * Complex.exp ((Complex.I * (⟪l₀, X P⟫_ℝ : ℂ)) * (t : ℂ)) := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℝ))
      ((Complex.continuous_ofReal.pow n).mul hf.continuous)
      (continuous_finset_sum _ fun P _ => continuous_const.mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))) ?_
    intro t ht
    have ht : t ≠ 0 := ht
    simp only [hfdef]
    rw [heq (smul_mem_generic hl₀ ht), sumM, mul_sum]
    refine sum_congr rfl fun P hP => ?_
    rw [eps_smul, card_sdiff_of_mem_parP hP, expFam, eL, real_inner_smul_left, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.2 ht)), one_mul]
    congr 2
    push_cast
    ring
  have h1 := iteratedDeriv_pow_mul n f hf
  rw [hfun, iteratedDeriv_sum_exp] at h1
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, hfdef, zero_smul] at h1
  rw [h1, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))]

theorem continuous_cM_expFam_zero : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅,
    ∀ (Z : Type) [TopologicalSpace Z] (X : Z → Finset (SV k) → A0 k), (∀ z, IsOrth 𝔞 (X z)) →
    (∀ P ∈ parP 𝔞 Q, Continuous fun z => X z P) → Continuous fun z => cM 𝔞 Q (expFam (X z)) 0 := by
  intro hFS k 𝔞 h𝔞 Q hQ Z _ X hX hc
  obtain ⟨l₀, hl₀⟩ : (generic k).Nonempty := dense_generic.nonempty
  simp_rw [cM_expFam_zero hFS h𝔞 hQ (hX _) hl₀]
  refine Continuous.div_const (continuous_finset_sum _ fun P hP => ?_) _
  exact continuous_const.mul ((continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_const.inner (hc P hP)))).pow _)

end GlobalTheory.FamCont
end
end

open MeasureTheory GlobalTheory.Chamber
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chamber_coefficient_continuous : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅, ∀ (Z : Type) [TopologicalSpace Z] (X : Z → Finset (SV k) → A0 k), (∀ z, IsOrth 𝔞 (X z)) → (∀ P ∈ parP 𝔞 Q, Continuous fun z => X z P) → Continuous fun z => cM 𝔞 Q (expFam (X z)) 0 := by
  atlas_forward_decl GlobalTheory.FamCont.continuous_cM_expFam_zero
end

section
section
open MeasureTheory GlobalTheory.Chamber

namespace GlobalTheory.Chamber.SumSplit

open Finset in
theorem empty_mem_parF {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) : (∅ : Finset (SV k)) ∈ parF 𝔞 ∅ := by
  refine mem_parF.2 ⟨⟨by simp, by simp⟩, ?_, subset_rfl⟩
  simp [aP]

theorem eL_zero {k : ℕ} (H : A0 k) : eL 0 H = 1 := by simp [eL]

theorem eL_add {k : ℕ} (l H H' : A0 k) : eL l (H + H') = eL l H * eL l H' := by
  simp only [eL, inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem sum_isOrth {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} {X Y W : Finset (SV k) → A0 k} (hX : IsOrth 𝔞 X)
    (hY : IsOrth 𝔞 Y) (hW : ∀ P ∈ parF 𝔞 ∅, W P = X P + Y P) : IsOrth 𝔞 W := by
  intro P hP Q e
  have hQ : Q ∈ parF 𝔞 ∅ := mem_parF.2 ⟨(mem_parF.1 hP).1.mono e, (vecSpan_mono e).trans (mem_parF.1 hP).2.1,
    Finset.empty_subset _⟩
  rw [hW P hP, hW Q hQ, map_add, ← hX P hP Q e, ← hY P hP Q e]

theorem cP_empty_empty {k : ℕ} (c : Finset (SV k) → A0 k → ℂ) (hc : Continuous (c ∅)) (l : A0 k) :
    cP ∅ ∅ c l = c ∅ l := by
  have hs : sumP ∅ ∅ c = c ∅ := by
    funext l
    have h : ∀ b : SV k → A0 k, epsOf (∅ \ ∅) b l = 1 := fun b => by
      have : IsEmpty ↥((∅ : Finset (SV k)) \ ∅) := ⟨fun x => by simpa using x.2⟩
      rw [epsOf, Matrix.det_isEmpty]; simp
    simp only [sumP, between, Finset.powerset_empty, Finset.filter_singleton, Finset.Subset.refl, if_true,
      Finset.sum_singleton, eps, epsHat, h]
    simp
  rw [cP, hs]
  refine extendFrom_eq (by rw [dense_generic.closure_eq]; trivial) ?_
  exact (hc.tendsto l).mono_left nhdsWithin_le_nhds

theorem volume_sum_split : ExpFamilyIntegral → FamilyProduct → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 →
    ∀ X Y W : Finset (SV k) → A0 k, IsOrth 𝔞 X → IsOrth 𝔞 Y → (∀ P ∈ parF 𝔞 ∅, W P = X P + Y P) →
    ((∫ H : aMQ 𝔞 ∅, gamM 𝔞 ∅ W H : ℝ) : ℂ) = cM 𝔞 ∅ (expFam W) 0 ∧
    cM 𝔞 ∅ (expFam W) 0 = ∑ Q ∈ parF 𝔞 ∅, cM 𝔞 Q (expFam X) 0 * cP Q ∅ (expFam Y) 0 ∧
    cP ∅ ∅ (expFam Y) 0 = 1 := by
  intro hI hF k 𝔞 hL X Y W hX hY hW
  have hWo := sum_isOrth hX hY hW
  refine ⟨?_, ?_, ?_⟩
  · rw [(((hI k 𝔞 hL W hWo).2 ∅ (empty_mem_parF 𝔞)).1.2 0)]
    simp only [eL_zero, one_mul]
    exact (integral_ofReal).symm
  · rw [← hF k 𝔞 hL _ _ hX.isGMFam hY.isGMFam ∅ (empty_mem_parF 𝔞) 0]
    have hs : sumM 𝔞 ∅ (expFam W) = sumM 𝔞 ∅ (expFam X * expFam Y) := by
      funext l
      refine Finset.sum_congr rfl fun P hP => ?_
      have hPF : P ∈ parF 𝔞 ∅ := mem_parF.2 ⟨(mem_parP.1 hP).1, (mem_parP.1 hP).2.1.le, Finset.empty_subset _⟩
      simp only [expFam, Pi.mul_apply, hW P hPF, eL_add]
    simp only [cM, hs]
  · rw [cP_empty_empty _ (by
      simpa [expFam] using (((hY.isGMFam) ∅ (empty_mem_parF 𝔞)).1.continuous)) 0]
    exact eL_zero _

end GlobalTheory.Chamber.SumSplit
end

open MeasureTheory GlobalTheory.Chamber
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chamber_coefficient_product_formula : ExpFamilyIntegral → FamilyProduct → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ X Y W : Finset (SV k) → A0 k, IsOrth 𝔞 X → IsOrth 𝔞 Y → (∀ P ∈ parF 𝔞 ∅, W P = X P + Y P) → ((∫ H : aMQ 𝔞 ∅, gamM 𝔞 ∅ W H : ℝ) : ℂ) = cM 𝔞 ∅ (expFam W) 0 ∧ cM 𝔞 ∅ (expFam W) 0 = ∑ Q ∈ parF 𝔞 ∅, cM 𝔞 Q (expFam X) 0 * cP Q ∅ (expFam Y) 0 ∧ cP ∅ ∅ (expFam Y) 0 = 1 := by
  atlas_forward_decl GlobalTheory.Chamber.SumSplit.volume_sum_split
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

open scoped NNReal

namespace GlobalTheory.TruncKer.PlaceAdd

section Abstract

variable {G : Type} [Group G] {P : Subgroup G} {δ : P →* ℝ≥0} {K : Subgroup G} (h : Doubling.IsIwasawa δ K)
  (e : G →* G) (hP : ∀ p ∈ P, e p ∈ P) (hK : ∀ k ∈ K, e k ∈ K) (hc : ∀ a b, Commute (e a) ((e b)⁻¹ * b))
include h hP hK hc

theorem iwAbs_eq_mul (g : G) :
    Doubling.iwAbs δ K g = Doubling.iwAbs δ K (e g) * Doubling.iwAbs δ K ((e g)⁻¹ * g) := by
  obtain ⟨p, k, hk, rfl⟩ := h.1 g
  let q : P := ⟨e p, hP _ p.2⟩
  have e1 : e (p * k) = (q : G) * e k := map_mul _ _ _
  have e2 : (e (p * k))⁻¹ * (p * k) = ((q⁻¹ * p : P) : G) * ((e k)⁻¹ * k) := by
    have := (hc k p).inv_left.eq
    change _ = (e p)⁻¹ * p * ((e k)⁻¹ * k)
    rw [← mul_assoc _ (e k)⁻¹, ← this, map_mul]
    group
  rw [e2, e1, h.iwAbs_mul _ hk, h.iwAbs_mul _ (hK _ hk), h.iwAbs_mul _ (mul_mem (inv_mem (hK _ hk)) hk), ← map_mul,
    mul_inv_cancel_left]

theorem iwAbs_four (w : G) {y z : G} (hy : e y = y) (hz : e z = 1) :
    Doubling.iwAbs δ K (w * (y * z)) * Doubling.iwAbs δ K w =
      Doubling.iwAbs δ K (w * y) * Doubling.iwAbs δ K (w * z) := by
  have c : y⁻¹ * ((e w)⁻¹ * w) = (e w)⁻¹ * w * y⁻¹ := by
    have := (hc y w).inv_left.eq
    rwa [hy] at this
  have a1 : e (w * (y * z)) = e (w * y) := by simp [hz]
  have a2 : e (w * z) = e w := by simp [hz]
  have b2 : (e (w * y))⁻¹ * (w * y) = (e w)⁻¹ * w := by
    rw [map_mul, hy, mul_inv_rev, mul_assoc, ← mul_assoc (e w)⁻¹, ← mul_assoc, c, inv_mul_cancel_right]
  have b1 : (e (w * y))⁻¹ * (w * (y * z)) = (e w)⁻¹ * (w * z) := by
    rw [← mul_assoc w, ← mul_assoc, b2, mul_assoc]
  rw [iwAbs_eq_mul h e hP hK hc (w * (y * z)), iwAbs_eq_mul h e hP hK hc w, iwAbs_eq_mul h e hP hK hc (w * y),
    iwAbs_eq_mul h e hP hK hc (w * z), a1, a2, b1, b2]
  ring

end Abstract

variable {D : D7} {V : HSp D} {Φ : WittFrame V} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
  {a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)}

theorem isIwasawa (hg : Φ.IsGood D.sp.cm L a) (i : Fin (wittIndex V)) :
    Doubling.IsIwasawa (absChi Φ i) (levelAll D.sp.cm.sig V.gram L a) := by
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  exact Doubling.isIwasawa_of_isCompact (Φ.flag0.isClosed_par _ _) (continuous_absChi i) hg.isCompact
    (GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg)

theorem continuous_H0 (hg : Φ.IsGood D.sp.cm L a) : Continuous (H0 Φ (levelAll D.sp.cm.sig V.gram L a)) := by
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact (NNReal.continuous_coe.comp ((isIwasawa hg i).continuous_iwAbs (Φ.flag0.isClosed_par _ _)
    (continuous_absChi i) hg.isCompact)).log fun x => NNReal.coe_ne_zero.2 (Doubling.iwAbs_pos _ _ x).ne'

theorem H0_mul_mul_add_eq_add (hg : Φ.IsGood D.sp.cm L a) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : GA D V) {y z : GA D V}
    (hy : y ∈ atPts D.sp.cm.sig V.gram S) (hz : z ∈ awayPts D.sp.cm.sig V.gram S) (i : Fin (wittIndex V)) :
    H0 Φ (levelAll D.sp.cm.sig V.gram L a) (w * (y * z)) i + H0 Φ (levelAll D.sp.cm.sig V.gram L a) w i =
      H0 Φ (levelAll D.sp.cm.sig V.gram L a) (w * y) i + H0 Φ (levelAll D.sp.cm.sig V.gram L a) (w * z) i := by
  let e : GA D V →* GA D V := (embAt D.sp.cm.sig V.gram S).comp (projAt D.sp.cm.sig V.gram S)
  have hm : ∀ g, e g ∈ atPts D.sp.cm.sig V.gram S := fun g => embAt_mem _ _ S _
  have hA : ∀ g u, projArch D.sp.cm.sig V.gram u (e g) = 1 := fun g =>
    mem_finPts_iff_forall.1 (mem_atPts.1 (hm g)).1
  have hF : ∀ g v, proj D.sp.cm.sig V.gram v (e g) = proj D.sp.cm.sig V.gram v g ∨
      proj D.sp.cm.sig V.gram v (e g) = 1 := fun g v => by
    by_cases hv : v ∈ S
    · exact .inl (proj_embAt _ _ S _ ⟨v, hv⟩)
    · exact .inr ((mem_atPts.1 (hm g)).2 v hv)
  have key := iwAbs_four (isIwasawa hg i) e (fun p hp => IsoFlag.mem_par_adelic.2
      ⟨fun u => by rw [hA]; exact one_mem _, fun v => by
        rcases hF p v with h | h <;> rw [h]
        exacts [(IsoFlag.mem_par_adelic.1 hp).2 v, one_mem _]⟩)
    (fun k hk => mem_levelAll.2 ⟨fun v => by
        rcases hF k v with h | h <;> rw [h]
        exacts [(mem_levelAll.1 hk).1 v, one_mem _], fun u => by rw [hA]; exact one_mem _⟩)
    (fun b c => commute_atPts_awayPts _ _ (hm b) (partAway D.sp.cm.sig V.gram S c).2) w (y := y) (z := z)
    (by
      obtain ⟨x, rfl⟩ := (range_embAt D.sp.cm.sig V.gram S).ge hy
      exact congrArg (embAt D.sp.cm.sig V.gram S) (projAt_embAt _ _ S x))
    (by
      have : projAt D.sp.cm.sig V.gram S z = 1 := funext fun v => mem_awayPts.1 hz v v.2
      exact (congrArg (embAt D.sp.cm.sig V.gram S) this).trans (map_one _))
  have n : ∀ x, ((Doubling.iwAbs (absChi Φ i) (levelAll D.sp.cm.sig V.gram L a) x : ℝ≥0) : ℝ) ≠ 0 := fun x =>
    NNReal.coe_ne_zero.2 (Doubling.iwAbs_pos _ _ x).ne'
  change Real.log _ + Real.log _ = Real.log _ + Real.log _
  rw [← Real.log_mul (n _) (n _), ← Real.log_mul (n _) (n _), ← NNReal.coe_mul, ← NNReal.coe_mul, key]

end GlobalTheory.TruncKer.PlaceAdd

namespace GlobalTheory.TruncKer

open PlaceAdd in

theorem yfam_continuous_add : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ Q, IsPar Q → (∀ Tr, Continuous fun x => Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q) ∧ ∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, ∀ Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (y * z) Tr Q = (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) y 0 Q - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0 Q) + Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr Q := by
  intro D V Φ L a hg Q hQ
  obtain ⟨π, ε, w, -, -, hY⟩ := exists_Yfam_eq (Φ := Φ) (K := levelAll D.sp.cm.sig V.gram L a) hQ
  refine ⟨fun Tr => ?_, fun S y hy z hz Tr => ?_⟩
  · simp only [hY]
    refine (pr Q).continuous.comp ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_))
    exact continuous_const.mul ((PiLp.continuous_apply 2 _ (π i)).comp
      (continuous_const.sub ((continuous_H0 hg).comp (continuous_const.mul continuous_id))))
  · rw [hY, hY, hY, hY, ← map_sub, ← map_add]
    congr 1
    ext i
    have := H0_mul_mul_add_eq_add hg S (rat V w) hy hz (π i)
    simp only [Ys, inverseChamberMap, PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply, mul_one]
    linear_combination (-((ε i : SignType) : ℝ)) * this

end GlobalTheory.TruncKer

end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_family_place_additive : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ Q, IsPar Q → (∀ Tr, Continuous fun x => Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q) ∧ ∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, ∀ Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (y * z) Tr Q = (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) y 0 Q - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0 Q) + Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr Q := by
  atlas_forward_decl GlobalTheory.TruncKer.yfam_continuous_add
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_family_unipotent_invariant : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ Q, IsPar Q → ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), ∀ n ∈ NA (IsoFlag.single hW), ∀ x Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (n * x) Tr Q = Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q := by
  first | exact @GlobalTheory.TruncKer.yfam_unipRad_mul | exact GlobalTheory.TruncKer.yfam_unipRad_mul | (intros; apply GlobalTheory.TruncKer.yfam_unipRad_mul <;> assumption)
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift

noncomputable section

open scoped TensorProduct NNReal

namespace GlobalTheory.LeviShift

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

theorem bas_stdVec (j i : Fin (wittIndex V)) : bas Φ (stdVec j) i = Φ.e i := by
  unfold bas; rw [if_neg]; unfold stdVec; split_ifs <;> decide

theorem dbas_stdVec (j i : Fin (wittIndex V)) : dbas Φ (stdVec j) i = Φ.f i := by
  unfold dbas; rw [if_neg]; unfold stdVec; split_ifs <;> decide

theorem detMat_stdVec_apply (j : Fin (wittIndex V)) (p : PA Φ.flag0) (a b : Supp (stdVec j)) :
    detMat Φ D.sp.cm (AF D.host.F) (stdVec j) p a b =
      Φ.coef D.sp.cm (AF D.host.F) a.1
        (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act D.sp.cm V (p : GA D V) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V (AF D.host.F) (Φ.e b.1))) := by
  simp only [detMat, Matrix.of_apply, bas_stdVec, dbas_stdVec]; rfl

theorem detMat_stdVec_blockTriangular (j : Fin (wittIndex V)) (p : PA Φ.flag0) :
    (detMat Φ D.sp.cm (AF D.host.F) (stdVec j) p).BlockTriangular id := by
  intro a b hba
  rw [detMat_stdVec_apply]
  apply Φ.coef_eq_zero
  have he : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V (AF D.host.F) (Φ.e b.1) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub (F := D.host.F) V (AF D.host.F) (Φ.flag0.X b.1.succ) :=
    coordR_mem V _ (Submodule.subset_span ⟨b.1, Nat.lt_succ_self _, rfl⟩)
  have h1 := mem_parab_iff_maps.1 (IsoFlag.mem_par.1 p.2 b.1.succ) _ he
  have hle : b.1.succ ≤ a.1.castSucc := by
    have : b.1.val < a.1.val := hba
    rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]; omega
  exact Submodule.span_mono (Set.image_mono (Φ.flag0.strictMono.monotone hle)) h1

theorem prod_absChi_eq_absA_detU (j : Fin (wittIndex V)) (p : PA Φ.flag0) :
    ∏ i ∈ Finset.Iic j, absChi Φ i p = absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) := by
  have hdet : detU Φ D.sp.cm (AF D.host.F) (stdVec j) p =
      ((∏ a : Supp (stdVec j), (Φ.chi D.sp.cm (AF D.host.F) a.1).toHomUnits p :
        (AF D.host.F ⊗[D.host.F] D.host.E)ˣ) : AF D.host.F ⊗[D.host.F] D.host.E) := by
    rw [detU, Matrix.det_of_upperTriangular (detMat_stdVec_blockTriangular Φ j p), Units.coe_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [detMat_stdVec_apply]; rfl
  rw [hdet, absA_unit, map_prod]
  rw [Finset.prod_subtype (Finset.Iic j) (p := fun i => stdVec j i ≠ 0)
    (fun i => by simp [stdVec])]
  rfl

end GlobalTheory.LeviShift

theorem GlobalTheory.LeviShift.prod_absChi_Iic : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (j : Fin (wittIndex V)) (p : PA Φ.flag0),
    ∏ i ∈ Finset.Iic j, absChi Φ i p = absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) :=
  fun _ _ Φ j p => GlobalTheory.LeviShift.prod_absChi_eq_absA_detU Φ j p

end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_character_product_eq_abs_det : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (j : Fin (wittIndex V)) (p : PA Φ.flag0), ∏ i ∈ Finset.Iic j, absChi Φ i p = absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) := by
  atlas_forward_decl GlobalTheory.LeviShift.prod_absChi_Iic
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift

noncomputable section

open scoped TensorProduct NNReal

namespace GlobalTheory.LeviShift.CptTriv

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : HSpace E} (Φ : WittFrame V) (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

theorem hLin_coordR (x y : V.V) :
    hLin hc.sig V.gram R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R x) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R y) = inclR R (V.hD x y) := by
  change hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)
  rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hR, Formalism.UG.hform, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig, TensorProduct.tmul_sum,
    starRingEnd_apply]

theorem hD_f_e (i j : Fin (wittIndex V)) : V.hD (Φ.f i) (Φ.e j) = if i = j then 1 else 0 := by
  have h := V.herm.eq (Φ.f i) (Φ.e j)
  simp only [HSpace.hD] at *
  have e2 := Φ.ef j i
  simp only [HSpace.hD] at e2
  rw [← h, e2]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]

theorem hD_bas_dbas (u : SV (wittIndex V)) (i j : Supp u) :
    V.hD (bas Φ u j) (dbas Φ u i) = if i = j then 1 else 0 := by
  have hij : (i = j) ↔ (j.1 = i.1) := by rw [Subtype.ext_iff, eq_comm]
  simp only [bas, dbas]
  by_cases hj : u j.1 = -1 <;> by_cases hi : u i.1 = -1
  · rw [if_pos hj, if_pos hi, hD_f_e]; exact if_congr hij.symm rfl rfl
  · rw [if_pos hj, if_neg hi, Φ.ff, if_neg]; intro h; rw [h] at hi; exact hi hj
  · rw [if_neg hj, if_pos hi, Φ.ee, if_neg]; intro h; rw [h] at hi; exact hj hi
  · rw [if_neg hj, if_neg hi, Φ.ef]; exact if_congr hij.symm rfl rfl

theorem detMat_one (u : SV (wittIndex V)) : detMat Φ hc R u 1 = 1 := by
  ext i j
  simp only [detMat, Matrix.of_apply, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one, hLin_coordR, hD_bas_dbas, Matrix.one_apply]
  split_ifs <;> simp [inclR, Algebra.TensorProduct.one_def]

theorem detU_one (u : SV (wittIndex V)) : detU Φ hc R u 1 = 1 := by
  rw [detU, detMat_one, Matrix.det_one]

end General

end GlobalTheory.LeviShift.CptTriv

namespace GlobalTheory.LeviShift.CptTriv

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (u : SV (wittIndex V))

local notation "PU" => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub u)

theorem detU_mul_inv (p : PU) :
    detU Φ D.sp.cm (AF D.host.F) u (p : GA D V) * detU Φ D.sp.cm (AF D.host.F) u ((p⁻¹ : PU) : GA D V) = 1 := by
  rw [← GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) u _ _ p.2 (p⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, detU_one]

def detUnit (p : PU) : (AF D.host.F ⊗[D.host.F] D.host.E)ˣ where
  val := detU Φ D.sp.cm (AF D.host.F) u (p : GA D V)
  inv := detU Φ D.sp.cm (AF D.host.F) u ((p⁻¹ : PU) : GA D V)
  val_inv := detU_mul_inv Φ u p
  inv_val := by rw [mul_comm]; exact detU_mul_inv Φ u p

def delta : PU →* ℝ≥0 where
  toFun p := absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u (p : GA D V))
  map_one' := by
    rw [Subgroup.coe_one, detU_one]
    have := absA_unit (F := D.host.F) (E := D.host.E) 1
    rwa [Units.val_one, map_one] at this
  map_mul' p q := by
    rw [Subgroup.coe_mul, GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) u _ _ p.2 q.2, absA_mul]

theorem delta_eq (p : PU) : delta Φ u p = Doubling.absE D.host.F D.host.E (detUnit Φ u p) := by
  rw [← absA_unit]; rfl

theorem continuous_detU : Continuous fun g : GA D V => detU Φ D.sp.cm (AF D.host.F) u g := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hm : Continuous fun g : GA D V => (HA.mat _ D.sp.cm.sig V.gram g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [detMat, Matrix.of_apply, hLin, hR_eq, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act]
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec (hm.matrix_mulVec continuous_const))

theorem continuous_delta : Continuous (delta Φ u) := by
  have h : Continuous fun p : PU => detU Φ D.sp.cm (AF D.host.F) u (p : GA D V) :=
    (continuous_detU Φ u).comp continuous_subtype_val
  have hu : Continuous (detUnit Φ u) := Units.continuous_iff.2 ⟨h, h.comp continuous_inv⟩
  have : (delta Φ u : PU → ℝ≥0) = fun p => Doubling.absE D.host.F D.host.E (detUnit Φ u p) :=
    funext (delta_eq Φ u)
  rw [this]
  exact Doubling.continuous_absE.comp hu

end GlobalTheory.LeviShift.CptTriv

theorem GlobalTheory.LeviShift.CptTriv.absA_detU_eq_one : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ (u : SV (wittIndex V)) (k : GA D V), k ∈ levelAll D.sp.cm.sig V.gram L a → k ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub u) → absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u k) = 1 := by
  intro D V Φ L a hG u k hk hp
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  exact Doubling.triv_of_isCompact (δ := GlobalTheory.LeviShift.CptTriv.delta Φ u)
    (GlobalTheory.Cusp.isClosed_parab (hc := D.sp.cm) (V := V) (R := AF D.host.F) (Φ.sub u)) (GlobalTheory.LeviShift.CptTriv.continuous_delta Φ u)
    hG.isCompact ⟨k, hp⟩ hk
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_parabolic_determinant_abs_one : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ (u : SV (wittIndex V)) (k : GA D V), k ∈ levelAll D.sp.cm.sig V.gram L a → k ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub u) → absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u k) = 1 := by
  atlas_forward_decl GlobalTheory.LeviShift.CptTriv.absA_detU_eq_one
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab diagH)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.LeviShift.WeylDelta

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : HSpace E} (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

theorem hLin_coordR (x y : V.V) :
    hLin hc.sig V.gram R (coordR V R x) (coordR V R y) = inclR R (V.hD x y) := by
  change hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hR, Formalism.UG.hform, coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig, TensorProduct.tmul_sum,
    starRingEnd_apply]

theorem coordR_smul (c : E) (x : V.V) : coordR (F := F) V R (c • x) = inclR (F := F) R c • coordR V R x := by
  funext i; simp [coordR]

theorem hLin_act_left (g : HA R hc.sig V.gram) (y x : Fin V.rank → R ⊗[F] E) :
    hLin hc.sig V.gram R (act hc V g y) x = hLin hc.sig V.gram R y (act hc V g⁻¹ x) := by
  change hR R hc.sig V.gram x (act hc V g y) = hR R hc.sig V.gram (act hc V g⁻¹ x) y
  rw [← hR_act hc V g (act hc V g⁻¹ x) y, ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, mul_inv_cancel, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one]

theorem hLin_zero_left (x : Fin V.rank → R ⊗[F] E) : hLin hc.sig V.gram R 0 x = 0 := by
  have h := hLin_smul_left hc.sig V.gram R 0 0 x
  rwa [zero_smul, zero_mul] at h

theorem hD_bas_dbas (Φ : WittFrame V) (u : SV (wittIndex V)) (t i : Fin (wittIndex V)) :
    V.hD (bas Φ u t) (dbas Φ u i) = if t = i then 1 else 0 := by
  unfold bas dbas
  by_cases ht : u t = -1 <;> by_cases hi : u i = -1
  · rw [if_pos ht, if_pos hi, HSpace.hD, ← V.herm.eq, ← HSpace.hD, Φ.ef]
    by_cases e : i = t
    · subst e; simp
    · rw [if_neg e, if_neg (Ne.symm e), map_zero]
  · rw [if_pos ht, if_neg hi, Φ.ff, if_neg (fun e : t = i => hi (e ▸ ht))]
  · rw [if_neg ht, if_pos hi, Φ.ee, if_neg (fun e : t = i => ht (e ▸ hi))]
  · rw [if_neg ht, if_neg hi, Φ.ef]

theorem bas_ne_zero (Φ : WittFrame V) (u : SV (wittIndex V)) (i : Fin (wittIndex V)) : bas Φ u i ≠ 0 := by
  unfold bas
  split_ifs
  · intro h
    have := Φ.ef i i
    rw [if_pos rfl, h] at this
    simp [HSpace.hD] at this
  · exact Φ.linearIndependent_e.ne_zero i

theorem bas_mem_sub (Φ : WittFrame V) {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) :
    bas Φ u i ∈ Φ.sub u := by
  unfold bas
  split_ifs with h
  · exact Submodule.subset_span (Or.inr ⟨i, h, rfl⟩)
  · have : u i = 1 := by
      generalize u i = s at hi h
      cases s <;> simp_all
    exact Submodule.subset_span (Or.inl ⟨i, this, rfl⟩)

theorem act_smul' (g : HA R hc.sig V.gram) (a : R ⊗[F] E) (y : Fin V.rank → R ⊗[F] E) :
    act hc V g (a • y) = a • act hc V g y := Matrix.mulVec_smul _ _ _

end General

end GlobalTheory.LeviShift.WeylDelta

namespace GlobalTheory.LeviShift.WeylDelta

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

theorem act_rat_coordR (γ : GF V) (x : V.V) :
    act D.sp.cm V (rat V γ) (coordR V (AF D.host.F) x) = coordR V (AF D.host.F) (ratAct D.sp.cm V γ x) :=
  act_diagH (AF D.host.F) γ x

theorem stdVec_ne_neg_one {k : ℕ} (j i : Fin k) : stdVec j i ≠ -1 := by
  unfold stdVec; split_ifs <;> decide

theorem exists_scalar {π : Equiv.Perm (Fin (wittIndex V))} {ε : Fin (wittIndex V) → SignTypeˣ} {w : GF V}
    (hw : Φ.IsWeylRep D.sp.cm π ε w) (j : Fin (wittIndex V)) :
    ∃ c : Fin (wittIndex V) → D.host.E, ∀ i, invSV π ε (stdVec j) i ≠ 0 →
      c i ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ (invSV π ε (stdVec j)) i) = c i • Φ.e (π i) := by
  have key : ∀ i, ∃ c : D.host.E, invSV π ε (stdVec j) i ≠ 0 →
      c ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ (invSV π ε (stdVec j)) i) = c • Φ.e (π i) := by
    intro i
    by_cases hu : invSV π ε (stdVec j) i = 0
    · exact ⟨1, fun h => absurd hu h⟩
    have hs : stdVec j (π i) = 1 := by
      have : stdVec j (π i) ≠ 0 := fun h => hu (by simp [invSV, h])
      unfold stdVec at this ⊢
      split_ifs at this ⊢ <;> simp_all
    have hv : invSV π ε (Pi.single (π i) 1) i = invSV π ε (stdVec j) i := by
      simp [invSV, hs]
    have hmem : bas Φ (invSV π ε (stdVec j)) i ∈ Φ.sub (invSV π ε (Pi.single (π i) 1)) := by
      have hb : bas Φ (invSV π ε (stdVec j)) i = bas Φ (invSV π ε (Pi.single (π i) 1)) i := by
        unfold bas; rw [hv]
      rw [hb]
      exact bas_mem_sub Φ (by rw [hv]; exact hu)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (RadInv.sub_single_le Φ (π i) (hw _ _ hmem))
    refine ⟨c, fun _ => ⟨?_, hc.symm⟩⟩
    rintro rfl
    rw [zero_smul] at hc
    apply bas_ne_zero Φ (invSV π ε (stdVec j)) i
    rw [← RadInv.ratAct_inv_apply w (bas Φ _ i), ← hc, map_zero]
  choose c hc using key
  exact ⟨c, hc⟩

variable {u : SV (wittIndex V)} {π : Equiv.Perm (Fin (wittIndex V))} {w : GF V} {c : Fin (wittIndex V) → D.host.E}

theorem hD_ratAct_f (hc : ∀ i, u i ≠ 0 → c i ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ u i) = c i • Φ.e (π i))
    (k : Fin (wittIndex V)) {x : V.V} (hx : x ∈ Φ.sub u) :
    V.hD (ratAct D.sp.cm V w x) (Φ.f k) = c (π.symm k) * V.hD x (dbas Φ u (π.symm k)) := by
  have gen : ∀ t, u t ≠ 0 → V.hD (ratAct D.sp.cm V w (bas Φ u t)) (Φ.f k) =
      c (π.symm k) * V.hD (bas Φ u t) (dbas Φ u (π.symm k)) := by
    intro t ht
    rw [(hc t ht).2, hD_bas_dbas]
    have e1 : V.hD (c t • Φ.e (π t)) (Φ.f k) = c t * V.hD (Φ.e (π t)) (Φ.f k) := by
      simp [HSpace.hD]
    rw [e1, Φ.ef]
    by_cases h : t = π.symm k
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (by rw [← e, Equiv.symm_apply_apply])), mul_zero, mul_zero]
  have h := (Submodule.span_le (p := LinearMap.ker ((V.hT (Φ.f k)).comp (ratAct D.sp.cm V w) -
      c (π.symm k) • V.hT (dbas Φ u (π.symm k))))).2 ?_ hx
  · have := LinearMap.mem_ker.1 h
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero] at this
    simpa [HSpace.hD] using this
  rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
  · have ht' : u t ≠ 0 := by rw [show u t = 1 from ht]; decide
    have hb : bas Φ u t = Φ.e t := by unfold bas; rw [if_neg (by rw [show u t = 1 from ht]; decide)]
    have := gen t ht'
    rw [hb] at this
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      smul_eq_mul, sub_eq_zero]
    simpa [HSpace.hD] using this
  · have ht' : u t ≠ 0 := by rw [show u t = -1 from ht]; decide
    have hb : bas Φ u t = Φ.f t := by unfold bas; rw [if_pos (show u t = -1 from ht)]
    have := gen t ht'
    rw [hb] at this
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      smul_eq_mul, sub_eq_zero]
    simpa [HSpace.hD] using this

theorem hLin_inv_f (hc : ∀ i, u i ≠ 0 → c i ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ u i) = c i • Φ.e (π i))
    (k : Fin (wittIndex V)) {z : Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ extSub (F := D.host.F) V (AF D.host.F) (Φ.sub u)) :
    hLin D.sp.cm.sig V.gram (AF D.host.F) z (act D.sp.cm V (rat V w)⁻¹ (coordR V (AF D.host.F) (Φ.f k))) =
      inclR (F := D.host.F) (AF D.host.F) (c (π.symm k)) *
        hLin D.sp.cm.sig V.gram (AF D.host.F) z (coordR V (AF D.host.F) (dbas Φ u (π.symm k))) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← hLin_act_left, act_rat_coordR, hLin_coordR, hLin_coordR, hD_ratAct_f Φ hc k hx, map_mul]
  | zero => rw [hLin_zero_left, hLin_zero_left, mul_zero]
  | add y y' _ _ ih ih' => rw [hLin_add_left, hLin_add_left, ih, ih', mul_add]
  | smul a y _ ih => rw [hLin_smul_left, hLin_smul_left, ih, mul_left_comm]

theorem act_inv_e (hc : ∀ i, u i ≠ 0 → c i ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ u i) = c i • Φ.e (π i))
    {l : Fin (wittIndex V)} (hl : u (π.symm l) ≠ 0) :
    act D.sp.cm V (rat V w)⁻¹ (coordR V (AF D.host.F) (Φ.e l)) =
      inclR (F := D.host.F) (AF D.host.F) (c (π.symm l))⁻¹ • coordR V (AF D.host.F) (bas Φ u (π.symm l)) := by
  obtain ⟨h0, h1⟩ := hc _ hl
  rw [Equiv.apply_symm_apply] at h1
  have e : Φ.e l = (c (π.symm l))⁻¹ • ratAct D.sp.cm V w (bas Φ u (π.symm l)) := by
    rw [h1, smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [← map_inv, act_rat_coordR, e, map_smul, RadInv.ratAct_inv_apply, coordR_smul]

end GlobalTheory.LeviShift.WeylDelta

namespace GlobalTheory.LeviShift.WeylDelta

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

theorem conj_mem_parab {π : Equiv.Perm (Fin (wittIndex V))} {ε : Fin (wittIndex V) → SignTypeˣ} {w : GF V}
    (hw : Φ.IsWeylRep D.sp.cm π ε w) (j : Fin (wittIndex V)) {m : GA D V}
    (hm : m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j)))) :
    rat V w * m * (rat V w)⁻¹ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) := by
  have h1 : ∀ y ∈ Φ.sub (invSV π ε (stdVec j)), ratAct D.sp.cm V w y ∈ Φ.sub (stdVec j) := fun y hy => hw _ y hy
  have h2 : ∀ y ∈ Φ.sub (stdVec j), ratAct D.sp.cm V w⁻¹ y ∈ Φ.sub (invSV π ε (stdVec j)) := by
    intro y hy
    rw [Φ.sub_stdVec] at hy
    refine (Submodule.span_le (p := (Φ.sub (invSV π ε (stdVec j))).comap (ratAct D.sp.cm V w⁻¹))).2 ?_ hy
    rintro _ ⟨i, hi, rfl⟩
    exact RadInv.ratAct_inv_e_mem Φ hw (show i ≤ j from Nat.lt_succ_iff.1 hi)
  have hi : (rat V w)⁻¹ = rat V w⁻¹ := (map_inv _ _).symm
  have hm' : ∀ y, y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) : Set _) ↔
      act D.sp.cm V m y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) : Set _) := hm
  show ∀ y, y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (stdVec j)) : Set _) ↔
      act D.sp.cm V (rat V w * m * (rat V w)⁻¹) y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (stdVec j)) : Set _)
  intro y
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul]
  constructor
  · intro hy
    have h3 : act D.sp.cm V (rat V w⁻¹) y ∈ extSub (F := D.host.F) V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) :=
      RadInv.act_rat_mem h2 hy
    rw [← hi] at h3
    exact RadInv.act_rat_mem h1 ((hm' _).1 h3)
  · intro hy
    have h3 := RadInv.act_rat_mem h2 hy
    rw [← hi, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_inv] at h3
    have h4 := RadInv.act_rat_mem h1 ((hm' _).2 h3)
    have e : act D.sp.cm V (rat V w) (act D.sp.cm V (rat V w)⁻¹ y) = y := by
      rw [← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, mul_inv_cancel, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one]
    rw [e] at h4
    exact h4

theorem detU_conj {π : Equiv.Perm (Fin (wittIndex V))} {ε : Fin (wittIndex V) → SignTypeˣ} {w : GF V}
    {j : Fin (wittIndex V)} {m : GA D V}
    (hm : m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))))
    {c : Fin (wittIndex V) → D.host.E}
    (hc : ∀ i, invSV π ε (stdVec j) i ≠ 0 →
      c i ≠ 0 ∧ ratAct D.sp.cm V w (bas Φ (invSV π ε (stdVec j)) i) = c i • Φ.e (π i)) :
    detU Φ D.sp.cm (AF D.host.F) (stdVec j) (rat V w * m * (rat V w)⁻¹) =
      detU Φ D.sp.cm (AF D.host.F) (invSV π ε (stdVec j)) m := by
  set u := invSV π ε (stdVec j) with hu
  have hsupp : ∀ k, stdVec j k ≠ 0 ↔ u (π.symm k) ≠ 0 := fun k => by
    rw [hu]
    simp only [invSV, Equiv.apply_symm_apply]
    exact ⟨fun h => mul_ne_zero (Units.ne_zero _) h, fun h h' => h (by rw [h', mul_zero])⟩
  let σe : Supp (stdVec j) ≃ Supp u := Equiv.subtypeEquiv π.symm hsupp
  have hm' : ∀ y, y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub u) : Set _) ↔
      act D.sp.cm V m y ∈ (extSub (F := D.host.F) V (AF D.host.F) (Φ.sub u) : Set _) := hm
  have hmat : detMat Φ D.sp.cm (AF D.host.F) (stdVec j) (rat V w * m * (rat V w)⁻¹) =
      Matrix.diagonal (fun k : Supp (stdVec j) => inclR (F := D.host.F) (AF D.host.F) (c (π.symm k))) *
        (detMat Φ D.sp.cm (AF D.host.F) u m).submatrix σe σe *
        Matrix.diagonal (fun l : Supp (stdVec j) => inclR (F := D.host.F) (AF D.host.F) (c (π.symm l))⁻¹) := by
    ext k l
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply]
    have hl : u (π.symm l) ≠ 0 := (hsupp l).1 l.2
    have hb : bas Φ (stdVec j) l = Φ.e l := if_neg (stdVec_ne_neg_one j l)
    have hdb : dbas Φ (stdVec j) k = Φ.f k := if_neg (stdVec_ne_neg_one j k)
    have hZ : act D.sp.cm V m (coordR V (AF D.host.F) (bas Φ u (π.symm l))) ∈
        extSub (F := D.host.F) V (AF D.host.F) (Φ.sub u) :=
      (hm' _).1 (Submodule.subset_span ⟨_, bas_mem_sub Φ hl, rfl⟩)
    simp only [detMat, Matrix.of_apply, σe, Equiv.subtypeEquiv_apply]
    rw [hb, hdb, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, act_inv_e Φ hc hl, act_smul', act_smul',
      hLin_smul_left, hLin_act_left D.sp.cm (AF D.host.F) (rat V w), hLin_inv_f Φ hc k hZ]
    ring
  unfold detU
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Matrix.det_submatrix_equiv_self,
    mul_comm _ (Finset.prod _ _), ← mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_one fun k _ => by rw [← map_mul, inv_mul_cancel₀ (hc _ ((hsupp k).1 k.2)).1, map_one], one_mul]

end GlobalTheory.LeviShift.WeylDelta

theorem GlobalTheory.LeviShift.logDelta_conj_weylRep : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (π : Equiv.Perm (Fin (wittIndex V))) (ε : Fin (wittIndex V) → SignTypeˣ) (w : GF V), Φ.IsWeylRep D.sp.cm π ε w → ∀ (j : Fin (wittIndex V)) (m : GA D V), m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) → rat V w * m * (rat V w)⁻¹ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) ∧ logDelta Φ (stdVec j) (rat V w * m * (rat V w)⁻¹) = logDelta Φ (invSV π ε (stdVec j)) m := by
  intro D V Φ π ε w hw j m hm
  obtain ⟨c, hc⟩ := WeylDelta.exists_scalar Φ hw j
  refine ⟨WeylDelta.conj_mem_parab Φ hw j hm, ?_⟩
  unfold logDelta
  rw [WeylDelta.detU_conj Φ hm hc]

end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_conjugate_parabolic_log_modulus : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (π : Equiv.Perm (Fin (wittIndex V))) (ε : Fin (wittIndex V) → SignTypeˣ) (w : GF V), Φ.IsWeylRep D.sp.cm π ε w → ∀ (j : Fin (wittIndex V)) (m : GA D V), m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) → rat V w * m * (rat V w)⁻¹ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) ∧ logDelta Φ (stdVec j) (rat V w * m * (rat V w)⁻¹) = logDelta Φ (invSV π ε (stdVec j)) m := by
  atlas_forward_decl GlobalTheory.LeviShift.logDelta_conj_weylRep
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift

noncomputable section
open scoped TensorProduct Classical

namespace GlobalTheory.LeviVec

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)
open GlobalTheory.LeviSign

section Comb

variable {k : ℕ}

def res (u : SV k) (A : Fin k → Prop) : SV k := fun i => if A i then u i else 0

theorem vec_res_add (u : SV k) (A : Fin k → Prop) : vec u = vec (res u A) + vec (res u fun i => ¬ A i) := by
  ext i
  by_cases h : A i <;> simp [vec, res, h]

theorem res_mem {P : Finset (SV k)} (hP : IsPar P) {w : SV k} (hw : w ∈ P) {u : SV k} (hu : vec u ∈ aP P) :
    vec (res u fun i => w i ≠ 0) ∈ aP P := by
  let a : A0 k →ₗ[ℝ] A0 k :=
    { toFun := fun x => WithLp.toLp 2 fun i => if w i ≠ 0 then x i else 0
      map_add' := fun x y => by ext i; by_cases h : w i = 0 <;> simp [h]
      map_smul' := fun c x => by ext i; by_cases h : w i = 0 <;> simp [h] }
  have ha : ∀ v : SV k, a (vec v) = vec (res v fun i => w i ≠ 0) := fun v => by
    ext i; by_cases h : w i = 0 <;> simp [a, vec, res, h]
  have hle : aP P ≤ (aP P).comap a := Submodule.span_le.2 (by
    rintro _ ⟨v, hv, rfl⟩
    change a (vec v) ∈ aP P
    rw [ha]
    rcases hP.2 v hv w hw with e | e
    · have : (res v fun i => w i ≠ 0) = v := funext fun i => by
        by_cases h : w i = 0
        · by_cases h' : v i = 0
          · simp [res, h']
          · exact absurd ((e i h').symm.trans h) h'
        · simp [res, h]
      rw [this]; exact Submodule.subset_span ⟨v, hv, rfl⟩
    · have : (res v fun i => w i ≠ 0) = w := funext fun i => by
        by_cases h : w i = 0
        · simp [res, h]
        · simp [res, h, e i h]
      rw [this]; exact Submodule.subset_span ⟨w, hw, rfl⟩)
  exact ha u ▸ hle hu

theorem signType_cancel_identity : ∀ a b c d : SignType, a ≠ 0 → c ≠ 0 → a * b = c * d → d = (b * a) * c := by decide

theorem sign_sq : ∀ a : SignType, a ≠ 0 → a * a = 1 := by decide

theorem sign_mul_ne : ∀ a b : SignType, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by decide

theorem exists_vec {P : Finset (SV k)} (hP : IsPar P) (l : SV k → ℝ)
    (hneg : ∀ u, vec u ∈ aP P → l (-u) = - l u)
    (hadd : ∀ u A, vec u ∈ aP P → vec (res u A) ∈ aP P → vec (res u fun i => ¬ A i) ∈ aP P →
      l u = l (res u A) + l (res u fun i => ¬ A i)) :
    ∃ h : A0 k, ∀ u, vec u ∈ aP P → inner ℝ (vec u) h = l u := by
  obtain ⟨p, -, hp⟩ := exists_top (r := Below) (fun a b c h h' i hi => (h' i (h i hi ▸ hi)).trans (h i hi))
    (insert 0 P) (Finset.insert_nonempty _ _) fun a ha b hb => by
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact .inl fun i hi => (hi rfl).elim
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact .inr fun i hi => (hi rfl).elim
      exact hP.2 a ha b hb
  have hp' : ∀ w ∈ P, ∀ i, w i ≠ 0 → p i = w i := fun w hw => hp w (Finset.mem_insert_of_mem hw)
  let c : Fin k → Finset (SV k) := fun i => P.filter fun w => w i ≠ 0
  let b : Finset (SV k) → SV k := fun C => res p fun i => c i = C
  let N : Finset (SV k) → ℝ := fun C => (Finset.univ.filter fun i => c i = C).card
  let h : A0 k := WithLp.toLp 2 fun i => (p i : ℝ) * (l (b (c i)) / N (c i))
  have hc : ∀ i j, c i = c j ↔ ∀ w ∈ P, (w i ≠ 0 ↔ w j ≠ 0) := fun i j => by
    simp only [c, Finset.ext_iff, Finset.mem_filter, and_congr_right_iff]
  have main : ∀ Q : Finset (SV k), Q ⊆ P → ∀ u, vec u ∈ aP P →
      (∀ i j, u i ≠ 0 → u j ≠ 0 → ∀ w ∈ P, w ∉ Q → (w i ≠ 0 ↔ w j ≠ 0)) → inner ℝ (vec u) h = l u := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
      intro _ u hu H
      by_cases h0 : u = 0
      · subst h0
        have e0 : vec (0 : SV k) = 0 := by ext i; simp [vec]
        have := hneg 0 hu
        rw [neg_zero] at this
        rw [e0, inner_zero_left]; linarith
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
      have hi : u i ≠ 0 := hi
      obtain ⟨w, hw, hwi⟩ : ∃ w ∈ P, w i ≠ 0 := by
        by_contra! hn
        have := pattern hu (s := 1) (t := 0) (i := i) (j := i) fun w hw => by simp [hn w hw]
        exact hi (by simpa using this)
      have hpj : ∀ j, c j = c i → p j ≠ 0 := fun j hj => by
        have := ((hc j i).1 hj w hw).2 hwi
        rwa [hp' w hw j this]
      have hu' : ∀ j, u j = (u i * p i) * b (c i) j := fun j => by
        by_cases hj : c j = c i
        · have := pattern hu (s := p i) (t := p j) (i := i) (j := j) fun v hv => by
            by_cases hv' : v i = 0
            · have : v j = 0 := by
                by_contra e; exact ((hc j i).1 hj v hv).1 e hv'
              rw [hv', this, mul_zero, mul_zero]
            · have hv'' := ((hc j i).1 hj v hv).2 hv'
              rw [hp' v hv i hv', hp' v hv j hv'', sign_sq _ hv', sign_sq _ hv'']
          simp only [b, res, if_pos hj]
          exact signType_cancel_identity _ _ _ _ (hpj i rfl) (hpj j hj) this
        · simp only [b, res, if_neg hj, mul_zero]
          by_contra e
          exact hj ((hc j i).2 fun v hv => H j i e hi v hv (Finset.notMem_empty v))
      have hb : inner ℝ (vec (b (c i))) h = l (b (c i)) := by
        have hN : N (c i) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, by simp⟩)
        have : ∀ j, inner ℝ (vec (b (c i)) j) (h j) = if c j = c i then l (b (c i)) / N (c i) else 0 := fun j => by
          by_cases hj : c j = c i
          · have : ((p j : ℝ)) * p j = 1 := by rw [← SignType.coe_mul, sign_sq _ (hpj j hj), SignType.coe_one]
            simp only [vec, b, res, h, if_pos hj, hj, if_true, RCLike.inner_apply, conj_trivial]
            linear_combination (l (b (c i)) / N (c i)) * this
          · simp [vec, b, res, hj]
        rw [PiLp.inner_apply, Finset.sum_congr rfl fun j _ => this j, ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul]
        exact mul_div_cancel₀ _ hN
      rcases sign_cases _ (sign_mul_ne _ _ hi (hpj i rfl)) with e | e
      · have : b (c i) = u := funext fun j => by rw [hu' j, e, one_mul]
        rwa [this] at hb
      · have : b (c i) = -u := funext fun j => by rw [Pi.neg_apply, hu' j, e, neg_one_mul, neg_neg]
        rw [this, vec_neg, inner_neg_left, hneg u hu] at hb
        linarith
    | insert w Q hwQ ih =>
      intro hQ u hu H
      have hw : w ∈ P := hQ (Finset.mem_insert_self _ _)
      have hQ' : Q ⊆ P := (Finset.subset_insert _ _).trans hQ
      have h1 := res_mem hP hw hu
      have h2 : vec (res u fun i => ¬ w i ≠ 0) ∈ aP P := by
        rw [eq_sub_of_add_eq' (vec_res_add u fun i => w i ≠ 0).symm]; exact sub_mem hu h1
      have key : ∀ A : Fin k → Prop, vec (res u A) ∈ aP P → (∀ i j, A i → A j → (w i ≠ 0 ↔ w j ≠ 0)) →
          inner ℝ (vec (res u A)) h = l (res u A) := fun A hA hA' => ih hQ' _ hA fun i j hi hj v hv hvQ => by
        have r : ∀ i, res u A i ≠ 0 → A i ∧ u i ≠ 0 := fun i hi => by
          by_cases e : A i <;> simp_all [res]
        by_cases e : v = w
        · subst e; exact hA' i j (r i hi).1 (r j hj).1
        · exact H i j (r i hi).2 (r j hj).2 v hv (by simp [e, hvQ])
      rw [hadd u _ hu h1 h2, ← key _ h1 fun i j a b => iff_of_true a b, ← key _ h2 fun i j a b => iff_of_false a b,
        ← inner_add_left, ← vec_res_add]
  exact ⟨h, fun u hu => main P subset_rfl u hu fun i j _ _ w hw hn => (hn hw).elim⟩

end Comb

section Det

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E} (Φ : WittFrame V) {R : Type} [CommRing R] [Algebra F R]

theorem bas_eq {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) : bas Φ u i = vecOf Φ (u i) i := by
  rcases sign_cases _ hi with e | e <;> simp [bas, vecOf, e]

theorem dbas_eq {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) : dbas Φ u i = dualOf Φ (u i) i := by
  rcases sign_cases _ hi with e | e <;> simp [dbas, dualOf, e]

theorem bas_neg {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) : bas Φ (-u) i = dbas Φ u i := by
  rcases sign_cases _ hi with e | e <;> simp [bas, dbas, e]

theorem dbas_neg {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) : dbas Φ (-u) i = bas Φ u i := by
  rcases sign_cases _ hi with e | e <;> simp [bas, dbas, e]

theorem bas_mem {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) : bas Φ u i ∈ Φ.sub u := by
  rw [bas_eq Φ hi]; exact vecOf_mem (x := (u i, i)) (mem_Aset.2 (sign_sq _ hi))

theorem cf_bas (u : SV (wittIndex V)) (i j : Supp u) :
    cf hc R (dbas Φ u i) (coordR V R (bas Φ u j)) = if i = j then 1 else 0 := by
  rw [cf_coordR, bas_eq Φ j.2, dbas_eq Φ i.2, hD_vecOf_dualOf Φ j.2 i.2]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg, map_zero]
    exact fun e => h (Subtype.ext (congrArg Prod.snd e).symm)

theorem expand (u : SV (wittIndex V)) {y : Fin V.rank → R ⊗[F] E} (hy : y ∈ extSub V R (Φ.sub u)) :
    y = ∑ l : Supp u, cf hc R (dbas Φ u l) y • coordR V R (bas Φ u l) := by
  let T : Module.End (R ⊗[F] E) (Fin V.rank → R ⊗[F] E) :=
    ∑ l : Supp u, (cf hc R (dbas Φ u l)).smulRight (coordR V R (bas Φ u l))
  have hT : ∀ y, T y = ∑ l : Supp u, cf hc R (dbas Φ u l) y • coordR V R (bas Φ u l) := fun y => by
    simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hb : ∀ j : Supp u, coordR V R (bas Φ u j) ∈ LinearMap.ker (T - LinearMap.id) := fun j => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, hT]
    simp [cf_bas]
  have hle : extSub (F := F) V R (Φ.sub u) ≤ LinearMap.ker (T - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    refine span_coord R _ _ (fun v hv => ?_) hv
    rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have hi' : u i = 1 := hi
      have := hb ⟨i, by rw [hi']; decide⟩
      simpa [bas, hi'] using this
    · have hi' : u i = -1 := hi
      have := hb ⟨i, by rw [hi']; decide⟩
      simpa [bas, hi'] using this
  have := hle hy
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, hT] at this
  exact this.symm

theorem hR_swap (x y : Fin V.rank → R ⊗[F] E) :
    hR R hc.sig V.gram x y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (hR R hc.sig V.gram y x) := by
  have hs : ∀ z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a e =>
      change a ⊗ₜ[F] star (star e) = _
      rw [star_star]
  have hg : ∀ i j, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (inclR (F := F) R (V.gram i j)) = inclR (F := F) R (V.gram j i) :=
    fun i j => congrArg (inclR (F := F) R) (congrFun (congrFun (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_gram hc V) j) i)
  simp only [GlobalTheory.Cusp.hR_eq, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul, hs, hg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem detU_neg (u : SV (wittIndex V)) {g : HA R hc.sig V.gram} (hg : g ∈ parab hc V R (Φ.sub u)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (detU Φ hc R (-u) g) * detU Φ hc R u g = 1 := by
  let e : Supp u ≃ Supp (-u) := Equiv.subtypeEquivRight fun i => by simp
  let N := (detMat Φ hc R (-u) g).submatrix e e
  have h : (N.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig)).transpose * detMat Φ hc R u g = 1 := by
    ext i j
    have h1 := cf_bas (hc := hc) (R := R) Φ u i j
    rw [cf_apply, ← hR_act hc V g, expand (hc := hc) Φ u (mem_parab.1 hg _ (bas_mem Φ j.2))] at h1
    rw [Matrix.one_apply, ← h1, Matrix.mul_apply]
    let ψ : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E :=
      { toFun := fun y => hLin hc.sig V.gram R y (act hc V g (coordR V R (dbas Φ u i)))
        map_add' := fun y y' => hLin_add_left _ _ _ y y' _
        map_smul' := fun c y => hLin_smul_left _ _ _ c y _ }
    change _ = ψ _
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    congr 1
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (hR R hc.sig V.gram (coordR V R (dbas Φ (-u) l))
      (act hc V g (coordR V R (bas Φ (-u) i)))) = hR R hc.sig V.gram _ _
    rw [dbas_neg Φ l.2, bas_neg Φ i.2, ← hR_swap]
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_submatrix_equiv_self] at this
  exact this

theorem det_block (u : SV (wittIndex V)) (A : Fin (wittIndex V) → Prop) (g : HA R hc.sig V.gram) :
    ((detMat Φ hc R u g).toSquareBlockProp fun i => A i).det = detU Φ hc R (res u A) g := by
  have r : ∀ i, res u A i ≠ 0 → A i ∧ u i ≠ 0 := fun i hi => by
    by_cases e : A i <;> simp_all [res]
  let e : Supp (res u A) ≃ {i : Supp u // A i} :=
    { toFun := fun i => ⟨⟨i.1, (r i.1 i.2).2⟩, (r i.1 i.2).1⟩
      invFun := fun i => ⟨i.1.1, by simpa [res, i.2] using i.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e, detU]
  congr 1
  ext i j
  have hi : res u A i = u i := if_pos (r i.1 i.2).1
  have hj : res u A j = u j := if_pos (r j.1 j.2).1
  simp only [detMat, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply, Matrix.of_apply, bas, dbas, hi, hj]
  rfl

theorem detU_res (u : SV (wittIndex V)) (A : Fin (wittIndex V) → Prop) {g : HA R hc.sig V.gram}
    (hg : g ∈ parab hc V R (Φ.sub (res u A))) :
    detU Φ hc R u g = detU Φ hc R (res u A) g * detU Φ hc R (res u fun i => ¬ A i) g := by
  rw [← det_block, ← det_block, detU]
  convert Matrix.twoBlockTriangular_det (detMat Φ hc R u g) (fun i => A i) fun i hi j hj => ?_
  have hj' : res u A j = u j := if_pos hj
  have hb : bas Φ u j ∈ Φ.sub (res u A) := by
    have := bas_mem Φ (u := res u A) (i := j) (hj' ▸ j.2)
    simpa only [bas, hj'] using this
  change cf hc R (dbas Φ u i) (act hc V g (coordR V R (bas Φ u j))) = 0
  rw [expand (hc := hc) Φ _ (mem_parab.1 hg _ hb), map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hl : A l := by by_contra e; exact l.2 (if_neg e)
  rw [map_smul, cf_coordR, bas_eq Φ l.2, dbas_eq Φ i.2, hD_vecOf_dualOf Φ l.2 i.2, if_neg, map_zero, smul_zero]
  intro e
  have e' : l.1 = i.1 := congrArg Prod.snd e
  exact hi (e' ▸ hl)

end Det

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

theorem absA_neg (u : SV (wittIndex V)) {g : GA D V} (hg : g ∈ parab D.sp.cm V (AF D.host.F) (Φ.sub u)) :
    absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (-u) g) *
      absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u g) = 1 := by
  have h := detU_neg Φ u hg
  set a := detU Φ D.sp.cm (AF D.host.F) (-u) g
  set b := detU Φ D.sp.cm (AF D.host.F) u g
  have hs : ∀ z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig z) = z :=
    fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a e =>
      change a ⊗ₜ[D.host.F] star (star e) = _
      rw [star_star]
  have ha : IsUnit a := by
    have := (IsUnit.of_mul_eq_one _ h).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig)
    rwa [hs] at this
  obtain ⟨a', ha'⟩ := ha
  have e : absA D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig a) = absA D.host.F D.host.E a := by
    rw [← ha', absA_unit, ← Doubling.absE_conjUnit D.sp.cm.sig, ← absA_unit]; rfl
  rw [← e, ← absA_mul, h]
  exact (absA_unit 1).trans (map_one _)

theorem exists_levi_vec : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))), IsPar P → ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∃ h : A0 (wittIndex V), ∀ u, vec u ∈ aP P → inner ℝ (vec u) h = - logDelta Φ u m := by
  intro D V Φ P hP m hm
  have hm' : ∀ u, vec u ∈ aP P → m ∈ parab D.sp.cm V (AF D.host.F) (Φ.sub u) := fun u hu =>
    (Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (levi_le Φ _ P u hu hm) u)
      (Finset.mem_singleton_self u))).1
  have hne : ∀ u, vec u ∈ aP P → (absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u m) : ℝ) ≠ 0 := fun u hu =>
    NNReal.coe_ne_zero.2 (right_ne_zero_of_mul_eq_one (absA_neg Φ u (hm' u hu)))
  refine exists_vec hP (fun u => - logDelta Φ u m) (fun u hu => ?_) fun u A hu h1 h2 => ?_
  · have h := congrArg NNReal.toReal (absA_neg Φ u (hm' u hu))
    rw [NNReal.coe_mul, NNReal.coe_one] at h
    simp only [logDelta]
    rw [eq_inv_of_mul_eq_one_left h, Real.log_inv]
  · simp only [logDelta]
    rw [detU_res Φ u A (hm' _ h1), absA_mul, NNReal.coe_mul, Real.log_mul (hne _ h1) (hne _ h2), neg_add]

end GlobalTheory.LeviVec

end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_log_modulus_vector : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))), IsPar P → ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∃ h : A0 (wittIndex V), ∀ u, vec u ∈ aP P → inner ℝ (vec u) h = - logDelta Φ u m := by
  atlas_forward_decl GlobalTheory.LeviVec.exists_levi_vec
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift

noncomputable section

namespace GlobalTheory.LeviShift

theorem sum_H0_parabolic_mul : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ (j : Fin (wittIndex V)) (q y : GA D V),
      q ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) →
      ∑ i ∈ Finset.Iic j, H0 Φ (levelAll D.sp.cm.sig V.gram L a) (q * y) i =
        logDelta Φ (stdVec j) q + ∑ i ∈ Finset.Iic j, H0 Φ (levelAll D.sp.cm.sig V.gram L a) y i := by
  intro D V Φ L a hg j q y hq
  have hK := hg.isCompact
  have hP0 : ∀ p : PA Φ.flag0, (p : GA D V) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) :=
    fun p => by rw [Φ.sub_stdVec]; exact Φ.flag0.par_le_parab _ _ j.succ p.2
  obtain ⟨p, k, hk, rfl⟩ := GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg y
  obtain ⟨p', k', hk', e⟩ := GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg (q * p)
  have hqy : q * (p * k) = p' * (k' * k) := by rw [← mul_assoc, e, mul_assoc]
  have hk'P : k' ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) := by
    have : k' = (p' : GA D V)⁻¹ * (q * p) := by rw [e]; group
    rw [this]; exact mul_mem (inv_mem (hP0 p')) (mul_mem hq (hP0 p))
  have hpos : ∀ (r : PA Φ.flag0) (i : Fin (wittIndex V)), ((absChi Φ i r : NNReal) : ℝ) ≠ 0 := fun r i =>
    NNReal.coe_ne_zero.2 (GlobalTheory.Doubling.hom_pos _ r).ne'
  simp only [hqy, mul_mem_riemannRochSpace_add hK _ (mul_mem hk' hk), mul_mem_riemannRochSpace_add hK _ hk]
  rw [← Real.log_prod (fun i _ => hpos p' i), ← Real.log_prod (fun i _ => hpos p i), ← NNReal.coe_prod,
    ← NNReal.coe_prod, GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j p', GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j p]
  have m1 := GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) (stdVec j) q p hq (hP0 p)
  have m2 := GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) (stdVec j) p' k' (hP0 p') hk'P
  have h3 := GlobalTheory.T.level_parabolic_determinant_abs_one D V Φ L a hg (stdVec j) k' hk' hk'P
  rw [← e] at m2
  have key : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p') =
      absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) q) *
        absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) := by
    have := congrArg (absA D.host.F D.host.E) (m1.symm.trans m2)
    rw [absA_mul, absA_mul, h3, mul_one] at this; exact this.symm
  have n1 : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p') ≠ 0 := by
    rw [← GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j _]; exact (Finset.prod_pos fun i _ => GlobalTheory.Doubling.hom_pos _ _).ne'
  have n2 : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) ≠ 0 := by
    rw [← GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j _]; exact (Finset.prod_pos fun i _ => GlobalTheory.Doubling.hom_pos _ _).ne'
  rw [key] at n1 ⊢
  unfold logDelta
  rw [NNReal.coe_mul, Real.log_mul (NNReal.coe_ne_zero.2 (left_ne_zero_of_mul n1)) (NNReal.coe_ne_zero.2 n2)]

theorem inner_vector_inverse_levi_shift {k : ℕ} (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) (j : Fin k) (H : A0 k) :
    inner ℝ (vec (invSV π ε (stdVec j))) (inverseChamberMap π ε H) = ∑ i ∈ Finset.Iic j, H i := by
  have sq : ∀ e : SignTypeˣ, ((e : SignType) : ℝ) * (e : SignType) = 1 := fun e => by
    by_cases h : e = 1
    · simp [h]
    · rw [sign_unit e h]; norm_num
  simp only [PiLp.inner_apply, vec, invSV, inverseChamberMap, RCLike.inner_apply, conj_trivial]
  have e : ∀ x, ((ε x : SignType) : ℝ) * H.ofLp (π x) * (((ε x : SignType) * stdVec j (π x) : SignType) : ℝ) =
      H.ofLp (π x) * (stdVec j (π x) : ℝ) := fun x => by
    rw [SignType.coe_mul]; linear_combination (H.ofLp (π x) * (stdVec j (π x) : ℝ)) * sq (ε x)
  simp only [e]
  rw [Equiv.sum_comp π (fun i => H.ofLp i * (stdVec j i : ℝ)),
    show Finset.Iic j = Finset.univ.filter (· ≤ j) by ext; simp, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ≤ j <;> simp [stdVec, h]

theorem yfam_mul_levi : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ P, IsPar P → ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∃ h : A0 (wittIndex V), ∀ Q ∈ parP (aP P) ∅, ∀ x Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (m * x) Tr Q = Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q + pr Q h := by
  intro D V Φ L a hg P hP m hm
  obtain ⟨h, hh⟩ := GlobalTheory.T.levi_log_modulus_vector D V Φ P hP m hm
  refine ⟨h, fun Q hQ x T => ?_⟩
  obtain ⟨hQp, hQa, -⟩ := mem_parP.1 hQ
  obtain ⟨π, ε, w, hw, hsub, hY⟩ := exists_Yfam_eq (Φ := Φ) (K := levelAll D.sp.cm.sig V.gram L a) hQp
  rw [hY, hY, ← sub_eq_iff_eq_add', ← map_sub, ← sub_eq_zero, ← map_sub, pr, Submodule.starProjection_apply_eq_zero_iff,
    Submodule.mem_orthogonal]
  intro v hv
  refine Submodule.span_induction (p := fun v _ => inner ℝ v _ = (0:ℝ)) ?_ (by simp)
    (fun x y _ _ hx hy => by rw [inner_add_left, hx, hy, add_zero])
    (fun c x _ hx => by rw [inner_smul_left, hx, mul_zero]) hv
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 (hsub hu)
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hs
  have hvu : vec (invSV π ε (stdVec j)) ∈ aP P := hQa ▸ Submodule.subset_span ⟨_, hu, rfl⟩
  have hmu : m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) := by
    have := GlobalTheory.T.levi_monotone_in_parabolic D V Φ (AF D.host.F) P hP _ hvu hm
    have h2 : Φ.levi D.sp.cm (AF D.host.F) {invSV π ε (stdVec j)} ≤
        GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) := by
      unfold WittFrame.levi
      exact (iInf₂_le (invSV π ε (stdVec j)) (Finset.mem_singleton_self _)).trans inf_le_left
    exact h2 this
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.weyl_conjugate_parabolic_log_modulus D V Φ π ε w hw j m hmu
  have e1 := sum_H0_parabolic_mul D V Φ L a hg j _ (rat V w * x) hg1
  have e2 : rat V w * (m * x) = rat V w * m * (rat V w)⁻¹ * (rat V w * x) := by group
  simp only [Ys, inner_sub_right, inner_vector_inverse_levi_shift, hh _ hvu, e2, PiLp.sub_apply, Finset.sum_sub_distrib] at e1 ⊢
  rw [e1, hg2]
  ring

end GlobalTheory.LeviShift

end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_family_levi_shift : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ P, IsPar P → ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∃ h : A0 (wittIndex V), ∀ Q ∈ parP (aP P) ∅, ∀ x Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (m * x) Tr Q = Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q + pr Q h := by
  atlas_forward_decl GlobalTheory.LeviShift.yfam_mul_levi
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory

theorem weight_split_places : GlobalTheory.Published.LabesseWaldspurger → ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ P, IsPar P → ∀ Tr, ∃ C Dd : Finset (SV (wittIndex V)) → GA D V → ℂ, (∀ Q ∈ parF (aP P) ∅, Continuous (C Q) ∧ (∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ y, C Q (m * y) = C Q y) ∧ ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), ∀ n ∈ NA (IsoFlag.single hW), ∀ y, C Q (n * y) = C Q y) ∧ (∀ z, Dd ∅ z = 1) ∧ (∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, (weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr (y * z) : ℂ) = ∑ Q ∈ parF (aP P) ∅, C Q y * Dd Q z) ∧ ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ x, weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr (m * x) = weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr x := by
  intro hLW D V Φ L a hG P hP Tr
  obtain ⟨⟨hEFI, hFS, hFP⟩, hY⟩ := hLW
  have hOrth : ∀ x T, IsOrth (aP P) (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x T) := fun x T =>
    ((hY D V Φ L a hG).1 x T).1.mono le_top
  have hLevi : IsLevi (aP P) := ⟨P, hP, rfl⟩
  refine ⟨fun Q y => cM (aP P) Q (expFam (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) y 0 - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0)) 0,
    fun Q z => cP Q ∅ (expFam (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr)) 0, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    have hsub : ∀ P' ∈ parP (aP P) Q, P' ∈ parP (aP P) ∅ ∧ IsPar P' ∧ Q ⊆ P' := fun P' h' => by
      obtain ⟨h1, h2, h3⟩ := mem_parP.1 h'
      exact ⟨mem_parP.2 ⟨h1, h2, Finset.empty_subset _⟩, h1, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact GlobalTheory.T.chamber_coefficient_continuous hFS _ (aP P) hLevi Q hQ (GA D V) (fun z => Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z 0 - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0)
        (fun z => (hOrth z 0).sub (hOrth 1 0))
        (fun P' hP' => ((GlobalTheory.T.truncation_family_place_additive D V Φ L a hG P' (hsub P' hP').2.1).1 0).sub continuous_const)
    · intro m hm y
      obtain ⟨h, hh⟩ := GlobalTheory.T.truncation_family_levi_shift D V Φ L a hG P hP m hm
      exact GlobalTheory.T.chamber_coefficient_translation hFS _ (aP P) hLevi Q hQ _ _ ((hOrth y 0).sub (hOrth 1 0)) h
        (fun P' hP' => by simp only [Pi.sub_apply, hh P' (hsub P' hP').1]; abel)
    · intro u hu hW n hn y
      exact GlobalTheory.T.chamber_coefficient_translation hFS _ (aP P) hLevi Q hQ _ _ ((hOrth y 0).sub (hOrth 1 0)) 0
        (fun P' hP' => by
          simp only [Pi.sub_apply, GlobalTheory.T.truncation_family_unipotent_invariant D V Φ L a hG P' (hsub P' hP').2.1 u ((hsub P' hP').2.2 hu) hW n hn,
            map_zero, add_zero])
  · intro z
    exact (GlobalTheory.T.chamber_coefficient_product_formula hEFI hFP _ (aP P) hLevi (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr) (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr)
      (fun Q => Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr Q + Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr Q) (hOrth z Tr) (hOrth z Tr) (fun _ _ => rfl)).2.2
  · intro S y hy z hz
    have e := GlobalTheory.T.chamber_coefficient_product_formula hEFI hFP _ (aP P) hLevi (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) y 0 - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0) (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr)
      (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (y * z) Tr) ((hOrth y 0).sub (hOrth 1 0)) (hOrth z Tr)
      (fun P' hP' => (GlobalTheory.T.truncation_family_place_additive D V Φ L a hG P' (mem_parF.1 hP').1).2 S y hy z hz Tr)
    exact e.1.trans e.2.1
  · intro m hm x
    obtain ⟨h, hh⟩ := GlobalTheory.T.truncation_family_levi_shift D V Φ L a hG P hP m hm
    have h0 : IsOrth (aP P) (0 : Finset (SV (wittIndex V)) → A0 (wittIndex V)) := fun _ _ _ _ => by simp
    have e : ∀ x, (weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr x : ℂ) = cM (aP P) ∅ (expFam (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr)) 0 := fun x =>
      (GlobalTheory.T.chamber_coefficient_product_formula hEFI hFP _ (aP P) hLevi (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr) 0 (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr) (hOrth x Tr) h0
        (fun _ _ => by simp)).1
    have hE : (∅ : Finset (SV (wittIndex V))) ∈ parF (aP P) ∅ :=
      mem_parF.2 ⟨⟨by simp, by simp⟩, vecSpan_mono (Finset.empty_subset P), Finset.Subset.refl _⟩
    apply Complex.ofReal_injective
    rw [e, e]
    exact GlobalTheory.T.chamber_coefficient_translation hFS _ (aP P) hLevi ∅ hE _ _ (hOrth x Tr) h (fun P' hP' => hh P' hP' x Tr)

end GlobalTheory
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_coefficients_invariant : GlobalTheory.Published.LabesseWaldspurger → ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ P, IsPar P → ∀ Tr, ∃ C Dd : Finset (SV (wittIndex V)) → GA D V → ℂ, (∀ Q ∈ parF (aP P) ∅, Continuous (C Q) ∧ (∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ y, C Q (m * y) = C Q y) ∧ ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), ∀ n ∈ NA (IsoFlag.single hW), ∀ y, C Q (n * y) = C Q y) ∧ (∀ z, Dd ∅ z = 1) ∧ (∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, (weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr (y * z) : ℂ) = ∑ Q ∈ parF (aP P) ∅, C Q y * Dd Q z) ∧ ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ x, weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr (m * x) = weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr x := by
  atlas_forward_decl GlobalTheory.weight_split_places
end
