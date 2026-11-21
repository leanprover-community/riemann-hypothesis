import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormNatEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariableStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMultiplicativeChartAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesTranslateNormLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPolesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowers
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledThetaTranslationQuotientElliptic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegralStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeCoordAddAndComplexMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImConjMulEqIntMulArea
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffSubstEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubstStatement

section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodReduction_algebraic_weierstrass_model : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (L : PeriodPair), d.Prime → d % 16 = 7 → IsOK d L → ∃ M : Mdl q, M.ι = ι ∧ M.L = L ∧ M.Ok ∧ IsAlgebraic ℚ M.W.a₁ ∧ IsAlgebraic ℚ M.W.a₂ ∧ IsAlgebraic ℚ M.W.a₃ ∧ IsAlgebraic ℚ M.W.a₄ ∧ IsAlgebraic ℚ M.W.a₆ := by
  first | exact @GlobalTheory.MomOne.exists_model | exact GlobalTheory.MomOne.exists_model | (intros; apply GlobalTheory.MomOne.exists_model <;> assumption)
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslateNorm

theorem inOK_neg {d : ℕ} {z : ℂ} (h : InOK d z) : InOK d (-z) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨-u, -v, by push_cast; ring⟩

theorem thetaTranslateValueAtZero_neg (d : ℕ) (θ : ℂ → ℂ) (he : ∀ z, θ (-z) = θ z) (t z : ℂ) :
    U1 d (-t) θ z = U1 d t θ (-z) := by
  unfold U1 h1
  rw [← he (z + -t)]
  congr 2
  · ring
  · simp only [map_neg]; ring

theorem cmLatticeTranslationOperator_mul_neg_translate (d : ℕ) (θ : ℂ → ℂ) (t w : ℂ) :
    U1 d t θ w * U1 d (-t) θ (w + t) = θ w * θ (w + t) := by
  unfold U1 h1
  have h0 : w + t + -t = w := by ring
  rw [h0, mul_mul_mul_comm, ← Complex.exp_add]
  have : -(Real.pi : ℂ) * (((2 / Real.sqrt d : ℝ) : ℂ) * (w * conj t)) -
      (Real.pi : ℂ) / 2 * (((2 / Real.sqrt d : ℝ) : ℂ) * (t * conj t)) +
      (-(Real.pi : ℂ) * (((2 / Real.sqrt d : ℝ) : ℂ) * ((w + t) * conj (-t))) -
      (Real.pi : ℂ) / 2 * (((2 / Real.sqrt d : ℝ) : ℂ) * (-t * conj (-t)))) = 0 := by
    simp only [map_neg]; ring
  rw [this, Complex.exp_zero]; ring

theorem differentiable_cmLatticeTranslationOperator_of_diff (d : ℕ) (θ : ℂ → ℂ) (hθ : Differentiable ℂ θ) (t : ℂ) : Differentiable ℂ (U1 d t θ) := by
  unfold U1 h1
  fun_prop

theorem ell_shift {L : PeriodPair} {φ : ℂ → ℂ} (h : Ell L φ) (a : ℂ) : Ell L (fun z => φ (z + a)) := by
  refine ⟨fun x => ?_, fun l hl z => ?_⟩
  · have h1 : MeromorphicAt φ ((fun z : ℂ => z + a) x) := h.1 _
    exact h1.comp_analyticAt (f := φ) (g := fun z : ℂ => z + a) (by fun_prop)
  · have := h.2 l hl (z + a)
    show φ (z + l + a) = φ (z + a)
    rw [← this]; congr 1; ring

theorem bd_one_of_inv {q : ℕ} [Fact q.Prime] (f g : ℂ_[q]⟦X⟧) (hf : Bdd f) (hg : Bdd g) (hfg : f * g = 1)
    (h : ∀ B, Bd B g → Bd B f) : Bd 1 f := by
  have h1 : Bd 1 (f * g) := by
    rw [hfg]
    intro n
    rw [coeff_one]
    split_ifs <;> simp
  have hm := (sup_norm_laws q).2.2.2.1 f g 1 hf hg h1
  intro i
  by_contra hi
  push_neg at hi
  have hp : 0 < ‖coeff i f‖ := lt_trans one_pos hi
  have hb : Bd (1 / ‖coeff i f‖) g := fun j => by
    rw [le_div_iff₀ hp, mul_comm]; exact hm i j
  have := h _ hb i
  rw [le_div_iff₀ hp] at this
  nlinarith

theorem bd_translate : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ t : ℂ, PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd 1 (hat M.ι (C ω * logS) (U1 d t θ)) := by
  intro d q _ M ω θ hd h16 hsp hOK hch hth t hpt hnt
  obtain ⟨s, hs, hsq, hst⟩ := id hpt
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  obtain ⟨hdiff, h0, hev, -, hz⟩ := id hth
  have hθt : θ t ≠ 0 := fun h => hnt (hz t h)
  have hP := GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd h16 hsp hOK hch hth t s hs hsq hst
  have hN := GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd h16 hsp hOK hch hth (-t) s hs hsq
    (by have := inOK_neg hst; rwa [← mul_neg] at this)
  simp only at hP hN
  set φp : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z) with hφp
  set φm : ℂ → ℂ := fun z => U1 d (-t) θ ((s : ℂ) * z) / θ ((s : ℂ) * z) with hφm
  obtain ⟨-, hPa, -, hPs, hPb⟩ := hP
  obtain ⟨hNe, hNa, hNp, -, hNb⟩ := hN
  set t' : ℂ := t / s with ht'
  have hst' : (s : ℂ) * t' = t := by rw [ht']; field_simp
  set ψ : ℂ → ℂ := fun z => φm (z + t') with hψ
  have hψe : Ell M.L ψ := ell_shift hNe t'
  have hψan : ∀ p, AnalyticAt ℂ φm (p + t') → AnalyticAt ℂ ψ p := fun p hp =>
    AnalyticAt.comp (g := φm) (f := fun z : ℂ => z + t') hp (by fun_prop)
  have hψ0 : AnalyticAt ℂ ψ 0 := hψan 0 (hNp _ (by rwa [zero_add, hst']))
  have hψt : AnalyticAt ℂ ψ (-t') := hψan _ (by rwa [neg_add_cancel])
  have hψp : ∀ p, meromorphicOrderAt ψ p < 0 → ¬ M.Small p := by
    intro p hp
    apply hPs p t hpt hnt
    by_contra hne
    have : AnalyticAt ℂ ψ p := hψan p (hNp _ (by rwa [mul_add, hst']))
    exact absurd this.meromorphicOrderAt_nonneg (not_le.mpr hp)
  have hψb := GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ ψ hch hψe hψ0 hψp
  have hback : (fun z => ψ (z + -t')) = φm := by
    funext z; simp [hψ]
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hch.2.1
  have hat1 := TaylorRead.hat_laws q M.ι _ hℓ
  have hmul := MulSeries.mulS_laws q

  have hb1 : ∀ B, Bd B (hat M.ι (C ω * logS) ψ) → Bd B (hat M.ι (C ω * logS) φm) := by
    intro B hB
    by_cases hsm : M.Small (-t')
    · have hin : InOK d (-t') := (GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd h16 hsp hOK hch).2.2.1 (-t')
        ⟨s * s, Nat.mul_pos hs hs, Nat.Coprime.mul_left hsq hsq, by
          have : ((s * s : ℕ) : ℂ) * (-t') = -((s : ℂ) * t) := by
            rw [← hst']; push_cast; ring
          rw [this]; exact inOK_neg hst⟩ hsm
      have hl : t' ∈ M.L.lattice := (hOK t').2 (by simpa using inOK_neg hin)
      have : ψ = φm := funext fun z => hNe.2 t' hl z
      rwa [← this]
    · have := GlobalTheory.T.cpTransportedTaylorSeries_translate_norm_le q M _ ψ (-t') B hch hψe hψ0 hψt hψp hsm (by rwa [hback]) hB
      rwa [hback] at this

  have hmp : φm = fun z => φp ((-1 : ℂ) * z) := by
    funext z
    simp only [hφm, hφp]
    rw [thetaTranslateValueAtZero_neg d θ hev, ← hev ((s : ℂ) * z)]
    congr 2 <;> ring
  have hb2 : ∀ B, Bd B (hat M.ι (C ω * logS) φm) → Bd B (hat M.ι (C ω * logS) φp) := by
    intro B hB
    rw [hmp, (hat_multiplicative_chart q M.ι ω φp hPa).2.2.1 (-1) (-1) (by simp [zc])] at hB
    exact (hmul.2.2.2.1 (-1) _ B (by simp)).1 hB

  have hprod : hat M.ι (C ω * logS) φp * hat M.ι (C ω * logS) ψ = 1 := by
    rw [← (hat1.1 φp ψ hPa hψ0).2.1]
    have hc := hat1.2.1 1
    rw [map_one, map_one] at hc
    rw [← hc]
    apply (hat1.1 _ _ (hPa.mul hψ0) analyticAt_const).2.2.1
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    have c1 : ContinuousAt (fun z : ℂ => θ ((s : ℂ) * z)) 0 :=
      (hdiff.continuous.comp (by fun_prop)).continuousAt
    have c2 : ContinuousAt (fun z : ℂ => θ ((s : ℂ) * z + t)) 0 :=
      (hdiff.continuous.comp (by fun_prop)).continuousAt
    filter_upwards [c1.eventually_ne (y := 0) (by simp [h0]), c2.eventually_ne (y := 0) (by simpa using hθt)]
      with z hz1 hz2
    simp only [hψ, hφm, hφp, Pi.mul_apply]
    rw [mul_add, hst', div_mul_div_comm, cmLatticeTranslationOperator_mul_neg_translate]
    exact div_self (mul_ne_zero hz1 hz2)
  have hP1 : Bd 1 (hat M.ι (C ω * logS) φp) :=
    bd_one_of_inv _ _ hPb hψb hprod fun B hB => hb2 B (hb1 B hB)

  have hθa : AnalyticAt ℂ θ 0 := hdiff.analyticAt 0
  have hUa : AnalyticAt ℂ (U1 d t θ) 0 := (differentiable_cmLatticeTranslationOperator_of_diff d θ hdiff t).analyticAt 0
  set f : ℂ → ℂ := fun z => U1 d t θ z / θ z with hf
  have hfa : AnalyticAt ℂ f 0 := hUa.div hθa (by simp [h0])
  have hf1 : Bd 1 (hat M.ι (C ω * logS) f) := by
    have e := (hat_multiplicative_chart q M.ι ω f hfa).2.2.1 (s : ℂ) (s : ℤ_[q]) (by simp [zc])
    have e' : φp = fun z => f ((s : ℂ) * z) := rfl
    rw [e', e] at hP1
    exact (hmul.2.2.2.1 (s : ℤ_[q]) _ 1 (PadicInt.norm_natCast_eq_one_iff.2 hsq.symm)).1 hP1
  have hθ1 := GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd h16 hsp hOK hch hth
  have hfin : hat M.ι (C ω * logS) (U1 d t θ) = hat M.ι (C ω * logS) f * hat M.ι (C ω * logS) θ := by
    rw [← (hat1.1 f θ hfa hθa).2.1]
    apply (hat1.1 _ _ hUa (hfa.mul hθa)).2.2.1
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [hdiff.continuous.continuousAt.eventually_ne (y := 0) (x := 0) (by simp [h0])] with z hz1
    simp only [hf, Pi.mul_apply]
    rw [div_mul_cancel₀ _ hz1]
  rw [hfin]
  simpa using ((sup_norm_laws q).1 _ _ 1 1 hf1 hθ1).2

end GlobalTheory.MomOne.TranslateNorm
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpSeriesBounded_one_torsionTranslate_cmTheta : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ t : ℂ, PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd 1 (hat M.ι (C ω * logS) (U1 d t θ)) := by
  atlas_forward_decl GlobalTheory.MomOne.TranslateNorm.bd_translate
end

section
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslNorm

lemma inOK_zero (d : ℕ) : InOK d 0 := ⟨0, 0, by simp⟩

lemma inOK_natMul {d : ℕ} {z : ℂ} (n : ℕ) (h : InOK d z) : InOK d ((n : ℂ) * z) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

lemma not_inOK_half {d : ℕ} (hd : 0 < d) : ¬ InOK d (0 - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exfalso; first | exact hs.ne' h | omega
  subst hv
  simp at hre
  have h2 : ((2 * u : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by push_cast; rw [← hre]; norm_num
  have h3 : 2 * u = -1 := by exact_mod_cast h2
  omega

lemma exists_common {d q m : ℕ} (s : Fin m → ℂ) (t : ℂ) (hs : ∀ j, PrimeTo d q (s j)) (ht : PrimeTo d q t) :
    ∃ S : ℕ, 0 < S ∧ Nat.Coprime S q ∧ InOK d ((S : ℂ) * t) ∧ ∀ j, InOK d ((S : ℂ) * s j) := by
  classical
  choose n hn0 hnq hn using hs
  obtain ⟨k, hk0, hkq, hk⟩ := ht
  refine ⟨k * ∏ j, n j, Nat.mul_pos hk0 (Finset.prod_pos fun j _ => hn0 j),
    Nat.Coprime.mul_left hkq (Nat.Coprime.prod_left fun j _ => hnq j), ?_, fun j => ?_⟩
  · have := inOK_natMul (∏ j, n j) hk
    convert this using 1
    rw [Nat.cast_mul]; ring
  · have := inOK_natMul (k * ∏ i ∈ Finset.univ.erase j, n i) (hn j)
    convert this using 1
    rw [← Finset.mul_prod_erase Finset.univ n (Finset.mem_univ j)]
    simp only [Nat.cast_mul]; ring

lemma differentiable_U1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) : Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

variable {q : ℕ} [Fact q.Prime]

lemma bd_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (a : ℕ) : Bd 1 (f ^ a) := by
  induction a with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ a ih =>
    have := ((GlobalTheory.MomOne.sup_norm_laws q).1 _ _ _ _ ih hf).2
    rwa [one_mul, ← pow_succ] at this

lemma hat_mul (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hl : constantCoeff ℓ = 0) {F G : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G :=
  ((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).1 F G hF hG).2.1

lemma hat_pow (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hl : constantCoeff ℓ = 0) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (a : ℕ) : hat ι ℓ (fun z => F z ^ a) = hat ι ℓ F ^ a := by
  induction a with
  | zero =>
    have := (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1 1
    simpa using this
  | succ a ih =>
    simp only [pow_succ]
    rw [hat_mul ι hl (F := fun z => F z ^ a) (by fun_prop) hF, ih]

lemma hat_comb (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hl : constantCoeff ℓ = 0) {κ : Type} (T : Finset κ)
    (c : κ → ℂ_[q]) (F : κ → ℂ → ℂ) (hF : ∀ j, AnalyticAt ℂ (F j) 0) (a : ℕ) :
    hat ι ℓ (fun z => ∑ j ∈ T, ι.symm (c j) * F j z ^ a) = ∑ j ∈ T, C (c j) * hat ι ℓ (F j) ^ a := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have := (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1 0
    simpa using this
  | insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    have hi' := hF i
    have h1 : AnalyticAt ℂ (fun z => ι.symm (c i) * F i z ^ a) 0 := by fun_prop
    have h2 : AnalyticAt ℂ (fun z => ∑ j ∈ T, ι.symm (c j) * F j z ^ a) 0 :=
      Finset.analyticAt_fun_sum _ fun j _ => by have := hF j; fun_prop
    rw [((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).1 _ _ h1 h2).1, ih,
      hat_mul ι hl (F := fun _ => ι.symm (c i)) (G := fun z => F i z ^ a) analyticAt_const (by fun_prop),
      hat_pow ι hl hi', (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1]
    simp

lemma bd_scale_iff (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) {S : ℕ} (hS : Nat.Coprime S q) {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 0) (B : ℝ) :
    Bd B (hat ι (C ω * logS) (fun z => G ((S : ℂ) * z))) ↔ Bd B (hat ι (C ω * logS) G) := by
  rw [(GlobalTheory.MomOne.hat_multiplicative_chart q ι ω G hG).2.2.1 (S : ℂ) (S : ℤ_[q]) (by simp [zc])]
  refine (GlobalTheory.MomOne.MulSeries.mulS_laws q).2.2.2.1 _ _ _ ?_
  exact PadicInt.norm_natCast_eq_one_iff.mpr hS.symm

theorem translate_bd : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  intro d q _ M ω θ hd hd16 hsp hL hM hθ a m c s t B hs ht ht2 hB
  obtain ⟨S, hS0, hSq, hSt, hSs⟩ := exists_common s t hs ht
  have hl : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hM.2.1
  have hSne : (S : ℂ) ≠ 0 := by exact_mod_cast hS0.ne'
  have hθd : Differentiable ℂ θ := hθ.1
  have hθt : θ t ≠ 0 := fun h => ht2 (hθ.2.2.2.2 t h)
  have hU : ∀ j, Differentiable ℂ (U1 d (s j) θ) := fun j => differentiable_U1 d _ hθd
  have hUU : ∀ j, Differentiable ℂ (U1 d t (U1 d (s j) θ)) := fun j => differentiable_U1 d _ (hU j)
  have hUt : Differentiable ℂ (U1 d t θ) := differentiable_U1 d _ hθd
  have E := fun j => GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hL hM hθ (s j) S hS0 hSq (hSs j)
  have Et := (GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hL hM hθ t S hS0 hSq hSt).2.2.2.1
  simp only at E
  set t' : ℂ := t / S with ht'
  have hSt' : (S : ℂ) * t' = t := by rw [ht']; field_simp
  set φ : ℂ → ℂ := fun z => ∑ j, M.ι.symm (c j) * (U1 d (s j) θ ((S : ℂ) * z) / θ ((S : ℂ) * z)) ^ a with hφ
  have hφan : ∀ p, θ ((S : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p := fun p hp =>
    Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.fun_mul (((E j).2.2.1 p hp).fun_pow a)
  have hφper : ∀ l ∈ M.L.lattice, ∀ z, φ (z + l) = φ z := fun l hl z =>
    Finset.sum_congr rfl fun j _ => by
      have := (E j).1.2 l hl z
      simp only at this
      rw [this]
  have hφmer : ∀ p, MeromorphicAt φ p := fun p =>
    MeromorphicAt.fun_sum fun j _ => (MeromorphicAt.const _ _).fun_mul (((E j).1.1 p).fun_pow a)
  have h0 : θ ((S : ℂ) * 0) ≠ 0 := by rw [mul_zero, hθ.2.1]; exact one_ne_zero
  have h0' : θ ((S : ℂ) * t') ≠ 0 := by rw [hSt']; exact hθt
  have hφ0 := hφan 0 h0
  have hφt := hφan t' h0'
  have hφt0 : AnalyticAt ℂ (fun z => φ (z + t')) 0 :=
    AnalyticAt.comp_of_eq hφt (f := fun z => z + t') (by fun_prop) (zero_add _)
  have hθS : AnalyticAt ℂ (fun z => θ ((S : ℂ) * z)) 0 :=
    (show Differentiable ℂ (fun z => θ ((S : ℂ) * z)) by fun_prop).analyticAt 0
  have hUtS : AnalyticAt ℂ (fun z => U1 d t θ ((S : ℂ) * z)) 0 :=
    (show Differentiable ℂ (fun z => U1 d t θ ((S : ℂ) * z)) by fun_prop).analyticAt 0

  have hBφ : Bd B (hat M.ι (C ω * logS) φ) := by
    have hG : Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ z ^ a) := by fun_prop
    rw [← hat_comb M.ι hl _ c _ (fun j => (hU j).analyticAt 0),
      ← bd_scale_iff M.ι ω hSq (hG.analyticAt 0)] at hB
    have hGS : AnalyticAt ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a) 0 :=
      (show Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a) by
        fun_prop).analyticAt 0
    have hpr : AnalyticAt ℂ (fun z => θ ((S : ℂ) * z) ^ a * φ z) 0 := (hθS.fun_pow a).fun_mul hφ0
    have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a)
        = θ ((S : ℂ) * z) ^ a * φ z := by
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      filter_upwards [hθS.continuousAt.eventually_ne h0] with z hz
      rw [hφ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_pow]; field_simp
    rw [((GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).1 _ _ hGS hpr).2.2.1 hev,
      hat_mul M.ι hl (hθS.fun_pow a) hφ0, hat_pow M.ι hl hθS] at hB
    have h1 : Bd 1 (hat M.ι (C ω * logS) (fun z => θ ((S : ℂ) * z))) :=
      (bd_scale_iff M.ι ω hSq (hθd.analyticAt 0) 1).mpr (GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd hd16 hsp hL hM hθ)
    refine (GlobalTheory.MomOne.sup_norm_laws q).2.2.2.2.2 _ _ 0 B (bd_pow h1 a) ?_ (by rwa [pow_zero, one_mul])
    rw [map_pow, (GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).2.2.2.1]
    simp [hθ.2.1]

  have hBφt : Bd B (hat M.ι (C ω * logS) (fun z => φ (z + t'))) := by
    by_cases hsm : M.Small t'
    · have hpt : PrimeTo d q t' :=
        ⟨S * S, Nat.mul_pos hS0 hS0, Nat.Coprime.mul_left hSq hSq, by
          rw [Nat.cast_mul, mul_assoc, hSt']; exact hSt⟩
      have hin := (hL t').mpr ((GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd16 hsp hL hM).2.2.1 t' hpt hsm)
      have : (fun z => φ (z + t')) = φ := funext fun z => hφper t' hin z
      rwa [this]
    · refine GlobalTheory.T.cpTransportedTaylorSeries_translate_norm_le q M _ φ t' B hM ⟨hφmer, hφper⟩ hφ0 hφt (fun p hp => ?_) hsm ?_ hBφ
      · refine Et p 0 ⟨1, one_pos, Nat.coprime_one_left q, by simpa using inOK_zero d⟩
          (not_inOK_half hd.pos) ?_
        by_contra hne
        rw [add_zero] at hne
        exact absurd (hφan p hne).meromorphicOrderAt_nonneg (not_le.mpr hp)
      · refine GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ _ hM ⟨fun p => ?_, fun l hl z => ?_⟩ hφt0 (fun p hp => ?_)
        · exact MeromorphicAt.comp_analyticAt (f := φ) (g := fun z => z + t') (hφmer _) (by fun_prop)
        · show φ (z + l + t') = φ (z + t')
          rw [add_right_comm, hφper l hl]
        · refine Et p t ht ht2 ?_
          by_contra hne
          have h2 : AnalyticAt ℂ φ (p + t') := hφan _ (by rwa [mul_add, hSt'])
          have h3 : AnalyticAt ℂ (fun z => φ (z + t')) p :=
            AnalyticAt.comp_of_eq h2 (f := fun z => z + t') (by fun_prop) rfl
          exact absurd h3.meromorphicOrderAt_nonneg (not_le.mpr hp)

  have hG : Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) z ^ a) := by fun_prop
  rw [← hat_comb M.ι hl _ c _ (fun j => (hUU j).analyticAt 0),
    ← bd_scale_iff M.ι ω hSq (hG.analyticAt 0)]
  have hGS : AnalyticAt ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a) 0 :=
    (show Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a) by
      fun_prop).analyticAt 0
  have hpr : AnalyticAt ℂ (fun z => U1 d t θ ((S : ℂ) * z) ^ a * φ (z + t')) 0 := (hUtS.fun_pow a).fun_mul hφt0
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a)
      = U1 d t θ ((S : ℂ) * z) ^ a * φ (z + t') := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    have hc : ContinuousAt (fun z => θ ((S : ℂ) * z + t)) 0 :=
      (show Differentiable ℂ (fun z => θ ((S : ℂ) * z + t)) by fun_prop).continuous.continuousAt
    filter_upwards [hc.eventually_ne (y := 0) (by simpa using hθt)] with z hz
    rw [hφ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have key : U1 d t (U1 d (s j) θ) ((S : ℂ) * z) = U1 d t θ ((S : ℂ) * z) *
        (U1 d (s j) θ ((S : ℂ) * (z + t')) / θ ((S : ℂ) * (z + t'))) := by
      rw [mul_add, hSt']
      generalize U1 d (s j) θ = F
      simp only [U1]
      field_simp
    rw [key, mul_pow]; ring
  rw [((GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).1 _ _ hGS hpr).2.2.1 hev,
    hat_mul M.ι hl (hUtS.fun_pow a) hφt0, hat_pow M.ι hl hUtS]
  have h1 : Bd 1 (hat M.ι (C ω * logS) (fun z => U1 d t θ ((S : ℂ) * z))) :=
    (bd_scale_iff M.ι ω hSq (hUt.analyticAt 0) 1).mpr (GlobalTheory.T.cpSeriesBounded_one_torsionTranslate_cmTheta d q M ω θ hd hd16 hsp hL hM hθ t ht ht2)
  have := ((GlobalTheory.MomOne.sup_norm_laws q).1 _ _ _ _ (bd_pow h1 a) hBφt).2
  rwa [one_mul] at this

end GlobalTheory.MomOne.TranslNorm
end
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_coprime_order_not_increase_theta_comb_norm : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  atlas_forward_decl GlobalTheory.MomOne.TranslNorm.translate_bd
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslNorm

theorem even_of_inOK_half {d : ℕ} (hd : 0 < d) {s : ℕ} (h : InOK d ((s : ℂ) / 2)) : 2 ∣ s := by
  obtain ⟨u, v, h⟩ := h
  have hs : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact (Real.sqrt_pos.mpr this).ne'
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exfalso
      first | exact hs h | omega
  subst hv
  have h2 : (s : ℝ) = 2 * u := by
    simp at hre
    linarith
  have h3 : (s : ℤ) = 2 * u := by exact_mod_cast h2
  omega

theorem inOK_add {d : ℕ} {x y : ℂ} (hx : InOK d x) (hy : InOK d y) : InOK d (x + y) := by
  obtain ⟨u, v, rfl⟩ := hx
  obtain ⟨u', v', rfl⟩ := hy
  exact ⟨u + u', v + v', by push_cast; ring⟩

theorem inOK_int_mul {d : ℕ} (k : ℤ) {x : ℂ} (hx : InOK d x) : InOK d ((k : ℂ) * x) := by
  obtain ⟨u, v, rfl⟩ := hx
  exact ⟨k * u, k * v, by push_cast; ring⟩

theorem primeTo_add {d q : ℕ} {x y : ℂ} (hx : PrimeTo d q x) (hy : PrimeTo d q y) :
    PrimeTo d q (x + y) := by
  obtain ⟨s, hs, hsq, hx⟩ := hx
  obtain ⟨r, hr, hrq, hy⟩ := hy
  refine ⟨s * r, Nat.mul_pos hs hr, Nat.Coprime.mul_left hsq hrq, ?_⟩
  have := inOK_add (inOK_int_mul (r : ℤ) hx) (inOK_int_mul (s : ℤ) hy)
  convert this using 1
  push_cast
  ring

theorem norm_law : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  intro d q hq M ω θ hd hd16 hsp hL hM hθ a m c s t B hs ht hB
  have law0 := GlobalTheory.T.translate_coprime_order_not_increase_theta_comb_norm d q M ω θ hd hd16 hsp hL hM hθ a m
  by_cases hhalf : InOK d (t - 1 / 2)
  swap
  · exact law0 c s t B hs ht hhalf hB
  have hd0 : 0 < d := hd.pos
  obtain ⟨hUU, -, hdiff, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd0
  obtain ⟨hlaws, hconst, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι (C ω * logS) hM.2.1
  have hcm : ∀ (r : ℂ) (F : ℂ → ℂ), Differentiable ℂ F →
      hat M.ι (C ω * logS) (fun z => r * F z) = C (M.ι r) * hat M.ι (C ω * logS) F := by
    intro r F hF
    rw [← hconst r]
    exact (hlaws (fun _ => r) F analyticAt_const (hF.analyticAt 0)).2.1
  have hτ : PrimeTo d q (t / 2) := by
    obtain ⟨n, hn, hnq, hnt⟩ := ht
    have h2 : 2 ∣ n := by
      apply even_of_inOK_half hd0
      have := inOK_add hnt (inOK_int_mul (-(n : ℤ)) hhalf)
      convert this using 1
      push_cast
      ring
    refine ⟨n * n, Nat.mul_pos hn hn, Nat.Coprime.mul_left hnq hnq, ?_⟩
    obtain ⟨k, hk⟩ := h2
    have := inOK_int_mul (k : ℤ) hnt
    convert this using 1
    have hk' : (n : ℂ) = 2 * k := by exact_mod_cast hk
    push_cast
    rw [hk']
    ring
  have hτ' : ¬ InOK d (t / 2 - 1 / 2) := by
    intro h
    have h1 : InOK d 1 := ⟨1, 0, by simp⟩
    have h2 : 2 ∣ 1 := by
      apply even_of_inOK_half hd0
      have := inOK_add (inOK_add (inOK_int_mul 2 h) h1) (inOK_int_mul (-1) hhalf)
      convert this using 1
      push_cast
      ring
    omega
  have hdouble : ∀ F : ℂ → ℂ, U1 d (t / 2) (U1 d (t / 2) F) = U1 d t F := by
    intro F
    rw [hUU]
    have him : (h1 d (t / 2) (t / 2)).im = 0 := by
      rw [h1, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_im]
    funext z
    rw [him, add_halves]
    simp
  set r : Fin m → ℂ := fun j =>
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d (t / 2) (s j)).im : ℝ) : ℂ)) with hr
  have hstep : ∀ j, U1 d (t / 2) (U1 d (s j) θ) = fun z => r j * U1 d (t / 2 + s j) θ z :=
    fun j => hUU _ _ _
  have hD : ∀ j, Differentiable ℂ (U1 d (t / 2 + s j) θ) := fun j => (hdiff _ _ hθ.1).1
  have h1 := law0 c s (t / 2) B hs hτ hτ' hB
  have h2 : Bd B (∑ j, C (c j * M.ι (r j) ^ a) *
      hat M.ι (C ω * logS) (U1 d (t / 2 + s j) θ) ^ a) := by
    convert h1 using 2 with j
    rw [hstep j, hcm _ _ (hD j), mul_pow, map_mul, map_pow, mul_assoc]
  have h3 := law0 _ _ (t / 2) B (fun j => primeTo_add hτ (hs j)) hτ hτ' h2
  convert h3 using 2 with j
  have : U1 d t (U1 d (s j) θ) = fun z => r j * U1 d (t / 2) (U1 d (t / 2 + s j) θ) z := by
    rw [← hdouble, hstep j]
    funext z
    simp only [U1]
    ring
  rw [this, hcm _ _ (hdiff _ _ (hD j)).1, mul_pow, map_mul, map_pow, mul_assoc]

end GlobalTheory.MomOne.TranslNorm
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  atlas_forward_decl GlobalTheory.MomOne.TranslNorm.norm_law
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.Norm

variable {q : ℕ} [hq : Fact q.Prime]

lemma cc_subst {a : ℂ_[q]⟦X⟧} (ha : constantCoeff a = 0) (f : ℂ_[q]⟦X⟧) :
    constantCoeff (f.subst a : ℂ_[q]⟦X⟧) = constantCoeff f := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
  · simp
  · intro k hk
    simp [ha, hk]

lemma coeff_expY_subst {a : ℂ_[q]⟦X⟧} (ha : constantCoeff a = 0) (f : ℂ_[q]⟦X⟧) :
    coeff 1 (f.subst a : ℂ_[q]⟦X⟧) = coeff 1 f * coeff 1 a := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  have e := congrArg constantCoeff (derivative_subst (f := f) hs)
  rw [map_mul, cc_subst ha] at e
  simpa [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] using e

lemma const_log (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [logS]
  simp [this]

lemma hat_scale (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ) (a : ℤ_[q]) :
    hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  obtain ⟨hm, -⟩ := MulSeries.mulS_laws q
  obtain ⟨-, h0, -, hl⟩ := hm a
  have hsub : HasSubst (mulS a : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' h0
  have hs : HasSubst (C ω * logS : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' (const_log ω)
  unfold hat
  rw [subst_comp_subst_apply hs hsub, ← smul_eq_C_mul (a := ω), subst_smul hsub, hl, smul_eq_C_mul,
    map_mul, mul_assoc]

lemma mchart_scale (M : Mdl q) {ω : ℂ_[q]} (h : M.MChart ω) {a : ℤ_[q]} (ha : ‖a‖ = 1) :
    M.MChart (ω * zc a) := by
  obtain ⟨hm, -, -, hb, -, hn⟩ := MulSeries.mulS_laws q
  obtain ⟨-, h0, h1, -⟩ := hm a
  obtain ⟨ok, -, bd, c1⟩ := h
  refine ⟨ok, const_log _, ?_, ?_⟩
  · rw [hat_scale, hb a _ _ ha]; exact bd
  · rw [hat_scale, coeff_expY_subst h0, norm_mul, c1, h1, hn, ha, one_mul]

lemma at_scale (M : Mdl q) {ω : ℂ_[q]} (h : M.MChart ω) {a : ℤ_[q]} {ξ : ℂ_[q]} {n k : ℕ} {y : ℂ}
    (hξ : ξ ^ (q ^ n) = 1) (hk : ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ))) (hy : M.At ω (ξ ^ k) y) :
    M.At (ω * zc a) ξ y := by
  obtain ⟨hm, -⟩ := MulSeries.mulS_laws q
  obtain ⟨-, h0, -, -⟩ := hm a
  obtain ⟨h1, h2⟩ := (GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 ξ n k a _ hξ hk ⟨1, h.2.2.1⟩
  obtain ⟨s, h3, h4⟩ := hy
  refine ⟨s, h1, ?_⟩
  rw [hat_scale, ← (Shift.shift_laws q ξ h1).2.2.2.2.1, h2, cc_subst h0,
    (Shift.shift_laws q _ h3).2.2.2.2.1, h4]

lemma at_pow (M : Mdl q) {ω : ℂ_[q]} (h : M.MChart ω) {ξ : ℂ_[q]} {p : ℂ} (hp : M.At ω ξ p) (k : ℕ) :
    M.At ω (ξ ^ k) ((k : ℂ) * p) := by
  induction k with
  | zero => simpa using (GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω h).2.2.2.2
  | succ k ih =>
    have := (GlobalTheory.T.multiplicativeCoord_add_and_complexMul q M ω h).1 _ _ _ _ ih hp
    rw [← pow_succ] at this
    convert this using 1
    push_cast; ring

noncomputable def rt (q n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((q ^ n : ℕ) : ℂ))

lemma rt_prim (n : ℕ) : IsPrimitiveRoot (rt q n) (q ^ n) :=
  Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ hq.out.ne_zero)

lemma rt_succ (n : ℕ) : rt q (n + 1) ^ q = rt q n := by
  unfold rt
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  push_cast
  field_simp
  ring

lemma kap_eq {d : ℕ} (hd : 0 < d) (n : ℕ) (u b : ℤ) :
    kap1 d 1 (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n) = rt q n ^ b := by
  unfold kap1 rt
  rw [← Complex.exp_int_mul]
  congr 1
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have : (h1 d 1 (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n)).im = -(b : ℝ) / (q : ℝ) ^ n := by
    unfold h1
    have e : ((q : ℂ) ^ n) = (((q : ℝ) ^ n : ℝ) : ℂ) := by push_cast; rfl
    rw [e, one_mul, Complex.im_ofReal_mul, Complex.conj_im, Complex.div_ofReal_im]
    simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re, OKArith.im_w]
    field_simp
    ring
  rw [this]
  push_cast
  ring

lemma norm_qpow (n : ℕ) : ‖(q : ℂ_[q]) ^ n‖ = (q : ℝ) ^ (-(n : ℤ)) := by
  have := OKArith.norm_zc (q := q) ((q : ℤ_[q]) ^ n)
  rw [PadicInt.norm_p_pow] at this
  simpa using this

lemma pow_le (n m : ℕ) (h : n ≤ m) : (q : ℝ) ^ (-(m : ℤ)) ≤ (q : ℝ) ^ (-(n : ℤ)) := by
  have : (1 : ℝ) ≤ q := by exact_mod_cast hq.out.one_lt.le
  exact zpow_le_zpow_right₀ this (by omega)

section
variable {d : ℕ} (hd : d.Prime) (h16 : d % 16 = 7) (hs : Split d q)
include hd h16 hs

lemma norm_le (ι : ℂ ≃+* ℂ_[q]) {α : ℂ} (h : InOK d α) : ‖ι α‖ ≤ 1 := by
  obtain ⟨⟨a, ha⟩, -⟩ := (okArith d q ι hd h16 hs).2.1 α h
  rw [ha, OKArith.zc_eq, OKArith.norm_zc]
  exact PadicInt.norm_le_one a

lemma div_ok (ι : ℂ ≃+* ℂ_[q]) (n : ℕ) (u b : ℤ) (hb : (q : ℤ) ^ n ∣ b)
    (hc : ‖ι (conj ((u : ℂ) + (b : ℂ) * wK d))‖ ≤ (q : ℝ) ^ (-(n : ℤ))) :
    InOK d (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n) := by
  refine (okArith d q ι hd h16 hs).2.2.1 _ n ⟨u, b, rfl⟩ ?_ hc
  obtain ⟨c, rfl⟩ := hb
  have h1 : ‖ι (((-c : ℤ) : ℂ) + ((2 * c : ℤ) : ℂ) * wK d)‖ ≤ 1 := norm_le hd h16 hs ι ⟨_, _, rfl⟩
  have e : (u : ℂ) + (((q : ℤ) ^ n * c : ℤ) : ℂ) * wK d =
      conj ((u : ℂ) + (((q : ℤ) ^ n * c : ℤ) : ℂ) * wK d) +
        (q : ℂ) ^ n * (((-c : ℤ) : ℂ) + ((2 * c : ℤ) : ℂ) * wK d) := by
    rw [OKArith.conj_el]; push_cast; ring
  rw [e, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc ?_)
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_qpow]
  exact mul_le_of_le_one_right (by positivity) h1

lemma gen (M : Mdl q) {ω : ℂ_[q]} (hL : IsOK d M.L) (h : M.MChart ω) (n : ℕ) :
    ∃ u b : ℤ, M.At ω (M.ι (rt q n)) (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n) ∧
      ‖M.ι (conj ((u : ℂ) + (b : ℂ) * wK d))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) ∧ (n ≠ 0 → ¬ (q : ℤ) ∣ b) := by
  obtain ⟨hex, -, huq, hlat, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω h
  obtain ⟨⟨-, -, hring⟩, hint, -, hid, -⟩ := okArith d q M.ι hd h16 hs
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
  have hη : M.ι (rt q n) ^ (q ^ n) = 1 := by rw [← map_pow, (rt_prim n).pow_eq_one, map_one]
  have hlt : ‖M.ι (rt q n) - 1‖ < 1 :=
    ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 _ n 0 0 0 hη (by simp) ⟨0, fun m => by simp⟩).1
  obtain ⟨p, hp⟩ := hex _ hlt
  have kill : ∀ z, M.At ω 1 z ↔ InOK d z := fun z => by
    rw [hlat 1 0 z h10, zero_sub, neg_mem_iff, hL]
  have h1 := at_pow M h hp (q ^ n)
  rw [hη, kill] at h1
  obtain ⟨u, b, hub⟩ := h1
  have hpe : p = ((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n := by
    rw [← hub]; push_cast; field_simp
  have hc : ‖M.ι (conj ((u : ℂ) + (b : ℂ) * wK d))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    obtain ⟨e, he, he1, he2⟩ := hid (n + 1) 1 (by simp)
    have hce := (hring e e he he).2.2.2
    obtain ⟨⟨a, ha⟩, -⟩ := hint _ hce
    have h2 := (GlobalTheory.T.multiplicativeCoord_add_and_complexMul q M ω h).2 (conj e) a n 0 _ p
      (fun l hl => (hL _).2 (hring _ _ hce ((hL _).1 hl)).2.1) ha
      (by
        rw [Nat.cast_zero, sub_zero, ← OKArith.norm_zc, ← OKArith.zc_eq, ← ha]
        exact he2.trans (pow_le _ _ (by omega))) hη hp
    rw [pow_zero, kill] at h2
    have h3 := norm_le hd h16 hs M.ι (hring _ _ h2 h2).2.2.2
    have hne : ‖M.ι e‖ = 1 := by
      rw [Nat.cast_one, one_mul] at he1
      have : ‖M.ι e - 1‖ < ‖(1 : ℂ_[q])‖ := by
        rw [norm_one]
        exact he1.trans_lt (zpow_lt_one_of_neg₀ hq1 (by omega))
      have h5 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this.ne
      rw [sub_add_cancel, max_eq_right this.le, norm_one] at h5
      exact h5
    have e1 : e * conj ((u : ℂ) + (b : ℂ) * wK d) = (q : ℂ) ^ n * conj (conj e * p) := by
      rw [← hub]; simp only [map_mul, Complex.conj_conj, map_natCast]; push_cast; ring
    have e2 := congrArg (fun z => ‖M.ι z‖) e1
    simp only [map_mul M.ι, norm_mul, hne, one_mul, map_pow M.ι, map_natCast, norm_qpow] at e2
    rw [e2]
    exact mul_le_of_le_one_right (by positivity) h3
  refine ⟨u, b, hpe ▸ hp, hc, fun hn hb => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h4 := div_ok hd h16 hs M.ι 1 u b (by simpa using hb) (hc.trans (pow_le _ _ (by omega)))
  have e3 : ((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ 1 = ((q ^ m : ℕ) : ℂ) * p := by
    rw [hpe, Nat.succ_eq_add_one]; push_cast; field_simp; ring
  rw [e3, ← kill] at h4
  have h5 := huq _ _ _ (at_pow M h hp (q ^ m)) h4
  rw [← map_pow, ← map_one M.ι] at h5
  have h6 := (rt_prim (q := q) (m + 1)).dvd_of_pow_eq_one _ (M.ι.injective h5)
  have := (Nat.pow_dvd_pow_iff_le_right hq.out.one_lt).1 h6
  omega

end

theorem exists_normalised_chart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → ∃ a : ℤ_[q], ‖a‖ = 1 ∧ M.MChart (ω * zc a) ∧ ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At (ω * zc a) (M.ι (kap1 d 1 y)) y := by
  intro d q hq M ω hd h16 hs hL h
  choose u b hat hc hb using gen hd h16 hs M hL h
  obtain ⟨-, -, -, hlat, -⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω h
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hdv : ∀ n, (q : ℤ) ^ n ∣ b (n + 1) - b n := fun n => by
    have h1 := at_pow M h (hat (n + 1)) q
    rw [← map_pow, rt_succ] at h1
    obtain ⟨s, t, hst⟩ := (hL _).1 ((hlat _ _ _ h1).1 (hat n))
    have : ((u (n + 1) - u n : ℤ) : ℂ) + ((b (n + 1) - b n : ℤ) : ℂ) * wK d =
        (((q : ℤ) ^ n * s : ℤ) : ℂ) + (((q : ℤ) ^ n * t : ℤ) : ℂ) * wK d := by
      push_cast
      have e : (q : ℂ) ^ n * s + (q : ℂ) ^ n * t * wK d = (q : ℂ) ^ n * ((s : ℂ) + t * wK d) := by ring
      rw [e, ← hst]
      field_simp
      ring
    exact ⟨t, (OKArith.coord_unique hd.pos this).2⟩
  set β : ℤ_[q] := PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub b q hdv) with hβ
  have hβn : ∀ n, PadicInt.toZModPow n β = b n :=
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub b q hdv
  have hβu : IsUnit β := by
    by_contra hu
    have h1 : ‖β‖ < 1 := PadicInt.not_isUnit_iff.1 hu
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := hβn 1
    rw [hc, map_mul, map_natCast] at h2
    have h3 : ((q : ℕ) : ZMod (q ^ 1)) = 0 := by rw [ZMod.natCast_eq_zero_iff]; simp
    rw [h3, zero_mul, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    exact hb 1 one_ne_zero (by simpa using h2)
  obtain ⟨a, ha⟩ := hβu.exists_left_inv
  have hna : ‖a‖ = 1 := PadicInt.isUnit_iff.1 (IsUnit.of_mul_eq_one _ ha)
  refine ⟨a, hna, mchart_scale M h hna, ?_⟩
  rintro n y ⟨v, ⟨s, t, rfl⟩, hv, rfl⟩
  rw [Nat.cast_one, one_mul, kap_eq hd.pos]
  have hqn : 0 < q ^ n := pow_pos hq.out.pos n
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = t % ((q ^ n : ℕ) : ℤ) :=
    ⟨_, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hqn.ne'))⟩
  have hrt : rt q n ^ t = rt q n ^ k := by
    have h0 : rt q n ≠ 0 := Complex.exp_ne_zero _
    conv_lhs => rw [← Int.emod_add_mul_ediv t ((q ^ n : ℕ) : ℤ), ← hk]
    rw [zpow_add₀ h0, zpow_mul, zpow_natCast, zpow_natCast, (rt_prim n).pow_eq_one, one_zpow, mul_one]
  have hξ : M.ι (rt q n ^ t) ^ (q ^ n) = 1 := by
    rw [hrt, ← map_pow, ← pow_mul, mul_comm, pow_mul, (rt_prim n).pow_eq_one, one_pow, map_one]
  refine ⟨hξ, at_scale M h (k := a.appr n) hξ ?_ ?_⟩
  · rw [PadicInt.norm_le_pow_iff_mem_span_pow]
    exact PadicInt.appr_spec n a
  · have h1 := at_pow M h (hat n) (k * a.appr n)
    rw [hrt, map_pow, ← pow_mul]
    refine (hlat _ _ _ h1).2 ((hL _).2 ?_)
    have hz : (q : ℤ) ^ n ∣ (k * a.appr n : ℕ) * b n - t := by
      have e1 : ((a.appr n : ℕ) : ZMod (q ^ n)) * (b n : ZMod (q ^ n)) = 1 := by
        rw [← hβn, show ((a.appr n : ℕ) : ZMod (q ^ n)) = PadicInt.toZModPow n a from rfl, ← map_mul, ha,
          map_one]
      have e2 : ((k : ℕ) : ZMod (q ^ n)) = (t : ZMod (q ^ n)) := by
        rw [← Int.cast_natCast, hk, ZMod.intCast_mod]
      have : ((((k * a.appr n : ℕ) : ℤ) * b n - t : ℤ) : ZMod (q ^ n)) = 0 := by
        push_cast
        rw [mul_assoc, e1, e2, mul_one, sub_self]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact_mod_cast this
    have h2 := div_ok hd h16 hs M.ι n ((k * a.appr n : ℕ) * u n - s) _ hz (by
      have e : conj (((((k * a.appr n : ℕ) : ℤ) * u n - s : ℤ) : ℂ) +
          ((((k * a.appr n : ℕ) : ℤ) * b n - t : ℤ) : ℂ) * wK d) =
          ((k * a.appr n : ℕ) : ℂ) * conj ((u n : ℂ) + (b n : ℂ) * wK d) +
            - conj ((s : ℂ) + (t : ℂ) * wK d) := by
        simp only [OKArith.conj_el]; push_cast; ring
      rw [e, map_add, map_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [map_mul, map_natCast, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans (hc n)
      · rw [norm_neg]
        refine hv.trans ?_
        have := pow_le (q := q) n (2 * n) (by omega)
        simpa using this)
    convert h2 using 1
    push_cast
    ring

end GlobalTheory.MomOne.Norm
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_multiplicativeChart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → ∃ a : ℤ_[q], ‖a‖ = 1 ∧ M.MChart (ω * zc a) ∧ ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At (ω * zc a) (M.ι (kap1 d 1 y)) y := by
  atlas_forward_decl GlobalTheory.MomOne.Norm.exists_normalised_chart
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section

namespace GlobalTheory.MomOne.ThetaZero

theorem indep {d : ℕ} (hd : 0 < d) : LinearIndependent ℝ ![(1 : ℂ), wK d] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have ht : t = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)
  subst ht
  simp at hre
  exact ⟨hre, rfl⟩

def pair {d : ℕ} (hd : 0 < d) : PeriodPair := ⟨1, wK d, indep hd⟩

theorem isOK_pair {d : ℕ} (hd : 0 < d) : IsOK d (pair hd) := by
  intro z
  rw [PeriodPair.mem_lattice]
  simp only [pair, mul_one, InOK]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

theorem G_eq {d : ℕ} {L : PeriodPair} (h : IsOK d L) {k : ℕ} (hk : k ≠ 0) :
    L.G (2 * k) = eis d k := by
  unfold PeriodPair.G eis
  have e1 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
  have e2 := tsum_subtype {w : ℂ | InOK d w ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine tsum_congr fun w => ?_
  by_cases h0 : w = 0
  · subst h0
    simp [Set.indicator, hk]
  · have hw : w ∈ (L.lattice : Set ℂ) ↔ w ∈ {w : ℂ | InOK d w ∧ w ≠ 0} :=
      ⟨fun a => ⟨(h w).1 a, h0⟩, fun a => (h w).2 a.1⟩
    by_cases hm : w ∈ (L.lattice : Set ℂ)
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hw.1 hm), one_div]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (hw.not.1 hm)]

def lam (d : ℕ) : AddSubgroup ℂ := AddSubgroup.closure {1, wK d}

theorem mem_lam (d : ℕ) (z : ℂ) : z ∈ lam d ↔ InOK d z := by
  rw [lam, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul, mul_one, InOK]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

theorem area_lam {d : ℕ} (hd : 0 < d) : Formalism.MainNotions.TaylorLogMetric.area (lam d) = Real.sqrt d / 2 := by
  rw [lam, GlobalTheory.TransInv.area_closure_pair (indep hd)]
  simp [wK, abs_div]

theorem thetaTranslationOperator_apply {d : ℕ} (hd : 0 < d) (x : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    Formalism.MainNotions.TaylorLogMetric.U1 (lam d) x F z = U1 d x F z := by
  simp only [Formalism.MainNotions.TaylorLogMetric.U1, U1, h1, area_lam hd]
  congr 2
  push_cast
  ring

theorem thetaTranslation_comp_eq_cocycle_mul (d : ℕ) (a b : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    U1 d a (U1 d b F) z =
      Complex.exp ((Real.pi : ℂ) / 2 * (h1 d b a - h1 d a b)) * U1 d (a + b) F z := by
  simp only [U1]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z a b]
  congr 2
  simp only [h1, map_add]
  ring

theorem half_not_mem {d : ℕ} (hd : 0 < d) (u v : ℤ) (h : ¬ (Odd u ∧ Even v)) :
    ((u : ℂ) + (v : ℂ) * wK d) / 2 + 1 / 2 ∉ lam d := by
  rw [mem_lam]
  rintro ⟨m, n, e⟩
  have := (LinearIndependent.pair_iff.1 (indep hd)) ((u + 1 - 2 * m : ℤ) : ℝ) ((v - 2 * n : ℤ) : ℝ) (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * e)
  have h1 : u + 1 - 2 * m = 0 := by exact_mod_cast this.1
  have h2 : v - 2 * n = 0 := by exact_mod_cast this.2
  exact h ⟨⟨m - 1, by omega⟩, ⟨n, by omega⟩⟩

theorem normSq_eq {d : ℕ} (c : ℤ) (hc : (d : ℤ) + 1 = 8 * c) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + 2 * c * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hc' : (d : ℝ) + 1 = 8 * c := by exact_mod_cast hc
  simp [Complex.normSq_apply, wK]
  linear_combination (v : ℝ) ^ 2 / 4 * hs + (v : ℝ) ^ 2 / 4 * hc'

theorem exp_even {n : ℤ} (h : Even n) : Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ)) = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [← Complex.exp_int_mul_two_pi_mul_I k]
  congr 1
  push_cast
  ring

theorem comm_eq {d : ℕ} (hd : 0 < d) (u v : ℤ) :
    h1 d (wK d) ((u : ℂ) + (v : ℂ) * wK d) - h1 d ((u : ℂ) + (v : ℂ) * wK d) (wK d) =
      2 * u * Complex.I := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  simp only [h1, wK, map_add, map_mul, map_div₀, map_intCast, map_one, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  push_cast
  field_simp
  ring

theorem exists_isTh {d : ℕ} (hd8 : d % 8 = 7) : ∃ θ : ℂ → ℂ, IsTh d θ := by
  have hd : 0 < d := by omega
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (d : ℤ) + 1 = 8 * c := ⟨((d : ℤ) + 1) / 8, by omega⟩
  have hlat : GlobalTheory.EvenTheta.IsLat (lam d) := ⟨1, wK d, indep hd, rfl⟩
  have ht : (1 / 2 : ℂ) ∉ lam d := by
    simpa using half_not_mem hd 0 0 (by simp)
  have ht2 : 2 * (1 / 2 : ℂ) ∈ lam d := (mem_lam d _).2 ⟨1, 0, by simp⟩
  obtain ⟨b1, b2, b3, -, b5, b6⟩ := GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties (lam d) hlat (1 / 2) ht ht2
  generalize Formalism.MainNotions.GL3Theta.th0 (lam d) (1 / 2) = θ at b1 b2 b3 b5 b6
  have fix : ∀ u v : ℤ, ¬ (Odd u ∧ Even v) → U1 d ((u : ℂ) + (v : ℂ) * wK d) θ = θ := by
    intro u v h
    funext z
    rw [← thetaTranslationOperator_apply hd]
    exact b6 _ ((mem_lam d _).2 ⟨u, v, rfl⟩) (half_not_mem hd u v h) z
  refine ⟨θ, b1, b2, b3, ?_, fun z hz => ?_⟩
  · rintro x ⟨u, v, rfl⟩
    funext z
    simp only [W1]
    rw [normSq_eq c hc, Complex.ofReal_intCast]
    by_cases h : Odd u ∧ Even v
    · have f1 := fix u (v - 1) (by
        rintro ⟨-, h2⟩
        rcases h2 with ⟨a, ha⟩
        rcases h.2 with ⟨b, hb⟩
        omega)
      have f2 : U1 d (wK d) θ = θ := by simpa using fix 0 1 (by simp)
      have k := thetaTranslation_comp_eq_cocycle_mul d ((u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d) (wK d) θ z
      rw [f2, f1, comm_eq hd,
        show (u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d + wK d = (u : ℂ) + (v : ℂ) * wK d by
          push_cast; ring] at k
      have hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2 - u) := by
        obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
        exact ⟨(2 * a + 1) * a + (2 * a + 1) * b + c * (b + b) ^ 2, by ring⟩
      have e := exp_even hev
      rw [k]
      congr 1
      rw [← one_mul (Complex.exp ((Real.pi : ℂ) / 2 * _)), ← e, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · have hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2) := by
        rcases Int.even_or_odd u with ⟨a, rfl⟩ | ⟨a, rfl⟩
        · exact ⟨2 * a ^ 2 + a * v + c * v ^ 2, by ring⟩
        · rcases Int.even_or_odd v with hv | ⟨b, rfl⟩
          · exact absurd ⟨⟨a, rfl⟩, hv⟩ h
          · exact ⟨(2 * a + 1) * (a + b + 1) + c * (2 * b + 1) ^ 2, by ring⟩
      rw [exp_even hev, one_mul, fix u v h]
  · obtain ⟨m, n, e⟩ := (mem_lam d _).1 ((b5 z).1 hz)
    exact ⟨m - 1, n, by push_cast; linear_combination e⟩

end GlobalTheory.MomOne.ThetaZero

namespace GlobalTheory.MomOne

theorem exists_pair_and_isTh : ∀ d : ℕ, d.Prime → d % 16 = 7 → (∃ L : PeriodPair, IsOK d L ∧ L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) ∧ ∃ θ : ℂ → ℂ, IsTh d θ := by
  intro d hp h
  refine ⟨⟨ThetaZero.pair hp.pos, ThetaZero.isOK_pair hp.pos, ?_⟩, ThetaZero.exists_isTh (by omega)⟩
  have h2 := ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 2) (by norm_num)
  have h3 := ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 3) (by norm_num)
  unfold discr PeriodPair.g₂ PeriodPair.g₃
  rw [← h2, ← h3]

end GlobalTheory.MomOne
end
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta : ∀ d : ℕ, d.Prime → d % 16 = 7 → (∃ L : PeriodPair, IsOK d L ∧ L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) ∧ ∃ θ : ℂ → ℂ, IsTh d θ := by
  atlas_forward_decl GlobalTheory.MomOne.exists_pair_and_isTh
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ThShift

variable {q : ℕ} [Fact q.Prime]

theorem hat_pow (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) (F : ℂ → ℂ)
    (hF : AnalyticAt ℂ F 0) (m : ℕ) : hat ι ℓ (fun z => F z ^ m) = hat ι ℓ F ^ m := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hℓ
  induction m with
  | zero => simpa using h2 1
  | succ k ih =>
    have hk : AnalyticAt ℂ (fun z => F z ^ k) 0 := hF.pow k
    have := (h1 _ F hk hF).2.1
    simp only [pow_succ]
    rw [this, ih]

theorem const_ell (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; simp [logS]
  simp [this]

theorem hat_funEq (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (F G : ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (hG : AnalyticAt ℂ G 0) (α : ℂ) (a : ℤ_[q]) (ha : ι α = zc a) (m : ℕ)
    (h : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (α * z) = F z ^ m * G z) :
    (hat ι (C ω * logS) F).subst (mulS a : ℂ_[q]⟦X⟧)
      = hat ι (C ω * logS) F ^ m * hat ι (C ω * logS) G := by
  obtain ⟨h1, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q ι _ (const_ell ω)
  rw [← (GlobalTheory.MomOne.hat_multiplicative_chart q ι ω F hF).2.2.1 α a ha,
    ← hat_pow ι _ (const_ell ω) F hF m]
  have hk : AnalyticAt ℂ (fun z => F z ^ m) 0 := hF.pow m
  rw [← (h1 _ G hk hG).2.1]
  have hα : AnalyticAt ℂ (fun z => F (α * z)) 0 := by
    have h0 : AnalyticAt ℂ (fun z : ℂ => α * z) 0 := by fun_prop
    exact AnalyticAt.comp_of_eq hF h0 (by simp)
  exact (h1 _ _ hα (hk.mul hG)).2.2.1 h

theorem bd_pow (f : ℂ_[q]⟦X⟧) (hf : Bd 1 f) (m : ℕ) : Bd 1 (f ^ m) := by
  induction m with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih =>
    have := ((GlobalTheory.MomOne.sup_norm_laws q).1 _ _ _ _ ih hf).2
    simpa [pow_succ] using this

theorem shift_pow (ζ : ℂ_[q]) (hζ : ‖ζ - 1‖ < 1) (f : ℂ_[q]⟦X⟧) (hf : Bd 1 f) (m : ℕ) :
    shiftS ζ (f ^ m) = shiftS ζ f ^ m := by
  obtain ⟨-, h2, h3, -⟩ := GlobalTheory.MomOne.Shift.shift_laws q ζ hζ
  induction m with
  | zero => simpa using h3 1
  | succ k ih =>
    rw [pow_succ, (h2 _ _ ⟨1, bd_pow f hf k⟩ ⟨1, hf⟩).2, ih, pow_succ]

theorem not_half (d : ℕ) (hd : 0 < d) : ¬ InOK d (0 - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exfalso; first | exact hs.ne' h | omega | (simp at h; omega)
  subst hv
  have : (2 * u : ℝ) = -1 := by simp at hre; linarith
  have : 2 * u = -1 := by exact_mod_cast this
  omega

theorem zc_natCast (k : ℕ) : zc (k : ℤ_[q]) = (k : ℂ_[q]) := by simp [zc]

theorem zc_sub_one (a : ℤ_[q]) : zc (a - 1) = zc a - 1 := by simp [zc]

theorem coprime_pred (m : ℕ) (hm : 1 ≤ m) (h : ‖(m : ℂ_[q])‖ < 1) : Nat.Coprime (m - 1) q := by
  have hn := (GlobalTheory.MomOne.MulSeries.mulS_laws q).2.2.2.2.2
  rw [← zc_natCast, hn] at h
  have h1 : (q : ℤ) ∣ (m : ℤ) := by
    rw [← PadicInt.norm_int_lt_one_iff_dvd]; simpa using h
  have h2 : q ∣ m := by exact_mod_cast h1
  rw [Nat.coprime_comm, (Fact.out : q.Prime).coprime_iff_not_dvd]
  intro h3
  have h4 : q ∣ m - (m - 1) := Nat.dvd_sub h2 h3
  have h5 : m - (m - 1) = 1 := by omega
  rw [h5] at h4
  exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h4)

theorem W_mul_eq (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (θ : ℂ → ℂ) (hd : d.Prime) (hd7 : d % 16 = 7)
    (hs : Split d q) (hθ : IsTh d θ) (n : ℕ) (y : ℂ) (hy : Good ι d n 1 y) (α : ℂ) (hα : InOK d α)
    (hα1 : ‖ι α - 1‖ ≤ (q : ℝ) ^ (-(n : ℤ))) : W1 d (α * y) θ = W1 d y θ := by
  obtain ⟨⟨o1, -, oR⟩, oZ, oD, -⟩ := GlobalTheory.MomOne.okArith d q ι hd hd7 hs
  have hn := (GlobalTheory.MomOne.MulSeries.mulS_laws q).2.2.2.2.2
  have hle : ∀ β, InOK d β → ‖ι β‖ ≤ 1 := by
    intro β hβ
    obtain ⟨a, ha⟩ := (oZ β hβ).1
    rw [ha, hn]; exact a.norm_le_one
  have hmul : ∀ a b, InOK d a → InOK d b → InOK d (a * b) := fun a b ha hb => (oR a b ha hb).2.1
  have hconj : ∀ a, InOK d a → InOK d (conj a) := fun a ha => (oR a a ha ha).2.2.2
  obtain ⟨v, hv, hvn, rfl⟩ := hy
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).one_lt.le
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hβ : InOK d (α - 1) := by
    have := (oR α (-1) hα (oR 1 1 o1 o1).2.2.1).1
    simpa [sub_eq_add_neg] using this
  have hl : InOK d ((α - 1) * v / (q : ℂ) ^ n) := by
    apply oD _ n (hmul _ _ hβ hv)
    · rw [map_mul, norm_mul, map_sub, map_one]
      calc _ ≤ (q : ℝ) ^ (-(n : ℤ)) * 1 :=
            mul_le_mul hα1 (hle v hv) (norm_nonneg _) (by positivity)
        _ = _ := mul_one _
    · rw [map_mul, map_mul, norm_mul]
      calc _ ≤ 1 * (q : ℝ) ^ (-(2 * n : ℤ)) :=
            mul_le_mul (hle _ (hconj _ hβ)) hvn (norm_nonneg _) (by positivity)
        _ ≤ _ := by
            rw [one_mul]; exact zpow_le_zpow_right₀ hq1 (by omega)
  have hc : InOK d (conj v * (v * conj (α - 1)) / (q : ℂ) ^ (2 * n)) := by
    apply oD _ (2 * n) (hmul _ _ (hconj _ hv) (hmul _ _ hv (hconj _ hβ)))
    · rw [map_mul, norm_mul]
      calc _ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) * 1 :=
            mul_le_mul hvn (hle _ (hmul _ _ hv (hconj _ hβ))) (norm_nonneg _) (by positivity)
        _ = _ := by push_cast; ring
    · have : conj (conj v * (v * conj (α - 1))) = conj v * (v * (α - 1)) := by
        simp only [map_mul, Complex.conj_conj]; ring
      rw [this, map_mul, norm_mul]
      calc _ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) * 1 :=
            mul_le_mul hvn (hle _ (hmul _ _ hv hβ)) (norm_nonneg _) (by positivity)
        _ = _ := by push_cast; ring
  have hW := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.2.2.2.1 (((1 : ℕ) : ℂ) * v / (q : ℂ) ^ n)
    ((α - 1) * v / (q : ℂ) ^ n) θ (by omega) (by
      convert hc using 1
      simp only [map_div₀, map_mul, map_pow, Complex.conj_natCast]
      field_simp
      push_cast
      ring)
  rw [hθ.2.2.2.1 _ hl] at hW
  rw [hW]
  congr 1
  push_cast
  ring

theorem theta_shift : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → hat M.ι (C ω * logS) (W1 d y θ) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) θ) := by
  intro d q _ M ω θ hd hd7 hs hL hM hθ hAt n y hy
  obtain ⟨hζq, hA⟩ := hAt n y hy
  set ζ := M.ι (kap1 d 1 y) with hζdef
  have hζ : ‖ζ - 1‖ < 1 := hA.2.1
  obtain ⟨⟨o1, -, oR⟩, oZ, oD, oE, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd hd7 hs
  obtain ⟨mu1, -, -, -, -, hn⟩ := GlobalTheory.MomOne.MulSeries.mulS_laws q
  obtain ⟨-, sh2, sh3, -⟩ := GlobalTheory.MomOne.Shift.shift_laws q ζ hζ
  obtain ⟨-, -, -, ht0, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ (const_ell ω)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hθy : θ y ≠ 0 := by
    intro h0
    have h1 := hθ.2.2.2.2 y h0
    have := (GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd7 hs hL hM).2.2.2 y 1 0 o1 one_ne_zero
      ⟨1, one_pos, Nat.coprime_one_left q, ⟨0, 0, by simp⟩⟩ (by simpa using h1) hA.1
    exact not_half d hd.pos this.2
  have hθan : AnalyticAt ℂ θ 0 := hθ.1.analyticAt 0
  have hWan : AnalyticAt ℂ (W1 d y θ) 0 :=
    ((GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.2.1 y θ hθ.1).2.analyticAt 0
  set f := hat M.ι (C ω * logS) θ with hf
  set g := hat M.ι (C ω * logS) (W1 d y θ) with hg
  have hfb : Bd 1 f := GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd hd7 hs hL hM hθ
  have hf0 : constantCoeff f = 1 := by rw [hf, ht0, hθ.2.1, map_one]
  have hff : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel f (by rw [hf0]; exact one_ne_zero)
  have hfi : Bd 1 f⁻¹ := (GlobalTheory.MomOne.sup_norm_laws q).2.2.1 f _ hfb (by rw [hf0, norm_one]) hff
  set h := shiftS ζ f with hh
  set h' := shiftS ζ f⁻¹ with hh'
  have hhh : h * h' = 1 := by
    rw [hh, hh', ← (sh2 _ _ ⟨1, hfb⟩ ⟨1, hfi⟩).2, hff]
    simpa using sh3 1
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 : constantCoeff g = 0 := by rw [h0, map_zero]
    rw [hg, ht0, _root_.map_eq_zero] at h1
    simp [W1, U1, hθy] at h1
  have hρ : g * h' ≠ 0 := mul_ne_zero hg0 (right_ne_zero_of_mul_eq_one hhh)
  have key : ∀ s : ℕ, Nat.Coprime s q → ∃ m : ℕ, 2 ≤ m ∧ ‖(m : ℂ_[q])‖ < 1 ∧ s ∣ m ∧
      ∃ c : ℂ_[q], g * h' = C c ∧ c ^ (m - 1) = 1 := by
    intro s hsq
    obtain ⟨e, he, he1, he2⟩ := oE (n + 1) s hsq
    have hsO : InOK d (s : ℂ) := ⟨s, 0, by simp⟩
    set α := (s : ℂ) * e with hαdef
    have hα : InOK d α := (oR _ _ hsO he).2.1
    obtain ⟨⟨a, ha⟩, -, -⟩ := oZ α hα
    obtain ⟨-, ⟨N, hN⟩, -⟩ := oZ e he
    obtain ⟨⟨b, hb⟩, -, -⟩ := oZ _ hsO
    have hlt : (q : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) < 1 := zpow_lt_one_of_neg₀ hq1 (by omega)
    have hlen : (q : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) ≤ (q : ℝ) ^ (-(n : ℤ)) :=
      zpow_le_zpow_right₀ hq1.le (by omega)
    have hα1 : ‖M.ι α‖ = 1 := by
      have h1 : ‖M.ι α - 1‖ < ‖(1 : ℂ_[q])‖ := by rw [norm_one]; exact lt_of_le_of_lt he1 hlt
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
      rw [sub_add_cancel, max_eq_right h1.le, norm_one] at this
      exact this
    have hα0 : α ≠ 0 := by
      intro h0; rw [h0] at hα1; simp at hα1
    have hm : ((s * s * N : ℕ) : ℂ) = α * conj α := by
      push_cast
      rw [hN, hαdef, map_mul, Complex.conj_natCast]; ring
    set m := s * s * N with hmdef
    have hmn : ‖(m : ℂ_[q])‖ < 1 := by
      have h1 : (m : ℂ_[q]) = M.ι α * (M.ι s * M.ι (conj e)) := by
        rw [← map_natCast M.ι m, hm, ← map_mul, ← map_mul, hαdef, map_mul (starRingEnd ℂ),
          Complex.conj_natCast]
      rw [h1, norm_mul, hα1, one_mul, norm_mul, hb, hn]
      calc _ ≤ 1 * (q : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) :=
            mul_le_mul b.norm_le_one he2 (norm_nonneg _) (by positivity)
        _ < 1 := by rw [one_mul]; exact hlt
    have hm2 : 2 ≤ m := by
      have h0 : m ≠ 0 := by
        intro h0
        rw [h0] at hm
        simp [hα0] at hm
      have h1 : m ≠ 1 := by
        intro h1
        rw [h1] at hmn
        simp at hmn
      omega
    refine ⟨m, hm2, hmn, ⟨s * N, by rw [hmdef]; ring⟩, ?_⟩
    obtain ⟨ε, hε1, hε2, -, hε4, hε5, hε6⟩ :=
      GlobalTheory.T.thetaNormQuotient_elliptic_unitSeries d q M ω θ hd hd7 hs hL hM hθ α m hα hα0 hm
    obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω ζ y ε hM hA hε1 hε2 ⟨1, hε4⟩
    have hWW := W_mul_eq d M.ι θ hd hd7 hs hθ n y hy α hα (he1.trans hlen)
    have e1 : f.subst (mulS a : ℂ_[q]⟦X⟧) = f ^ m * hat M.ι (C ω * logS) ε := by
      apply hat_funEq M.ι ω θ ε hθan hε2 α a ha m
      have : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0 :=
        hθan.continuousAt.eventually_ne (by rw [hθ.2.1]; exact one_ne_zero)
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun z hz => hε5 z hz
    have e2 : g.subst (mulS a : ℂ_[q]⟦X⟧) = g ^ m * hat M.ι (C ω * logS) ψ := by
      apply hat_funEq M.ι ω _ ψ hWan hψ1 α a ha m
      have hc : ContinuousAt (fun z => θ (z + y)) 0 :=
        (hθ.1.continuous.comp (continuous_id.add continuous_const)).continuousAt
      have : ∀ᶠ z in 𝓝 (0 : ℂ), θ (z + y) ≠ 0 := hc.eventually_ne (by simpa using hθy)
      filter_upwards [this.filter_mono nhdsWithin_le_nhds, hψ2] with z hz hz2
      rw [hz2, ← hε6 y z hz, hWW]
    have ha1 : ‖a - ((1 : ℕ) : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
      rw [Nat.cast_one, ← hn, zc_sub_one, ← ha]; exact he1.trans hlen
    have e3 : h.subst (mulS a : ℂ_[q]⟦X⟧) = h ^ m * hat M.ι (C ω * logS) ψ := by
      have := ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 ζ n 1 a f hζq ha1 ⟨1, hfb⟩).2
      rw [pow_one, e1, (sh2 _ _ ⟨1, bd_pow f hfb m⟩ ⟨1, hε4⟩).2, shift_pow ζ hζ f hfb m] at this
      rw [hψ3, this]
    have hsub : HasSubst (mulS a : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' (mu1 a).2.1
    have e4 : h.subst (mulS a : ℂ_[q]⟦X⟧) * h'.subst (mulS a : ℂ_[q]⟦X⟧) = 1 := by
      rw [← subst_mul hsub, hhh, ← coe_substAlgHom hsub, map_one]
    have e5 : (g * h').subst (mulS a : ℂ_[q]⟦X⟧) = (g * h') ^ m := by
      rw [subst_mul hsub, e2]
      rw [e3] at e4
      have e6 : h ^ m * h' ^ m = 1 := by rw [← mul_pow, hhh, one_pow]
      rw [mul_pow]
      linear_combination (g ^ m * h' ^ m) * e4
        - (g ^ m * hat M.ι (C ω * logS) ψ * h'.subst (mulS a : ℂ_[q]⟦X⟧)) * e6
    exact (GlobalTheory.MomOne.FeUniq.funEq_unique q (mulS a) m (mu1 a).2.1
      (by rw [(mu1 a).2.2.1, ← ha, hα1]) hmn hm2).1 _ hρ e5
  obtain ⟨m₁, h12, h1n, -, c, hc, hc1⟩ := key 1 (Nat.coprime_one_left q)
  obtain ⟨m₂, h22, -, ⟨k, hk⟩, c', hc', hc2⟩ := key (m₁ - 1) (coprime_pred m₁ (by omega) h1n)
  have hcc : c' = c := C_injective (hc'.symm.trans hc)
  rw [hcc] at hc2
  have hone : c = 1 := by
    have h1 : c ^ m₂ = 1 := by rw [hk, pow_mul, hc1, one_pow]
    have h2 : m₂ = (m₂ - 1) + 1 := by omega
    rw [h2, pow_succ, hc2, one_mul] at h1
    exact h1
  rw [hone, map_one] at hc
  linear_combination h * hc - g * hhh

end GlobalTheory.MomOne.ThShift
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLatticeWeylOperator_eq_theta_rootOfUnity_shift : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → hat M.ι (C ω * logS) (W1 d y θ) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) θ) := by
  atlas_forward_decl GlobalTheory.MomOne.ThShift.theta_shift
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslateLaw

variable {q : ℕ} [Fact q.Prime]

theorem inOK_natMul {d : ℕ} (s : ℕ) {v : ℂ} (h : InOK d v) : InOK d ((s : ℂ) * v) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨s * a, s * b, by push_cast; ring⟩

theorem cmLatticeCommutatorPairing_natMul_right (d s : ℕ) (x y : ℂ) : kap1 d x ((s : ℂ) * y) = kap1 d x y ^ s := by
  unfold kap1
  rw [← Complex.exp_nat_mul]
  congr 1
  have : h1 d x ((s : ℂ) * y) = ((s : ℝ) : ℂ) * h1 d x y := by
    simp only [h1, map_mul, map_natCast, Complex.ofReal_natCast]; ring
  rw [this, Complex.im_ofReal_mul]
  push_cast
  ring

theorem norm_natCast_eq_one {s : ℕ} (h : Nat.Coprime s q) : ‖(s : ℤ_[q])‖ = 1 := by
  rw [PadicInt.norm_natCast_eq_one_iff]
  exact h.symm

theorem zc_natCast (s : ℕ) : zc (s : ℤ_[q]) = (s : ℂ_[q]) := by
  simp [zc]

theorem hasSubst_mulS (a : ℤ_[q]) : HasSubst (mulS a : ℂ_[q]⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' ((MulSeries.mulS_laws q).1 a).2.1

theorem subst_mulS_cancel {a : ℤ_[q]} (ha : ‖a‖ = 1) {f g : ℂ_[q]⟦X⟧}
    (h : f.subst (mulS a : ℂ_[q]⟦X⟧) = g.subst (mulS a : ℂ_[q]⟦X⟧)) : f = g := by
  obtain ⟨u, rfl⟩ := PadicInt.isUnit_iff.mpr ha
  have key : ∀ f : ℂ_[q]⟦X⟧, PowerSeries.subst (mulS ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℂ_[q]⟦X⟧)
      (show ℂ_[q]⟦X⟧ from f.subst (mulS (u : ℤ_[q]) : ℂ_[q]⟦X⟧)) = f := by
    intro f
    dsimp only
    rw [subst_comp_subst_apply (hasSubst_mulS _) (hasSubst_mulS _), (MulSeries.mulS_laws q).2.1,
      Units.mul_inv, (MulSeries.mulS_laws q).2.2.1]
    rw [← map_algebraMap_eq_subst_X]
    simp
  have h1 := key f
  have h2 := key g
  dsimp only at h1 h2
  rw [← h1, h, h2]

theorem main : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (t y : ℂ) (n s : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good M.ι d n s y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ hat M.ι (C ω * logS) (W1 d y (U1 d t θ)) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) (U1 d t θ)) := by
  intro d q hq M ω θ hd hd16 hsp hOK hM hθ hgood t y n s hs ht hy
  obtain ⟨v, hv, hvn, hyv⟩ := hy
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h
      exact absurd ((Nat.coprime_zero_left q).mp hs) hq.out.one_lt.ne'
    · exact h
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsn : ‖(s : ℤ_[q])‖ = 1 := norm_natCast_eq_one hs
  have hιs : M.ι (s : ℂ) = zc (s : ℤ_[q]) := by rw [zc_natCast, map_natCast]
  set y' : ℂ := v / (q : ℂ) ^ n with hy'
  have hyy : y = (s : ℂ) * y' := by rw [hyv, hy']; ring
  have hg' : Good M.ι d n 1 y' := ⟨v, hv, hvn, by rw [hy']; simp⟩
  have hg : Good M.ι d n 1 y := by
    refine ⟨(s : ℂ) * v, inOK_natMul s hv, ?_, by rw [hyv]; simp⟩
    rw [map_mul, map_mul, map_natCast, hιs, norm_mul, (MulSeries.mulS_laws q).2.2.2.2.2, hsn, one_mul]
    exact hvn
  obtain ⟨hζ, hAt⟩ := hgood n y hg
  obtain ⟨hζ', hAt'⟩ := hgood n y' hg'
  refine ⟨hζ, ?_⟩
  have hζζ : M.ι (kap1 d 1 y) = M.ι (kap1 d 1 y') ^ s := by rw [hyy, cmLatticeCommutatorPairing_natMul_right, map_pow]
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hM.2.1
  obtain ⟨hring, -⟩ := TaylorRead.hat_laws q M.ι (C ω * logS) hℓ
  obtain ⟨-, -, hdiff, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos
  have hθd : Differentiable ℂ θ := hθ.1
  have hθ0 : θ 0 ≠ 0 := by rw [hθ.2.1]; exact one_ne_zero
  have hUd : Differentiable ℂ (U1 d t θ) := (hdiff t θ hθd).1
  have hWUd : Differentiable ℂ (W1 d y (U1 d t θ)) := (hdiff y _ hUd).2
  have hWd : Differentiable ℂ (W1 d y θ) := (hdiff y _ hθd).2
  set f : ℂ → ℂ := fun z => U1 d t θ z / θ z with hf
  have hfa : AnalyticAt ℂ f 0 := (hUd.analyticAt 0).div (hθd.analyticAt 0) hθ0
  obtain ⟨hEll, hφa, -, -, hφb⟩ := GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hOK hM hθ t s hs0 hs ht
  have hscale : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → hat M.ι (C ω * logS) (fun z => G ((s : ℂ) * z)) =
      (hat M.ι (C ω * logS) G).subst (mulS (s : ℤ_[q]) : ℂ_[q]⟦X⟧) :=
    fun G hG => (hat_multiplicative_chart q M.ι ω G hG).2.2.1 _ _ hιs
  have hφf : hat M.ι (C ω * logS) (fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)) =
      (hat M.ι (C ω * logS) f).subst (mulS (s : ℤ_[q]) : ℂ_[q]⟦X⟧) := hscale f hfa
  have hfb : Bdd (hat M.ι (C ω * logS) f) := by
    obtain ⟨B, hB⟩ := hφb
    rw [hφf] at hB
    exact ⟨B, ((MulSeries.mulS_laws q).2.2.2.1 _ _ B hsn).mp hB⟩
  have hθb : Bdd (hat M.ι (C ω * logS) θ) := ⟨1, GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd hd16 hsp hOK hM hθ⟩
  obtain ⟨ψ, hψa, hψ, hψh⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω _ y' _ hM hAt' hEll hφa hφb
  rw [hφf] at hψh
  have hsc := ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 _ n s (s : ℤ_[q]) _ hζ' (by
    rw [sub_self, norm_zero]; positivity) hfb).2
  rw [hsc, ← hζζ] at hψh

  have hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), θ ((s : ℂ) * z + y) ≠ 0 := by
    have hA : AnalyticOnNhd ℂ (fun z : ℂ => θ ((s : ℂ) * z + y)) Set.univ :=
      fun z _ => (hθd.comp (hlin.add_const y)).analyticAt z
    rcases (hA 0 trivial).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) h
        (Set.mem_univ (-y / (s : ℂ)))
      apply hθ0
      have e : (s : ℂ) * (-y / (s : ℂ)) + y = 0 := by field_simp; ring
      simpa [e] using this
    · exact h
  have hWs : AnalyticAt ℂ (fun z => W1 d y θ ((s : ℂ) * z)) 0 := (hWd.comp hlin).analyticAt 0
  have hWUs : AnalyticAt ℂ (fun z => W1 d y (U1 d t θ) ((s : ℂ) * z)) 0 := (hWUd.comp hlin).analyticAt 0
  have hprod : hat M.ι (C ω * logS) (fun z => ψ z * W1 d y θ ((s : ℂ) * z)) =
      hat M.ι (C ω * logS) (fun z => W1 d y (U1 d t θ) ((s : ℂ) * z)) := by
    refine (hring _ _ (hψa.mul hWs) hWUs).2.2.1 ?_
    filter_upwards [hψ, hne] with z h1z h2z
    have e : (s : ℂ) * (z + y') = (s : ℂ) * z + y := by rw [hyy]; ring
    change ψ z * W1 d y θ ((s : ℂ) * z) = _
    rw [h1z, e]
    simp only [W1]
    generalize U1 d t θ = G
    simp only [U1]
    field_simp
  rw [(hring _ _ hψa hWs).2.1, hψh, hscale _ (hWd.analyticAt 0), hscale _ (hWUd.analyticAt 0),
    ← subst_mul (hasSubst_mulS _)] at hprod
  rw [← subst_mulS_cancel hsn hprod, GlobalTheory.T.cmLatticeWeylOperator_eq_theta_rootOfUnity_shift d q M ω θ hd hd16 hsp hOK hM hθ hgood n y hg,
    ← ((Shift.shift_laws q _ hAt.2.1).2.1 _ _ hfb hθb).2, ← (hring _ _ hfa (hθd.analyticAt 0)).2.1]
  congr 1
  refine (hring _ _ (hfa.mul (hθd.analyticAt 0)) (hUd.analyticAt 0)).2.2.1 ?_
  have : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0 := hθd.continuous.continuousAt.eventually_ne hθ0
  filter_upwards [nhdsWithin_le_nhds this] with z hz
  change U1 d t θ z / θ z * θ z = _
  field_simp

end GlobalTheory.MomOne.TranslateLaw
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_theta_translate_shift_prime_to_q : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (t y : ℂ) (n s : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good M.ι d n s y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ hat M.ι (C ω * logS) (W1 d y (U1 d t θ)) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) (U1 d t θ)) := by
  atlas_forward_decl GlobalTheory.MomOne.TranslateLaw.main
end

section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.GenusOne

variable {q : ℕ} [Fact q.Prime]

theorem norm_root_eq (M : Mdl q) (h : M.Ok) (δ : ℂ) (hδ : δ ^ 12 = M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2) :
    ‖M.ι δ‖ = ‖M.ι M.c‖ ∧ ‖M.ι M.c‖ ≠ 0 := by
  obtain ⟨hc, -, -, -, -, -, hΔ, h4, h6⟩ := h
  have hιc : M.ι M.c ≠ 0 := (map_ne_zero M.ι).mpr hc
  refine ⟨?_, norm_ne_zero_iff.mpr hιc⟩

  rw [map_div₀, map_pow, eq_div_iff (pow_ne_zero 4 hιc)] at h4
  rw [map_div₀, map_pow, eq_div_iff (pow_ne_zero 6 hιc)] at h6
  have key : M.ι δ ^ 12 = M.ι M.c ^ 12 * M.W.Δ := by
    have e : M.ι δ ^ 12 = M.ι M.L.g₂ ^ 3 - 27 * M.ι M.L.g₃ ^ 2 := by
      rw [← map_pow, hδ]; simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [e, ← h4, ← h6]
    linear_combination (-(M.ι M.c ^ 12) / 1728) * M.W.c_relation
  have hn := congrArg norm key
  rw [norm_mul, norm_pow, norm_pow, hΔ, mul_one] at hn
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hn

theorem norm_period (M : Mdl q) (ω : ℂ_[q]) (h : M.MChart ω) : ‖ω‖ * ‖M.ι M.c‖ = 1 := by
  obtain ⟨hok, h0, -, h1⟩ := h
  obtain ⟨-, -, -, -, -, -, hdu, -, hsmall⟩ := uw_elliptic_flow q M hok
  obtain ⟨han, -⟩ := hsmall 0 (Or.inl (zero_mem _))
  obtain ⟨-, -, -, hcc, hder, -, -⟩ := TaylorRead.hat_laws q M.ι (C ω * logS) h0

  have hd0 : ∀ f : ℂ_[q]⟦X⟧, constantCoeff (derivative ℂ_[q] f) = coeff 1 f := by
    intro f
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simp
  have hℓ : coeff 1 (C ω * logS : ℂ_[q]⟦X⟧) = ω := by
    simp [logS, coeff_C_mul, coeff_mk]
  have e : coeff 1 (hat M.ι (C ω * logS) M.u) = ω * M.ι M.c := by
    rw [← hd0, hder M.u han, map_mul, hd0, hℓ, hcc, hdu]
  rw [e, norm_mul] at h1
  exact h1

theorem thetaLaws_unit_period : ∀ (d q : ℕ) [Fact q.Prime] (δ : ℂ), d.Prime → d % 16 = 7 → Split d q →
    δ ^ 12 = discr d → ∃ θ : ℂ → ℂ, IsTh d θ ∧ δ ≠ 0 ∧
      ∀ ι : ℂ ≃+* ℂ_[q], ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ := by
  intro d q _ δ hd h16 hsp hδ
  obtain ⟨⟨L, hL, hLd⟩, θ, hθ⟩ := GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta d hd h16
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact (Basic.discr_eq hL).2 (by rw [← hδ]; norm_num)
  refine ⟨θ, hθ, hδ0, fun ι => ?_⟩
  obtain ⟨M, hMι, hML, hok, a1, a2, a3, a4, a6⟩ := GlobalTheory.T.exists_goodReduction_algebraic_weierstrass_model d q ι L hd h16 hL
  subst hMι
  have hL' : IsOK d M.L := by rw [hML]; exact hL
  obtain ⟨ω₀, hω₀⟩ := GlobalTheory.T.exists_multiplicativeChart_at_splitPrime d q M hd h16 hsp hL' hok a1 a2 a3 a4 a6
  obtain ⟨a, -, hω, hgood⟩ := GlobalTheory.T.exists_normalised_multiplicativeChart d q M ω₀ hd h16 hsp hL' hω₀
  have hδM : δ ^ 12 = M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2 := by rw [hML, hLd]; exact hδ
  obtain ⟨hn, -⟩ := norm_root_eq M hok δ hδM
  have hp := norm_period M (ω₀ * zc a) hω
  have hιδ : M.ι δ ≠ 0 := (map_ne_zero M.ι).mpr hδ0
  refine ⟨ω₀ * zc a * M.ι δ, by rw [norm_mul, hn]; exact hp, ?_⟩
  rw [mul_div_cancel_right₀ _ hιδ]
  have hU0 : U1 d 0 θ = θ := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.1 θ
  have h0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left q, 0, 0, by simp⟩
  have hB := GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ
  refine ⟨fun t ht => ?_, GlobalTheory.T.weilOperator_theta_translate_shift_prime_to_q d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ hgood,
    GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ⟩

  have := GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ 1 1 (fun _ => 1) (fun _ => 0) t 1
    (fun _ => h0) ht (by simpa [hU0] using hB)
  simpa [hU0] using this

end GlobalTheory.MomOne.GenusOne
end
