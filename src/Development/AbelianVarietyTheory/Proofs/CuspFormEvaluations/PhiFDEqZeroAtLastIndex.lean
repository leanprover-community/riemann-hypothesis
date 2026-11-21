import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExists

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate nonZeroDivisors

namespace GlobalTheory.DefiniteMin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_mulVec_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    FD.hermC τ G (P.mulVec w) (P.mulVec w) = ∑ a, ∑ b, w a * FD.gram τ G P a b * conj (w b) := by
  have h1 : FD.hermC τ G (P.mulVec w) (P.mulVec w) =
      ∑ a, ∑ b, ∑ c, ∑ d, w c * (P a c * τ (G a b) * conj (P b d)) * conj (w d) := by
    simp only [FD.hermC, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have h2 : ∑ a, ∑ b, w a * FD.gram τ G P a b * conj (w b) =
      ∑ c, ∑ d, ∑ a, ∑ b, w c * (P a c * τ (G a b) * conj (P b d)) * conj (w d) := by
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [h1, h2]
  calc _ = ∑ a, ∑ c, ∑ b, ∑ d, w c * (P a c * τ (G a b) * conj (P b d)) * conj (w d) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, w c * (P a c * τ (G a b) * conj (P b d)) * conj (w d) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, w c * (P a c * τ (G a b) * conj (P b d)) * conj (w d) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem hermC_neg (X : FD.Data E r) (h0 : X.p0 = 0) (τ : X.Ψ) {v : Fin r → ℂ} (hv : v ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ FD.hermC τ.1 X.Gm v v = -(s : ℂ) := by
  obtain ⟨P, hP, hG⟩ := X.signature τ
  set w := P⁻¹.mulVec v with hw
  have hPw : P.mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hP), Matrix.one_mulVec]
  have hw0 : w ≠ 0 := by
    intro h
    apply hv
    rw [← hPw, h, Matrix.mulVec_zero]
  refine ⟨∑ a, Complex.normSq (w a), ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Function.ne_iff.mp hw0
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr ha)
      (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (w i)) (Finset.mem_univ a))
  · rw [← hPw, hermC_mulVec_mulVec, hG]
    simp only [Matrix.diagonal_apply, FD.sgn, h0, Nat.not_lt_zero, if_false]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Complex.mul_conj]
    ring

theorem map_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    τ (FD.herm G u v) = FD.hermC τ G (FD.Data.emb τ u) (FD.Data.emb τ v) := by
  simp only [FD.herm, FD.hermC, FD.Data.emb, FD.cc, map_sum, map_mul,
    NumberField.IsCMField.complexEmbedding_complexConj]

theorem posPart_eq_zero (X : FD.Data E r) (h0 : X.p0 = 0) (x : FD.Frame X.Ψ r) (τ : X.Ψ)
    (v : Fin r → ℂ) : X.posPart x τ v = 0 := by
  have : IsEmpty (Fin X.p0) := by rw [h0]; infer_instance
  simp [FD.Data.posPart]

theorem sum_norm_eq_two_mul (X : FD.Data E r) (y : E) :
    ∑ σ : E →+* ℂ, ‖σ y‖ = ∑ τ : X.Ψ, 2 * ‖τ.1 y‖ := by
  classical
  rw [← Finset.sum_add_sum_compl X.Ψ (fun σ => ‖σ y‖)]
  have hc : ∑ σ ∈ X.Ψᶜ, ‖σ y‖ = ∑ σ ∈ X.Ψ, ‖σ y‖ := by
    refine Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_compl] at hσ ⊢
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E σ]
      exact hσ
    · intro σ hσ
      simp only [Finset.mem_compl] at hσ ⊢
      exact (X.cmType σ).mp hσ
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  rw [hc, ← two_mul, Finset.mul_sum, ← Finset.sum_coe_sort X.Ψ]

private theorem one_le_abs_norm_mul_abs_discr_of_trace_int {β : E}
    (hβ : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (β * a) = k) (h0 : β ≠ 0) :
    (1 : ℚ) ≤ |Algebra.norm ℚ β| * |(NumberField.discr E : ℚ)| := by
  classical
  set D : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ 1 with hDdef
  have h1ne : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hD : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ h1ne
  have hmem : β ∈ D := by
    rw [hDdef, FractionalIdeal.mem_dual h1ne]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).mp ha
    obtain ⟨k, hk⟩ := hβ a'
    exact ⟨k, by rw [Algebra.traceForm_apply]; exact hk.symm⟩
  have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * D⁻¹ ≤ 1 := by
    calc _ ≤ D * D⁻¹ := mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem) _
      _ = 1 := mul_inv_cancel₀ hD
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    rw [FractionalIdeal.coeIdeal_bot, eq_comm, mul_eq_zero,
      FractionalIdeal.spanSingleton_eq_zero_iff, inv_eq_zero] at hI
    rcases hI with h | h
    · exact h0 h
    · exact hD h
  have hdiff : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = D⁻¹ :=
    coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E)
  have key := congrArg FractionalIdeal.absNorm hI
  rw [FractionalIdeal.coeIdeal_absNorm, map_mul, FractionalIdeal.absNorm_span_singleton, ← hdiff,
    FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal E (𝓞 E)] at key
  have h1 : (1 : ℚ) ≤ Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  rw [key] at h1
  simpa [Nat.cast_natAbs] using h1

theorem finrank_div_rd_le {β : E} (hβ : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (β * a) = k)
    (h0 : β ≠ 0) : (Module.finrank ℚ E : ℝ) / I2.PT.rd E ≤ ∑ σ : E →+* ℂ, ‖σ β‖ := by
  classical
  have hNq := one_le_abs_norm_mul_abs_discr_of_trace_int hβ h0
  have hN : (1 : ℝ) ≤ |(Algebra.norm ℚ β : ℝ)| * |(NumberField.discr E : ℝ)| := by
    have := (Rat.cast_le (K := ℝ)).mpr hNq
    simpa using this
  set n := Module.finrank ℚ E with hn_def
  have hn : 0 < n := Module.finrank_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : Fintype.card (E →+* ℂ) = n := NumberField.Embeddings.card E ℂ
  have hprod : ∏ σ : E →+* ℂ, ‖σ β‖ = |(Algebra.norm ℚ β : ℝ)| := by
    have h := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ β)
    rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => ‖f β‖)
      (fun φ => ‖φ β‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
    rw [← h, eq_ratCast, Complex.norm_ratCast]
  have hgm : (∏ σ : E →+* ℂ, ‖σ β‖) ^ ((n : ℝ)⁻¹) ≤ (∑ σ : E →+* ℂ, ‖σ β‖) / n := by
    have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : E →+* ℂ => (1 : ℝ))
      (fun σ => ‖σ β‖) (fun _ _ => zero_le_one) (by simp [hcard, hn]) (fun _ _ => norm_nonneg _)
    simpa [hcard] using h
  rw [hprod] at hgm
  have hd : 0 < |(NumberField.discr E : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast NumberField.discr_ne_zero E
  have hdN : |(NumberField.discr E : ℝ)|⁻¹ ≤ |(Algebra.norm ℚ β : ℝ)| := by
    rw [inv_eq_one_div, div_le_iff₀ hd]
    exact hN
  have hlow : (I2.PT.rd E)⁻¹ ≤ |(Algebra.norm ℚ β : ℝ)| ^ ((n : ℝ)⁻¹) := by
    have hrd : I2.PT.rd E = |(NumberField.discr E : ℝ)| ^ (1 / (n : ℝ)) := rfl
    rw [hrd, ← Real.inv_rpow (abs_nonneg _), one_div]
    exact Real.rpow_le_rpow (inv_nonneg.mpr (abs_nonneg _)) hdN (inv_nonneg.mpr hnR.le)
  calc (n : ℝ) / I2.PT.rd E = n * (I2.PT.rd E)⁻¹ := div_eq_mul_inv _ _
    _ ≤ n * ((∑ σ : E →+* ℂ, ‖σ β‖) / n) :=
        mul_le_mul_of_nonneg_left (hlow.trans hgm) hnR.le
    _ = ∑ σ : E →+* ℂ, ‖σ β‖ := by field_simp

theorem two_f_div_rd_le_la1sq (X : FD.Data E r) (hr : 0 < r) (h0 : X.p0 = 0)
    (hint : ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm u v) = k)
    (x : FD.Frame X.Ψ r) : 2 * (I2.PT.f E : ℝ) / I2.PT.rd E ≤ X.firstMinimumSq x := by
  classical
  have hne : ∃ v ∈ X.Λ, v ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥ :=
      Submodule.span_le.mpr fun v hv => by simp [h v hv]
    rw [X.Λ_span] at hle
    have h1 : (fun _ : Fin r => (1 : E)) ∈ (⊥ : Submodule E (Fin r → E)) := hle Submodule.mem_top
    rw [Submodule.mem_bot] at h1
    have := congrFun h1 ⟨0, hr⟩
    simp at this
  have hΨ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨σ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : σ0 ∈ X.Ψ
    · exact ⟨σ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate σ0, ?_⟩
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E σ0]
      exact h
  have hbound : ∀ v ∈ X.Λ, v ≠ 0 →
      2 * (I2.PT.f E : ℝ) / I2.PT.rd E ≤ ∑ τ, X.c τ * X.maj x τ (FD.Data.emb τ.1 v) := by
    intro v hv hv0
    have hemb : ∀ τ : X.Ψ, FD.Data.emb τ.1 v ≠ 0 := by
      intro τ h
      apply hv0
      funext a
      have := congrFun h a
      simpa [FD.Data.emb] using this
    set y := X.ξ0 * FD.herm X.Gm v v with hy
    have hterm : ∀ τ : X.Ψ, X.c τ * X.maj x τ (FD.Data.emb τ.1 v) = 2 * ‖τ.1 y‖ := by
      intro τ
      obtain ⟨s, hs, hseq⟩ := hermC_neg X h0 τ (hemb τ)
      rw [FD.Data.maj, posPart_eq_zero X h0 x τ, hseq, FD.Data.c, hy, map_mul, norm_mul,
        map_herm, hseq]
      simp [abs_of_pos hs]
      ring
    have hh0 : FD.herm X.Gm v v ≠ 0 := by
      intro h
      obtain ⟨τ0, hτ0⟩ := hΨ
      obtain ⟨s, hs, hseq⟩ := hermC_neg X h0 ⟨τ0, hτ0⟩ (hemb ⟨τ0, hτ0⟩)
      rw [← map_herm, h, map_zero] at hseq
      have := congrArg Complex.re hseq
      simp at this
      linarith
    have hy0 : y ≠ 0 := mul_ne_zero X.ξ0_ne hh0
    have htr : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (y * a) = k := by
      intro a
      obtain ⟨k, hk⟩ := hint (a • v) (X.Λ.smul_mem a hv) v hv
      refine ⟨k, ?_⟩
      rw [← hk]
      congr 1
      simp only [hy, FD.herm, Pi.smul_apply, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hc : (algebraMap (𝓞 E) E) a = (a : E) := rfl
      rw [Algebra.smul_def, hc]
      ring
    have hsum : ∑ τ, X.c τ * X.maj x τ (FD.Data.emb τ.1 v) = ∑ σ : E →+* ℂ, ‖σ y‖ := by
      rw [Finset.sum_congr rfl fun τ _ => hterm τ, sum_norm_eq_two_mul X y]
    rw [hsum]
    refine le_trans ?_ (finrank_div_rd_le htr hy0)
    have hrd0 : 0 ≤ I2.PT.rd E := Real.rpow_nonneg (abs_nonneg _) _
    have h2f : 2 * I2.PT.f E ≤ Module.finrank ℚ E := Nat.mul_div_le (Module.finrank ℚ E) 2
    have h2fR : 2 * (I2.PT.f E : ℝ) ≤ Module.finrank ℚ E := by exact_mod_cast h2f
    exact div_le_div_of_nonneg_right h2fR hrd0
  obtain ⟨v0, hv0, hv00⟩ := hne
  refine le_csInf ⟨_, v0, hv0, hv00, rfl⟩ ?_
  rintro t ⟨v, hv, hv0, rfl⟩
  exact hbound v hv hv0

theorem th_sq_le {q : ℕ} {R0 : ℝ} (hrd : 1 ≤ I2.PT.rd E) (hq : 0 < q)
    (hb : 1 ≤ I2.b0 (E := E) q R0) :
    I2.PT.f E * R0 ^ 2 * I2.RR (E := E) ^ 3 / q ≤ 2 * (I2.PT.f E : ℝ) / I2.PT.rd E := by
  have hRR : 1 ≤ I2.RR (E := E) := one_le_pow₀ hrd
  have hRRpos : 0 < I2.RR (E := E) := lt_of_lt_of_le zero_lt_one hRR
  have hrdpos : 0 < I2.PT.rd E := lt_of_lt_of_le zero_lt_one hrd
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hf : (0 : ℝ) ≤ I2.PT.f E := Nat.cast_nonneg _
  have hb' : (1 : ℝ) ≤ q / (R0 ^ 2 * I2.RR (E := E) ^ 4) := hb
  have hden : 0 < R0 ^ 2 * I2.RR (E := E) ^ 4 := by
    by_contra hle
    push Not at hle
    have : (q : ℝ) / (R0 ^ 2 * I2.RR (E := E) ^ 4) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hqpos.le hle
    linarith
  have hq' : R0 ^ 2 * I2.RR (E := E) ^ 4 ≤ q := by rwa [one_le_div hden] at hb'
  have hR0 : R0 ≠ 0 := by
    rintro rfl
    simp at hden
  have hRRne : I2.RR (E := E) ≠ 0 := hRRpos.ne'
  have hrdle : I2.PT.rd E ≤ I2.RR (E := E) := le_self_pow₀ hrd (by norm_num)
  have hnum : 0 ≤ (I2.PT.f E : ℝ) * R0 ^ 2 * I2.RR (E := E) ^ 3 :=
    mul_nonneg (mul_nonneg hf (sq_nonneg _)) (pow_nonneg hRRpos.le 3)
  calc (I2.PT.f E : ℝ) * R0 ^ 2 * I2.RR (E := E) ^ 3 / q
        ≤ I2.PT.f E * R0 ^ 2 * I2.RR (E := E) ^ 3 / (R0 ^ 2 * I2.RR (E := E) ^ 4) :=
        div_le_div_of_nonneg_left hnum hden hq'
    _ = I2.PT.f E / I2.RR (E := E) := by field_simp
    _ ≤ I2.PT.f E / I2.PT.rd E := div_le_div_of_nonneg_left hf hrdpos hrdle
    _ ≤ 2 * I2.PT.f E / I2.PT.rd E := by
        apply div_le_div_of_nonneg_right _ hrdpos.le
        linarith

theorem firstMinimumSq_ge_and_phi_eq_zero_definite :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r), 0 < r → X.p0 = 0 → (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm u v) = k) → ∀ x ∈ X.dom, 2 * (I2.PT.f E : ℝ) / I2.PT.rd E ≤ X.firstMinimumSq x ∧ ∀ (q : ℕ) (R0 : ℝ), 1 ≤ I2.PT.rd E → 0 < q → 1 ≤ I2.b0 (E := E) q R0 → I2.phiFD X (I2.th (E := E) q R0) x = 0 := by
  intro E _ _ _ r X hr h0 hint x _hx
  have hla := two_f_div_rd_le_la1sq X hr h0 hint x
  refine ⟨hla, fun q R0 hrd hq hb => ?_⟩
  have hth := th_sq_le (E := E) hrd hq hb
  unfold I2.phiFD
  rw [if_neg]
  rw [not_lt]
  unfold FD.Data.la1 I2.th
  exact Real.sqrt_le_sqrt (hth.trans hla)

end GlobalTheory.DefiniteMin
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.la1sq_ge_two_f_div_rd_of_p0_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r), 0 < r → X.p0 = 0 → (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm u v) = k) → ∀ x ∈ X.dom, 2 * (I2.PT.f E : ℝ) / I2.PT.rd E ≤ X.firstMinimumSq x ∧ ∀ (q : ℕ) (R0 : ℝ), 1 ≤ I2.PT.rd E → 0 < q → 1 ≤ I2.b0 (E := E) q R0 → I2.phiFD X (I2.th (E := E) q R0) x = 0 := by
  atlas_forward_decl GlobalTheory.DefiniteMin.firstMinimumSq_ge_and_phi_eq_zero_definite
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusSign

theorem cmHostUnit_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, h]
    have h2 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h1] at h2
    have h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa using this
    have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
    have h4 := congrArg Complex.re h3
    simp [sq, him] at h4
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  have hb : H.bar H.rt = -H.rt := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, hb, map_ofNat] at this
    rw [this]; ring
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero this

theorem exists_torusAt_of_isom {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {r : ℕ} (X : FD.Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ E (-X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)))
    (x : FD.Frame X.Ψ r) (hx : x ∈ X.dom) : ∃ A : I2.TorusAt X x, A.w0 = H.w0 := by
  have key : ∀ a b, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)) = -((D.EF a b : ℤ) : ℚ) := by
    intro a b
    rw [isom, neg_mul, map_neg, neg_neg]
  refine GlobalTheory.torusAtExists E r X ?_ H.w0 ?_ x hx
  · intro f
    obtain ⟨a, ha⟩ := D.unimod.2 (-(f.comp φ.toLinearMap.toAddMonoidHom).toIntLinearMap)
    refine ⟨φ a, (φ a).2, fun v => ?_⟩
    obtain ⟨b, rfl⟩ := φ.surjective v
    rw [key, ha]
    simp
  · intro u hu v hv
    obtain ⟨a, ha⟩ := φ.surjective ⟨u, hu⟩
    obtain ⟨b, hb⟩ := φ.surjective ⟨v, hv⟩
    have hu' : u = (φ a : Fin r → E) := by rw [ha]
    have hv' : v = (φ b : Fin r → E) := by rw [hb]
    have hw : H.w0 - H.bar H.w0 = 1 - (H.bar H.w0 + H.bar H.w0) := by
      have := cmHostUnit_add_conj_eq_one H
      linear_combination this
    have hs : ((H.w0 : E) - FD.cc (H.w0 : E)) • v = (φ ((H.w0 - H.bar H.w0) • b) : Fin r → E) := by
      rw [map_smul, hb, FD.cc, ← H.bar_eq]
      funext i
      simp [Algebra.smul_def]
    refine ⟨D.EF a (H.bar H.w0 • b), ?_⟩
    rw [hs, hu', hv', key, key, hw, sub_smul, add_smul, one_smul, map_sub, map_add]
    push_cast
    ring

theorem exists_torusAt_w0_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x), ∃ A : I2.TorusAt (U.X k) x.1, A.w0 = H.w0 := by
  intro E _ _ _ H Dw l Xo c σ r U k x W
  exact exists_torusAt_of_isom (W.F.Di (W.ik k)) (U.X k) (W.φ k) (W.isom k) x.1 x.2

end GlobalTheory.TorusSign
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusWithSign_uniformisationFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x), ∃ A : I2.TorusAt (U.X k) x.1, A.w0 = H.w0 := by
  atlas_forward_decl GlobalTheory.TorusSign.exists_torusAt_w0_eq
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem phiFD_eq_zero_at_last_index : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), j = D.R.m → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp), ∀ x ∈ ((T.U j σ).X k).dom, I2.phiFD ((T.U j σ).X k) (I2.th (E := D.host.E) q R0) x = 0 := by
  intro D T h j hj hjm DF q R0 hrun σ hσ k x hx
  have hu := h.unf j hj σ hσ
  have hq0 : (T.Q.Dw j).q = 0 := by
    rw [(h.pins.2.2.2 j hj).2.1, hjm]
    exact Nat.sub_self _
  have hp0 : ((T.U j σ).X k).p0 = 0 := ((hu.2.1 k).1).trans hq0
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hu k ⟨x, hx⟩
  have hint : ∀ u ∈ ((T.U j σ).X k).Λ, ∀ v ∈ ((T.U j σ).X k).Λ, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (((T.U j σ).X k).ξ0 * FD.herm ((T.U j σ).X k).Gm u v) = z := by
    intro u hu' v hv'
    have hEF := W.isom k ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)
    simp only [LinearEquiv.apply_symm_apply] at hEF
    refine ⟨-((W.F.Di (W.ik k)).EF ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)), ?_⟩
    rw [Int.cast_neg, hEF, neg_mul, map_neg, neg_neg]
  obtain ⟨A, -⟩ := GlobalTheory.T.exists_torusWithSign_uniformisationFrame _ _ _ _ _ _ _ _ (T.U j σ) k ⟨x, hx⟩ W
  obtain ⟨τ0⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ ((T.U j σ).X k).Ψ := by
    by_cases h1 : τ0 ∈ ((T.U j σ).X k).Ψ
    · exact ⟨τ0, h1⟩
    · refine ⟨NumberField.ComplexEmbedding.conjugate τ0, ?_⟩
      rw [((T.U j σ).X k).cmType]
      simpa using h1
  have hpos := A.dim_pos ⟨τ, hτ⟩
  have hneg := A.dim_neg ⟨τ, hτ⟩
  have hsum := A.T.dim_conj τ
  have hr : A.T.r = D.R.r := by
    simp only at hpos hneg
    omega
  obtain ⟨P, hPq, hPR, -⟩ := hrun A.T hr ⟨τ, by simp only at hpos; omega⟩
  have hr0 : 0 < D.R.r := by
    have h2m := D.R.two_le_m
    show 0 < D.R.k + D.R.m - 1
    omega
  refine (GlobalTheory.T.la1sq_ge_two_f_div_rd_of_p0_eq_zero D.host.E D.R.r ((T.U j σ).X k) hr0 hp0 hint x hx).2 q R0
    ?_ ?_ ?_
  · have h16 := P.hrd
    linarith
  · have h1q := P.hq
    omega
  · have hb := P.C2
    rwa [hPq, hPR] at hb

end GlobalTheory
end
