import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAddLeDegOfIdealSmulLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulTwistingSectionEqConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanksStatement

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory.Rounding

variable {K : Type} [Field K] [NumberField K]

theorem lw_nonneg_here (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw K w := by
  unfold lw
  refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
  have : Ideal.absNorm w.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

theorem vAdd_int_nonneg (w : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ≠ 0) : 0 ≤ vAdd w (x : K) := by
  rw [← vla_span hx w]; exact Nat.cast_nonneg _

theorem vAdd_int_pos (w : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ≠ 0) (hm : x ∈ w.asIdeal) :
    1 ≤ vAdd w (x : K) := by
  rw [← vla_span hx w]
  have h0 : Ideal.span {x} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  have := (Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff w h0).2
    (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hm))
  omega

theorem finite_vla {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => (Formalism.L2.Pj.QAt.vla w I : ℝ)).Finite :=
  (Ideal.finite_factors hI).subset fun w h => by
    refine (Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff w hI).1 fun h0 => h ?_
    simp [h0]

theorem sum_vla_lw {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∑ᶠ w, (Formalism.L2.Pj.QAt.vla w I : ℝ) * lw K w = Real.log (Ideal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) := by
  rw [finsum_eq_sum_of_support_subset (s := (finite_vla hI).toFinset) _
    (by simpa using Function.support_mul_subset_left _ _)]
  have h1 := Formalism.L2.Pj.QAt.BeSumPf.sum_vla_log_fin I hI (finite_vla hI).toFinset fun v hv => by
    simpa using hv
  rw [← h1, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [lw, mul_div_assoc]

theorem vAdd_mul_here (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  simp only [vAdd, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]; ring

theorem vAdd_inv_here (w : HeightOneSpectrum (𝓞 K)) (x : K) : vAdd w x⁻¹ = -vAdd w x := by
  simp [vAdd, map_inv₀, WithZero.log_inv]

theorem count_inv_span (w : HeightOneSpectrum (𝓞 K)) {c : 𝓞 K} (hc : c ≠ 0) :
    FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K c)⁻¹) =
      vAdd w (algebraMap (𝓞 K) K c)⁻¹ := by
  have hspan : Ideal.span {c} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hI : ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hspan
  rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.coeIdeal_span_singleton, vAdd_inv_here]
  have h1 := FractionalIdeal.count_mul K w hI (inv_ne_zero hI)
  rw [mul_inv_cancel₀ hI, FractionalIdeal.count_one] at h1
  have h2 : FractionalIdeal.count K w ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      vAdd w (algebraMap (𝓞 K) K c) := by
    rw [FractionalIdeal.count_coe K w hspan]
    exact vla_span hc w
  omega

theorem vla_eq_count (w : HeightOneSpectrum (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (Formalism.L2.Pj.QAt.vla w I : ℤ) = FractionalIdeal.count K w (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  (FractionalIdeal.count_coe K w hI).symm

theorem exists_rounding (K : Type) [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (hB : ∀ p ∈ B, p.Prime) (hρ : (Function.support ρ).Finite)
    (hint : ∀ w : HeightOneSpectrum (𝓞 K), (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n) :
    ∃ (a : K) (𝔞 : Ideal (𝓞 K)), a ≠ 0 ∧ 𝔞 ≠ ⊥ ∧
      (∀ b ∈ 𝔞, b ≠ 0 → ∀ w, 0 ≤ (vAdd w ((b : K) * a) : ℝ) + ρ w) ∧
      (∑ᶠ w, ρ w * lw K w) - ∑ p ∈ B, Real.log p ≤
        -((∑ σ : K →+* ℂ, Real.log ‖σ a‖) / (Module.finrank ℚ K : ℝ)) -
          Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  set f : HeightOneSpectrum (𝓞 K) → ℤ := fun w => -⌊ρ w⌋ with hf
  have hfs : Function.support f ⊆ Function.support ρ := fun w h h0 => h (by simp [hf, h0])
  have hfin : ∀ᶠ w in Filter.cofinite, f w = 0 := by
    rw [Filter.eventually_cofinite]; exact hρ.subset hfs
  set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ f w with hJdef
  have hJ0 : J ≠ 0 := by
    rw [hJdef, finprod_eq_prod_of_mulSupport_subset (s := hρ.toFinset)]
    · exact Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot)
    · intro w hw
      simp only [Set.Finite.coe_toFinset]
      intro h0; apply hw; simp [hf, h0]
  have hcJ : ∀ w, FractionalIdeal.count K w J = f w := fun w => FractionalIdeal.count_finprod K w f hfin
  obtain ⟨c, 𝔞, hc, hJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
  set a : K := (algebraMap (𝓞 K) K c)⁻¹ with ha
  have ha0 : a ≠ 0 := inv_ne_zero (by simpa using hc)
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rintro rfl; apply hJ0; rw [hJ]; simp
  have hsa0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a ≠ 0 :=
    FractionalIdeal.spanSingleton_eq_zero_iff.not.2 ha0
  have h𝔞0 : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔞
  have hsum : ∀ w, vAdd w a + (Formalism.L2.Pj.QAt.vla w 𝔞 : ℤ) = f w := fun w => by
    rw [← hcJ w, hJ, FractionalIdeal.count_mul K w hsa0 h𝔞0, vla_eq_count w h𝔞, ha, count_inv_span w hc]
  refine ⟨a, 𝔞, ha0, h𝔞, ?_, ?_⟩
  · intro b hb hb0 w
    have hspan : Ideal.span {b} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    obtain ⟨e, he⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb)
    have he0 : e ≠ ⊥ := by rintro rfl; apply hspan; rw [he]; simp
    have hbK : (b : K) ≠ 0 := by simpa using hb0
    have h1 : vAdd w ((b : K) * a) = vAdd w (b : K) + vAdd w a := vAdd_mul_here w hbK ha0
    have h2 : vAdd w (b : K) = Formalism.L2.Pj.QAt.vla w 𝔞 + Formalism.L2.Pj.QAt.vla w e := by
      rw [← vla_span hb0 w, vla_eq_count w hspan, vla_eq_count w h𝔞, vla_eq_count w he0, he,
        FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K w h𝔞0 (FractionalIdeal.coeIdeal_ne_zero.2 he0)]
    have h3 : f w ≤ vAdd w ((b : K) * a) := by
      rw [h1, h2, ← hsum w]; have := (Formalism.L2.Pj.QAt.vla w e).zero_le; omega
    have h4 : (f w : ℝ) ≤ vAdd w ((b : K) * a) := by exact_mod_cast h3
    have h5 := Int.fract_nonneg (ρ w)
    rw [Int.fract] at h5
    simp only [hf, Int.cast_neg] at h4
    linarith
  · have e1 := lineDeg_num ha0
    unfold lineDeg at e1
    have e2 := sum_vla_lw h𝔞
    have e3 : (∑ᶠ w, (vAdd w a : ℝ) * lw K w) + ∑ᶠ w, (Formalism.L2.Pj.QAt.vla w 𝔞 : ℝ) * lw K w =
        ∑ᶠ w, (f w : ℝ) * lw K w := by
      rw [← finsum_add_distrib (fin_mul (finite_vAdd ha0) _) (fin_mul (finite_vla h𝔞) _)]
      refine finsum_congr fun w => ?_
      rw [← add_mul, ← hsum w]; push_cast; ring
    set n : ℕ := ∏ p ∈ B, p with hn
    have hn0 : n ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero
    have e4 : ∑ p ∈ B, Real.log p = ∑ᶠ w, (vAdd w (n : K) : ℝ) * lw K w := by
      rw [sum_vAdd_nat hn0, hn, Nat.cast_prod, Real.log_prod]
      intro p hp; exact_mod_cast (hB p hp).ne_zero
    have hfinf : (Function.support fun w => (f w : ℝ) * lw K w).Finite :=
      (hρ.subset fun w h h0 => h (by simp [hf, h0]))
    have e5 : (∑ᶠ w, ρ w * lw K w) + ∑ᶠ w, (f w : ℝ) * lw K w ≤ ∑ᶠ w, (vAdd w (n : K) : ℝ) * lw K w := by
      rw [← finsum_add_distrib (fin_mul hρ _) hfinf]
      refine finsum_le_finsum' ((fin_mul hρ _).union hfinf |>.subset (Function.support_add _ _))
        (fin_mul (finite_vAdd (Nat.cast_ne_zero.2 hn0)) _) fun w => ?_
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (lw_nonneg_here w)
      have hfr : ρ w + (f w : ℝ) = Int.fract (ρ w) := by
        show ρ w + ((-⌊ρ w⌋ : ℤ) : ℝ) = Int.fract (ρ w)
        rw [Int.fract, Int.cast_neg]; ring
      rw [hfr]
      have hnK : ((n : 𝓞 K) : K) = (n : K) := by simp
      have hn0' : (n : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn0
      by_cases h : ∃ p ∈ B, ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
      · obtain ⟨p, hp, hpw⟩ := h
        obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
        have hmem : (n : 𝓞 K) ∈ w.asIdeal := by
          rw [hn, hk, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpw
        have h1 := vAdd_int_pos w hn0' hmem
        rw [hnK] at h1
        have h2 : (1 : ℝ) ≤ vAdd w (n : K) := by exact_mod_cast h1
        linarith [Int.fract_lt_one (ρ w)]
      · push_neg at h
        obtain ⟨m, hm⟩ := hint w h
        have h1 := vAdd_int_nonneg w hn0'
        rw [hnK] at h1
        rw [hm, Int.fract_intCast]
        have h2 : (0 : ℝ) ≤ (vAdd w (n : K) : ℝ) := Int.cast_nonneg h1
        simpa using h2
    have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.2 (Module.finrank_pos (R := ℚ) (M := K))
    linarith

end GlobalTheory.Rounding
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes : ∀ (K : Type) [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ), (∀ p ∈ B, p.Prime) → (Function.support ρ).Finite → (∀ w : HeightOneSpectrum (𝓞 K), (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n) → ∃ (a : K) (𝔞 : Ideal (𝓞 K)), a ≠ 0 ∧ 𝔞 ≠ ⊥ ∧ (∀ b ∈ 𝔞, b ≠ 0 → ∀ w, 0 ≤ (vAdd w ((b : K) * a) : ℝ) + ρ w) ∧ (∑ᶠ w, ρ w * lw K w) - ∑ p ∈ B, Real.log p ≤ -((∑ σ : K →+* ℂ, Real.log ‖σ a‖) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  atlas_forward_decl GlobalTheory.Rounding.exists_rounding
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_add_le_deg_of_ideal_smul_le_alt : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (φ : V →ₗ[K] W) (t : (K →+* ℂ) → ℝ) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)), HasGram N → HasGram N' → Function.Injective φ → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ (φ x) ≤ t σ * N σ x) → L.FG → L'.FG → 𝔞 ≠ ⊥ → 𝔞 • L.map (φ.restrictScalars (𝓞 K)) ≤ L' → Formalism.HN.rkK L' = Formalism.HN.rkK L → deg N L + (Formalism.HN.rkK L : ℝ) * (-((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) ≤ deg N' L' := by
  first | exact @GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le | exact GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le | (intros; apply GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearEquiv_mul_twistingSection_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∃ φ : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀), (∀ f, (φ f : Rul Xo c) = f * s.sig) ∧ (∀ g, (φ.symm g : Rul Xo c) = g * s.inv) ∧ (∀ a : c.F, a ≠ 0 → (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) → ∀ f ∈ latOn U Z G, ∀ g : cuspOn U Z (G + G₀), (g : Rul Xo c) = a • (φ f : Rul Xo c) → g ∈ latOn U Z (G + G₀)) ∧ (∀ b : c.F, b ≠ 0 → (∀ w, s.hi w ≤ (vAdd w b : ℝ)) → ∀ g ∈ latOn U Z (G + G₀), ∀ f : cuspOn U Z G, (f : Rul Xo c) = b • (φ.symm g : Rul Xo c) → f ∈ latOn U Z G) := by
  first | exact @GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral | exact GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral | (intros; apply GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral <;> assumption)
end

section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

theorem degOn_add_rank_mul_degLo_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E) (B : Finset ℕ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ p ∈ B, p.Prime) → IntOff B s.lo → GoodOn U x V dict Z G → degOn U x V dict Z G + (rankOn U Z G : ℝ) * (s.degLo - logSum B) ≤ degOn U x V dict Z (G + G₀) := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G₀ s G B hU hG hB hInt hGood
  haveI : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  obtain ⟨a, 𝔞, ha, h𝔞, hint, hsum⟩ := GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes c.F B s.lo hB s.finite_lo hInt
  obtain ⟨φ, hφ, -, hlat, -⟩ := GlobalTheory.T.exists_linearEquiv_mul_twistingSection_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨hGood', hrk⟩ := GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks E H Dw l Xo c r U x D V dict Z G₀ s G hU hG hGood
  have hna : ∀ σ : c.F →+* ℂ, 0 < ‖σ a‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  set t : (c.F →+* ℂ) → ℝ := fun σ => ‖σ a‖ * s.cInf σ with ht
  have ht0 : ∀ σ, 0 < t σ := fun σ => mul_pos (hna σ) (s.cInf_pos σ)
  have htc : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ := fun σ => by
    simp only [ht, RingHom.comp_apply, Complex.norm_conj]
    rw [s.cInf_congr (CompHt.goodOf_conj σ)]
  let ψ : cuspOn U Z G →ₗ[c.F] cuspOn U Z (G + G₀) := a • φ.toLinearMap
  have hψ : Function.Injective ψ := fun f g h => φ.injective (smul_right_injective _ ha h)
  have hN : ∀ σ f, normOn U x V dict Z (G + G₀) σ (ψ f) ≤ t σ * normOn U x V dict Z G σ f := by
    intro σ f
    apply le_of_eq
    have e : ((ψ f : cuspOn U Z (G + G₀)) : Rul Xo c) = a • ((f : Rul Xo c) * s.sig) := by
      simp [ψ, hφ]
    simp only [normOn]
    rw [e, petOn_smul, petOn, petOn, GlobalTheory.T.petersson_norm_mul_twistingSection_eq_const_mul E H Dw l Xo c r U x Z G₀ s G hG f f.2.2 σ D _ _ _]
    simp only [ht]
    ring
  have hL : 𝔞 • (latOn U Z G).map (ψ.restrictScalars (𝓞 c.F)) ≤ latOn U Z (G + G₀) := by
    rw [Submodule.smul_le]
    rintro b hb _ ⟨f, hf, rfl⟩
    by_cases hb0 : b = 0
    · rw [hb0, zero_smul]; exact zero_mem _
    · have hb' : (b : c.F) ≠ 0 := by simpa using hb0
      refine hlat ((b : c.F) * a) (mul_ne_zero hb' ha) (hint b hb hb0) f hf _ ?_
      rw [← IsScalarTower.algebraMap_smul c.F b]
      simp [ψ, mul_smul]
      rfl
  have key := GlobalTheory.T.deg_add_le_deg_of_ideal_smul_le_alt c.F _ _ (normOn U x V dict Z G) (normOn U x V dict Z (G + G₀)) ψ t (latOn U Z G)
    (latOn U Z (G + G₀)) 𝔞 hGood.1 hGood'.1 hψ ht0 htc hN hGood.2.1 hGood'.2.1 h𝔞 hL hrk
  have hlog : ∑ σ, Real.log (t σ) = ∑ σ : c.F →+* ℂ, Real.log ‖σ a‖ + ∑ σ, Real.log (s.cInf σ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => Real.log_mul (hna σ).ne' (s.cInf_pos σ).ne'
  have hdeg : s.degLo - logSum B ≤ -((∑ σ, Real.log (t σ)) / (Module.finrank ℚ c.F : ℝ)) -
      Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ c.F : ℝ) := by
    rw [hlog, add_div]
    unfold TwSec.degLo lineDeg logSum
    linarith [hsum]
  exact le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _))) key

end GlobalTheory.FlatTw
end
end
