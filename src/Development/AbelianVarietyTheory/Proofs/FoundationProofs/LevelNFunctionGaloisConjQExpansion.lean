import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VactVmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyIffValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInftyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQVadd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionOfPeriodicBoundedHolomorphic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicRootNormLeOneAddSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariant
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFamConstLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModularFormLevelOneOfInvariantQExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularFormPolynomialE4E6
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PermutedModularFamilyMonicPolyCoeffInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagOneUnitConjLiftsSl2IntReductionMod

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem hasQ_periodic {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N) (h : HasQ N f a) (τ : ℍ) :
    f ((N : ℝ) +ᵥ τ) = f τ := by
  have h1 := hasQ_vadd N f a (N : ℝ) h
  have hc : (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * ((N : ℝ) : ℂ) / N)) = a := by
    funext n
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : 2 * Real.pi * Complex.I * n * ((N : ℝ) : ℂ) / N = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; field_simp
    rw [this, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [hc] at h1
  exact congrFun (GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique.2 N _ _ a h1 h) τ

theorem hasQ_of_integral_quot : ∀ (N n : ℕ) (A D : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N →
    (∃ a, HasQ N A a) → (∃ d, HasQ N D d) → (∀ j, ∃ c, HasQ N (s j) c) → D ≠ 0 →
    (∀ τ, A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) = 0) →
    ∃ (h : ℍ → ℂ) (b : ℕ → ℂ), HasQ N h b ∧ ∀ τ, A τ = h τ * D τ := by
  intro N n A D s hN ⟨a, hA⟩ ⟨d, hD⟩ hs hD0 heq
  choose c hc using hs
  obtain ⟨hAm, -⟩ := GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N A a hN hA
  obtain ⟨hDm, -⟩ := GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N D d hN hD
  have hsm : ∀ j, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s j) ∧ UpperHalfPlane.IsBoundedAtImInfty (s j) :=
    fun j => GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N (s j) (c j) hN (hc j)
  have hUo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, D τ ≠ 0 := by
    by_contra hc'
    push_neg at hc'
    exact hD0 (funext hc')
  have hofc : ∀ z : ℂ, 0 < z.im → ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  obtain ⟨h₀, hh₀d, hh₀A, hh₀p⟩ := GlobalTheory.T.exists_differentiableOn_quotient_of_integral {z : ℂ | 0 < z.im} n
    (A ∘ UpperHalfPlane.ofComplex) (D ∘ UpperHalfPlane.ofComplex)
    (fun j => s j ∘ UpperHalfPlane.ofComplex) hUo hUc (UpperHalfPlane.mdifferentiable_iff.1 hAm)
    (UpperHalfPlane.mdifferentiable_iff.1 hDm) (fun j => UpperHalfPlane.mdifferentiable_iff.1 (hsm j).1)
    ⟨(τ₀ : ℂ), τ₀.im_pos, by simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hτ₀⟩
    (fun z _ => heq _)
  set h : ℍ → ℂ := fun τ => h₀ τ with hdef
  have hAh : ∀ τ, A τ = h τ * D τ := fun τ => by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh₀A (τ : ℂ) τ.im_pos
  have hhp : ∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0 := fun τ => by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh₀p (τ : ℂ) τ.im_pos
  have hhm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    refine UpperHalfPlane.mdifferentiable_iff.2 (hh₀d.congr fun z hz => ?_)
    simp only [Function.comp_apply, hdef, hofc z hz]
  have hhNm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => h ((N : ℝ) +ᵥ τ)) := by
    have hd : DifferentiableOn ℂ (fun z : ℂ => h₀ (((N : ℝ) : ℂ) + z)) {z : ℂ | 0 < z.im} :=
      hh₀d.comp ((differentiableOn_const _).add differentiableOn_id) fun z hz => by
        show 0 < (((N : ℝ) : ℂ) + z).im
        simpa using hz
    refine UpperHalfPlane.mdifferentiable_iff.2 (hd.congr fun z hz => ?_)
    simp only [Function.comp_apply, hdef, UpperHalfPlane.coe_vadd, hofc z hz]
  have hper : ∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ := by
    have hz : ∀ τ, (fun τ => h ((N : ℝ) +ᵥ τ) - h τ) τ * D τ = 0 := fun τ => by
      have e1 := hAh ((N : ℝ) +ᵥ τ)
      rw [hasQ_periodic hN hA, hasQ_periodic hN hD, hAh τ] at e1
      simp only
      linear_combination -e1
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ D (hhNm.sub hhm) hDm hz with h0 | h0
    · exact fun τ => sub_eq_zero.1 (congrFun h0 τ)
    · exact absurd h0 hD0
  have hbd : UpperHalfPlane.IsBoundedAtImInfty h := by
    have hS : (fun τ => ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
      have hb : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          (fun τ => ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := fun j _ => by
        have : (s j) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := (hsm j).2
        exact this.norm_left
      exact (Asymptotics.IsBigO.sum hb).congr_left fun τ => Finset.sum_apply _ _ _
    have h1 : (fun τ => 1 + ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) :=
      ((Asymptotics.isBigO_refl (1 : ℍ → ℝ) _).add hS).congr_left fun τ => rfl
    have h2 : h =O[UpperHalfPlane.atImInfty] (fun τ => 1 + ∑ j, ‖s j τ‖) := by
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_)
      have hb := GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff n (fun j => s j τ) (h τ) (hhp τ)
      have hnn : (0 : ℝ) ≤ 1 + ∑ j, ‖s j τ‖ := by positivity
      rw [Real.norm_of_nonneg hnn, one_mul]
      exact hb
    exact h2.trans h1
  obtain ⟨b, hb⟩ := GlobalTheory.T.hasQExpansion_of_periodic_bounded_holomorphic N h hN hhm hper hbd
  exact ⟨h, b, hb, hAh⟩

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hasQ_quotient_of_integral : ∀ (N n : ℕ) (A D : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N → (∃ a, HasQ N A a) → (∃ d, HasQ N D d) → (∀ j, ∃ c, HasQ N (s j) c) → D ≠ 0 → (∀ τ, A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) = 0) → ∃ (h : ℍ → ℂ) (b : ℕ → ℂ), HasQ N h b ∧ ∀ τ, A τ = h τ * D τ := by
  atlas_forward_decl GlobalTheory.FN.hasQ_of_integral_quot
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

theorem conjEx_hasQ_zero (N : ℕ) : HasQ N (fun _ => (0 : ℂ)) (fun _ => 0) := fun _ => by
  simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)

theorem conjEx_conv_coeff (a b : ℕ → ℂ) (n : ℕ) :
    conv a b n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) := by
  simp [conv, PowerSeries.coeff_mul]

theorem conjEx_conv_map (g : ℂ ≃+* ℂ) (a b : ℕ → ℂ) :
    (fun n => g (conv a b n)) = conv (fun n => g (a n)) (fun n => g (b n)) := by
  funext n; simp [conv, map_sum, map_mul]

theorem conjEx_conv_cancel (a b d : ℕ → ℂ) (hd : d ≠ 0) (h : conv a d = conv b d) : a = b := by
  have hmk : PowerSeries.mk d ≠ 0 := by
    intro h0; apply hd; funext n
    have := congrArg (PowerSeries.coeff n) h0
    simpa using this
  have hm : PowerSeries.mk a * PowerSeries.mk d = PowerSeries.mk b * PowerSeries.mk d := by
    ext n
    have := congrFun h n
    rwa [conjEx_conv_coeff, conjEx_conv_coeff] at this
  have := mul_right_cancel₀ hmk hm
  funext n
  have := congrArg (PowerSeries.coeff n) this
  simpa using this

theorem conj_exists : ∀ (g : ℂ ≃+* ℂ) (N n : ℕ) (f D D' A A' : ℍ → ℂ) (s s' : Fin n → ℍ → ℂ), 0 < N → (∃ a, HasQ N f a) → QConj g N D D' → QConj g N A A' → (∀ j, QConj g N (s j) (s' j)) → D ≠ 0 → (∀ τ, f τ * D τ = A τ) → (∀ τ, f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ) = 0) → ∃ f' : ℍ → ℂ, QConj g N f f' ∧ ∀ τ, f' τ * D' τ = A' τ := by
  intro g N n f D D' A A' s s' hN ⟨a, ha⟩ ⟨d, hd, hd'⟩ ⟨e, he, he'⟩ hs hD hfA hpol
  obtain ⟨uc, uf⟩ := GlobalTheory.QFam.hasQ_unique_both
  have hz := conjEx_hasQ_zero N
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD (uf N D (fun _ => 0) _ hd hz)
  have hgd0 : (fun n => g (d n)) ≠ 0 := by
    intro h0; apply hd0; funext k
    have := congrFun h0 k
    simpa using this
  have hD' : D' ≠ 0 := by
    rintro rfl
    exact hgd0 (uc N (fun _ => 0) _ _ hN hd' hz)
  obtain ⟨_, hadd, _, hmul, hpow, hsumprod⟩ := GlobalTheory.QFam.qConj_ring g N hN
  have hA : QConj g N A A' := ⟨e, he, he'⟩
  have hDD : QConj g N D D' := ⟨d, hd, hd'⟩
  have hP : QConj g N (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j))
      (fun τ => A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) := by
    refine hadd _ _ _ _ (hpow _ _ n hA) ?_
    refine (hsumprod (Fin n) Finset.univ (fun j τ => s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j))
      (fun j τ => s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) ?_).1
    intro j _
    exact hmul _ _ _ _ (hmul _ _ _ _ (hs j) (hpow _ _ _ hA)) (hpow _ _ _ hDD)
  have hP0 : (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j)) = fun _ => 0 := by
    funext τ
    have hx : A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) =
        D τ ^ n * (f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ)) := by
      rw [mul_add, Finset.mul_sum, ← hfA τ, mul_pow]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow, show D τ ^ n = D τ ^ (j : ℕ) * D τ ^ (n - j) by
          rw [← pow_add, Nat.add_sub_cancel' j.2.le]]
        ring
    rw [hx, hpol τ, mul_zero]
  have hP'0 : ∀ τ, A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j) = 0 := by
    obtain ⟨c, hc, hc'⟩ := hP
    rw [hP0] at hc
    have hc0 : c = fun _ => 0 := uc N _ _ _ hN hc hz
    subst hc0
    simp only [map_zero] at hc'
    have := uf N _ _ _ hc' hz
    exact fun τ => congrFun this τ
  obtain ⟨h, b, hb, hAh⟩ := GlobalTheory.T.exists_hasQ_quotient_of_integral N n A' D' s' hN ⟨_, he'⟩ ⟨_, hd'⟩
    (fun j => by obtain ⟨c, _, hc'⟩ := hs j; exact ⟨_, hc'⟩) hD' hP'0
  have hfD : HasQ N A (conv a d) := by
    have := GlobalTheory.QFam.hasQ_mul_conv N f D a d hN ha hd
    have hAe : (fun τ => f τ * D τ) = A := funext hfA
    rwa [hAe] at this
  have he1 : e = conv a d := uc N A _ _ hN he hfD
  have hhD : HasQ N A' (conv b fun n => g (d n)) := by
    have := GlobalTheory.QFam.hasQ_mul_conv N h D' b _ hN hb hd'
    have hAe : (fun τ => h τ * D' τ) = A' := funext fun τ => (hAh τ).symm
    rwa [hAe] at this
  have he2 : (fun n => g (e n)) = conv b fun n => g (d n) := uc N A' _ _ hN he' hhD
  rw [he1, conjEx_conv_map] at he2
  have hba : b = fun n => g (a n) := (conjEx_conv_cancel _ _ _ hgd0 he2).symm
  refine ⟨h, ⟨a, ha, hba ▸ hb⟩, fun τ => (hAh τ).symm⟩

end GlobalTheory.FN
end
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffwiseConjugate_of_integral_quotient : ∀ (g : ℂ ≃+* ℂ) (N n : ℕ) (f D D' A A' : ℍ → ℂ) (s s' : Fin n → ℍ → ℂ), 0 < N → (∃ a, HasQ N f a) → QConj g N D D' → QConj g N A A' → (∀ j, QConj g N (s j) (s' j)) → D ≠ 0 → (∀ τ, f τ * D τ = A τ) → (∀ τ, f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ) = 0) → ∃ f' : ℍ → ℂ, QConj g N f f' ∧ ∀ τ, f' τ * D' τ = A' τ := by
  atlas_forward_decl GlobalTheory.FN.conj_exists
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.QFam.LagrangeFam

def esymmOff {ι : Type} [Fintype ι] [DecidableEq ι] (t : ι → ℍ → ℂ) (j : ℕ) (i : ι) (τ : ℍ) : ℂ :=
  ∑ s ∈ Finset.powersetCard j (Finset.univ.erase i), ∏ l ∈ s, t l τ

def lagCoeff {ι : Type} [Fintype ι] [DecidableEq ι] (t F : ι → ℍ → ℂ) (j : ℕ) (τ : ℍ) : ℂ :=
  (-1) ^ j * ∑ i, F i τ * esymmOff t j i τ

theorem prod_sub_eq_sum {κ : Type} (s : Finset κ) (y : κ → ℂ) (x : ℂ) :
    ∏ l ∈ s, (x - y l) = ∑ j ∈ Finset.range (s.card + 1),
      (-1) ^ j * (∑ u ∈ Finset.powersetCard j s, ∏ l ∈ u, y l) * x ^ (s.card - j) := by
  have h := congrArg (Polynomial.eval x) (Multiset.prod_X_sub_X_eq_sum_esymm (s.val.map y))
  simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one, Multiset.card_map,
    Finset.esymm_map_val] at h
  rw [Finset.prod_eq_multiset_prod]
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.card_val]
  ring

theorem lag_eval {ι : Type} [Fintype ι] [DecidableEq ι] (t F : ι → ℍ → ℂ) (i : ι) (τ : ℍ) :
    F i τ * ∏ l ∈ Finset.univ.erase i, (t i τ - t l τ) =
      ∑ j ∈ Finset.range (Fintype.card ι), lagCoeff t F j τ * t i τ ^ (Fintype.card ι - 1 - j) := by
  have hc : ∀ i' : ι, (Finset.univ.erase i').card + 1 = Fintype.card ι := fun i' => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i'⟩
    omega
  have hc' : ∀ i' : ι, (Finset.univ.erase i').card = Fintype.card ι - 1 := fun i' => by
    have := hc i'; omega
  have key : ∀ i' : ι, F i' τ * ∏ l ∈ Finset.univ.erase i', (t i τ - t l τ) =
      ∑ j ∈ Finset.range (Fintype.card ι),
        (-1) ^ j * (F i' τ * esymmOff t j i' τ) * t i τ ^ (Fintype.card ι - 1 - j) := by
    intro i'
    rw [prod_sub_eq_sum, hc i', hc' i', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [esymmOff]
    ring
  have hz : ∀ i' ∈ (Finset.univ : Finset ι), i' ≠ i →
      F i' τ * ∏ l ∈ Finset.univ.erase i', (t i τ - t l τ) = 0 := by
    intro i' _ hne
    rw [Finset.prod_eq_zero (i := i) (Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ _⟩)
      (sub_self _), mul_zero]
  rw [← Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hz]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [lagCoeff, Finset.mul_sum, Finset.sum_mul]

theorem esymmOff_value {ι : Type} [Fintype ι] [DecidableEq ι] {act : ι → SL(2, ℤ) → ι} {m : ℕ}
    {t : ι → ℍ → ℂ} (hb : ActBij act) (ht : IsFam act m t) (γ : SL(2, ℤ)) (j : ℕ) (i : ι)
    (τ : ℍ) :
    esymmOff t j i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ)) =
      esymmOff t j (act i γ) τ := by
  unfold esymmOff
  rw [Finset.sum_mul]
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  have he : ∀ l, e l = act l γ := fun l => rfl
  refine Finset.sum_equiv e.finsetCongr (fun s => ?_) (fun s hs => ?_)
  · simp only [Finset.mem_powersetCard, Equiv.finsetCongr_apply, Finset.card_map]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx => ?_, h2⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      have := h1 hy
      rw [Finset.mem_erase] at this ⊢
      refine ⟨fun h => this.1 ?_, Finset.mem_univ _⟩
      rw [← he] at h
      exact e.injective h
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx => ?_, h2⟩
      have := h1 (Finset.mem_map_of_mem e.toEmbedding hx)
      rw [Finset.mem_erase] at this ⊢
      exact ⟨fun h => this.1 (by rw [Equiv.coe_toEmbedding, h]; rfl), Finset.mem_univ _⟩
  · have hc : s.card = j := (Finset.mem_powersetCard.mp hs).2
    have h1 : UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ)) =
        ∏ _l ∈ s, UpperHalfPlane.denom γ τ ^ (-(m : ℤ)) := by
      rw [Finset.prod_const, hc, ← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [h1, ← Finset.prod_mul_distrib, Equiv.finsetCongr_apply, Finset.prod_map]
    exact Finset.prod_congr rfl fun l _ => ht.value_mul_denom l γ τ

theorem lagCoeff_slash {ι : Type} [Fintype ι] [DecidableEq ι] {act : ι → SL(2, ℤ) → ι} {m k : ℕ}
    {t F : ι → ℍ → ℂ} (hb : ActBij act) (ht : IsFam act m t) (hF : IsFam act k F) (j : ℕ)
    (γ : SL(2, ℤ)) :
    lagCoeff t F j ∣[((k + m * j : ℕ) : ℤ)] γ = lagCoeff t F j := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  unfold lagCoeff
  have hD : UpperHalfPlane.denom γ τ ^ (-(((k + m * j : ℕ) : ℤ))) =
      UpperHalfPlane.denom γ τ ^ (-(k : ℤ)) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ)) := by
    rw [← zpow_add₀ (UpperHalfPlane.denom_ne_zero _ τ)]
    congr 1
    push_cast
    ring
  rw [hD, mul_assoc, Finset.sum_mul]
  congr 1
  have : ∀ i, F i (γ • τ) * esymmOff t j i (γ • τ) *
      (UpperHalfPlane.denom γ τ ^ (-(k : ℤ)) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ))) =
      F (act i γ) τ * esymmOff t j (act i γ) τ := fun i => by
    rw [← hF.value_mul_denom i γ τ, ← esymmOff_value hb ht γ j i τ]
    ring
  simp only [this]
  exact (hb γ).sum_comp (fun i => F i τ * esymmOff t j i τ)

theorem lagrange_fam : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (act : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t F : ι → ℍ → ℂ), 0 < N → ActBij act → IsFam act m t → IsFam act k F → (∀ i, ∃ a, HasQ N (t i) a) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ c : ℕ → ℍ → ℂ, (∀ j, (∀ γ : SL(2, ℤ), c j ∣[((k + m * j : ℕ) : ℤ)] γ = c j) ∧ ∃ a, HasQ N (c j) a) ∧ ∀ i τ, F i τ * ∏ l ∈ Finset.univ.erase i, (t i τ - t l τ) = ∑ j ∈ Finset.range (Fintype.card ι), c j τ * t i τ ^ (Fintype.card ι - 1 - j) := by
  intro ι _ _ act m k N t F _ hb ht hF hqt hqF
  refine ⟨lagCoeff t F, fun j => ⟨fun γ => lagCoeff_slash hb ht hF j γ, ?_⟩,
    fun i τ => lag_eval t F i τ⟩
  have qt : ∀ i, QAll (· ∈ (⊤ : Subring ℂ)) N (t i) := fun i =>
    let ⟨a, ha⟩ := hqt i; ⟨a, ha, fun _ => Subring.mem_top _⟩
  have qF : ∀ i, QAll (· ∈ (⊤ : Subring ℂ)) N (F i) := fun i =>
    let ⟨a, ha⟩ := hqF i; ⟨a, ha, fun _ => Subring.mem_top _⟩
  have hq : QAll (· ∈ (⊤ : Subring ℂ)) N (lagCoeff t F j) :=
    QAllSubring.mul (QAllSubring.const (Subring.mem_top ((-1 : ℂ) ^ j)))
      (QAllSubring.sum _ fun i _ => QAllSubring.mul (qF i)
        (QAllSubring.sum _ fun s _ => QAllSubring.prod s fun l _ => qt l))
  obtain ⟨a, ha, _⟩ := hq
  exact ⟨a, ha⟩

end GlobalTheory.QFam.LagrangeFam
end
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modular_form_symmetric_function_decomp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (act : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t F : ι → ℍ → ℂ), 0 < N → ActBij act → IsFam act m t → IsFam act k F → (∀ i, ∃ a, HasQ N (t i) a) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ c : ℕ → ℍ → ℂ, (∀ j, (∀ γ : SL(2, ℤ), c j ∣[((k + m * j : ℕ) : ℤ)] γ = c j) ∧ ∃ a, HasQ N (c j) a) ∧ ∀ i τ, F i τ * ∏ l ∈ Finset.univ.erase i, (t i τ - t l τ) = ∑ j ∈ Finset.range (Fintype.card ι), c j τ * t i τ ^ (Fintype.card ι - 1 - j) := by
  atlas_forward_decl GlobalTheory.QFam.LagrangeFam.lagrange_fam
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_conj_level_one : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F : ℍ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → (∃ a, HasQ N F a) →
    ∃ F' : ℍ → ℂ, (∀ γ : SL(2, ℤ), F' ∣[(w : ℤ)] γ = F') ∧ QConj g N F F' := by
  intro g w N F hN hinv ⟨a, ha⟩
  have hmf : IsMF (w : ℤ) F := GlobalTheory.QFam.isMF_of_invariant_of_hasQ N w F a hN hinv ha
  obtain ⟨s, c, hwt, hF⟩ := GlobalTheory.QFam.isMF_eq_sum_monomials w F hmf
  refine ⟨fun τ => ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2), ?_, ?_⟩
  ·
    let act : Unit → SL(2, ℤ) → Unit := fun i _ => i
    have hfam : IsFam act (w : ℤ)
        (fun _ τ => ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) := by
      refine IsFam.sum_fun s (f := fun p _ τ => g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ?_
      intro p hp
      have h4 := (isFam_const_E4 Unit act).pow_fun p.1
      have h6 := (isFam_const_E6 Unit act).pow_fun p.2
      have hm := (h4.mul_fun h6).const_mul_fun (g (c p))
      have e : ((p.1 : ℕ) : ℤ) * 4 + ((p.2 : ℕ) : ℤ) * 6 = (w : ℤ) := by
        rw [← hwt p hp]; push_cast; ring
      rw [e] at hm
      exact hm
    intro γ
    exact hfam () γ
  · have hFe : F = fun τ => ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := funext hF
    rw [hFe]
    refine QConj.sum s (f := fun p τ => c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2))
      (f' := fun p τ => g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ?_
    intro p _
    have h4 : QConj g N ⇑E₄ ⇑E₄ := eis_qConj N hN _ (Or.inl rfl) g
    have h6 : QConj g N ⇑E₆ ⇑E₆ := eis_qConj N hN _ (Or.inr (Or.inl rfl)) g
    exact QConj.mul hN (QConj.const g N (c p))
      (QConj.mul hN (QConj.pow hN p.1 h4) (QConj.pow hN p.2 h6))

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qConj_level_one_invariant : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → (∃ a, HasQ N F a) → ∃ F' : ℍ → ℂ, (∀ γ : SL(2, ℤ), F' ∣[(w : ℤ)] γ = F') ∧ QConj g N F F' := by
  atlas_forward_decl GlobalTheory.FN.exists_conj_level_one
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN.Lag

theorem mdiff_of_hasQ {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ} (h : ∃ a, HasQ N f a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  obtain ⟨a, ha⟩ := h
  exact (GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N f a hN ha).1

theorem hasQ_of_qConj {g : ℂ ≃+* ℂ} {N : ℕ} {f f' : ℍ → ℂ} (h : QConj g N f f') :
    (∃ a, HasQ N f a) ∧ ∃ a, HasQ N f' a := by
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨⟨a, ha⟩, ⟨_, hb⟩⟩

theorem qConj_refl {N : ℕ} {f : ℍ → ℂ} (h : ∃ a, HasQ N f a) : QConj (RingEquiv.refl ℂ) N f f := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha, by simpa using ha⟩

theorem hasQ_zero (N : ℕ) : HasQ N (0 : ℍ → ℂ) (fun _ => 0) := by
  intro τ
  simp only [zero_mul, Pi.zero_apply]
  exact hasSum_zero

theorem qConj_ne_zero {g : ℂ ≃+* ℂ} {N : ℕ} (hN : 0 < N) {f f' : ℍ → ℂ} (h : QConj g N f f') (hf : f ≠ 0) :
    f' ≠ 0 := by
  obtain ⟨a, ha, hb⟩ := h
  rintro rfl
  have h1 := (GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique).1 N 0 _ _ hN hb (hasQ_zero N)
  have h2 : a = fun _ => 0 := funext fun n => by
    have := congrFun h1 n
    simpa using this
  subst h2
  exact hf ((GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique).2 N f 0 _ ha (hasQ_zero N))

theorem prod_ne_zero {N : ℕ} (hN : 0 < N) {κ : Type} (s : Finset κ) (u : κ → ℍ → ℂ)
    (hu : ∀ l ∈ s, u l ≠ 0 ∧ ∃ a, HasQ N (u l) a) : (fun τ => ∏ l ∈ s, u l τ) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h
    have := congrFun h UpperHalfPlane.I
    simp at this
  | insert x s hx ih =>
    have hs : ∀ l ∈ s, u l ≠ 0 ∧ ∃ a, HasQ N (u l) a := fun l hl => hu l (Finset.mem_insert_of_mem hl)
    have hQ : ∃ b, HasQ N (fun τ => ∏ l ∈ s, u l τ) b :=
      (hasQ_of_qConj ((GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure (RingEquiv.refl ℂ) N hN).2.2.2.2.2 κ s u u
        fun l hl => qConj_refl (hs l hl).2).2).1
    intro h
    have hprod : ∀ τ, u x τ * (∏ l ∈ s, u l τ) = 0 := fun τ => by
      have := congrFun h τ
      simpa [Finset.prod_insert hx] using this
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff (u x) _ (mdiff_of_hasQ hN (hu x (Finset.mem_insert_self x s)).2)
      (mdiff_of_hasQ hN hQ) hprod with h1 | h1
    · exact (hu x (Finset.mem_insert_self x s)).1 h1
    · exact ih hs h1

end GlobalTheory.FN.Lag

namespace GlobalTheory.FN.Lag

open Finset in

theorem conj_family_of_injective : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → Function.Injective t → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  intro g ι _ act act' m k N t t' F hN hb hb' ht ht' hF hinj htt' hFq
  classical
  have hR := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure g N hN
  have hRr := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure (RingEquiv.refl ℂ) N hN
  have hA := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act'

  obtain ⟨c, hc, hlag⟩ := GlobalTheory.T.modular_form_symmetric_function_decomp ι act m k N t F hN hb ht hF (fun i => (hasQ_of_qConj (htt' i)).1) hFq
  choose c' hc' using fun j => GlobalTheory.T.exists_qConj_level_one_invariant g (k + m * j) N (c j) hN (hc j).1 (hc j).2

  obtain ⟨s, hs, hmin⟩ := GlobalTheory.T.permutedModularFamily_monic_poly_coeff_invariant ι act k N F ⊤ hN hb hF
    (fun i => let ⟨a, ha⟩ := hFq i; ⟨a, ha, fun _ => Subring.mem_top _⟩)
  choose s' hs' using fun j : Fin (Fintype.card ι) => GlobalTheory.T.exists_qConj_level_one_invariant g (k * (Fintype.card ι - j)) N (s j) hN (hs j).1
    (let ⟨a, ha, _⟩ := (hs j).2; ⟨a, ha⟩)

  obtain ⟨D, hD⟩ : ∃ D : ι → ℍ → ℂ, ∀ i, D i = fun τ => ∏ l ∈ univ.erase i, (t i τ - t l τ) := ⟨_, fun _ => rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : ι → ℍ → ℂ, ∀ i, D' i = fun τ => ∏ l ∈ univ.erase i, (t' i τ - t' l τ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ι → ℍ → ℂ, ∀ i, A i = fun τ =>
      ∑ j ∈ range (Fintype.card ι), c j τ * t i τ ^ (Fintype.card ι - 1 - j) := ⟨_, fun _ => rfl⟩
  obtain ⟨A', hA'd⟩ : ∃ A' : ι → ℍ → ℂ, ∀ i, A' i = fun τ =>
      ∑ j ∈ range (Fintype.card ι), c' j τ * t' i τ ^ (Fintype.card ι - 1 - j) := ⟨_, fun _ => rfl⟩
  have hDD : ∀ i, QConj g N (D i) (D' i) := fun i => by
    rw [hD i, hD' i]
    exact (hR.2.2.2.2.2 ι (univ.erase i) (fun l τ => t i τ - t l τ) (fun l τ => t' i τ - t' l τ)
      (fun l _ => hR.2.2.1 _ _ _ _ (htt' i) (htt' l))).2
  have hAA : ∀ i, QConj g N (A i) (A' i) := fun i => by
    rw [hAd i, hA'd i]
    exact (hR.2.2.2.2.2 ℕ (range (Fintype.card ι)) (fun j τ => c j τ * t i τ ^ (Fintype.card ι - 1 - j))
      (fun j τ => c' j τ * t' i τ ^ (Fintype.card ι - 1 - j))
      (fun j _ => hR.2.2.2.1 _ _ _ _ (hc' j).2 (hR.2.2.2.2.1 _ _ _ (htt' i)))).1
  have hDne : ∀ i, D i ≠ 0 := fun i => by
    rw [hD i]
    refine prod_ne_zero hN (univ.erase i) (fun l τ => t i τ - t l τ) fun l hl => ⟨?_, ?_⟩
    · intro h
      apply Finset.ne_of_mem_erase hl
      apply hinj
      funext τ
      have := congrFun h τ
      simp only [Pi.zero_apply] at this
      exact (sub_eq_zero.mp this).symm
    · exact (hasQ_of_qConj (hRr.2.2.1 _ _ _ _ (qConj_refl (hasQ_of_qConj (htt' i)).1)
        (qConj_refl (hasQ_of_qConj (htt' l)).1))).1
  have hD'ne : ∀ i, D' i ≠ 0 := fun i => qConj_ne_zero hN (hDD i) (hDne i)

  choose F' hF'1 hF'2 using fun i => GlobalTheory.T.exists_coeffwiseConjugate_of_integral_quotient g N (Fintype.card ι) (F i) (D i) (D' i) (A i) (A' i) s s' hN
    (hFq i) (hDD i) (hAA i) (fun j => (hs' j).2) (hDne i)
    (fun τ => by simp only [hD, hAd]; exact hlag i τ) (fun τ => hmin i τ)
  refine ⟨F', ?_, hF'1⟩

  have hv := (GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values ι act' m t').1 ht'
  have hD'fam : IsFam act' ((m * (Fintype.card ι - 1) : ℕ) : ℤ) D' := by
    rw [GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values]
    intro i γ τ
    simp only [hD', hv]
    set X : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)
    have e : ∀ l ∈ univ.erase i, X ^ (m : ℤ) * t' (act' i γ) τ - X ^ (m : ℤ) * t' (act' l γ) τ =
        X ^ (m : ℤ) * (t' (act' i γ) τ - t' (act' l γ) τ) := fun _ _ => by ring
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (mem_univ _),
      Finset.card_univ]
    congr 1
    · rw [← zpow_natCast, ← zpow_mul]
      push_cast
      ring_nf
    · apply Finset.prod_nbij (fun l => act' l γ)
      · intro l hl
        exact Finset.mem_erase.mpr ⟨fun h => Finset.ne_of_mem_erase hl ((hb' γ).1 h), mem_univ _⟩
      · intro l _ l' _ h
        exact (hb' γ).1 h
      · intro y hy
        obtain ⟨l, hl⟩ := (hb' γ).2 y
        refine ⟨l, ?_, hl⟩
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun h => ?_, mem_univ _⟩)
        subst h
        exact Finset.ne_of_mem_erase (Finset.mem_coe.mp hy) hl.symm
      · intro l _
        rfl
  have hA'fam : IsFam act' ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) A' := by
    have e : A' = fun i τ => ∑ j ∈ range (Fintype.card ι), (fun j i τ => c' j τ * t' i τ ^ (Fintype.card ι - 1 - j)) j i τ := by
      funext i τ
      rw [hA'd i]
    rw [e]
    refine hA.2.2.2.2.2.1 ℕ _ _ _ fun j hj => ?_
    have hj' : j < Fintype.card ι := Finset.mem_range.mp hj
    have hw : ((k + m * j : ℕ) : ℤ) + ((Fintype.card ι - 1 - j : ℕ) : ℤ) * (m : ℤ) =
        ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) := by
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.le_sub_one_of_lt hj')
      rw [hr, show j + r - j = r by omega]
      push_cast
      ring
    rw [← hw]
    exact hA.2.2.2.1 _ _ (fun _ => c' j) (fun i τ => t' i τ ^ (Fintype.card ι - 1 - j))
      (fun _ γ => (hc' j).1 γ) (hA.2.2.2.2.1 _ _ _ ht')
  intro i γ
  have e1 : (F' i ∣[(k : ℤ)] γ) * (D' i ∣[((m * (Fintype.card ι - 1) : ℕ) : ℤ)] γ) =
      A' i ∣[((k + m * (Fintype.card ι - 1) : ℕ) : ℤ)] γ := by
    rw [show ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) = (k : ℤ) + ((m * (Fintype.card ι - 1) : ℕ) : ℤ) by push_cast; ring,
      ← ModularForm.mul_slash_SL2]
    congr 1
    funext τ
    exact hF'2 i τ
  rw [hD'fam i γ, hA'fam i γ] at e1
  have hz : ∀ τ, ((F' i ∣[(k : ℤ)] γ) τ - F' (act' i γ) τ) * D' (act' i γ) τ = 0 := fun τ => by
    have := congrFun e1 τ
    simp only [Pi.mul_apply] at this
    rw [sub_mul, this, hF'2, sub_self]
  have hol1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F' i ∣[(k : ℤ)] γ) := by
    rw [ModularForm.SL_slash]
    exact MDifferentiable.slash (mdiff_of_hasQ hN (hasQ_of_qConj (hF'1 i)).2) _ _
  rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ (hol1.sub (mdiff_of_hasQ hN (hasQ_of_qConj (hF'1 (act' i γ))).2))
    (mdiff_of_hasQ hN (hasQ_of_qConj (hDD (act' i γ))).2) hz with h | h
  · funext τ
    exact sub_eq_zero.mp (congrFun h τ)
  · exact absurd h (hD'ne _)

end GlobalTheory.FN.Lag
end
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_family_of_injective : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → Function.Injective t → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  atlas_forward_decl GlobalTheory.FN.Lag.conj_family_of_injective
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem conj_family_sep : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → (∀ i j, t i = t j → F i = F j) → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  intro g ι _ act act' m k N t t' F hN hA hA' ht ht' hF htF hc hq
  classical

  have key : ∀ i j, t i = t j ↔ t' i = t' j := by
    intro i j
    obtain ⟨a, ha, ha'⟩ := hc i
    obtain ⟨b, hb, hb'⟩ := hc j
    constructor
    · intro h
      have hab : a = b := HasQ.coeff_unique hN ha (h ▸ hb)
      subst hab
      exact HasQ.fun_unique ha' hb'
    · intro h
      have hab : (fun n => g (a n)) = fun n => g (b n) := HasQ.coeff_unique hN ha' (h ▸ hb')
      have : a = b := funext fun n => g.injective (congrFun hab n)
      subst this
      exact HasQ.fun_unique ha hb
  let s : Setoid ι := Setoid.ker t
  let κ := Quotient s
  have hs : ∀ i j, (Quotient.mk s i = Quotient.mk s j) ↔ t i = t j := fun i j =>
    ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  haveI : Fintype κ := Fintype.ofFinite κ
  let actκ : κ → SL(2, ℤ) → κ := fun c γ =>
    Quotient.lift (fun i => Quotient.mk s (act i γ)) (fun i j (h : t i = t j) => by
      apply (hs _ _).2
      rw [← ht i γ, ← ht j γ, h]) c
  let actκ' : κ → SL(2, ℤ) → κ := fun c γ =>
    Quotient.lift (fun i => Quotient.mk s (act' i γ)) (fun i j (h : t i = t j) => by
      apply (hs _ _).2
      rw [key, ← ht' i γ, ← ht' j γ, (key i j).1 h]) c
  let tκ : κ → ℍ → ℂ := fun c => Quotient.lift t (fun i j (h : t i = t j) => h) c
  let tκ' : κ → ℍ → ℂ := fun c => Quotient.lift t' (fun i j (h : t i = t j) => (key i j).1 h) c
  let Fκ : κ → ℍ → ℂ := fun c => Quotient.lift F (fun i j (h : t i = t j) => htF i j h) c
  have bij : ∀ (a : ι → SL(2, ℤ) → ι) (aκ : κ → SL(2, ℤ) → κ), ActBij a →
      (∀ i γ, aκ (Quotient.mk s i) γ = Quotient.mk s (a i γ)) → ActBij aκ := by
    intro a aκ hB hcomp γ
    rw [← Finite.surjective_iff_bijective]
    intro c
    induction c using Quotient.inductionOn with
    | h i =>
      obtain ⟨j, hj⟩ := (hB γ).2 i
      exact ⟨Quotient.mk s j, by simp only [hcomp, hj]⟩
  have hAκ : ActBij actκ := bij act actκ hA (fun _ _ => rfl)
  have hAκ' : ActBij actκ' := bij act' actκ' hA' (fun _ _ => rfl)
  have htκ : IsFam actκ m tκ := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact ht i γ
  have htκ' : IsFam actκ' m tκ' := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact ht' i γ
  have hFκ : IsFam actκ k Fκ := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact hF i γ
  have hinj : Function.Injective tκ := by
    intro c d h
    induction c using Quotient.inductionOn with
    | h i =>
      induction d using Quotient.inductionOn with
      | h j => exact (hs i j).2 h
  have hcκ : ∀ c, QConj g N (tκ c) (tκ' c) := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact hc i
  have hqκ : ∀ c, ∃ a, HasQ N (Fκ c) a := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact hq i
  obtain ⟨G, hG, hGc⟩ := GlobalTheory.T.exists_conjugate_family_of_injective g κ actκ actκ' m k N tκ tκ' Fκ hN hAκ hAκ' htκ htκ' hFκ hinj hcκ hqκ
  refine ⟨fun i => G (Quotient.mk s i), ?_, fun i => hGc (Quotient.mk s i)⟩
  intro i γ
  exact hG (Quotient.mk s i) γ

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_modularFamily_along_separatingFamily : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → (∀ i j, t i = t j → F i = F j) → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  atlas_forward_decl GlobalTheory.FN.conj_family_sep
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.WpSep

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 →
    wp N x τ = wp N y τ → x = y ∨ x = -y := by
  intro N _ τ x y hx hy h1
  obtain ⟨hsub, hadd, hmem, -, -⟩ := GlobalTheory.WpFam.TorsMem.main N τ
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hz : tors N τ x ∉ (tauPair τ).lattice := fun h => hx ((hmem x).1 h)
  have hw : tors N τ y ∉ (tauPair τ).lattice := fun h => hy ((hmem y).1 h)
  rw [wp, wp, div_left_inj' (pow_ne_zero _ hc)] at h1
  rcases (Formalism.L2.Th1.F.pInjective (tauPair τ) _ _ hz hw).1 h1 with h | h
  · exact Or.inl ((hsub x y).1 h)
  · right
    have h2 := (tauPair τ).lattice.add_mem (hadd x y) h
    rw [sub_add_cancel] at h2
    have h3 := (hmem (x + y)).1 h2
    exact eq_neg_of_add_eq_zero_left h3

end GlobalTheory.FN.WpSep
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 → wp N x τ = wp N y τ → x = y ∨ x = -y := by
  atlas_forward_decl GlobalTheory.FN.WpSep.main
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNSep

theorem finite_nat_roots (a b c : ℂ) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    {n : ℕ | a + (n : ℂ) * b + (n : ℂ) ^ 2 * c = 0}.Finite := by
  set P : Polynomial ℂ := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hPdef
  have hP : P ≠ 0 := by
    intro h0
    apply h
    have e0 := congrArg (fun q => q.coeff 0) h0
    have e1 := congrArg (fun q => q.coeff 1) h0
    have e2 := congrArg (fun q => q.coeff 2) h0
    simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  have hf := (Polynomial.finite_setOf_isRoot hP).preimage (f := (Nat.cast : ℕ → ℂ)) Nat.cast_injective.injOn
  refine hf.subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hn ⊢
  rw [Polynomial.IsRoot.def]
  simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  linear_combination hn

theorem vmul_apply {N : ℕ} (a b : ZMod N) (α : GL (Fin 2) (ZMod N)) (j : Fin 2) :
    vmul ![a, b] α j = a * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 j + b * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 j := by
  simp [vmul, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)) (hx : x ≠ 0) : vmul x α ≠ 0 := by
  intro h
  apply hx
  have : Matrix.vecMul (vmul x α) ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [vmul, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  rw [← this, h, Matrix.zero_vecMul]

end GlobalTheory.FNSep

namespace GlobalTheory.FNSep

theorem eq_or_eq_neg_of_rows {N : ℕ} (α β : GL (Fin 2) (ZMod N))
    (h0 : vmul ![1, 0] α = vmul ![1, 0] β ∨ vmul ![1, 0] α = -vmul ![1, 0] β)
    (h1 : vmul ![0, 1] α = vmul ![0, 1] β ∨ vmul ![0, 1] α = -vmul ![0, 1] β)
    (h2 : vmul ![1, 1] α = vmul ![1, 1] β ∨ vmul ![1, 1] α = -vmul ![1, 1] β) :
    α = β ∨ α = -β := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
  · have E0 : ∀ j, _ := fun j => congrFun h0 j
    have E1 : ∀ j, _ := fun j => congrFun h1 j
    have E2 : ∀ j, _ := fun j => congrFun h2 j
    simp only [Pi.neg_apply, vmul_apply] at E0 E1 E2
    first
    | (left; apply Units.ext; ext i j; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> first | linear_combination E0 j | linear_combination E1 j | linear_combination E2 j - E0 j | linear_combination E2 j - E1 j)
    | (right; apply Units.ext; ext i j; rw [Units.val_neg, Matrix.neg_apply]; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> first | linear_combination E0 j | linear_combination E1 j | linear_combination E2 j - E0 j | linear_combination E2 j - E1 j)

theorem sep_family : ∀ (N : ℕ) [NeZero N], ∃ c₁ c₂ : ℕ, ∀ α β : GL (Fin 2) (ZMod N), (fun τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ) = (fun τ => wp N (vmul ![1, 0] β) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] β) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] β) τ) → α = β ∨ α = -β := by
  intro N _
  classical
  let u : GL (Fin 2) (ZMod N) × GL (Fin 2) (ZMod N) → (Fin 2 → ZMod N) → ℍ → ℂ :=
    fun p e τ => wp N (vmul e p.1) τ - wp N (vmul e p.2) τ
  let S : Set ℕ := ⋃ p : GL (Fin 2) (ZMod N) × GL (Fin 2) (ZMod N),
    {n : ℕ | ¬ (∀ τ, u p ![1, 0] τ = 0 ∧ u p ![0, 1] τ = 0 ∧ u p ![1, 1] τ = 0) ∧
      ∀ τ, u p ![1, 0] τ + (n : ℂ) * u p ![0, 1] τ + (n : ℂ) ^ 2 * u p ![1, 1] τ = 0}
  have hfin : Finite (GL (Fin 2) (ZMod N)) :=
    Finite.of_injective (fun a : GL (Fin 2) (ZMod N) => (a : Matrix (Fin 2) (Fin 2) (ZMod N))) fun a b h => Units.ext h
  have hS : S.Finite := by
    refine Set.finite_iUnion fun p => ?_
    by_cases hz : ∀ τ, u p ![1, 0] τ = 0 ∧ u p ![0, 1] τ = 0 ∧ u p ![1, 1] τ = 0
    · exact Set.finite_empty.subset fun n hn => absurd hz hn.1
    · obtain ⟨τ, hτ⟩ := not_forall.mp hz
      exact (finite_nat_roots _ _ _ hτ).subset fun n hn => hn.2 τ
  obtain ⟨n, hn⟩ := hS.infinite_compl.nonempty
  refine ⟨n, n ^ 2, fun α β hfun => ?_⟩
  have hroot : ∀ τ, u (α, β) ![1, 0] τ + (n : ℂ) * u (α, β) ![0, 1] τ + (n : ℂ) ^ 2 * u (α, β) ![1, 1] τ = 0 := by
    intro τ
    have := congrFun hfun τ
    push_cast at this
    simp only [u]
    linear_combination this
  have hz : ∀ τ, u (α, β) ![1, 0] τ = 0 ∧ u (α, β) ![0, 1] τ = 0 ∧ u (α, β) ![1, 1] τ = 0 := by
    by_contra hz
    exact hn (Set.mem_iUnion.mpr ⟨(α, β), hz, hroot⟩)
  rcases Nat.lt_or_ge 1 N with hN | hN
  · haveI : Fact (1 < N) := ⟨hN⟩
    obtain ⟨z0, z1, z2⟩ := hz UpperHalfPlane.I
    have ne0 : (![1, 0] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    have ne1 : (![0, 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 1; simp at this
    have ne2 : (![1, 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    exact eq_or_eq_neg_of_rows α β
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne0) (vmul_ne_zero _ β ne0) (sub_eq_zero.mp z0))
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne1) (vmul_ne_zero _ β ne1) (sub_eq_zero.mp z1))
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne2) (vmul_ne_zero _ β ne2) (sub_eq_zero.mp z2))
  · have h1 : N = 1 := le_antisymm hN (Nat.pos_of_ne_zero (NeZero.ne N))
    subst h1
    left
    apply Units.ext
    ext i j
    exact Subsingleton.elim _ _

end GlobalTheory.FNSep
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weierstrassP_family_separating_gl2ZMod : ∀ (N : ℕ) [NeZero N], ∃ c₁ c₂ : ℕ, ∀ α β : GL (Fin 2) (ZMod N), (fun τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ) = (fun τ => wp N (vmul ![1, 0] β) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] β) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] β) τ) → α = β ∨ α = -β := by
  atlas_forward_decl GlobalTheory.FNSep.sep_family
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNConj

theorem slash_neg_one_even {k : ℤ} (hk : Even k) (f : ℍ → ℂ) : f ∣[k] (-1 : SL(2, ℤ)) = f := by
  ext τ
  simp only [ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, one_smul]
  have : UpperHalfPlane.denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = (-1) * UpperHalfPlane.denom ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := by
    simp [UpperHalfPlane.denom]
  rw [this, mul_zpow, (hk.neg).neg_one_zpow]
  simp [UpperHalfPlane.denom]

theorem redGL_neg_one (N : ℕ) : redGL N (-1) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redGL, Matrix.SpecialLinearGroup.coe_neg]

theorem redGL_gamma (N : ℕ) (γ : SL(2, ℤ)) (h : γ ∈ CongruenceSubgroup.Gamma N) : redGL N γ = 1 := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redGL, h00, h01, h10, h11]

end GlobalTheory.FNConj

namespace GlobalTheory.FNConj

theorem main : ∀ (g : ℂ ≃+* ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (k : ℕ) (f : ℍ → ℂ), ZetaAct g N d → Even k →
    (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[(k : ℤ)] γ = f) → (∀ γ : SL(2, ℤ), ∃ a, HasQ N (f ∣[(k : ℤ)] γ) a) →
    ∃ f' : ℍ → ℂ, (∀ γ ∈ CongruenceSubgroup.Gamma N, f' ∣[(k : ℤ)] γ = f') ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (f ∣[(k : ℤ)] γ) (f' ∣[(k : ℤ)] γ') := by
  intro g N _ d k f hg hk hinv hq
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hvact, hgact, hvass, -, -, -, -, -, -⟩ := GlobalTheory.WpFam.Act.rightActions N
  obtain ⟨c₁, c₂, hsep⟩ := GlobalTheory.T.exists_weierstrassP_family_separating_gl2ZMod N
  obtain ⟨-, hadd, hsmul, -⟩ := GlobalTheory.QFam.isFam_algebra (GL (Fin 2) (ZMod N)) (gact N 1)
  obtain ⟨-, hadd', hsmul', -⟩ := GlobalTheory.QFam.isFam_algebra (GL (Fin 2) (ZMod N)) (gact N (dg d))
  obtain ⟨qc, qadd, -, qmul, -⟩ := GlobalTheory.QFam.qConj_ring g N hN

  set t : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ +
    (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ with ht
  set t' : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α => t (α * dg d) with ht'
  have hw : ∀ e : Fin 2 → ZMod N, IsFam (gact N 1) 2 (fun α => wp N (vmul e α)) := fun e => by
    have := (GlobalTheory.WpFamGL.main N 1 e).1
    simpa only [mul_one] using this
  have hw' : ∀ e : Fin 2 → ZMod N, IsFam (gact N (dg d)) 2 (fun α => wp N (vmul e (α * dg d))) := fun e =>
    (GlobalTheory.WpFamGL.main N (dg d) e).1
  have htF : IsFam (gact N 1) 2 t :=
    (hadd _ _ _ (hadd _ _ _ (hw _) (hsmul _ _ _ (hw _))).1 (hsmul _ _ _ (hw _))).1
  have htF' : IsFam (gact N (dg d)) 2 t' :=
    (hadd' _ _ _ (hadd' _ _ _ (hw' _) (hsmul' _ _ _ (hw' _))).1 (hsmul' _ _ _ (hw' _))).1
  have hqw : ∀ (e : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)),
      QConj g N (wp N (vmul e α)) (wp N (vmul e (α * dg d))) := fun e α => by
    rw [← hvass]
    exact (GlobalTheory.WpFam.ConjExp.qConj_torsion N g d hg (vmul e α)).1
  have hqn : ∀ (c : ℕ) (e : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)),
      QConj g N (fun τ => (c : ℂ) * wp N (vmul e α) τ) (fun τ => (c : ℂ) * wp N (vmul e (α * dg d)) τ) := by
    intro c e α
    have := qmul _ _ _ _ (qc (c : ℂ)) (hqw e α)
    simpa only [map_natCast] using this
  have htq : ∀ α, QConj g N (t α) (t' α) := fun α =>
    qadd _ _ _ _ (qadd _ _ _ _ (hqw _ α) (hqn c₁ _ α)) (hqn c₂ _ α)

  obtain ⟨F, hF, hFγ, hF0⟩ := GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level N (k : ℤ) f hinv
  have hFneg : ∀ α, F (-α) = F α := fun α => by
    have h1 := hF α (-1)
    rw [slash_neg_one_even (by exact_mod_cast hk.natCast) (F α)] at h1
    rw [h1, gact_one, redGL_neg_one, mul_neg_one]
  have hsepF : ∀ i j, t i = t j → F i = F j := fun i j h => by
    rcases hsep i j h with rfl | rfl
    · rfl
    · exact hFneg j
  have hFq : ∀ i, ∃ a, HasQ N (F i) a := fun i => by
    rcases hF0 i with ⟨γ, rfl⟩ | h0
    · rw [hFγ]; exact hq γ
    · refine ⟨fun _ => 0, fun τ => ?_⟩
      rw [h0]; simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  obtain ⟨F', hF', hFF'⟩ := GlobalTheory.T.conjugate_modularFamily_along_separatingFamily g (GL (Fin 2) (ZMod N)) (gact N 1) (gact N (dg d)) 2 k N t t' F hN
    (IsRAct.actBij (hgact 1)) (IsRAct.actBij (hgact (dg d))) htF htF' hF hsepF htq hFq
  have hslash : ∀ γ : SL(2, ℤ), F' 1 ∣[(k : ℤ)] γ = F' (dg d * redGL N γ * (dg d)⁻¹) := fun γ => by
    rw [hF' 1 γ, gact, one_mul]
  refine ⟨F' 1, fun γ hγ => ?_, fun γ γ' hγγ' => ?_⟩
  · rw [hslash, redGL_gamma N γ hγ, mul_one, mul_inv_cancel]
  · rw [hslash, hγγ', mul_inv_cancel_right, ← hFγ]
    exact hFF' _

end GlobalTheory.FNConj
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shimuraReciprocity_conjugate_form_level : ∀ (g : ℂ ≃+* ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (k : ℕ) (f : ℍ → ℂ), ZetaAct g N d → Even k → (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[(k : ℤ)] γ = f) → (∀ γ : SL(2, ℤ), ∃ a, HasQ N (f ∣[(k : ℤ)] γ) a) → ∃ f' : ℍ → ℂ, (∀ γ ∈ CongruenceSubgroup.Gamma N, f' ∣[(k : ℤ)] γ = f') ∧ ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (f ∣[(k : ℤ)] γ) (f' ∣[(k : ℤ)] γ') := by
  atlas_forward_decl GlobalTheory.FNConj.main
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem lv_galois_conj : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ),
    (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d →
        QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  intro g E N _ d w f hE hZ hf
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set F : ℍ → ℂ := fun τ => DD τ ^ w * f τ with hFdef
  have hsl : ∀ (h : ℍ → ℂ) (γ : SL(2, ℤ)),
      ((fun τ => DD τ ^ w * h τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * h (γ • τ) :=
    fun h γ => GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul w h γ
  have hev : Even (12 * w) := ⟨6 * w, by ring⟩
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∣[((12 * w : ℕ) : ℤ)] γ = F := by
    intro γ hγ
    rw [hFdef, hsl]
    funext τ
    rw [hf.1 γ hγ τ]
  have hq : ∀ γ : SL(2, ℤ), ∃ a, HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) a := by
    intro γ
    obtain ⟨a, ha, -⟩ := hf.2 γ
    exact ⟨a, by rw [hFdef, hsl]; exact ha⟩
  obtain ⟨F', hF'inv, hF'c⟩ := GlobalTheory.T.shimuraReciprocity_conjugate_form_level g N d (12 * w) F hZ hev hinv hq
  refine ⟨fun τ => F' τ / DD τ ^ w, ?_, ?_⟩
  · have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * (F' (γ • τ) / DD (γ • τ) ^ w)) =
        F' ∣[((12 * w : ℕ) : ℤ)] γ := by
      intro γ
      have := hsl (fun τ => F' τ / DD τ ^ w) γ
      rw [hF'eq] at this
      exact this.symm
    refine ⟨fun γ hγ τ => ?_, fun γ' => ?_⟩
    · have h1 := congrFun (key γ) τ
      rw [hF'inv γ hγ] at h1
      have h2 := congrFun hF'eq τ
      have hne := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      exact mul_left_cancel₀ hne (h1.trans h2.symm)
    · obtain ⟨γ, hγ⟩ := (GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod N d).2 γ'
      obtain ⟨a, ha, ha'⟩ := hF'c γ γ' hγ
      obtain ⟨b, hb, hbE⟩ := hf.2 γ
      have hb' : HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) b := by rw [hFdef, hsl]; exact hb
      have hab : a = b := GlobalTheory.QFam.hasQ_unique_both.1 N _ a b hN ha hb'
      refine ⟨fun n => g (a n), ?_, fun n => ?_⟩
      · rw [key γ']; exact ha'
      · rw [hab]; exact hE _ (hbE n)
  · intro γ γ' hγ
    have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w)) = F' ∣[((12 * w : ℕ) : ℤ)] γ' := by
      have := hsl (fun τ => F' τ / DD τ ^ w) γ'
      rw [hF'eq] at this
      exact this.symm
    have kf : (fun τ => DD τ ^ w * f (γ • τ)) = F ∣[((12 * w : ℕ) : ℤ)] γ := by rw [hFdef, hsl]
    show QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w))
    rw [key, kf]
    exact hF'c γ γ' hγ

end GlobalTheory.FN
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelN_function_galois_conj_qExpansion : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ), (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧ ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  atlas_forward_decl GlobalTheory.FN.lv_galois_conj
end
