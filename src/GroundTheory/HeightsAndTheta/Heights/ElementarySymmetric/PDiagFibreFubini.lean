import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def wwLinPot {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (X₀ X₁ A₀ : HermLine ι) (k : ℕ)
    (u : ℕ → Fin 2 → ℝ) : Fin e → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z =>
    if (j : ℕ) < 2 * k then u j 0 * Real.log (X₀.h z) + u j 1 * Real.log (X₁.h z) else Real.log (A₀.h z)

def wwLinProd (k : ℕ) (u : ℕ → Fin 2 → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∏ n ∈ Finset.range (2 * k), (C (u n 0) * X 0 + C (u n 1) * X 1)

def wwFibreMoment (w : S2 × S2 → ℝ) (Q : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure) w
    (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] (pderiv 0 (pderiv 1 Q)))

def wwLogWeight (p : S2 × S2) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2)

def WWFibrePoly.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      ∃ Λ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ, ∀ u : ℕ → Fin 2 → ℝ,
        ptsIntegral S.WW (wwLinPot (e := D + 1) X₀ X₁ A₀ k u) (diagLogNorm S.g S.h X₀ X₁) =
            2 ^ (2 * k) * Λ (wwFibreMoment wwLogWeight (wwLinProd k u)) ∧
          ptsIntegral S.WW (wwLinPot (e := D + 1) X₀ X₁ A₀ k u) (fun _ => 1) =
            2 ^ (2 * k) * Λ (wwFibreMoment (fun _ => 1) (wwLinProd k u))

end

end GroundTheory.Heights₂.Heights.Inter
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def DiagFibreMoment.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      ∑ i ∈ Finset.range k, diagInt S.WW S.g S.h X₀ X₁ (word D k i X₀ X₁ A₀) =
        -kappa k * ptsIntegral S.WW
          (pot (Fin.cons X₀ (mix (2 * k - 1) X₁ A₀ : Fin D → HermLine S.WIdx) : Fin (D + 1) → HermLine S.WIdx))
          (fun _ => 1)

end

end GroundTheory.Heights₂.Heights.Inter
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def diagWordMomentPoly (k i : ℕ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure)
    (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
    (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd]
      (pderiv 0 (pderiv 1 ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ))))

def DiagFibreFubini.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      ∃ Λ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ,
        (∀ i < k, diagInt S.WW S.g S.h X₀ X₁ (word D k i X₀ X₁ A₀) =
          2 ^ (2 * k) * Λ (diagWordMomentPoly k i)) ∧
        ptsIntegral S.WW
            (pot (Fin.cons X₀ (mix (2 * k - 1) X₁ A₀ : Fin D → HermLine S.WIdx) : Fin (D + 1) → HermLine S.WIdx))
            (fun _ => 1) =
          -(2 ^ (2 * k) * Λ (pushMomentPoly k))

end

end GroundTheory.Heights₂.Heights.Inter
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagFibreMoment

theorem coeff_momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) (m : Fin 3 →₀ ℕ) :
    coeff m (momentPoly μ w Q) = ∫ p, w p * coeff m Q p ∂μ := by
  rw [momentPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h]
    simp

theorem momentPoly_sum {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ) (s : Finset ι)
    (Q : ι → MvPolynomial (Fin 3) (Ω → ℝ)) (hQ : ∀ i ∈ s, ∀ m, Integrable (fun p => w p * coeff m (Q i) p) μ) :
    momentPoly μ w (∑ i ∈ s, Q i) = ∑ i ∈ s, momentPoly μ w (Q i) := by
  ext m
  rw [coeff_momentPoly, coeff_sum, coeff_sum]
  simp only [coeff_momentPoly, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => hQ i hi m

theorem continuous_coeff_aeval (Q : MvPolynomial (Fin 2) ℝ) (m : Fin 3 →₀ ℕ) :
    Continuous (coeff m (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) := by
  set φ : C(S2 × S2, ℝ) →ₐ[ℝ] (S2 × S2 → ℝ) := ContinuousMap.coeFnAlgHom (α := S2 × S2) (A := ℝ) ℝ
  set v : Fin 2 → MvPolynomial (Fin 3) C(S2 × S2, ℝ) :=
    ![∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.fst),
      ∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.snd)]
  have hv : ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] = fun r => mapAlgHom φ (v r) := by
    funext r
    fin_cases r
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, v, dotPoly, mapAlgHom_apply, map_sum, map_mul, map_X, map_C]
      rfl
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, v, dotPoly, mapAlgHom_apply, map_sum,
        map_mul, map_X, map_C]
      rfl
  rw [hv, ← comp_aeval, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]
  exact (coeff m (aeval v Q)).continuous

theorem sum_words (k : ℕ) :
    ∑ i ∈ Finset.range k, ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ) =
      gPoly k := by
  rw [FibreLocal.gPoly_eq, FlagBundles.gKernel]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  rw [show 2 * k - 2 * i = (2 * k - 1 - 2 * i) + 1 by omega, pow_succ, pow_succ]
  ring

theorem sum_diagWordMomentPoly (k : ℕ) :
    ∑ i ∈ Finset.range k, diagWordMomentPoly k i = fibreMomentPoly k := by
  simp only [diagWordMomentPoly]
  rw [← momentPoly_sum _ _ _ _ fun i _ m =>
    FibreLocal.integrable_mul _ (continuous_coeff_aeval _ m)]
  rw [← map_sum, ← map_sum, ← map_sum, sum_words]
  rfl

theorem fibreMomentPoly_eq (k : ℕ) :
    fibreMomentPoly k = C (-kappa k) * (∑ i, X i ^ 2) ^ (k - 1) := by
  have h := FibreLocal.proof.2.1 k (MvPolynomial (Fin 3) ℝ) X
  rwa [aeval_X_left_apply, MvPolynomial.algebraMap_eq] at h

theorem proof (h : DiagFibreFubini.Statement) : DiagFibreMoment.Statement := by
  intro D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  obtain ⟨Λ, hw, hp⟩ := h D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  rw [Finset.sum_congr rfl fun i hi => hw i (Finset.mem_range.1 hi), ← Finset.mul_sum, ← map_sum,
    sum_diagWordMomentPoly, fibreMomentPoly_eq, hp, FibreLocal.pushMomentPoly_eq k hk, C_mul', map_smul,
    map_neg, smul_eq_mul]
  ring

end DiagFibreMoment

end

end GroundTheory.Heights₂.Heights.Inter
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagonalFibreFubini

def wordCoef (i : ℕ) : ℕ → Fin 2 → ℝ := fun n =>
  if n = 0 then ![1, -1] else if n = 1 then ![0, 1] else if n < 2 + 2 * i then ![1, 0] else ![0, 1]

def topCoef : ℕ → Fin 2 → ℝ := fun n => if n = 0 then ![1, 0] else ![0, 1]

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem cons_pot_word (D k i : ℕ) (hik : i < k) (X₀ X₁ A₀ : HermLine ι) :
    (Fin.cons (α := fun _ => ((Σ k, ι k) → ℂ) → ℝ) (fun z => Real.log (X₀.h z) - Real.log (X₁.h z))
        (pot (word D k i X₀ X₁ A₀)) : Fin (D + 1) → ((Σ k, ι k) → ℂ) → ℝ) =
      wwLinPot X₀ X₁ A₀ k (wordCoef i) := by
  funext j z
  refine Fin.cases ?_ (fun j => ?_) j
  · have h0 : (0 : ℕ) < 2 * k := by omega
    simp [wwLinPot, wordCoef, h0]
    ring
  · simp only [Fin.cons_succ, pot, word, wwLinPot, wordCoef, Fin.val_succ]
    split_ifs <;> first | contradiction | omega | simp

theorem linProd_word (k i : ℕ) (hik : i < k) :
    wwLinProd k (wordCoef i) = (X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * k = 2 + 2 * i + r := ⟨2 * k - 2 - 2 * i, by omega⟩
  rw [wwLinProd, hr, Finset.prod_range_add, Finset.prod_range_add]
  have h1 : ∏ x ∈ Finset.range 2, (C (wordCoef i x 0) * X 0 + C (wordCoef i x 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
      (X 0 - X 1) * X 1 := by
    simp [Finset.prod_range_succ, wordCoef]
    ring
  have h2 : ∏ x ∈ Finset.range (2 * i),
      (C (wordCoef i (2 + x) 0) * X 0 + C (wordCoef i (2 + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) = X 0 ^ (2 * i) := by
    rw [← Finset.card_range (2 * i), ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x hx => ?_
    have hx' : x < 2 * i := Finset.mem_range.1 hx
    simp [wordCoef, show 2 + x ≠ 1 by omega, show 2 + x < 2 + 2 * i by omega]
  have h3 : ∏ x ∈ Finset.range r,
      (C (wordCoef i (2 + 2 * i + x) 0) * X 0 + C (wordCoef i (2 + 2 * i + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
        X 1 ^ r := by
    rw [← Finset.card_range r, ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x _ => ?_
    simp [wordCoef, show 2 + 2 * i + x ≠ 1 by omega,
      show ¬ 2 + 2 * i + x < 2 + 2 * i by omega]
  rw [h1, h2, h3, show 2 + 2 * i + r - 1 - 2 * i = r + 1 by omega, pow_succ]
  ring

theorem cons_pot_top (D k : ℕ) (hk : 1 ≤ k) (X₀ X₁ A₀ : HermLine ι) :
    pot (Fin.cons X₀ (mix (2 * k - 1) X₁ A₀ : Fin D → HermLine ι) : Fin (D + 1) → HermLine ι) =
      wwLinPot X₀ X₁ A₀ k topCoef := by
  funext j z
  refine Fin.cases ?_ (fun j => ?_) j
  · have h0 : (0 : ℕ) < 2 * k := by omega
    simp [pot, wwLinPot, topCoef, h0]
  · simp only [pot, Fin.cons_succ, mix, wwLinPot, topCoef, Fin.val_succ]
    split_ifs <;> first | contradiction | omega | simp

theorem linProd_top (k : ℕ) (hk : 1 ≤ k) : wwLinProd k topCoef = X 0 * X 1 ^ (2 * k - 1) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * k = 1 + r := ⟨2 * k - 1, by omega⟩
  rw [wwLinProd, hr, Finset.prod_range_add, show 1 + r - 1 = r by omega]
  have h1 : ∏ x ∈ Finset.range 1, (C (topCoef x 0) * X 0 + C (topCoef x 1) * X 1 : MvPolynomial (Fin 2) ℝ) = X 0 := by
    simp [topCoef]
  have h2 : ∏ x ∈ Finset.range r, (C (topCoef (1 + x) 0) * X 0 + C (topCoef (1 + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
      X 1 ^ r := by
    rw [← Finset.card_range r, ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x _ => ?_
    simp [topCoef]
  rw [h1, h2]

theorem pderiv_top (N : ℕ) :
    pderiv 0 (pderiv 1 (X 0 * X 1 ^ (N + 1) : MvPolynomial (Fin 2) ℝ)) = C ((N + 1 : ℕ) : ℝ) * X 1 ^ N := by
  simp [Derivation.leibniz, Derivation.leibniz_pow]

def sndHom : (S2 → ℝ) →+* (S2 × S2 → ℝ) :=
  RingHom.pi fun p => Pi.evalRingHom (fun _ : S2 => ℝ) p.2

theorem dotPoly_snd : dotPoly (Prod.snd : S2 × S2 → S2) = map sndHom (dotPoly (id : S2 → S2)) := by
  simp only [dotPoly, map_sum, map_mul, map_X, map_C]
  rfl

theorem moment_top (k : ℕ) (hk : 1 ≤ k) :
    wwFibreMoment (fun _ => 1) (X 0 * X 1 ^ (2 * k - 1)) = -pushMomentPoly k := by
  have := FibreLocal.isProbabilityMeasure_sphere
  obtain ⟨N, hN⟩ : ∃ N, 2 * k - 1 = N + 1 := ⟨2 * k - 2, by omega⟩
  have hN2 : 2 * k - 2 = N := by omega
  have hc : ((N + 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    have h2 : ((N + 1 + 1 : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) := by rw [show N + 1 + 1 = 2 * k by omega]
    push_cast at h2 ⊢
    linarith
  rw [wwFibreMoment, hN, pderiv_top, pushMomentPoly, hN2]
  ext m
  rw [DiagFibreMoment.coeff_momentPoly, coeff_neg, coeff_smul, DiagFibreMoment.coeff_momentPoly]
  have hpt : ∀ p : S2 × S2,
      coeff m (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd]
        (C ((N + 1 : ℕ) : ℝ) * X 1 ^ N : MvPolynomial (Fin 2) ℝ)) p =
        ((N + 1 : ℕ) : ℝ) * coeff m (dotPoly (id : S2 → S2) ^ N) p.2 := by
    intro p
    rw [map_mul, aeval_C, map_pow, aeval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, dotPoly_snd, ← map_pow,
      MvPolynomial.algebraMap_apply, coeff_C_mul, coeff_map]
    rfl
  simp_rw [hpt]
  have hsnd := integral_fun_snd (μ := sphereMeasure) (ν := sphereMeasure)
    (fun y : S2 => (1 : ℝ) * (((N + 1 : ℕ) : ℝ) * coeff m (dotPoly (id : S2 → S2) ^ N) y))
  rw [hsnd, probReal_univ, one_smul]
  simp only [one_mul, smul_eq_mul]
  rw [integral_const_mul, hc]
  ring

end DiagonalFibreFubini

open DiagonalFibreFubini in

theorem DiagFibreFubini.proof (h : WWFibrePoly.Statement) : DiagFibreFubini.Statement := by
  intro D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  obtain ⟨Λ, hΛ⟩ := h D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  refine ⟨Λ, fun i hi => ?_, ?_⟩
  · rw [diagInt, cons_pot_word D k i hi, (hΛ _).1, linProd_word k i hi]
    rfl
  · rw [cons_pot_top D k hk, (hΛ _).2, linProd_top k hk, moment_top k hk, map_neg]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end
