import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormUnitPair
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaSpherical
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialGaloisPlaceDegreeTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SummableUnitBounds.SBoundOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizationPureIntegrand

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WeilPsi

theorem choose_congr {α : Type*} {p q : α → Prop} (hpq : p = q) (hp : ∃ a, p a) (hq : ∃ a, q a) :
    hp.choose = hq.choose := by
  subst hpq
  rfl

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem unipotent_mul_val_real (x : F) (g : GL (Fin 2) F) :
    (uni2 x * g).val =
      !![g.val 0 0 + x * g.val 1 0, g.val 0 1 + x * g.val 1 1; g.val 1 0, g.val 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_left_unipotent_mul (x : F) (g : GL (Fin 2) F) : ((uni2 x * g).val).det = (g.val).det := by
  rw [unipotent_mul_val_real, Matrix.det_fin_two_of, Matrix.det_fin_two g.val]
  ring

theorem rW_shift (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d x : F)
    (hc0 : c = 0 → a * d = 1) (Φ : E → ℂ) :
    rW χ σ μE lam (a + x * c) (b + x * d) c d Φ 1 = (χ x : ℂ) * rW χ σ μE lam a b c d Φ 1 := by
  by_cases hc : c = 0
  · have had := hc0 hc
    subst hc
    have h1 : a * (b + x * d) * Algebra.norm F (1 : E) = x + a * b * Algebra.norm F (1 : E) := by
      rw [map_one]
      linear_combination x * had
    simp only [rW, if_true, mul_zero, add_zero]
    rw [h1, AddChar.map_add_eq_mul]
    push_cast
    ring
  · have hk : ∀ u : E,
        ((χ (((a + x * c) * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c) : Circle) : ℂ) * Φ u =
          (χ x : ℂ) * (((χ ((a * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c) : Circle) : ℂ) * Φ u) := by
      intro u
      have h2 : ((a + x * c) * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c =
          x + (a * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c := by
        rw [map_one]
        field_simp
        ring
      rw [h2, AddChar.map_add_eq_mul]
      push_cast
      ring
    simp only [rW, if_neg hc, hk]
    rw [integral_const_mul]
    ring

theorem weil_whittaker_unipotent_equivariance (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ)
    (Φ : E → ℂ) (x : F) (g : GL (Fin 2) F) :
    Wc χ σ μE lam c Φ (uni2 x * g) = (χ x : ℂ) * Wc χ σ μE lam c Φ g := by
  have hdet := det_left_unipotent_mul x g
  have hΔ : (g.val).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g.val).1 g.isUnit).ne_zero
  unfold Wc
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · have h' : ∃ t : Eˣ, Algebra.norm F (t : E) = ((uni2 x * g).val).det := by rwa [hdet]
    rw [dif_pos h', dif_pos h]
    have hch : h'.choose = h.choose :=
      choose_congr (by simp only [hdet]) h' h
    have e00 : (uni2 x * g).val 0 0 = g.val 0 0 + x * g.val 1 0 := by
      rw [unipotent_mul_val_real]; simp
    have e01 : (uni2 x * g).val 0 1 = g.val 0 1 + x * g.val 1 1 := by
      rw [unipotent_mul_val_real]; simp
    have e10 : (uni2 x * g).val 1 0 = g.val 1 0 := by
      rw [unipotent_mul_val_real]; simp
    have e11 : (uni2 x * g).val 1 1 = g.val 1 1 := by
      rw [unipotent_mul_val_real]; simp
    have hsplit : (g.val 0 0 + x * g.val 1 0) / (g.val).det =
        g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det) := by
      ring
    have hc0 : g.val 1 0 / (g.val).det = 0 → g.val 0 0 / (g.val).det * g.val 1 1 = 1 := by
      intro h0
      have hC : g.val 1 0 = 0 := by
        rcases div_eq_zero_iff.1 h0 with h1 | h1
        · exact h1
        · exact absurd h1 hΔ
      have hD : (g.val).det = g.val 0 0 * g.val 1 1 := by
        rw [Matrix.det_fin_two g.val, hC]
        ring
      rw [div_mul_eq_mul_div, ← hD]
      exact div_self hΔ
    rw [hch, hdet, e00, e01, e10, e11, hsplit,
      rW_shift χ σ μE lam _ _ _ _ x hc0]
    ring
  · have h' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((uni2 x * g).val).det := by rwa [hdet]
    rw [dif_neg h', dif_neg h, mul_zero]

end

theorem wPsi : Ad3.K.GL2LocalData.WPsi := by
  unfold Ad3.K.GL2LocalData.WPsi Ad3.K.GL2LocalData.ForEF
  intro F _ _ _ _ _ _ _ χ _ _ E _ _ _ _ _ _ _ _ _ σ _ η _ c Φ x g
  exact weil_whittaker_unipotent_equivariance χ σ _ _ c Φ x g

end GlobalTheory.CompanionTheory.WeilPsi
end
end

section
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open Ad3 Ad3.K GlobalTheory.CompanionTheory.WeilSplit

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSplit.Uni

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem rW_shift {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d x : F)
    (Φ : E → ℂ) (z : E) (hz : Algebra.norm F z = 1) (hc : c = 0 → a * d = 1) :
    GL2LocalData.rW χ σ μE lam (a + x * c) (b + x * d) c d Φ z =
      (χ x : ℂ) * GL2LocalData.rW χ σ μE lam a b c d Φ z := by
  unfold GL2LocalData.rW
  by_cases h0 : c = 0
  · have had := hc h0
    subst h0
    simp only [if_true, mul_zero, add_zero, hz, mul_one]
    have e : a * (b + x * d) = a * b + x := by
      linear_combination x * had
    rw [e, AddChar.map_add_eq_mul]
    push_cast
    ring
  · rw [if_neg h0, if_neg h0]
    have key : ∀ u : E, (χ (((a + x * c) * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ)
        = (χ x : ℂ) * (χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) := by
      intro u
      have e : ((a + x * c) * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c
          = x + (a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c := by
        rw [hz]; field_simp; ring
      rw [e, AddChar.map_add_eq_mul]
      push_cast
      rfl
    simp only [key, mul_assoc]
    rw [integral_const_mul]
    ring

theorem unipotent_mul_val_real (x : F) (g : GL (Fin 2) F) :
    (uni2 x * g).val 0 0 = g.val 0 0 + x * g.val 1 0 ∧ (uni2 x * g).val 0 1 = g.val 0 1 + x * g.val 1 1 ∧
    (uni2 x * g).val 1 0 = g.val 1 0 ∧ (uni2 x * g).val 1 1 = g.val 1 1 := by
  simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_unipotent_mul (x : F) (g : GL (Fin 2) F) : (uni2 x * g).val.det = g.val.det := by
  obtain ⟨h1, h2, h3, h4⟩ := unipotent_mul_val_real x g
  rw [Matrix.det_fin_two, Matrix.det_fin_two, h1, h2, h3, h4]
  ring

theorem split_weil_whittaker_unipotent_equivariant (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Φ : F × F → ℂ) (x : F)
    (g : GL (Fin 2) F) :
    GL2LocalData.WcS χ c₁ c₂ Φ (uni2 x * g) = (χ x : ℂ) * GL2LocalData.WcS χ c₁ c₂ Φ g := by
  obtain ⟨h1, h2, h3, h4⟩ := unipotent_mul_val_real x g
  have hd := det_unipotent_mul x g
  have hdet : Matrix.GeneralLinearGroup.det (uni2 x * g) = Matrix.GeneralLinearGroup.det g := by
    ext; simpa using hd
  have hΔ : (g.val).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).ne_zero
    simpa using this
  unfold GL2LocalData.WcS
  rw [hdet, hd, h1, h2, h3, h4]
  have e : (g.val 0 0 + x * g.val 1 0) / (g.val).det = g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det) := by
    ring
  rw [e]
  have hc : g.val 1 0 / (g.val).det = 0 → g.val 0 0 / (g.val).det * g.val 1 1 = 1 := by
    intro h
    have h0 : g.val 1 0 = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h hΔ
    rw [Matrix.det_fin_two, h0] at hΔ ⊢
    field_simp
    simp
  have hint : ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1
        (g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det)) (g.val 0 1 + x * g.val 1 1)
        (g.val 1 0 / (g.val).det) (g.val 1 1) (fun y => Φ (y * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) =
      (χ x : ℂ) * GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1
        (g.val 0 0 / (g.val).det) (g.val 0 1)
        (g.val 1 0 / (g.val).det) (g.val 1 1) (fun y => Φ (y * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) :=
    fun u => rW_shift χ _ _ 1 _ _ _ _ x _ _ (norm_unit_pair u) hc
  simp only [hint, mul_assoc]
  rw [integral_const_mul]
  ring

end GlobalTheory.CompanionTheory.WeilSplit.Uni
end
end

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WeilSplit.SplitAdditiveCharacter

theorem sPsi : Ad3.K.GL2LocalData.SPsi := by
  intro F _ _ _ _ _ _ _ χ _ _ c₁ c₂ Φ x g
  exact GlobalTheory.CompanionTheory.WeilSplit.Uni.split_weil_whittaker_unipotent_equivariant F χ c₁ c₂ Φ x g

end GlobalTheory.CompanionTheory.WeilSplit.SplitAdditiveCharacter
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.GlobalWhittakerPsi

abbrev eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

theorem unipotent_mul_val_real (x : ℝ) (g : GL (Fin 2) ℝ) :
    (uni2 x * g).val = !![g.val 0 0 + x * g.val 1 0, g.val 0 1 + x * g.val 1 1; g.val 1 0, g.val 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem local_whittaker_unipotent_character {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    {c : HeckeCharacter K} {v : Pl} (M : LM c v) (hok : M.ok) (x : Qv v) (g : GL (Fin 2) (Qv v)) :
    M.W (uni2 x * g) = (((GP.psiF v)⁻¹ x : Circle) : ℂ) * M.W g := by
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases M with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    exact GlobalTheory.CompanionTheory.WeilSplit.SplitAdditiveCharacter.sPsi (Qv v) _ hχc hχ1 _ _ Φ x g
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨-, hσ, hη, -⟩ := hok
    exact GlobalTheory.CompanionTheory.WeilPsi.wPsi (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη _ Φ x g

theorem LM_W_sph {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    {c : HeckeCharacter K} {v : Pl} (M : LM c v) (hok : M.ok) (hU : Unr c v) (hs : M.std) :
    SphN M.W := by
  refine GlobalTheory.CompanionTheory.StdSph.stdTh_sphN K h2 c v hU _ ?_
  cases M with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    obtain rfl : Φ = _ := hs
    exact Or.inl ⟨w₁, w₂, i₁, i₂, hok.1, rfl⟩
  | @ns w i σ η Φ =>
    obtain rfl : Φ = _ := hs
    exact Or.inr ⟨w, i, hok.1, σ, η, hok.2.1, hok.2.2.1, rfl⟩

theorem finiteComponent_unipotent (v : Pl) (x : 𝔸[ℚ]) : finAt v (uni2 x) = uni2 (x.2 v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, GroundTheory.Automorphic.Reduction.finAt_apply] <;> rfl

theorem realPart_unipotent_adele (x : 𝔸[ℚ]) :
    GL2Classical.realPart (uni2 x) = uni2 (GP.eR (x.1 GP.wR)) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change RationalIdeles.realEquiv ((uni2 x : GL (Fin 2) 𝔸[ℚ]) i j).1 = _
  fin_cases i <;> fin_cases j <;> simp [uni2]
  all_goals first | exact (GlobalTheory.CompanionTheory.GL2Factorization.PT.eR_eq _).symm | exact Prod.fst_one | rfl

end GlobalTheory.CompanionTheory.GlobalWhittakerPsi
end
end
