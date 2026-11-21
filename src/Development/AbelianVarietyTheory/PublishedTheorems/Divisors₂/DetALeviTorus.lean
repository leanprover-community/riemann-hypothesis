import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreInducedUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreFiniteUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotIsConstTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published.LeviCentreModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F) in

def big (δ : E) : Spc F E 3 := ⟨!![0, 0, 1; 0, δ, 0; -1, 0, 0], ⊥, fun _ => 1, fun _ => 1⟩

variable (F) in

def small (δ : E) : Spc F E 1 := ⟨!![δ], ⊥, fun _ => 1, fun _ => 1⟩

variable (E) in

def pl : Plane E 3 1 := ⟨![1, 0, 0], ![0, 0, 1], !![0; 1; 0], 1⟩

def detA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J →* AE F E :=
  Matrix.detMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))






open Matrix GlobalTheory.LeviUnitary in

theorem exists_levi (hcm : IsCMExt F E σ) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hsk : ∀ i j, σ (W.J j i) = -W.J i j)
    (horth : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0)
    (hgram : H'.ιᵀ * W.J * H'.ι.map σ = W₁.J) (hd : W₁.J.det ≠ 0) (h₁ : UA σ W₁.J) :
    ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' 1 h₁ m := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hdet : IsUnit W₁.J.det := hd.isUnit
  obtain ⟨π, p1, p2, p3, p4, p5⟩ : ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧ W.J * H'.ι.map σ = πᵀ * W₁.J ∧
      H'.ιᵀ * W.J = W₁.J * π.map σ ∧ π *ᵥ H'.x = 0 ∧ π *ᵥ H'.y = 0 := by
    have mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (A.map σ).map σ = A := fun A => by
      ext i j; exact hσ _
    have mul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E),
        (A * A').map σ = A.map σ * A'.map σ := fun A A' => Matrix.map_mul (f := σ.toRingHom)
    have sk : W.J.map σ = -W.Jᵀ := by ext i j; exact hsk j i
    have sk₁ : W₁.J.map σ = -W₁.Jᵀ := by
      rw [← hgram, mul, mul, mm, sk, transpose_mul, transpose_mul, transpose_transpose]
      simp [Matrix.mul_assoc, Matrix.transpose_map]
    set P : Matrix (Fin d₁) (Fin d) E := W₁.J⁻¹ * (H'.ιᵀ * W.J) with hP
    have h2 : H'.ιᵀ * W.J = W₁.J * P := by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
    have hz : ∀ z : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) z = 0) → P.map σ *ᵥ z = 0 := by
      intro z hz
      have e1 : (H'.ιᵀ * W.J) *ᵥ (fun i => σ (z i)) = 0 := by
        funext j
        have := hz (Pi.single j 1)
        rw [form, mulVec_single_one] at this
        rw [← mulVec_mulVec]
        exact this
      have e2 : P *ᵥ (fun i => σ (z i)) = 0 := by rw [hP, ← mulVec_mulVec, e1, mulVec_zero]
      funext j
      have := congrArg σ (congrFun e2 j)
      simpa [mulVec, dotProduct, map_sum, map_mul, hσ] using this
    refine ⟨P.map σ, ?_, ?_, by rw [mm, h2], hz _ fun u => (horth u).1, hz _ fun u => (horth u).2⟩
    · have : P * H'.ι.map σ = 1 := by rw [hP, Matrix.mul_assoc, hgram, Matrix.nonsing_inv_mul _ hdet]
      rw [← mm H'.ι, ← mul, this]
      exact Matrix.map_one _ (map_zero σ) (map_one σ)
    · have := congrArg (fun A => (Matrix.map A σ)ᵀ) h2
      simp only [mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg,
        neg_inj] at this
      exact this
  have q1 : incM F π * incM F H'.ι = 1 := by
    rw [← incM_mul, p1]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F W₁.J := by
    rw [incM_conj, ← incM_mul, p2, incM_mul]; rfl
  have q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map (cA σ).toRingHom := by
    rw [incM_conj, ← incM_mul, ← p3, incM_mul]; rfl
  have hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) *ᵥ incV F z = incV F z := by
    intro z hz
    have h0 : incV F (0 : Fin d₁ → E) = 0 := by funext i; exact map_zero _
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]
  refine ⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * incM F π, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [ext_mul q1, mat, Units.mul_inv]; simp
  · rw [ext_mul q1, mat, Units.inv_mul]; simp
  · exact ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2
  · rw [Units.val_one, one_smul]; exact hfix _ p4
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hfix _ p5
  · show (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) * incM F H'.ι = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

theorem exists_anti (hσ : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hs := GlobalTheory.SiegelSet.sigma_sigma hσ
  haveI := hσ.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_contra hcon
  push Not at hcon
  have : ∀ x, σ x = x := fun x => by
    by_contra hx
    exact hcon (x - σ x) (sub_ne_zero.2 (Ne.symm hx)) (by rw [map_sub, hs]; ring)
  exact IsTotallyComplex.complexEmbedding_not_isReal τ
    (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
      have := hσ.2.2.2 τ x
      rw [‹∀ x, σ x = x› x] at this
      simpa using this.symm))

example (hσ : IsCMExt F E σ) {δ : E} (hJ : IsHermND σ (δ • (small F δ).J.map σ)) :
    ∃ φ₁ : GAd σ (δ • (small F δ).J.map σ) → ℂ, GlobalTheory.UAut.IsSm σ _ φ₁ ∧ ¬ FiniteDimensional ℂ (Submodule.span ℂ
      {u | ∃ z, GlobalTheory.UAut.IsCentral σ (δ • (small F δ).J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ₁}) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  exact ⟨_, GlobalTheory.UAut.Model.not_zfin_exp hσ hJ τ 0⟩

end GlobalTheory.Published.LeviCentreModel

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Published.LeviCentreModel

namespace GlobalTheory.Published.LeviInducedModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_conj (hσ : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (a : AE F E) :
    piInf τ (cA σ a) = starRingEnd ℂ (piInf τ a) := by
  change _ = starRingEnd ℂ (infEmb τ _)
  rw [infEmb_sigR hσ]
  change infEmb τ _ = _
  congr 1
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem cont_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ : AE F E → ℂ) := by
  let L : AE F E →+ ℂ := (piInf τ).toAddMonoidHom
  refine IsModuleTopology.continuous_of_distribMulActionHomₑ (R := AF F) (σ := (piInf τ).toMonoidHom.comp (algebraMap (AF F) (AE F E)).toMonoidHom) ?_
    { L with map_smul' := fun r x => by simp [L, Algebra.smul_def] }
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst) |>.congr fun a => by
    change _ = infEmb τ (_ ⊗ₜ[F] (1 : E))
    rw [infEmb_tmul, map_one, mul_one]; rfl

def chi (hσ : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) : Chr F E where
  toFun t := ⟨piInf τ (t.1 * cA σ (t⁻¹).1), by
    have : piInf τ t.1 * piInf τ (t⁻¹).1 = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrArg norm this
    simpa [Submonoid.unitSphere, piInf_conj hσ] using h2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change piInf τ ((a * b).1 * cA σ ((a * b)⁻¹).1) = piInf τ (a.1 * cA σ (a⁻¹).1) * piInf τ (b.1 * cA σ (b⁻¹).1)
    simp only [mul_inv_rev, Units.val_mul, map_mul]; ring)



example (hσ : IsCMExt F E σ) {δ : E} (hJ : IsHermND σ (δ • (big F δ).J.map σ)) :
    ∃ φ : GAd σ (δ • (big F δ).J.map σ) → ℂ, GlobalTheory.UAut.IsSm σ _ φ ∧ ¬ FiniteDimensional ℂ (Submodule.span ℂ
      {u | ∃ z, GlobalTheory.UAut.IsCentral σ (δ • (big F δ).J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ}) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  exact ⟨_, GlobalTheory.UAut.Model.not_zfin_exp hσ hJ τ 0⟩

end GlobalTheory.Published.LeviInducedModel

end
end
