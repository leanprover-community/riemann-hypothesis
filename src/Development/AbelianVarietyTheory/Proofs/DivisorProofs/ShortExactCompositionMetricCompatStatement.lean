import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotStages

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.HermFrame

open Matrix

section Exists

variable {m l n : Type} [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l]
  [DecidableEq n]

open scoped MatrixOrder in

theorem exists_chg_eq_one {H : Matrix n n ℂ} (hH : H.PosDef) :
    ∃ R : Matrix n n ℂ, IsUnit R.det ∧ chg R H = 1 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.transpose.posSemidef.nonneg
  have hd : Hᵀ.det ≠ 0 := hH.transpose.det_pos.ne'
  have hu : IsUnit B.det := by
    rw [hB, det_mul] at hd
    exact (right_ne_zero_of_mul hd).isUnit
  refine ⟨B⁻¹, isUnit_nonsing_inv_det _ hu, ?_⟩
  apply transpose_injective
  have e : (chg B⁻¹ H)ᵀ = (B⁻¹)ᴴ * Hᵀ * B⁻¹ := by
    simp only [chg, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [e, hB, star_eq_conjTranspose, conjTranspose_nonsing_inv, Matrix.mul_assoc, Matrix.mul_assoc,
    mul_nonsing_inv _ hu, Matrix.mul_one,
    nonsing_inv_mul _ (by rw [det_conjTranspose]; exact hu.star), transpose_one]

theorem exists_chg_fromBlocks_eq_one {H : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hH : H.PosDef)
    {R : Matrix l l ℂ} (hR : chg R (quotGram H) = 1) :
    ∃ (A : Matrix m m ℂ) (B : Matrix m l ℂ), IsUnit A.det ∧ chg (fromBlocks A B 0 R) H = 1 := by
  obtain ⟨A, hA, hA1⟩ := exists_chg_eq_one (posDef_subGram hH)
  have hs : IsUnit H.toBlocks₁₁.det := (posDef_subGram hH).det_pos.ne'.isUnit
  set B : Matrix m l ℂ := -(orthCoeff H * R) with hBdef
  have hBt : Bᵀ = -(Rᵀ * (H.toBlocks₂₁ * H.toBlocks₁₁⁻¹)) := by
    simp [hBdef, orthCoeff, transpose_mul, transpose_nonsing_inv]
  have hW : Bᵀ * H.toBlocks₁₁ + Rᵀ * H.toBlocks₂₁ = 0 := by
    rw [hBt, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hs,
      Matrix.mul_one, neg_add_cancel]
  have hZ : Bᵀ * H.toBlocks₁₂ + Rᵀ * H.toBlocks₂₂ = Rᵀ * quotGram H := by
    rw [hBt, quotGram, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    abel
  have hherm : (chg (fromBlocks A B 0 R) H).IsHermitian := by
    have := isHermitian_mul_mul_conjTranspose (fromBlocks A B 0 R)ᵀ hH.isHermitian
    rwa [show (fromBlocks A B 0 R)ᵀᴴ = (fromBlocks A B 0 R)ᴴᵀ from rfl] at this
  have e21 : (chg (fromBlocks A B 0 R) H).toBlocks₂₁ = 0 := by
    rw [chg_fromBlocks, toBlocks_fromBlocks₂₁, hW, Matrix.zero_mul]
  have e12 : (chg (fromBlocks A B 0 R) H).toBlocks₁₂ = 0 := by
    have := conjTranspose_toBlocks₁₂ hherm
    rw [e21] at this
    simpa using congrArg conjTranspose this
  have e11 : (chg (fromBlocks A B 0 R) H).toBlocks₁₁ = 1 := by
    rw [chg_fromBlocks, toBlocks_fromBlocks₁₁]; exact hA1
  have e22 : (chg (fromBlocks A B 0 R) H).toBlocks₂₂ = 1 := by
    rw [chg_fromBlocks, toBlocks_fromBlocks₂₂, hW, hZ, Matrix.zero_mul, zero_add]; exact hR
  refine ⟨A, B, hA, ?_⟩
  rw [← fromBlocks_toBlocks (chg (fromBlocks A B 0 R) H), e11, e12, e21, e22, fromBlocks_one]

theorem exists_triangular_chg_eq_one {H : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ} (hH : H.PosDef) :
    ∃ (A₁ : Matrix m m ℂ) (B : Matrix m (l ⊕ n) ℂ) (A₂ : Matrix l l ℂ) (C : Matrix l n ℂ)
      (A₃ : Matrix n n ℂ), IsUnit A₁.det ∧ IsUnit A₂.det ∧ IsUnit A₃.det ∧
        chg (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)) H = 1 := by
  have hQ := posDef_quotGram hH
  obtain ⟨A₃, h₃, e₃⟩ := exists_chg_eq_one (posDef_quotGram hQ)
  obtain ⟨A₂, C, h₂, e₂⟩ := exists_chg_fromBlocks_eq_one hQ e₃
  obtain ⟨A₁, B, h₁, e₁⟩ := exists_chg_fromBlocks_eq_one hH e₂
  exact ⟨A₁, B, A₂, C, A₃, h₁, h₂, h₃, e₁⟩

theorem chg_submatrix_first (A₁ : Matrix m m ℂ) (B : Matrix m (l ⊕ n) ℂ) (A₂ : Matrix l l ℂ)
    (C : Matrix l n ℂ) (A₃ : Matrix n n ℂ) (H : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ) :
    (chg (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)) H).submatrix (Sum.map id Sum.inl)
        (Sum.map id Sum.inl) =
      chg (fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂)
        (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) := by
  set J : Matrix (m ⊕ (l ⊕ n)) (m ⊕ l) ℂ :=
    (1 : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ).submatrix id (Sum.map id Sum.inl) with hJ
  have h0 : ∀ T : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ,
      chg (T.submatrix id (Sum.map id Sum.inl)) H =
        (chg T H).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) := fun T => by
    have := chg_submatrix T H (Equiv.refl _) (Sum.map id Sum.inl : m ⊕ l → m ⊕ (l ⊕ n))
    simpa using this
  have h1 : H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) = chg J H := by
    rw [hJ, h0, chg_one]
  have h2 : (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)).submatrix id (Sum.map id Sum.inl)
      = J * fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂ := by
    ext (a | a | a) (b | b) <;>
      simp [hJ, mul_apply, Fintype.sum_sum_type, one_apply]
  rw [h1, chg_chg, ← h2, h0]

end Exists

section Forms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l n : Type} [Fintype m] [Fintype l] [Fintype n] [DecidableEq m]
  [DecidableEq l] [DecidableEq n]

theorem extTrace_eq_sum_of_eq_one {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
    (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (h1 : K z = 1) (ξ η : E) :
    extTrace K z ξ η = kappa * ∑ a : m, ∑ b : l,
      mdel K z ξ (Sum.inl a) (Sum.inr b) * star (mdel K z η (Sum.inl a) (Sum.inr b)) := by
  have hs : subGram (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ) = 1 := by
    ext a b; simp [subGram, toBlocks₁₁, one_apply]
  have hq : quotGram (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ) = 1 := by
    have e1 : (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ).toBlocks₂₁ = 0 := by
      ext a b; simp [toBlocks₂₁, one_apply]
    have e2 : (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ).toBlocks₂₂ = 1 := by
      ext a b; simp [toBlocks₂₂, one_apply]
    rw [quotGram, e1, e2]; simp
  have hb : ∀ ξ, secondForm K z ξ = (mdel K z ξ).toBlocks₁₂ᵀ := fun ξ => by
    rw [secondForm_eq, conn, h1, transpose_one, inv_one, Matrix.one_mul]; rfl
  rw [extTrace_eq h hp, secondFormAdj, h1, hs, hq, hb, hb, adj]
  simp only [transpose_one, inv_one, Matrix.one_mul, Matrix.mul_one, trace, diag_apply, mul_apply,
    transpose_apply, conjTranspose_apply, toBlocks₁₂, of_apply]
  rw [Finset.sum_comm]

theorem mdel_quotGram_of_eq_one {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
    (h : MContDiffAt 1 K z) (h1 : K z = 1) (ξ : E) :
    mdel (fun x => quotGram (K x)) z ξ = (mdel K z ξ).toBlocks₂₂ := by
  have hu : IsUnit (subGram (K z)).det := by
    have : subGram (K z) = 1 := by rw [h1]; ext a b; simp [subGram, toBlocks₁₁, one_apply]
    rw [this]; simp
  have e12 : (K z).toBlocks₁₂ = 0 := by rw [h1]; ext a b; simp [toBlocks₁₂, one_apply]
  have e21 : (K z).toBlocks₂₁ = 0 := by rw [h1]; ext a b; simp [toBlocks₂₁, one_apply]
  have h21 : MContDiffAt 1 (fun x => (K x).toBlocks₂₁) z := h.submatrix Sum.inr Sum.inl
  have h12 : MContDiffAt 1 (fun x => (K x).toBlocks₁₂) z := h.submatrix Sum.inl Sum.inr
  have h22 : MContDiffAt 1 (fun x => (K x).toBlocks₂₂) z := h.submatrix Sum.inr Sum.inr
  have h11 : MContDiffAt 1 (fun x => (K x).toBlocks₁₁⁻¹) z := h.subGram.inv hu
  have hP := h21.mul h11
  have e : (fun x => quotGram (K x)) =
      fun x => (K x).toBlocks₂₂ + -((K x).toBlocks₂₁ * (K x).toBlocks₁₁⁻¹ * (K x).toBlocks₁₂) := by
    funext x; rw [quotGram, sub_eq_add_neg]
  rw [e, mdel_add h22 (hP.mul h12).neg, mdel_neg, mdel_mul hP h12, e12, e21]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, neg_zero]
  rfl

theorem extTrace_add_of_eq_one {K : E → Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ} {z : E}
    (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (h1 : K z = 1) (ξ η : E) :
    extTrace (fun x => (K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z ξ η +
        extTrace (fun x => (K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z ξ η =
      extTrace K z ξ η + extTrace (fun x => quotGram (K x)) z ξ η := by
  have hf : Function.Injective (Sum.map id Sum.inl : m ⊕ l → m ⊕ (l ⊕ n)) :=
    Function.injective_id.sumMap Sum.inl_injective
  have he := (Equiv.sumAssoc m l n).injective
  have hsub : subGram (K z) = 1 := by rw [h1]; ext a b; simp [subGram, toBlocks₁₁, one_apply]
  have hu : IsUnit (subGram (K z)).det := by rw [hsub]; simp
  have hq : quotGram (K z) = 1 := by
    have e1 : (K z).toBlocks₂₁ = 0 := by rw [h1]; ext a b; simp [toBlocks₂₁, one_apply]
    have e2 : (K z).toBlocks₂₂ = 1 := by rw [h1]; ext a b; simp [toBlocks₂₂, one_apply]
    rw [quotGram, e1, e2]; simp
  rw [extTrace_eq_sum_of_eq_one (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix hf)
      (by rw [h1]; exact submatrix_one _ hf),
    extTrace_eq_sum_of_eq_one (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix he)
      (by rw [h1]; exact submatrix_one _ he),
    extTrace_eq_sum_of_eq_one h hp h1,
    extTrace_eq_sum_of_eq_one (h.quotGram hu) (hp.mono fun x hx => posDef_quotGram hx) hq,
    mdel_quotGram_of_eq_one h h1, mdel_quotGram_of_eq_one h h1]
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, mdel_apply, submatrix_apply,
    Sum.map_inl, Sum.map_inr, id, Equiv.sumAssoc_apply_inl_inl, Equiv.sumAssoc_apply_inl_inr,
    Equiv.sumAssoc_apply_inr, toBlocks₂₂, of_apply]
  ring

variable {K : E → Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ} {z : E}

theorem extTrace_add_chg (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef)
    {A₁ : Matrix m m ℂ} (B : Matrix m (l ⊕ n) ℂ) {A₂ : Matrix l l ℂ} (C : Matrix l n ℂ)
    {A₃ : Matrix n n ℂ} (h₁ : IsUnit A₁.det) (h₂ : IsUnit A₂.det) (h₃ : IsUnit A₃.det) :
    let A := fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)
    extTrace (fun x => (chg A (K x)).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z =
        extTrace (fun x => (K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z ∧
      extTrace (fun x => (chg A (K x)).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z =
        extTrace (fun x => (K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z ∧
      extTrace (fun x => chg A (K x)) z = extTrace K z ∧
      extTrace (fun x => quotGram (chg A (K x))) z = extTrace (fun x => quotGram (K x)) z := by
  intro A
  have hf : Function.Injective (Sum.map id Sum.inl : m ⊕ l → m ⊕ (l ⊕ n)) :=
    Function.injective_id.sumMap Sum.inl_injective
  have he := (Equiv.sumAssoc m l n).injective
  have hA₂ : IsUnit (fromBlocks A₂ C 0 A₃).det := by
    rw [det_fromBlocks_zero₂₁]; exact h₂.mul h₃
  have hA : IsUnit A.det := by
    simp only [A]; rw [det_fromBlocks_zero₂₁]; exact h₁.mul hA₂
  have hs : IsUnit (subGram (K z)).det := (posDef_subGram hp.self_of_nhds).det_pos.ne'.isUnit
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (fun x => (chg A (K x)).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) =
        fun x => chg (fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂)
          ((K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) :=
      funext fun x => chg_submatrix_first A₁ B A₂ C A₃ (K x)
    rw [e]
    refine extTrace_chg (A := fun _ => fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂)
      (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix hf) (mContDiffAt_const _)
      (by rw [det_fromBlocks_zero₂₁]; exact h₁.mul h₂) (fun η => mdbar_const _ _ _)
      (.of_forall fun _ => toBlocks_fromBlocks₂₁ _ _ _ _)
  · have e : (fun x => (chg A (K x)).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) =
        fun x => chg (A.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n))
          ((K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) :=
      funext fun x => (chg_submatrix A (K x) (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)).symm
    rw [e]
    refine extTrace_chg (A := fun _ => A.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n))
      (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix he) (mContDiffAt_const _)
      (by rw [det_submatrix_equiv_self]; exact hA) (fun η => mdbar_const _ _ _)
      (.of_forall fun _ => ?_)
    ext a (b | b) <;> simp [A, toBlocks₂₁]
  · exact extTrace_chg (A := fun _ => A) h hp (mContDiffAt_const _) hA
      (fun η => mdbar_const _ _ _) (.of_forall fun _ => toBlocks_fromBlocks₂₁ _ _ _ _)
  · rw [extTrace_congr (K' := fun x => chg (fromBlocks A₂ C 0 A₃) (quotGram (K x)))
      (hp.mono fun x hx => quotGram_chg B _ h₁ (posDef_subGram hx).det_pos.ne'.isUnit)]
    exact extTrace_chg (A := fun _ => fromBlocks A₂ C 0 A₃) (h.quotGram hs)
      (hp.mono fun x hx => posDef_quotGram hx) (mContDiffAt_const _) hA₂
      (fun η => mdbar_const _ _ _) (.of_forall fun _ => toBlocks_fromBlocks₂₁ _ _ _ _)

end Forms

theorem extTrace_add_extTrace :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
      (m l n : Type) [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l]
      [DecidableEq n] (K : E → Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ) (z ξ η : E),
      MContDiffAt 1 K z → (∀ᶠ x in 𝓝 z, (K x).PosDef) →
      extTrace (fun x => (K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z ξ η +
          extTrace (fun x => (K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z ξ η =
        extTrace K z ξ η + extTrace (fun x => quotGram (K x)) z ξ η := by
  intro E _ _ _ _ m l n _ _ _ _ _ _ K z ξ η h hp
  obtain ⟨A₁, B, A₂, C, A₃, h₁, h₂, h₃, e⟩ := exists_triangular_chg_eq_one hp.self_of_nhds
  obtain ⟨t₁, t₂, t₃, t₄⟩ := extTrace_add_chg h hp B C h₁ h₂ h₃
  have hA : IsUnit (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)).det := by
    rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]; exact h₁.mul (h₂.mul h₃)
  have := extTrace_add_of_eq_one (K := fun x => chg (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)) (K x))
    (((mContDiffAt_const _).mul h).mul (mContDiffAt_const _))
    (hp.mono fun x hx => posDef_chg ((isUnit_iff_isUnit_det _).2 hA) hx) e ξ η
  rwa [t₁, t₂, t₃, t₄] at this

end GlobalTheory.HermFrame
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HermFrame.Renumber
open Matrix

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
variable {m l m' l' : Type} [Fintype m] [Fintype l] [Fintype m'] [Fintype l'] [DecidableEq m]
  [DecidableEq l] [DecidableEq m'] [DecidableEq l']

theorem mdbar_submatrix {a b a' b' : Type} (A : E → Matrix a b ℂ) (e : a' → a) (f : b' → b) (z η : E) :
    mdbar (fun x => (A x).submatrix e f) z η = (mdbar A z η).submatrix e f := by
  ext i j; simp [mdbar]

theorem subGram_submatrix (e : m' ≃ m) (f : l' ≃ l) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    subGram (H.submatrix (Sum.map e f) (Sum.map e f)) = (subGram H).submatrix e e := by
  ext i j; simp [subGram, toBlocks₁₁]

theorem quotGram_submatrix (e : m' ≃ m) (f : l' ≃ l) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    quotGram (H.submatrix (Sum.map e f) (Sum.map e f)) = (quotGram H).submatrix f f := by
  have h11 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₁ = H.toBlocks₁₁.submatrix e e := by
    ext i j; simp [toBlocks₁₁]
  have h12 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₂ = H.toBlocks₁₂.submatrix e f := by
    ext i j; simp [toBlocks₁₂]
  have h21 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₁ = H.toBlocks₂₁.submatrix f e := by
    ext i j; simp [toBlocks₂₁]
  have h22 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₂ = H.toBlocks₂₂.submatrix f f := by
    ext i j; simp [toBlocks₂₂]
  rw [quotGram, quotGram, h11, h12, h21, h22, inv_submatrix_equiv, submatrix_mul_equiv,
    submatrix_mul_equiv]; rfl

theorem orthCoeff_submatrix (e : m' ≃ m) (f : l' ≃ l) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    orthCoeff (H.submatrix (Sum.map e f) (Sum.map e f)) = (orthCoeff H).submatrix e f := by
  have h11 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₁ = H.toBlocks₁₁.submatrix e e := by
    ext i j; simp [toBlocks₁₁]
  have h21 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₁ = H.toBlocks₂₁.submatrix f e := by
    ext i j; simp [toBlocks₂₁]
  rw [orthCoeff, orthCoeff, h11, h21, transpose_submatrix, transpose_submatrix, inv_submatrix_equiv,
    submatrix_mul_equiv]

theorem adj_submatrix {a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b']
    [DecidableEq a] [DecidableEq a'] (e : a' ≃ a) (f : b' ≃ b)
    (H : Matrix a a ℂ) (K : Matrix b b ℂ) (T : Matrix b a ℂ) :
    adj (H.submatrix e e) (K.submatrix f f) (T.submatrix f e) = (adj H K T).submatrix e f := by
  rw [adj, adj, transpose_submatrix, transpose_submatrix, conjTranspose_submatrix,
    inv_submatrix_equiv, submatrix_mul_equiv, submatrix_mul_equiv]

theorem extForm_submatrix (e : m' ≃ m) (f : l' ≃ l) (K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : E) :
    extForm (fun x => (K x).submatrix (Sum.map e f) (Sum.map e f)) z η =
      (extForm K z η).submatrix e f := by
  rw [extForm_eq_neg_mdbar, extForm_eq_neg_mdbar]
  simp_rw [orthCoeff_submatrix]
  rw [mdbar_submatrix]; rfl

theorem extFormAdj_submatrix (e : m' ≃ m) (f : l' ≃ l) (K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : E) :
    extFormAdj (fun x => (K x).submatrix (Sum.map e f) (Sum.map e f)) z ξ =
      (extFormAdj K z ξ).submatrix f e := by
  rw [extFormAdj, extFormAdj, extForm_submatrix, quotGram_submatrix, subGram_submatrix, adj_submatrix]

end GlobalTheory.HermFrame.Renumber

open Matrix in

theorem GlobalTheory.HermFrame.extTrace_submatrix_sumMap : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (m l m' l' : Type) [Fintype m] [Fintype l] [Fintype m'] [Fintype l'] [DecidableEq m] [DecidableEq l] [DecidableEq m'] [DecidableEq l'] (e : m' ≃ m) (f : l' ≃ l) (K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E), extTrace (fun x => (K x).submatrix (Sum.map e f) (Sum.map e f)) z = extTrace K z := by
  intro E _ _ _ _ m l m' l' _ _ _ _ _ _ _ _ e f K z
  funext ξ η
  rw [extTrace, extTrace, Renumber.extFormAdj_submatrix, Renumber.extForm_submatrix,
    submatrix_mul_equiv]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp f (fun i => (extFormAdj K z ξ * extForm K z η) i i)
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.CurveDens

open Matrix
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

set_option maxHeartbeats 2000000 in

theorem bcDens_stage_of_frames {A M B L Q V : X.Modules} {f : A ⟶ M} {g : M ⟶ B} {u : A ⟶ B}
    {q₀ : M ⟶ L} {q₁ : B ⟶ Q} {q₂ : B ⟶ V} {w₀ : f ≫ q₀ = 0} {w₁ : g ≫ q₁ = 0} {w₂ : u ≫ q₂ = 0}
    (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact)
    (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) {l : L ⟶ V} {m : V ⟶ Q} {w₃ : l ≫ m = 0}
    (hS₃ : (ShortComplex.mk l m w₃).ShortExact) {n : ℕ} (hA : IsVB A n) (hM : IsVB M (n + 1))
    (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g)
    {h : Met p σ B (n + 1 + 1)} (hfg : f ≫ g = u) (hlq : q₀ ≫ l = g ≫ q₂) (hmq : q₂ ≫ m = q₁)
    (H : h.IsCInf) (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) {U : X.Opens}
    (hyU : y ∈ ptsIn p σ U) (e : Fin n → Γ(A, U)) (t : Fin 1 → Γ(M, U)) (t₁ : Fin 1 → Γ(B, U))
    (he : IsFrame e) (ht : IsFrame fun i => q₀.app U (t i))
    (ht₁ : IsFrame fun i => q₁.app U (t₁ i)) :
    Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y +
        Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y =
      Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y +
        Met.bcDens (S := ShortComplex.mk l m w₃)
          (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  have hfg' (s : Γ(A, U)) : g.app U (f.app U s) = u.app U s := congr(($hfg).app U s)
  have hlq' (s : Γ(M, U)) : l.app U (q₀.app U s) = q₂.app U (g.app U s) := congr(($hlq).app U s)
  have hmq' (s : Γ(B, U)) : m.app U (q₂.app U s) = q₁.app U s := congr(($hmq).app U s)
  let a₀ : AdaptedChart (ShortComplex.mk f q₀ w₀) n 1 := ⟨U, e, t, he, ht⟩
  let a₁ : AdaptedChart (ShortComplex.mk g q₁ w₁) (n + 1) 1 :=
    ⟨U, (a₀.mid hS₀).e, t₁, (a₀.mid hS₀).isFrame, ht₁⟩
  have ht₃ : IsFrame fun i => m.app U (q₂.app U (t₁ i)) := by simpa only [hmq'] using ht₁
  let a₃ : AdaptedChart (ShortComplex.mk l m w₃) 1 1 :=
    ⟨U, fun i => q₀.app U (t i), fun i => q₂.app U (t₁ i), ht, ht₃⟩
  let t₂ : Fin (1 + 1) → Γ(B, U) :=
    Sum.elim (fun i => g.app U (t i)) t₁ ∘ finSumFinEquiv.symm
  have ht₂e (j : Fin 1 ⊕ Fin 1) : q₂.app U (t₂ (finSumFinEquiv j)) = a₃.frame j := by
    rcases j with j | j
    · simp [t₂, a₃, AdaptedChart.frame, hlq']
    · simp [t₂, a₃, AdaptedChart.frame]
  have ht₂ : IsFrame fun i => q₂.app U (t₂ i) := by
    have e₀ : (fun i => q₂.app U (t₂ i)) = (a₃.mid hS₃).e := by
      funext i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
      rw [ht₂e]
      simp [AdaptedChart.mid]
    rw [e₀]
    exact (a₃.mid hS₃).isFrame
  let a₂ : AdaptedChart (ShortComplex.mk u q₂ w₂) n (1 + 1) := ⟨U, e, t₂, he, ht₂⟩
  let T : Fin n ⊕ (Fin 1 ⊕ Fin 1) → Γ(B, U) :=
    Sum.elim (fun i => u.app U (e i)) (Sum.elim (fun i => g.app U (t i)) t₁)
  have hT₀ (x : Fin n ⊕ Fin 1) : g.app U (a₀.frame x) = T (Sum.map id Sum.inl x) := by
    rcases x with i | i
    · simp [a₀, T, AdaptedChart.frame, hfg']
    · simp [a₀, T, AdaptedChart.frame]
  have hT₁ (x : (Fin n ⊕ Fin 1) ⊕ Fin 1) :
      a₁.frame (Sum.map finSumFinEquiv id x) = T (Equiv.sumAssoc _ _ _ x) := by
    rcases x with (i | i) | i
    · simp [a₀, a₁, T, AdaptedChart.frame, AdaptedChart.mid, hfg']
    · simp [a₀, a₁, T, AdaptedChart.frame, AdaptedChart.mid]
    · simp [a₁, T, AdaptedChart.frame]
  have hT₂ (x : Fin n ⊕ (Fin 1 ⊕ Fin 1)) :
      a₂.frame (Sum.map id finSumFinEquiv x) = T x := by
    rcases x with i | i | i
    · simp [a₂, T, AdaptedChart.frame]
    · simp [a₂, t₂, T, AdaptedChart.frame]
    · simp [a₂, t₂, T, AdaptedChart.frame]

  let K : CxPts p σ → Matrix (Fin n ⊕ (Fin 1 ⊕ Fin 1)) (Fin n ⊕ (Fin 1 ⊕ Fin 1)) ℂ := h.gram T
  have g₀ {z : CxPts p σ} (hz : z ∈ ptsIn p σ U) :
      (h.restrict hg hM).gram a₀.frame z =
        (K z).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) := by
    ext i j
    refine ((h.form_restrict hg hM _ _ hz).trans ?_)
    rw [hT₀, hT₀]
    rfl
  have g₁ {z : CxPts p σ} : (K z).submatrix (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) =
      (h.gram a₁.frame z).submatrix (Sum.map finSumFinEquiv (Equiv.refl (Fin 1)))
        (Sum.map finSumFinEquiv (Equiv.refl (Fin 1))) := by
    ext i j
    change h.form (T _) (T _) z = h.form (a₁.frame _) (a₁.frame _) z
    exact congrArg₂ (fun s s' => h.form s s' z) (hT₁ i).symm (hT₁ j).symm
  have g₂ {z : CxPts p σ} : K z =
      (h.gram a₂.frame z).submatrix (Sum.map (Equiv.refl (Fin n)) finSumFinEquiv)
        (Sum.map (Equiv.refl (Fin n)) finSumFinEquiv) := by
    ext i j
    change h.form (T _) (T _) z = h.form (a₂.frame _) (a₂.frame _) z
    exact congrArg₂ (fun s s' => h.form s s' z) (hT₂ i).symm (hT₂ j).symm
  have g₃ {z : CxPts p σ} (hz : z ∈ ptsIn p σ U) :
      (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).gram a₃.frame z =
        quotGram (K z) := by
    have e₀ := (QuotStage.quotStages (Fin n) (Fin (1 + 1)) Unit).2 (Fin n) (Fin 1 ⊕ Fin 1)
      (Equiv.refl _) finSumFinEquiv (h.gram a₂.frame z)
    ext i j
    rw [g₂, e₀, submatrix_apply, ← Met.quot_G h hS₂ hA hV a₂ hz,
      ← Met.form_frame _ a₂.quot hz]
    exact congrArg₂ (fun s s' => (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1)
      h hS₂ hA hV).form s s' z) (ht₂e i).symm (ht₂e j).symm
  have hW : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ U :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds
      (ChartGlue.mem_over c.e hy hyU)) fun _ hv => hv.2
  have d₀ : Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y =
      2 * diagVal (extTrace (fun v => (K (c.e.symm v)).submatrix (Sum.map id Sum.inl)
        (Sum.map id Sum.inl)) (c.e y)) (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₀ hA hL a₀ c (H.restrict hg hM) hy hyU, Met.bcForm,
      extTrace_congr (hW.mono fun v hv => g₀ hv)]
  have d₁ : Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y =
      2 * diagVal (extTrace (fun v => (K (c.e.symm v)).submatrix (Equiv.sumAssoc _ _ _)
        (Equiv.sumAssoc _ _ _)) (c.e y)) (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₁ hM hQ a₁ c H hy hyU, Met.bcForm]
    simp only [g₁]
    rw [extTrace_submatrix_sumMap]
  have d₂ : Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y =
      2 * diagVal (extTrace (fun v => K (c.e.symm v)) (c.e y)) (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₂ hA hV a₂ c H hy hyU, Met.bcForm]
    simp only [g₂]
    rw [extTrace_submatrix_sumMap]
  have d₃ : Met.bcDens (S := ShortComplex.mk l m w₃)
      (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y =
      2 * diagVal (extTrace (fun v => quotGram (K (c.e.symm v))) (c.e y))
        (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₃ hL hQ a₃ c (Met.IsCInf.quot hS₂ hA hV H) hy hyU, Met.bcForm,
      extTrace_congr (hW.mono fun v hv => g₃ hv)]
  have hK : MContDiffAt 1 (fun v => K (c.e.symm v)) (c.e y) :=
    ((H.gram T hyU).mContDiffAt c hy).of_le (by norm_cast)
  have hp : ∀ᶠ v in 𝓝 (c.e y), (K (c.e.symm v)).PosDef := hW.mono fun v hv => by
    rw [g₂]
    exact (Met.posDef_gram_frame (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ a₂ hv).submatrix
      ((Equiv.refl (Fin n)).injective.sumMap finSumFinEquiv.injective)
  have key := congrArg (fun w => (-Complex.I * w).re)
    (extTrace_add_extTrace (ReciprocityTheory.L2DbarEstimates.V 1) (Fin n) (Fin 1) (Fin 1) (fun v => K (c.e.symm v))
      (c.e y) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) hK hp)
  simp only [mul_add, Complex.add_re] at key
  rw [d₀, d₁, d₂, d₃]
  simp only [diagVal]
  linarith

theorem bcDens_add_bcDens_stage : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact) (n : ℕ) (hA : IsVB A n) (hM : IsVB M (n + 1)) (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g) (h : Met p σ B (n + 1 + 1)), f ≫ g = u → q₀ ≫ l = g ≫ q₂ → q₂ ≫ m = q₁ → h.IsCInf → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y + Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y = Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y + Met.bcDens (S := ShortComplex.mk l m w₃) (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  intro k _ X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ l m w₃ hS₃ n hA hM hL hQ hV hg h
    hfg hlq hmq H c y hy
  obtain ⟨b₀, hb₀⟩ := Met.exists_adapted (p := p) (σ := σ) hS₀ hA hL y
  obtain ⟨b₁, hb₁⟩ := Met.exists_adapted hS₁ hM hQ y
  refine bcDens_stage_of_frames hS₀ hS₁ hS₂ hS₃ hA hM hL hQ hV hg hfg hlq hmq H c hy
    (U := b₀.U ⊓ b₁.U) (mem_ptsIn_inf.2 ⟨hb₀, hb₁⟩) (fun i => resM A inf_le_left (b₀.e i))
    (fun i => resM M inf_le_left (b₀.t i)) (fun i => resM B inf_le_right (b₁.t i))
    (b₀.he.res inf_le_left) ?_ ?_
  · simp only [app_resM]
    exact b₀.ht.res inf_le_left
  · simp only [app_resM]
    exact b₁.ht.res inf_le_right

end GlobalTheory.CurveDens
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_composition_metric_compat : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact) (n : ℕ) (hA : IsVB A n) (hM : IsVB M (n + 1)) (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g) (h : Met p σ B (n + 1 + 1)), f ≫ g = u → q₀ ≫ l = g ≫ q₂ → q₂ ≫ m = q₁ → h.IsCInf → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y + Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y = Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y + Met.bcDens (S := ShortComplex.mk l m w₃) (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  first | exact @GlobalTheory.CurveDens.bcDens_add_bcDens_stage | exact GlobalTheory.CurveDens.bcDens_add_bcDens_stage | (intros; apply GlobalTheory.CurveDens.bcDens_add_bcDens_stage <;> assumption)
end
