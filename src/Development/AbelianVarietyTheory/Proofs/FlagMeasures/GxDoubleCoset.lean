import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstA

open scoped Classical ComplexConjugate ENNReal
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

noncomputable section

namespace GlobalTheory.GxConj

variable {r n : ℕ}

def LoUni (L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Prop :=
  (∀ a b, a < b → L a b = 0) ∧ ∀ a, L a a = 1

theorem LoUni.conj {L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : LoUni L) :
    LoUni (L.map (starRingEnd ℂ)) :=
  ⟨fun a b hab => by simp [h.1 a b hab], fun a => by simp [h.2 a]⟩

theorem sub_mul_left {l : ℕ} {ι : Type*} (hl : l ≤ r + 1) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (B : Matrix (Fin (r + 1)) ι ℂ) (c : Fin l → ι) (hA : ∀ a b, a < b → A a b = 0) :
    (A * B).submatrix (Fin.castLE hl) c =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) c := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun _ => rfl)
  intro i hi
  have hli : l ≤ i.1 := by
    by_contra hc
    exact hi ⟨⟨i.1, by omega⟩, rfl⟩
  rw [hA _ _ (by
    show a.1 < i.1
    have := a.2
    omega), zero_mul]

theorem sub_mul_right {l : ℕ} {ι : Type*} (hl : l ≤ r + 1) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (B : Matrix ι (Fin (r + 1)) ℂ) (c : Fin l → ι) (hA : ∀ a b, a < b → A a b = 0) :
    (B * Aᵀ).submatrix c (Fin.castLE hl) =
      B.submatrix c (Fin.castLE hl) * (A.submatrix (Fin.castLE hl) (Fin.castLE hl))ᵀ := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun _ => rfl)
  intro i hi
  have hli : l ≤ i.1 := by
    by_contra hc
    exact hi ⟨⟨i.1, by omega⟩, rfl⟩
  rw [hA _ _ (by
    show b.1 < i.1
    have := b.2
    omega), mul_zero]

theorem det_sub {l : ℕ} (hl : l ≤ r + 1) {L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : LoUni L) :
    (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun a _ => h.2 _
  · intro i j hij
    exact h.1 _ _ hij




theorem fam_last (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : fam e z (Fin.last r) = z :=
  Fin.snoc_last (α := fun _ => Fin n → ℂ) z e

theorem fam_castSucc (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin r) : fam e z a.castSucc = e a :=
  Fin.snoc_castSucc (α := fun _ => Fin n → ℂ) z e a

theorem fam_span (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (h : InS e z A)
    (a : Fin (r + 1)) : (A - 1) *ᵥ fam e z a ∈ Submodule.span ℂ (fam e z '' {b | b < a}) := by
  refine Fin.lastCases ?_ (fun a => ?_) a
  · rw [fam_last]
    refine Submodule.span_mono ?_ h.2
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.castSucc, Fin.castSucc_lt_last b, fam_castSucc e z b⟩
  · rw [fam_castSucc]
    refine Submodule.span_mono ?_ (h.1 a)
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.castSucc, hb, fam_castSucc e z b⟩

theorem hJ_adj (ε : Fin n → Bool) (A Ai : Matrix (Fin n) (Fin n) ℂ)
    (hU : Aiᴴ * Formalism.REAL.Jm ε * Ai = Formalism.REAL.Jm ε) (h1 : Ai * A = 1) (x y : Fin n → ℂ) :
    hJ ε x (A *ᵥ y) = hJ ε (Ai *ᵥ x) y := by
  have e : Aiᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * A := by
    calc Aiᴴ * Formalism.REAL.Jm ε = Aiᴴ * Formalism.REAL.Jm ε * (Ai * A) := by rw [h1, Matrix.mul_one]
      _ = (Aiᴴ * Formalism.REAL.Jm ε * Ai) * A := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * A := by rw [hU]
  have e2 : Aiᴴ *ᵥ (Formalism.REAL.Jm ε *ᵥ y) = Formalism.REAL.Jm ε *ᵥ (A *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, e2]

theorem hJ_sum_left {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (s : ι → ℂ) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ c, s c • x c) y = ∑ c, conj (s c) * hJ ε (x c) y := by
  unfold hJ
  simp only [star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem hJ_sum_right {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (s : ι → ℂ) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, s c • y c) = ∑ c, s c * hJ ε x (y c) := by
  unfold hJ
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem mulVec_lin {ι : Type*} [Fintype ι] (B : Matrix (Fin n) (Fin n) ℂ) (s : ι → ℂ) (y : ι → Fin n → ℂ) :
    B *ᵥ ∑ c, s c • y c = ∑ c, s c • (B *ᵥ y c) := by
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem zhat_conj (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (A Ai B C : Matrix (Fin n) (Fin n) ℂ)
    (hadj : ∀ x y, hJ ε x (A *ᵥ y) = hJ ε (Ai *ᵥ x) y) (L M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hL : ∀ a, Ai *ᵥ f a = ∑ c, L a c • f c) (hM : ∀ b, C *ᵥ f' b = ∑ d, M b d • f' d) :
    Zhat ε f f' (A * B * C) = L.map (starRingEnd ℂ) * Zhat ε f f' B * Mᵀ := by
  ext a b
  have e1 : (A * B * C) *ᵥ f' b = A *ᵥ (B *ᵥ (C *ᵥ f' b)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  simp only [Formalism.L2.SG.RealObj.Zhat, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [e1, hadj, hL, hM, mulVec_lin, hJ_sum_left]
  simp only [hJ_sum_right, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.GxConj

namespace GlobalTheory

open GlobalTheory.GxConj


end GlobalTheory
