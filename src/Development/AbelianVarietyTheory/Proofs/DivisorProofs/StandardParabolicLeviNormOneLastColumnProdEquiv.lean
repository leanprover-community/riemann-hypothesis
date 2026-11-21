import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumns
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionCommuteOfFixesIsotropicColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviElem

open Matrix

section Abstract

variable {R : Type} [CommRing R]

def cols2 {n : ℕ} (x y : Fin n → R) : Matrix (Fin n) (Fin 2) R := Matrix.of fun i k => ![x i, y i] k

theorem conj_eq {n κ : Type} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ] (s : R →+* R)
    (P : Matrix n κ R) (Q : Matrix κ n R) (hPQ : P * Q = 1) (J : Matrix n n R) (D : Matrix κ κ R)
    (hK : Dᵀ * (Pᵀ * J * P.map s) * D.map s = Pᵀ * J * P.map s) :
    (P * D * Q)ᵀ * J * (P * D * Q).map s = J := by
  have h1 : (P * D * Q)ᵀ * J * (P * D * Q).map s = Qᵀ * (Dᵀ * (Pᵀ * J * P.map s) * D.map s) * Q.map s := by
    simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [h1, hK]
  have h2 : Qᵀ * (Pᵀ * J * P.map s) * Q.map s = (P * Q)ᵀ * J * (P * Q).map s := by
    simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [h2, hPQ]
  simp

def swap2 : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

def blk {b : ℕ} (g : Matrix (Fin b) (Fin b) R) (t u : R) : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) R :=
  fromBlocks g 0 0 (diagonal ![t, u])

theorem levi_mat {b : ℕ} (s : R →+* R) (hs : ∀ z, s (s z) = z) (ι : Matrix (Fin (b + 2)) (Fin b) R)
    (x y : Fin (b + 2) → R) (J : Matrix (Fin (b + 2)) (Fin (b + 2)) R) (J₁ : Matrix (Fin b) (Fin b) R)
    (Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) R) (hQP : Q * fromCols ι (cols2 x y) = 1)
    (hK : (fromCols ι (cols2 x y))ᵀ * J * (fromCols ι (cols2 x y)).map s = fromBlocks J₁ 0 0 swap2)
    (l : Rˣ) (G : GL (Fin b) R) (hG : (G : Matrix (Fin b) (Fin b) R)ᵀ * J₁ * (G : Matrix (Fin b) (Fin b) R).map s = J₁) :
    ∃ m : GL (Fin (b + 2)) R, (m : Matrix _ _ R)ᵀ * J * (m : Matrix _ _ R).map s = J ∧
      (m : Matrix _ _ R) *ᵥ x = l.1 • x ∧ (m : Matrix _ _ R) *ᵥ y = s (l⁻¹).1 • y ∧
      (m : Matrix _ _ R) * ι = ι * (G : Matrix (Fin b) (Fin b) R) := by
  set P := fromCols ι (cols2 x y) with hP
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP
  set D := blk (G : Matrix (Fin b) (Fin b) R) l.1 (s (l⁻¹).1)
  set D' := blk ((G⁻¹ : GL (Fin b) R) : Matrix (Fin b) (Fin b) R) (l⁻¹).1 (s l.1)
  have hDD : D * D' = 1 := by
    simp only [D, D', blk, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      diagonal_mul_diagonal]
    rw [← fromBlocks_one]
    congr 1
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal, ← map_mul]
  have hDD' : D' * D = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hDD
  refine ⟨⟨P * D * Q, P * D' * Q, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · calc P * D * Q * (P * D' * Q) = P * D * (Q * P) * D' * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P, hDD, Matrix.mul_one, hPQ]
  · calc P * D' * Q * (P * D * Q) = P * D' * (Q * P) * D * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P, hDD', Matrix.mul_one, hPQ]
  · refine conj_eq s P Q hPQ J D ?_
    rw [hK]
    simp only [D, blk, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, Matrix.transpose_zero,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.map_zero _ (map_zero s), diagonal_map (map_zero s),
      diagonal_transpose, hG]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap2, diagonal, Matrix.mul_apply, Fin.sum_univ_two, hs, ← map_mul]
  all_goals simp only [Units.val_mk]
  · have hx : P *ᵥ Pi.single (Sum.inr 0) 1 = x := by
      rw [mulVec_single_one]; ext i; simp [P, cols2, Matrix.col]
    have hDx : D *ᵥ Pi.single (Sum.inr 0) 1 = l.1 • Pi.single (Sum.inr 0) 1 := by
      rw [mulVec_single_one]; ext (i | i)
      · simp [D, blk, Matrix.col]
      · fin_cases i <;> simp [D, blk, diagonal, Matrix.col]
    rw [← hx, mulVec_mulVec, show P * D * Q * P = P * D by rw [Matrix.mul_assoc, hQP, Matrix.mul_one],
      ← mulVec_mulVec, hDx, mulVec_smul]
  · have hy : P *ᵥ Pi.single (Sum.inr 1) 1 = y := by
      rw [mulVec_single_one]; ext i; simp [P, cols2, Matrix.col]
    have hDy : D *ᵥ Pi.single (Sum.inr 1) 1 = s (l⁻¹).1 • Pi.single (Sum.inr 1) 1 := by
      rw [mulVec_single_one]; ext (i | i)
      · simp [D, blk, Matrix.col]
      · fin_cases i <;> simp [D, blk, diagonal, Matrix.col]
    rw [← hy, mulVec_mulVec, show P * D * Q * P = P * D by rw [Matrix.mul_assoc, hQP, Matrix.mul_one],
      ← mulVec_mulVec, hDy, mulVec_smul]
  · set E1 := fromRows (1 : Matrix (Fin b) (Fin b) R) (0 : Matrix (Fin 2) (Fin b) R) with hE1
    have hι : P * E1 = ι := by
      simp [P, E1, fromCols_mul_fromRows]
    have hDι : D * E1 = E1 * (G : Matrix (Fin b) (Fin b) R) := by
      rw [hE1, fromRows_mul]
      ext (i | i) j <;> simp [D, blk, Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
    have h3 : P * D * Q * (P * E1) = P * D * E1 := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (P * D), hQP, Matrix.mul_one]
    have fin : P * D * Q * ι = ι * (G : Matrix (Fin b) (Fin b) R) := by
      rw [← hι, h3, Matrix.mul_assoc, hDι, ← Matrix.mul_assoc]
    exact fin

end Abstract

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_gram {n : ℕ} {p q : Type} [Fintype p] [Fintype q] (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin n) p E) (B : Matrix (Fin n) q E) (j : p) (k : q) :
    (Aᵀ * J * B.map σ) j k = form σ J (fun i => A i j) (fun i => B i k) := by
  simp only [form, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_flip (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (herm : ∀ i j, σ (J j i) = J i j) (v w : Fin n → E) : form σ J v w = σ (form σ J w v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [herm]
  ring

theorem det_ne_of_sig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  set Dg : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := fromBlocks 1 0 0 (-1)
  have hD : Dg * Dg = 1 := by simp [Dg, fromBlocks_multiply, fromBlocks_one]
  have h1 : Dg * Aᵀ * M * A.map star = 1 := by
    have : Dg * Aᵀ * M * A.map star = Dg * (Aᵀ * M * A.map star) := by simp only [Matrix.mul_assoc]
    rw [this, hA, hD]
  have h2 := (Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv.trans (finCongr hrs))).1 h1
  exact Matrix.det_ne_zero_of_left_inverse (B := A.map star * Dg * Aᵀ) (by simpa [Matrix.mul_assoc] using h2)

theorem gram_block (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {b : ℕ} {Y : Spc F E (b + 2)}
    {Y₁ : Spc F E b} (herm : ∀ i j, σ (Y.J j i) = Y.J i j) {H : Plane E (b + 2) b} {i₀ i₁ : ℕ}
    (hA : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    (fromCols H.ι (cols2 H.x H.y))ᵀ * Y.J * (fromCols H.ι (cols2 H.x H.y)).map σ = fromBlocks Y₁.J 0 0 swap2 := by
  have hmap : (fromCols H.ι (cols2 H.x H.y)).map σ = fromCols (H.ι.map σ) ((cols2 H.x H.y).map σ) := by
    ext i (j | j) <;> rfl
  have ho : ∀ j, (fun i => H.ι i j) = H.ι *ᵥ Pi.single j 1 := fun j => by rw [mulVec_single_one]; rfl
  have orth' : ∀ j, form σ Y.J (fun i => H.ι i j) H.x = 0 ∧ form σ Y.J (fun i => H.ι i j) H.y = 0 := fun j => by
    rw [ho]; exact hA.orth _
  rw [hmap, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols, hA.gram]
  congr 1
  · ext j k
    rw [form_gram, ho]
    fin_cases k
    · simpa [cols2] using (hA.orth (Pi.single j 1)).1
    · simpa [cols2] using (hA.orth (Pi.single j 1)).2
  · ext k j
    rw [form_gram, form_flip σ hσ herm]
    fin_cases k
    · simp [cols2, (orth' j).1]
    · simp [cols2, (orth' j).2]
  · ext k k'
    rw [form_gram]
    fin_cases k <;> fin_cases k' <;>
      simp [cols2, swap2, hA.xx, hA.yy, hA.xy, form_flip σ hσ herm H.y H.x]

theorem cA_invol {σ : E →ₐ[F] E} (hσ : ∀ z, σ (σ z) = z) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, hσ]
  | add u v hu hv => simp [map_add, hu, hv]

theorem levi_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∃ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, ∀ l g₀, IsLevi H l g₀ (m l g₀) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hcf : ∀ e, cA σ (f e) = f (σ e) := fun e => by simp [cA, hf, inclR]
  have hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hK' : (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)))ᵀ * incM F G.V.J *
      (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y))).map (cA σ).toRingHom =
      fromBlocks (incM F G₁.V.J) 0 0 swap2 := by
    rw [← hPf]
    have h1 : (P.map f).map (cA σ).toRingHom = (P.map σ).map f := by
      ext i j; simp [hcf]
    have h2 : incM F G.V.J = G.V.J.map f := rfl
    rw [h1, h2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hK, hKdef, fromBlocks_map]
    congr 1
    · simp
    · simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [swap2]
  have key : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J), ∃ m : GL (Fin (b + 2)) (AE F E),
      (m : Matrix _ _ (AE F E))ᵀ * incM F G.V.J * (m : Matrix _ _ (AE F E)).map (cA σ).toRingHom = incM F G.V.J ∧
      (m : Matrix _ _ (AE F E)) *ᵥ incV F H.x = l.1 • incV F H.x ∧
      (m : Matrix _ _ (AE F E)) *ᵥ incV F H.y = (cA σ).toRingHom (l⁻¹).1 • incV F H.y ∧
      (m : Matrix _ _ (AE F E)) * incM F H.ι = incM F H.ι * (g₀.1 : Matrix (Fin b) (Fin b) (AE F E)) :=
    fun l g₀ => levi_mat (cA σ).toRingHom (cA_invol hσ) (incM F H.ι) (incV F H.x) (incV F H.y) (incM F G.V.J)
      (incM F G₁.V.J) (Q.map f) hQP' hK' l g₀.1 g₀.2
  choose m hm using key
  exact ⟨fun l g₀ => ⟨m l g₀, (hm l g₀).1⟩, fun l g₀ => ⟨(hm l g₀).2.1, (hm l g₀).2.2.1, (hm l g₀).2.2.2⟩⟩

end Field

end GlobalTheory.LeviElem
end
end

section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviHom

open Matrix GlobalTheory.LeviElem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem levi_mul_cols {σ : E →ₐ[F] E} {b : ℕ} {W : Spc F E (b + 2)} {W₁ : Spc F E b}
    (H : Plane E (b + 2) b) (l : (AE F E)ˣ) (g₀ : UA σ W₁.J) (h : UA σ W.J) (hL : IsLevi H l g₀ h) :
    mat h * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) =
      fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) * blk (mat g₀) l.1 (cA σ (l⁻¹).1) := by
  obtain ⟨hx, hy, hι⟩ := hL
  rw [mul_fromCols, blk, fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, zero_add]
  refine congrArg₂ fromCols hι ?_
  ext i k
  rw [mul_diagonal]
  fin_cases k
  · have := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp [cols2, Matrix.mul_apply]
    first | (rw [this]; ring) | (rw [mul_comm (incV F H.x i), ← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  · have := congrFun hy i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp [cols2, Matrix.mul_apply]
    first | (rw [this]; ring) | (rw [mul_comm (incV F H.y i), ← this]; done) | (rw [mul_comm (incV F H.y i), ← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)

theorem isLevi_mul {σ : E →ₐ[F] E} {b : ℕ} {W : Spc F E (b + 2)} {W₁ : Spc F E b} (H : Plane E (b + 2) b)
    {l l' : (AE F E)ˣ} {g₀ g₀' : UA σ W₁.J} {h h' : UA σ W.J} (hL : IsLevi H l g₀ h) (hL' : IsLevi H l' g₀' h') :
    IsLevi H (l * l') (g₀ * g₀') (h * h') := by
  obtain ⟨hx, hy, hι⟩ := hL
  obtain ⟨hx', hy', hι'⟩ := hL'
  have hm : ∀ (A B : UA σ W.J), mat (A * B) = mat A * mat B := fun _ _ => rfl
  have hm₁ : ∀ (A B : UA σ W₁.J), mat (A * B) = mat A * mat B := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, ← mulVec_mulVec, hx', mulVec_smul, hx, smul_smul, Units.val_mul, mul_comm]
  · rw [hm, ← mulVec_mulVec, hy', mulVec_smul, hy, smul_smul, _root_.mul_inv_rev, Units.val_mul, map_mul]
  · rw [hm, hm₁, Matrix.mul_assoc, hι', ← Matrix.mul_assoc, hι, Matrix.mul_assoc]

theorem levi_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    (∀ l l' g₀ g₀', m (l * l') (g₀ * g₀') = m l g₀ * m l' g₀') ∧ Continuous (fun x : (AE F E)ˣ × UA σ G₁.V.J => m x.1 x.2) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ m hm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set PA := fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) with hPA
  have hPf : P.map f = PA := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * PA = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hPQ' : PA * Q.map f = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'
  set QA := Q.map f

  have hform : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h : UA σ G.V.J), IsLevi H l g₀ h → mat h = PA * blk (mat g₀) l.1 (cA σ (l⁻¹).1) * QA := by
    intro l g₀ h hL
    rw [← levi_mul_cols H l g₀ h hL, Matrix.mul_assoc, hPQ', Matrix.mul_one]
  have huniq : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h h' : UA σ G.V.J), IsLevi H l g₀ h → IsLevi H l g₀ h' → h = h' := by
    intro l g₀ h h' hL hL'
    have e : mat h = mat h' := by rw [hform l g₀ h hL, hform l g₀ h' hL']
    exact Subtype.ext (Units.ext e)
  have hmul : ∀ l l' g₀ g₀', m (l * l') (g₀ * g₀') = m l g₀ * m l' g₀' := fun l l' g₀ g₀' =>
    huniq _ _ _ _ (hm _ _) (isLevi_mul H (hm l g₀) (hm l' g₀'))
  refine ⟨hmul, ?_⟩
  have m11 : m 1 1 = 1 := by
    have := hmul 1 1 1 1
    simp only [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hinv : ∀ l g₀, (m l g₀)⁻¹ = m l⁻¹ g₀⁻¹ := fun l g₀ =>
    inv_eq_of_mul_eq_one_right (by rw [← hmul, mul_inv_cancel, mul_inv_cancel, m11])
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hmat : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, Continuous fun g : UA σ J => mat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hvec : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => ![x.1.1, cA σ (x.1⁻¹).1] := by
    refine continuous_pi fun k => ?_
    fin_cases k
    · exact Units.continuous_val.comp continuous_fst
    · exact hcA.comp (Units.continuous_coe_inv.comp continuous_fst)
  have hval : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2) := by
    have : (fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2)) =
        fun x => PA * blk (mat x.2) x.1.1 (cA σ (x.1⁻¹).1) * QA := funext fun x => hform _ _ _ (hm _ _)
    rw [this]
    refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
    exact Continuous.matrix_fromBlocks (hmat.comp continuous_snd) continuous_const continuous_const
      (Continuous.matrix_diagonal hvec)
  have hGL : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => ((m x.1 x.2 : UA σ G.V.J) : GL (Fin (b + 2)) (AE F E)) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have : (fun x : (AE F E)ˣ × UA σ G₁.V.J => ((((m x.1 x.2 : UA σ G.V.J) : GL (Fin (b + 2)) (AE F E))⁻¹ :
        GL (Fin (b + 2)) (AE F E)) : Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E))) =
        (fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2)) ∘ fun x => (x.1⁻¹, x.2⁻¹) := by
      funext x
      simp only [Function.comp_apply, ← hinv]
      rfl
    rw [this]
    exact hval.comp ((continuous_inv.comp continuous_fst).prodMk (continuous_inv.comp continuous_snd))
  exact continuous_induced_rng.2 hGL

end GlobalTheory.LeviHom
end
end

section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.LeviPlaneHom

open Matrix GlobalTheory.LeviElem GlobalTheory.LeviHom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_flip_skew (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (skew : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → E) : form σ J v w = -σ (form σ J w v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [skew]
  ring

def skew2 : Matrix (Fin 2) (Fin 2) E := !![0, 1; -1, 0]

theorem gram_block_skew (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {b : ℕ} (W : Spc F E (b + 2)) (W₁ : Spc F E b)
    (H : Plane E (b + 2) b) (skew : ∀ i j, σ (W.J j i) = -W.J i j)
    (hxx : form σ W.J H.x H.x = 0) (hyy : form σ W.J H.y H.y = 0) (hxy : form σ W.J H.x H.y = 1)
    (horth : ∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) (hgram : H.ιᵀ * W.J * H.ι.map σ = W₁.J) :
    (fromCols H.ι (cols2 H.x H.y))ᵀ * W.J * (fromCols H.ι (cols2 H.x H.y)).map σ = fromBlocks W₁.J 0 0 skew2 := by
  have hmap : (fromCols H.ι (cols2 H.x H.y)).map σ = fromCols (H.ι.map σ) ((cols2 H.x H.y).map σ) := by
    ext i (j | j) <;> rfl
  have ho : ∀ j, (fun i => H.ι i j) = H.ι *ᵥ Pi.single j 1 := fun j => by rw [mulVec_single_one]; rfl
  have orth' : ∀ j, form σ W.J (fun i => H.ι i j) H.x = 0 ∧ form σ W.J (fun i => H.ι i j) H.y = 0 := fun j => by
    rw [ho]; exact horth _
  rw [hmap, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols, hgram]
  congr 1
  · ext j k
    rw [form_gram, ho]
    fin_cases k
    · simpa [cols2] using (horth (Pi.single j 1)).1
    · simpa [cols2] using (horth (Pi.single j 1)).2
  · ext k j
    rw [form_gram, form_flip_skew σ hσ skew]
    fin_cases k
    · simp [cols2, (orth' j).1]
    · simp [cols2, (orth' j).2]
  · ext k k'
    rw [form_gram]
    fin_cases k <;> fin_cases k' <;>
      simp [cols2, skew2, hxx, hyy, hxy, form_flip_skew σ hσ skew H.y H.x]

theorem levi_section_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ a b, M (a * b) = M a * M b) ∧ ∀ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H t 1 m → ∀ y, m * M y = M y * m := by
  intro F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H hskew hn hxx hyy hxy horth hgram c₀ hc₀ hND₁ _ M hM
  subst hn
  have hdet : W₁.J.det ≠ 0 := by
    intro h0
    apply hND₁.2
    rw [det_smul, show (W₁.J.map σ).det = σ W₁.J.det from (RingHom.map_det (σ : E →+* E) _).symm, h0, map_zero, mul_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * W.J * P.map σ = fromBlocks W₁.J 0 0 skew2 :=
    gram_block_skew σ hσ W W₁ H hskew hxx hyy hxy horth hgram
  set K : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := fromBlocks W₁.J 0 0 skew2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [skew2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * W.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * W.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set PA := fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) with hPA
  have hPf : P.map f = PA := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * PA = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hPQ' : PA * Q.map f = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'
  have huniq : ∀ (l : (AE F E)ˣ) (g₀ : UA σ W₁.J) (h h' : UA σ W.J), IsLevi (W₁ := W₁) H l g₀ h →
      IsLevi (W₁ := W₁) H l g₀ h' → h = h' := by
    intro l g₀ h h' hL hL'
    have e : mat h = mat h' := by
      rw [← Matrix.mul_one (mat h), ← Matrix.mul_one (mat h'), ← hPQ', ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        levi_mul_cols H l g₀ h hL, levi_mul_cols H l g₀ h' hL']
    exact Subtype.ext (Units.ext e)
  refine ⟨fun a b => ?_, fun t m hm y => ?_⟩
  · have h2 := isLevi_mul H (hM a) (hM b)
    rw [mul_one] at h2
    exact huniq _ _ _ _ (hM (a * b)) h2
  · have h1 := isLevi_mul H hm (hM y)
    have h2 := isLevi_mul H (hM y) hm
    rw [mul_one, one_mul] at h1
    rw [mul_one, one_mul] at h2
    exact huniq _ _ _ _ h1 h2

end GlobalTheory.LeviPlaneHom
end
end

section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.LeviSplit

open Matrix

section Ring

variable {R : Type} [CommRing R] {n n₁ k : ℕ}

theorem frame_up {g : Matrix (Fin n) (Fin n) R} {h : Matrix (Fin n₁) (Fin n₁) R} {ι : Matrix (Fin n) (Fin n₁) R}
    {C' : Matrix (Fin n) (Fin (k + 1)) R} {C : Matrix (Fin n₁) (Fin k) R} {B : Matrix (Fin k) (Fin k) R} {t : R}
    (hC : ∀ i j, C' i j.succ = (ι * C) i j) (hv : g *ᵥ (fun i => C' i 0) = t • fun i => C' i 0) (hι : g * ι = ι * h)
    (hB : h * C = C * B) : ∃ B' : Matrix (Fin (k + 1)) (Fin (k + 1)) R, B'.det = t * B.det ∧ g * C' = C' * B' := by
  refine ⟨Matrix.of (Fin.cons (Fin.cons t 0) fun i => Fin.cons 0 (B i)), ?_, ?_⟩
  · rw [det_succ_column_zero, Fin.sum_univ_succ]
    simp only [of_apply, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [Fin.val_zero, pow_zero, one_mul]
    congr 1
  · ext i j
    refine Fin.cases ?_ (fun j => ?_) j
    · have := congrFun hv i
      rw [mul_apply, mul_apply, Fin.sum_univ_succ]
      simp only [of_apply, Fin.cons_zero, Fin.cons_succ, mul_zero, Finset.sum_const_zero, add_zero]
      simpa [mulVec, dotProduct, mul_comm] using this
    · have e : g * (ι * C) = (ι * C) * B := by
        rw [← Matrix.mul_assoc, hι, Matrix.mul_assoc, hB, Matrix.mul_assoc]
      have := congrFun (congrFun e i) j
      rw [mul_apply, mul_apply] at this
      rw [mul_apply, mul_apply, Fin.sum_univ_succ]
      simp only [of_apply, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, mul_zero, zero_add, hC]
      exact this

theorem frame_down {g : Matrix (Fin n) (Fin n) R} {h : Matrix (Fin n₁) (Fin n₁) R} {ι : Matrix (Fin n) (Fin n₁) R}
    {C' : Matrix (Fin n) (Fin (k + 1)) R} {C : Matrix (Fin n₁) (Fin k) R} {B' : Matrix (Fin (k + 1)) (Fin (k + 1)) R} {t : R}
    {L : Matrix (Fin n₁) (Fin n) R} {Λ : Matrix (Fin (k + 1)) (Fin n) R} (hΛ : Λ * C' = 1) (hL : L * ι = 1)
    (hL0 : L *ᵥ (fun i => C' i 0) = 0)
    (hC : ∀ i j, C' i j.succ = (ι * C) i j) (hv : g *ᵥ (fun i => C' i 0) = t • fun i => C' i 0) (hι : g * ι = ι * h)
    (hB : g * C' = C' * B') : ∃ B : Matrix (Fin k) (Fin k) R, B'.det = t * B.det ∧ h * C = C * B := by
  have e0 : (fun i => C' i 0) = C' *ᵥ Pi.single 0 1 := by rw [mulVec_single_one]; rfl
  have hcol : B' *ᵥ Pi.single 0 1 = t • (Pi.single 0 1 : Fin (k + 1) → R) := by
    rw [e0, mulVec_mulVec, hB] at hv
    have := congrArg (Λ *ᵥ ·) hv
    simpa only [mulVec_mulVec, ← Matrix.mul_assoc, hΛ, Matrix.one_mul, mulVec_smul, one_mulVec] using this
  rw [mulVec_single_one] at hcol
  have h0 : B' 0 0 = t := by simpa using congrFun hcol 0
  have hs : ∀ i : Fin k, B' i.succ 0 = 0 := fun i => by simpa using congrFun hcol i.succ
  refine ⟨B'.submatrix Fin.succ Fin.succ, ?_, ?_⟩
  · rw [det_succ_column_zero, Fin.sum_univ_succ]
    simp [h0, hs]
  · have e1 : C'.submatrix id Fin.succ = ι * C := by ext i j; exact hC i j
    have e2 : L * C' = Matrix.of fun i => Fin.cons 0 (C i) := by
      ext i j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact congrFun hL0 i
      · have : L * (C'.submatrix id Fin.succ) = C := by rw [e1, ← Matrix.mul_assoc, hL, Matrix.one_mul]
        exact congrFun (congrFun this i) j
    have e3 : h * C = (L * (g * C')).submatrix id Fin.succ := by
      have : (L * (g * C')).submatrix id Fin.succ = L * (g * C'.submatrix id Fin.succ) := rfl
      rw [this, e1, ← Matrix.mul_assoc g, hι, Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul]
    rw [e3, hB, ← Matrix.mul_assoc, e2]
    ext i j
    simp [mul_apply, Fin.sum_univ_succ]

end Ring

theorem exists_prod_equiv {G B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group B] [TopologicalSpace B]
    (A T : Subgroup G) (m : B → A) (π : A → B) (hm : Continuous m) (hπ : Continuous π) (hmm : ∀ a b, m (a * b) = m a * m b)
    (hππ : ∀ a b, π (a * b) = π a * π b) (hπm : ∀ b, π (m b) = b) (hTA : T ≤ A) (hT : ∀ a : A, a.1 ∈ T ↔ π a = 1)
    (hc : ∀ τ ∈ T, ∀ b, τ * (m b : G) = m b * τ) : ∃ φ : T × B ≃ₜ* A, ∀ p, (φ p : G) = p.1 * m p.2 := by
  let π' := MonoidHom.mk' π hππ
  have h1 : ∀ τ : T, π' ⟨τ, hTA τ.2⟩ = 1 := fun τ => (hT ⟨τ, hTA τ.2⟩).1 τ.2
  have h2 : ∀ b, π' (m b) = b := hπm
  have h3 : ∀ (τ : T) b, π' (⟨τ, hTA τ.2⟩ * m b) = b := fun τ b => by rw [map_mul, h1, h2, one_mul]
  refine ⟨{ toFun := fun p => ⟨p.1, hTA p.1.2⟩ * m p.2
            invFun := fun a => (⟨(a * (m (π' a))⁻¹ : A), (hT _).2 (show π' _ = 1 by rw [map_mul, map_inv, h2, mul_inv_cancel])⟩, π' a)
            left_inv := fun p => Prod.ext (Subtype.ext ?_) (h3 _ _)
            right_inv := fun a => Subtype.ext ?_
            map_mul' := fun p q => Subtype.ext ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun p => rfl⟩
  · simp only [h3]
    simp
  · simp
  · simp only [Prod.fst_mul, Prod.snd_mul, hmm, Subgroup.coe_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc (q.1 : G), hc _ q.1.2, mul_assoc]
  · exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).mul (hm.comp continuous_snd)
  · exact ((continuous_subtype_val.comp (continuous_id.mul (hm.comp hπ).inv)).subtype_mk _).prodMk hπ

theorem vmv_zero {R : Type} [CommRing R] {n m : ℕ} (x : Fin n → R) : vecMulVec x (0 : Fin m → R) = 0 := by
  ext i j
  simp [vecMulVec_apply]

theorem lines_ring {R : Type} [CommRing R] {n n₁ : ℕ} (c : R →+* R) {J g : Matrix (Fin n) (Fin n) R}
    {ι : Matrix (Fin n) (Fin n₁) R} {L : Matrix (Fin n₁) (Fin n) R} {x y : Fin n → R} {t s : Rˣ}
    (hxy : x ⬝ᵥ J *ᵥ (c ∘ y) = 1) (hx : (J *ᵥ (c ∘ x)) ᵥ* ι = 0) (hy : (J *ᵥ (c ∘ y)) ᵥ* ι = 0)
    (hD : ι * L + vecMulVec x (J *ᵥ (c ∘ y)) - vecMulVec y (J *ᵥ (c ∘ x)) = 1)
    (hg : gᵀ * J * g.map c = J) (gx : g *ᵥ x = t.1 • x) (gy : g *ᵥ y = s.1 • y) :
    t.1 * c s = 1 ∧ g * ι = ι * (L * g * ι) := by
  have key : ∀ (v : Fin n → R) (u : Rˣ), g *ᵥ v = u.1 • v → c u • ((J *ᵥ (c ∘ v)) ᵥ* g) = J *ᵥ (c ∘ v) := fun v u hv => by
    have e : g.map c *ᵥ (c ∘ v) = c u • (c ∘ v) := by
      funext i
      rw [← RingHom.map_mulVec, hv]
      simp
    conv_rhs => rw [← hg, ← mulVec_mulVec, e, mulVec_smul, ← mulVec_mulVec, mulVec_transpose]
  have key2 : ∀ (v : Fin n → R) (u : Rˣ), g *ᵥ v = u.1 • v → (J *ᵥ (c ∘ v)) ᵥ* ι = 0 → (J *ᵥ (c ∘ v)) ᵥ* (g * ι) = 0 :=
    fun v u hv h0 => by
      rw [← key v u hv, smul_vecMul, vecMul_vecMul] at h0
      exact ((u.isUnit.map c).smul_eq_zero).1 h0
  refine ⟨?_, ?_⟩
  · have := congrArg (x ⬝ᵥ ·) (key y s gy)
    rw [dotProduct_smul, dotProduct_comm, ← dotProduct_mulVec, gx, dotProduct_smul, dotProduct_comm, hxy] at this
    simpa [mul_comm] using this
  · conv_lhs => rw [← Matrix.one_mul (g * ι), ← hD, Matrix.sub_mul, Matrix.add_mul, vecMulVec_mul, vecMulVec_mul,
      key2 x t gx hx, key2 y s gy hy]
    simp [Matrix.mul_assoc, vmv_zero]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.LeviElem GlobalTheory.LeviHom GlobalTheory.LeviPlaneHom in

theorem exists_proj (hσ : ∀ z, σ (σ z) = z) {b : ℕ} (W : Spc F E (b + 2)) (W₁ : Spc F E b)
    (H : Plane E (b + 2) b) (skew : ∀ i j, σ (W.J j i) = -W.J i j)
    (hxx : form σ W.J H.x H.x = 0) (hyy : form σ W.J H.y H.y = 0) (hxy : form σ W.J H.x H.y = 1)
    (horth : ∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) (hgram : H.ιᵀ * W.J * H.ι.map σ = W₁.J)
    (hdet : W₁.J.det ≠ 0) : ∃ L : Matrix (Fin b) (Fin (b + 2)) E, L * H.ι = 1 ∧ L *ᵥ H.x = 0 ∧ L *ᵥ H.y = 0 ∧
      (W.J *ᵥ (σ ∘ H.x)) ᵥ* H.ι = 0 ∧ (W.J *ᵥ (σ ∘ H.y)) ᵥ* H.ι = 0 ∧
      H.ι * L + vecMulVec H.x (W.J *ᵥ (σ ∘ H.y)) - vecMulVec H.y (W.J *ᵥ (σ ∘ H.x)) = 1 := by
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * W.J * P.map σ = fromBlocks W₁.J 0 0 skew2 :=
    gram_block_skew σ hσ W W₁ H skew hxx hyy hxy horth hgram
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks W₁.J 0 0 skew2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [skew2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * W.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * W.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP
  set L := Q.submatrix Sum.inl id
  have h1 : L * H.ι = 1 := by
    ext i j
    exact (congrFun (congrFun hQP (.inl i)) (.inl j)).trans (by simp [Matrix.one_apply])
  have h2 : L *ᵥ H.x = 0 := by
    funext i
    exact (congrFun (congrFun hQP (.inl i)) (.inr 0)).trans (by simp [Matrix.one_apply])
  have h3 : L *ᵥ H.y = 0 := by
    funext i
    exact (congrFun (congrFun hQP (.inl i)) (.inr 1)).trans (by simp [Matrix.one_apply])
  have ho : ∀ v, (∀ u, form σ W.J (H.ι *ᵥ u) v = 0) → (W.J *ᵥ (σ ∘ v)) ᵥ* H.ι = 0 := fun v hv => by
    funext j
    have := hv (Pi.single j 1)
    rw [mulVec_single_one, form, dotProduct_comm] at this
    exact this
  have h4 := ho _ fun u => (horth u).1
  have h5 := ho _ fun u => (horth u).2
  have hyx : form σ W.J H.y H.x = -1 := by rw [form_flip_skew σ hσ skew, hxy, map_one]
  refine ⟨L, h1, h2, h3, h4, h5, ?_⟩
  set D := H.ι * L + vecMulVec H.x (W.J *ᵥ (σ ∘ H.y)) - vecMulVec H.y (W.J *ᵥ (σ ∘ H.x)) with hD
  have hv : ∀ v, L *ᵥ v = 0 → D *ᵥ v = form σ W.J v H.y • H.x - form σ W.J v H.x • H.y := fun v hv => by
    rw [hD, sub_mulVec, add_mulVec, ← mulVec_mulVec, hv, mulVec_zero, zero_add, vecMulVec_mulVec, vecMulVec_mulVec,
      op_smul_eq_smul, op_smul_eq_smul, dotProduct_comm _ v, dotProduct_comm _ v]
    rfl
  have d1 : D * H.ι = H.ι := by
    rw [hD, Matrix.sub_mul, Matrix.add_mul, vecMulVec_mul, vecMulVec_mul, h4, h5, Matrix.mul_assoc, h1]
    simp [vmv_zero]
  have d2 : D *ᵥ H.x = H.x := by rw [hv _ h2, hxy, hxx]; simp
  have d3 : D *ᵥ H.y = H.y := by rw [hv _ h3, hyy, hyx]; simp
  have hDP : D * P = P := by
    ext i (j | j)
    · exact congrFun (congrFun d1 i) j
    · fin_cases j
      · exact congrFun d2 i
      · exact congrFun d3 i
  rw [← Matrix.mul_one D, ← hPQ, ← Matrix.mul_assoc, hDP]

theorem incM_mul {l m k : ℕ} (A : Matrix (Fin l) (Fin m) E) (B : Matrix (Fin m) (Fin k) E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

theorem incM_mulVec {l m : ℕ} (A : Matrix (Fin l) (Fin m) E) (v : Fin m → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := funext fun i => (RingHom.map_mulVec (inclR (F := F) (AF F)) A v i).symm

theorem incM_one {l : ℕ} : incM F (1 : Matrix (Fin l) (Fin l) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem incV_zero {l : ℕ} : incV F (0 : Fin l → E) = 0 := funext fun _ => map_zero (inclR (F := F) (AF F))

theorem isLevi_of_lines {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {L : Matrix (Fin n₁) (Fin n) E}
    (hxy : form σ W.J H.x H.y = 1) (hgram : H.ιᵀ * W.J * H.ι.map σ = W₁.J) (hdet : W₁.J.det ≠ 0)
    (hσ : ∀ z, σ (σ z) = z)
    (hx : (W.J *ᵥ (σ ∘ H.x)) ᵥ* H.ι = 0) (hy : (W.J *ᵥ (σ ∘ H.y)) ᵥ* H.ι = 0)
    (hD : H.ι * L + vecMulVec H.x (W.J *ᵥ (σ ∘ H.y)) - vecMulVec H.y (W.J *ᵥ (σ ∘ H.x)) = 1)
    (g : UA σ W.J) {t s : (AE F E)ˣ} (gx : mat g *ᵥ incV F H.x = t.1 • incV F H.x)
    (gy : mat g *ᵥ incV F H.y = s.1 • incV F H.y) : ∃ h₁ : UA σ W₁.J, IsLevi H t h₁ g := by
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  let c : AE F E →+* AE F E := cA σ
  have hcc : ∀ z, c (c z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [c, cA, hσ]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have e : ∀ v : Fin n → E, incM F W.J *ᵥ (c ∘ incV F v) = incV F (W.J *ᵥ (σ ∘ v)) := fun v => incM_mulVec W.J (σ ∘ v)
  have ev : ∀ v : Fin n → E, v ᵥ* H.ι = 0 → incV F v ᵥ* incM F H.ι = 0 := fun v hv => funext fun i =>
    (RingHom.map_vecMul f H.ι v i).symm.trans (by rw [hv]; exact map_zero f)
  have hg : (mat g)ᵀ * incM F W.J * (mat g).map c = incM F W.J := g.2
  obtain ⟨h1, h2⟩ := lines_ring c (J := incM F W.J) (ι := incM F H.ι) (L := incM F L) (x := incV F H.x) (y := incV F H.y)
    (by rw [e]; exact (RingHom.map_dotProduct f _ _).symm.trans (by rw [← map_one f, ← hxy]; rfl))
    (by rw [e]; exact ev _ hx) (by rw [e]; exact ev _ hy)
    (by
      rw [e, e, ← incM_one, ← hD, ← incM_mul]
      ext i j
      simp only [incM, incV, vecMulVec_apply, map_apply, Matrix.sub_apply, Matrix.add_apply, map_sub, map_add, map_mul]) hg gx gy
  set h := incM F L * mat g * incM F H.ι
  have hgr : (incM F H.ι)ᵀ * incM F W.J * (incM F H.ι).map c = incM F W₁.J := by
    rw [← hgram, incM_mul, incM_mul]; rfl
  have hu : hᵀ * incM F W₁.J * h.map c = incM F W₁.J := by
    have : (mat g * incM F H.ι)ᵀ * incM F W.J * (mat g * incM F H.ι).map c = incM F W₁.J := by
      rw [← hgr, transpose_mul, Matrix.map_mul]
      conv_rhs => rw [← hg]
      simp only [Matrix.mul_assoc]
    rw [h2, transpose_mul, Matrix.map_mul] at this
    conv_lhs => rw [← hgr]
    rw [← this]
    simp only [Matrix.mul_assoc]
  have hunit : IsUnit h := by
    have hJ : IsUnit (incM F W₁.J).det := by
      rw [show (incM F W₁.J).det = f W₁.J.det from (RingHom.map_det f _).symm]
      exact (IsUnit.mk0 _ hdet).map f
    rw [← hu, det_mul, det_mul, det_transpose, mul_assoc] at hJ
    exact (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hJ)
  refine ⟨⟨hunit.unit, hu⟩, gx, ?_, h2⟩
  rw [gy]
  congr 1
  have : c s = t⁻¹.1 := by rw [← Units.inv_mul_cancel_left t (c s), h1, mul_one]
  rw [← hcc s, this]
  rfl

open GlobalTheory.StdPar GlobalTheory.SiegelSet in
theorem mem_frameStab {n k : ℕ} {J : Matrix (Fin n) (Fin n) E} {C : Matrix (Fin n) (Fin k) E} {D : Subgroup (AE F E)ˣ}
    {g : GAd σ J} : g ∈ frameStab σ J C (D.comap Matrix.GeneralLinearGroup.det) ↔
      ∃ (B : Matrix (Fin k) (Fin k) (AE F E)) (u : (AE F E)ˣ), u ∈ D ∧ B.det = u ∧ (matHom _ σ J g).1 * incM F C = incM F C * B := by
  refine ⟨fun ⟨B, hB, e⟩ => ⟨B, _, hB, rfl, e⟩, fun ⟨B, u, hu, hd, e⟩ => ?_⟩
  have hB : IsUnit B := (isUnit_iff_isUnit_det _).2 (hd ▸ u.isUnit)
  refine ⟨hB.unit, ?_, e⟩
  rwa [Subgroup.mem_comap, show Matrix.GeneralLinearGroup.det hB.unit = u from Units.ext hd]

open GlobalTheory.StdPar GlobalTheory.SiegelSet in

theorem frameStab_succ {n n₁ r : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    {X' : Matrix (Fin n) (Fin (r + 1)) E} {X : Matrix (Fin n₁) (Fin r) E} {ι : Matrix (Fin n) (Fin n₁) E}
    {L : Matrix (Fin n₁) (Fin n) E} {Λ : Matrix (Fin (r + 1)) (Fin n) E} (hΛ : Λ * X' = 1) (hL : L * ι = 1)
    (hL0 : L *ᵥ (fun i => X' i 0) = 0) (hX : ∀ i j, X' i j.succ = (ι * X) i j) {D : Subgroup (AE F E)ˣ} {t : (AE F E)ˣ}
    (ht : t ∈ D) {g : GAd σ J} {h : GAd σ J₁}
    (hv : (matHom _ σ J g).1 *ᵥ incV F (fun i => X' i 0) = t.1 • incV F fun i => X' i 0)
    (hι : (matHom _ σ J g).1 * incM F ι = incM F ι * (matHom _ σ J₁ h).1) (k : Fin r) :
    g ∈ frameStab σ J (initCols X' k.succ) (D.comap Matrix.GeneralLinearGroup.det) ↔
      h ∈ frameStab σ J₁ (initCols X k) (D.comap Matrix.GeneralLinearGroup.det) := by
  have hC : ∀ i (j : Fin (k.val + 1)), incM F (initCols X' k.succ) i j.succ = (incM F ι * incM F (initCols X k)) i j :=
    fun i j => by
      rw [← incM_mul]
      exact congrArg (inclR (F := F) (AF F)) (hX i (j.castLE k.2))
  have hΛ' : Λ.submatrix (Fin.castLE k.succ.2) id * initCols X' k.succ = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun hΛ (i.castLE k.succ.2)) (j.castLE k.succ.2)).trans (by simp [Matrix.one_apply])
  rw [mem_frameStab, mem_frameStab]
  refine ⟨fun ⟨B', u, hu, hd, e⟩ => ?_, fun ⟨B, u, hu, hd, e⟩ => ?_⟩
  · obtain ⟨B, h1, h2⟩ := frame_down (k := k.val + 1) (L := incM F L) (Λ := incM F (Λ.submatrix (Fin.castLE k.succ.2) id))
      (by rw [← incM_mul, hΛ', incM_one]) (by rw [← incM_mul, hL, incM_one])
      ((incM_mulVec L fun i => X' i 0).trans (by rw [hL0, incV_zero])) hC hv hι e
    refine ⟨B, t⁻¹ * u, mul_mem (inv_mem ht) hu, ?_, h2⟩
    rw [Units.val_mul, ← hd, h1, Units.inv_mul_cancel_left]
  · obtain ⟨B', h1, h2⟩ := frame_up (k := k.val + 1) hC hv hι e
    exact ⟨B', t * u, mul_mem ht hu, by rw [h1, hd, Units.val_mul], h2⟩

open GlobalTheory.StdPar GlobalTheory.SiegelSet in

theorem frameStab_zero {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X' : Matrix (Fin n) (Fin (r + 1)) E}
    {D : Subgroup (AE F E)ˣ} {g : GAd σ J} :
    g ∈ frameStab σ J (initCols X' 0) (D.comap Matrix.GeneralLinearGroup.det) ↔
      ∃ t ∈ D, (matHom _ σ J g).1 *ᵥ incV F (fun i => X' i 0) = t.1 • incV F fun i => X' i 0 := by
  rw [mem_frameStab]
  refine ⟨fun ⟨B, u, hu, hd, e⟩ => ⟨u, hu, funext fun i => ?_⟩, fun ⟨t, ht, e⟩ => ⟨Matrix.of fun _ _ => t.1, t, ht, ?_, ?_⟩⟩
  · have h1 : B.det = B 0 0 := det_fin_one B
    have h2 : (incM F (initCols X' 0) * B) i 0 = incM F (initCols X' 0) i 0 * B 0 0 := Fin.sum_univ_one _
    rw [← hd, h1, Pi.smul_apply, smul_eq_mul, mul_comm]
    exact (congrFun (congrFun e i) 0).trans h2
  · exact det_fin_one _
  · ext i j
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    refine (congrFun e i).trans (Eq.symm ((Fin.sum_univ_one _).trans ?_))
    exact mul_comm _ _

open GlobalTheory.StdPar GlobalTheory.SiegelSet in
theorem mem_leviOne {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E} {S : Finset (Fin r)}
    {g : GAd σ J} : g ∈ leviOne σ J X Y S ↔ ∀ k ∈ S,
      g ∈ frameStab σ J (initCols X k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ frameStab σ J (initCols Y k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ frameStab σ J (initCols X k) ((GlobalTheory.Doubling.absE F E).ker.comap Matrix.GeneralLinearGroup.det) := by
  simp only [leviOne, levi, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.comap_top, MonoidHom.comap_ker]
  exact ⟨fun h k hk => ⟨(h.1 k hk).1, (h.1 k hk).2, h.2 k hk⟩, fun h => ⟨fun k hk => ⟨(h k hk).1, (h k hk).2.1⟩,
    fun k hk => (h k hk).2.2⟩⟩

theorem mat_of_isLevi {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {L : Matrix (Fin n₁) (Fin n) E}
    (hL : L * H.ι = 1) {t : (AE F E)ˣ} {h : UA σ W₁.J} {g : UA σ W.J} (hg : IsLevi H t h g) :
    mat h = incM F L * mat g * incM F H.ι := by
  rw [Matrix.mul_assoc, hg.2.2, ← Matrix.mul_assoc, ← incM_mul, hL, incM_one, Matrix.one_mul]

theorem rat_of_isLevi {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {L : Matrix (Fin n₁) (Fin n) E}
    (hL : L * H.ι = 1) {t : (AE F E)ˣ} {h : UA σ W₁.J} {g : UA σ W.J} (hg : IsLevi H t h g) (hr : g ∈ ratU σ W.J) :
    h ∈ ratU σ W₁.J := by
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 hr
  have e : mat h = incM F (L * γ.1 * H.ι) := by
    have : mat g = incM F γ.1 := (congrArg Units.val hγ).symm
    rw [mat_of_isLevi hL hg, incM_mul, incM_mul, this]
  rcases subsingleton_or_nontrivial (AE F E) with _ | _
  · exact Subgroup.mem_subgroupOf.2 ⟨1, Units.ext (Subsingleton.elim _ _)⟩
  · have hd : (L * γ.1 * H.ι).det ≠ 0 := fun h0 => by
      have : IsUnit (mat h).det := (isUnit_iff_isUnit_det _).1 h.1.isUnit
      rw [e, show (incM F (L * γ.1 * H.ι)).det = inclR (F := F) (AF F) (L * γ.1 * H.ι).det from (RingHom.map_det _ _).symm,
        h0, map_zero] at this
      exact not_isUnit_zero this
    exact Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext e.symm⟩

set_option maxHeartbeats 600000 in
open GlobalTheory.StdPar GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.GLTwo in
theorem leviOne_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∃ (T : Subgroup (GAd σ (c₀ • W.J.map σ)))
        (φ : T × GlobalTheory.StdPar.leviOne σ (c₀ • W₁.J.map σ) Xf Yf S' ≃ₜ*
          GlobalTheory.StdPar.leviOne σ (c₀ • W.J.map σ) X' Y' (insert 0 (S'.map (Fin.succEmb r)))),
        IsClosed (T : Set (GAd σ (c₀ • W.J.map σ))) ∧
        (∀ τ : T, ∃ t : (AE F E)ˣ, GlobalTheory.Doubling.absE F E t = 1 ∧
          IsLevi (W₁ := W₁) H t 1 ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).symm τ)) ∧
        (∀ p, ((φ p : GAd σ (c₀ • W.J.map σ))) = (p.1 : GAd σ (c₀ • W.J.map σ)) *
          GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm p.2))) ∧
        (∀ p, (φ p : GAd σ (c₀ • W.J.map σ)) ∈ ratPts σ (c₀ • W.J.map σ) ↔
          (p.1 : GAd σ (c₀ • W.J.map σ)) ∈ ratPts σ (c₀ • W.J.map σ) ∧
          (p.2 : GAd σ (c₀ • W₁.J.map σ)) ∈ ratPts σ (c₀ • W₁.J.map σ)) := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hskew hn hxx hyy hxy horth hgram c₀ hc₀ hND₁ hND M hMc hM hMr r Xf Yf hW₁ X' Y' hW
    hX0 hY0 hXY S'
  obtain ⟨hMm, hMcomm⟩ := GlobalTheory.LeviPlaneHom.levi_section_hom F E σ hcm hσ n n₁ W W₁ H hskew hn hxx hyy hxy horth hgram c₀ hc₀
    hND₁ hND M hM
  subst hn
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  have hdet : W₁.J.det ≠ 0 := by
    intro h0
    apply hND₁.2
    rw [det_smul, show (W₁.J.map σ).det = σ W₁.J.det from (RingHom.map_det (σ : E →+* E) _).symm, h0, map_zero, mul_zero]
  obtain ⟨L, hL, hLx, hLy, hx, hy, hD⟩ := exists_proj hσ W W₁ H hskew hxx hyy hxy horth hgram hdet
  set e := toGAd hσ W.J hc₀
  set e₁ := toGAd hσ W₁.J hc₀
  set A := leviOne σ (c₀ • W.J.map σ) X' Y' (insert 0 (S'.map (Fin.succEmb r))) with hA
  set B := leviOne σ (c₀ • W₁.J.map σ) Xf Yf S' with hB
  have eX : (fun i => X' i 0) = H.x := funext hX0
  have eY : (fun i => Y' i 0) = c₀⁻¹ • H.y := funext hY0
  have eY' : incV F (c₀⁻¹ • H.y) = inclR (F := F) (AF F) c₀⁻¹ • incV F H.y := funext fun i => map_mul _ _ _
  have lineY : ∀ (g : Matrix _ _ (AE F E)) (s : AE F E), g *ᵥ incV F (fun i => Y' i 0) = s • incV F (fun i => Y' i 0) ↔
      g *ᵥ incV F H.y = s • incV F H.y := fun g s => by
    rw [eY, eY', mulVec_smul, smul_comm s]
    exact ((IsUnit.mk0 _ (inv_ne_zero hc₀)).map (inclR (F := F) (AF F))).smul_left_cancel
  have trans : ∀ {t h g}, IsLevi (W₁ := W₁) H t h g → GlobalTheory.Doubling.absE F E t = 1 → (e g ∈ A ↔ e₁ h ∈ B) := by
    intro t h g hl ht
    have hv : (matHom _ σ _ (e g)).1 *ᵥ incV F (fun i => X' i 0) = t.1 • incV F fun i => X' i 0 := by
      rw [eX]; exact hl.1
    have hw : (matHom _ σ _ (e g)).1 *ᵥ incV F (fun i => Y' i 0) =
        (Units.map (cA σ : AE F E →* AE F E) t⁻¹).1 • incV F fun i => Y' i 0 := (lineY _ _).2 hl.2.1
    have hι : (matHom _ σ _ (e g)).1 * incM F H.ι = incM F H.ι * (matHom _ σ _ (e₁ h)).1 := hl.2.2
    have a1 := fun D (hD : t ∈ D) => frameStab_succ (yx hcm hND hW) hL (by rw [eX, hLx]) (fun i j => (hXY i j).1) hD hv hι
    have a2 := frameStab_succ hW.xy hL (by rw [eY, mulVec_smul, hLy, smul_zero]) (fun i j => (hXY i j).2)
      (Subgroup.mem_top _) hw hι
    rw [hA, hB, mem_leviOne, mem_leviOne]
    simp only [Finset.mem_insert, Finset.mem_map, forall_eq_or_imp, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Fin.coe_succEmb, a1 ⊤ (Subgroup.mem_top _), a1 _ (MonoidHom.mem_ker.2 ht), a2]
    exact and_iff_right ⟨frameStab_zero.2 ⟨t, trivial, hv⟩, frameStab_zero.2 ⟨_, trivial, hw⟩, frameStab_zero.2 ⟨t, ht, hv⟩⟩
  have ex : ∀ a : A, ∃ b : B, ∃ t, GlobalTheory.Doubling.absE F E t = 1 ∧ IsLevi (W₁ := W₁) H t (e₁.symm b) (e.symm a) := fun a => by
    obtain ⟨-, h2, h3⟩ := mem_leviOne.1 a.2 0 (Finset.mem_insert_self _ _)
    obtain ⟨s, -, hs⟩ := frameStab_zero.1 h2
    obtain ⟨t, ht, hv⟩ := frameStab_zero.1 h3
    rw [eX] at hv
    obtain ⟨h, hh⟩ := isLevi_of_lines hxy hgram hdet hσ hx hy hD (e.symm a) hv ((lineY _ _).1 hs)
    exact ⟨⟨e₁ h, (trans hh ht).1 a.2⟩, t, ht, hh⟩
  choose π t ht hπ using ex
  have uniq : ∀ (a : A) (b : B) s, IsLevi (W₁ := W₁) H s (e₁.symm b) (e.symm a) → π a = b := fun a b s hs =>
    Subtype.ext (Subtype.ext (Units.ext ((mat_of_isLevi hL (hπ a)).trans (mat_of_isLevi hL hs).symm)))
  let m : B → A := fun b => ⟨e (M (e₁.symm b)), (trans (hM _) (map_one _)).2 (by rw [e₁.apply_symm_apply]; exact b.2)⟩
  have hππ : ∀ a b, π (a * b) = π a * π b := fun a b => uniq _ _ (t a * t b) (by
    simpa only [Subgroup.coe_mul, map_mul] using GlobalTheory.LeviHom.isLevi_mul H (hπ a) (hπ b))
  have hπc : Continuous π := by
    have h1 : Continuous fun a : A => mat (e₁.symm (π a)) := by
      simp only [fun a => mat_of_isLevi hL (hπ a)]
      exact (continuous_const.matrix_mul (continuous_mat.comp continuous_subtype_val)).matrix_mul continuous_const
    refine Continuous.subtype_mk (p := fun x => x ∈ B) (f := fun a => (π a).1) ?_ _
    refine (continuous_toGAd hσ W₁.J hc₀).1.comp (f := fun a => e₁.symm (π a)) ?_
    refine Continuous.subtype_mk (f := fun a => (e₁.symm (π a)).1) (Units.continuous_iff.2 ⟨h1, ?_⟩) _
    refine (h1.comp continuous_inv).congr fun a => ?_
    have : π a⁻¹ = (π a)⁻¹ := map_inv (MonoidHom.mk' π hππ) a
    simp only [Function.comp, this]
    rfl
  have hT : ∀ a : A, a.1 ∈ A ⊓ frameStab σ _ H.ι ⊥ ↔ π a = 1 := fun a => by
    refine ⟨fun ⟨_, b, hb, hab⟩ => uniq _ _ (t a) ⟨(hπ a).1, (hπ a).2.1, ?_⟩, fun h => ⟨a.2, 1, rfl, ?_⟩⟩
    · obtain rfl : b = 1 := hb
      exact hab
    · have := (hπ a).2.2
      rw [h] at this
      exact this
  have hTl : ∀ τ ∈ A ⊓ frameStab σ _ H.ι ⊥, ∃ t : (AE F E)ˣ, GlobalTheory.Doubling.absE F E t = 1 ∧
      IsLevi (W₁ := W₁) H t 1 (e.symm τ) := fun τ hτ => by
    have := hπ ⟨τ, hτ.1⟩
    rw [(hT ⟨τ, hτ.1⟩).1 hτ] at this
    exact ⟨_, ht _, this⟩
  have hπm : ∀ b, π (m b) = b := fun b => uniq _ _ _ (hM _)
  obtain ⟨φ, hφ⟩ := exists_prod_equiv A (A ⊓ frameStab σ _ H.ι ⊥) m π
    (((continuous_toGAd hσ W.J hc₀).1.comp (hMc.comp ((continuous_toGAd hσ W₁.J hc₀).2.comp continuous_subtype_val))).subtype_mk _)
    hπc (fun a b => Subtype.ext (by simp only [m, Subgroup.coe_mul, map_mul, hMm])) hππ hπm inf_le_left hT
    (fun τ hτ b => by
      obtain ⟨s, -, hs⟩ := hTl τ hτ
      have := congrArg e (hMcomm s _ hs (e₁.symm b))
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this)
  refine ⟨_, φ, ?_, fun τ => hTl τ τ.2, hφ, fun p => ?_⟩
  · rw [Subgroup.coe_inf]
    exact (isClosed_levi _ hcm hND hW).2.inter (isClosed_frameStab hL isClosed_singleton)
  · have r1 : ∀ x, e.symm x ∈ ratU σ W.J ↔ x ∈ ratPts σ _ := fun x => by
      rw [← toGAd_mem_ratPts hσ W.J hc₀, MulEquiv.apply_symm_apply]
    have r2 : ∀ x, e₁.symm x ∈ ratU σ W₁.J ↔ x ∈ ratPts σ _ := fun x => by
      rw [← toGAd_mem_ratPts hσ W₁.J hc₀, MulEquiv.apply_symm_apply]
    have hm : (p.2 : GAd σ (c₀ • W₁.J.map σ)) ∈ ratPts σ _ → (m p.2 : GAd σ (c₀ • W.J.map σ)) ∈ ratPts σ _ := fun h =>
      (toGAd_mem_ratPts hσ W.J hc₀ _).2 (hMr _ ((r2 _).2 h))
    refine ⟨fun h => ?_, fun h => hφ p ▸ mul_mem h.1 (hm h.2)⟩
    have h2 : (p.2 : GAd σ (c₀ • W₁.J.map σ)) ∈ ratPts σ _ := by
      have e1 : π (φ p) = p.2 := by
        rw [show φ p = ⟨p.1, p.1.2.1⟩ * m p.2 from Subtype.ext (hφ p), hππ, (hT ⟨p.1, p.1.2.1⟩).1 p.1.2, one_mul, hπm]
      rw [← e1]
      exact (r2 _).1 (rat_of_isLevi hL (hπ (φ p)) ((r1 _).2 h))
    rw [hφ] at h
    exact ⟨(mul_mem_cancel_right (hm h2)).1 h, h2⟩

end GlobalTheory.LeviSplit
end
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.LeviLast

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem cT_mul_sq {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} (A B : Matrix (Fin k) (Fin k) R) :
    cT s (A * B) = cT s B * cT s A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} : cT s (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  simp only [Formalism.UG.cT, Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

def cTUnit {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} (β : GL (Fin k) R) : GL (Fin k) R where
  val := cT s (β⁻¹).1
  inv := cT s β.1
  val_inv := by rw [← cT_mul_sq, Units.mul_inv, cT_one_sq]
  inv_val := by rw [← cT_mul_sq, Units.inv_mul, cT_one_sq]

theorem adMat_mul' {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    adMat F (A * B) = adMat F A * adMat F B := Matrix.map_mul

theorem adMat_one' {a : ℕ} : adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

def blk {k : ℕ} (P : Matrix (Fin k) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (g : GAd σ J) :
    Matrix (Fin k) (Fin k) (AF F ⊗[F] E) :=
  adMat F P * (matHom _ σ J g).1 * adMat F X

theorem blk_of {k : ℕ} {P : Matrix (Fin k) (Fin n) E} {X : Matrix (Fin n) (Fin k) E} (hPX : P * X = 1) {g : GAd σ J}
    {B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)} (h : (matHom _ σ J g).1 * adMat F X = adMat F X * B) : blk P X g = B := by
  rw [blk, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← adMat_mul', hPX, adMat_one', Matrix.one_mul]

theorem blk_mul {k : ℕ} {P : Matrix (Fin k) (Fin n) E} {X : Matrix (Fin n) (Fin k) E} (hPX : P * X = 1) (a : GAd σ J)
    {b : GAd σ J} {B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)} (h : (matHom _ σ J b).1 * adMat F X = adMat F X * B) :
    blk P X (a * b) = blk P X a * blk P X b := by
  rw [blk_of hPX h, blk, blk, map_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [h]

variable {r : ℕ}

theorem mem_leviOne_last {X Y : Matrix (Fin n) (Fin (r + 1)) E} {g : GAd σ J} :
    g ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ↔
      (∃ B : GL (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F X = adMat F X * B.1) ∧
      (∃ B : GL (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F Y = adMat F Y * B.1) ∧
      (∃ B ∈ ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker,
        (matHom _ σ J g).1 * adMat F X = adMat F X * B.1) := by
  rw [GlobalTheory.LeviSplit.mem_leviOne]
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨⟨B, -, h⟩, ⟨B', -, h'⟩, ⟨B'', h2, h''⟩⟩
    exact ⟨⟨B, h⟩, ⟨B', h'⟩, ⟨B'', h2, h''⟩⟩
  · rintro ⟨⟨B, h⟩, ⟨B', h'⟩, ⟨B'', h2, h''⟩⟩
    exact ⟨⟨B, Subgroup.mem_top _, h⟩, ⟨B', Subgroup.mem_top _, h'⟩, ⟨B'', h2, h''⟩⟩

set_option maxHeartbeats 1000000 in
open GlobalTheory.UAut GlobalTheory.EisLine in

theorem leviOne_last_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∃ φ : (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) × ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ≃ₜ* GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∀ p, ((φ p : GAd σ J) ∈ ratPts σ J ↔ (p.1 : GAd σ J) ∈ ratPts σ J ∧ (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range) := by
  intro F E _ _ _ _ _ σ n J r m X Y Z J₀ hF
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  obtain ⟨lv, hlv, -, -⟩ := GlobalTheory.SphEis.Inhabitant.existsUnique_isLv hF
  set K := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker with hK
  set A := GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} with hA
  set T := (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) with hT
  set P : Matrix (Fin (r + 1)) (Fin n) E := cT (σ : E →+* E) Y * J with hP
  set Q : Matrix (Fin (r + 1)) (Fin n) E := cT (σ : E →+* E) X * J with hQ
  have hPX : P * X = 1 := hF.dc
  have hQY : Q * Y = 1 := hF.cd
  have h1X : ∀ g : GAd σ J, (matHom _ σ J g).1 * adMat F X = adMat F X →
      (matHom _ σ J g).1 * adMat F X = adMat F X * (1 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1 := fun g h => by
    rw [Units.val_one, Matrix.mul_one]; exact h
  have hinv : ∀ a : A, blk P X (a : GAd σ J) * blk P X ((a⁻¹ : A) : GAd σ J) = 1 ∧
      blk P X ((a⁻¹ : A) : GAd σ J) * blk P X (a : GAd σ J) = 1 := by
    intro a
    obtain ⟨⟨B, hB⟩, -, -⟩ := mem_leviOne_last.1 a.2
    obtain ⟨⟨B', hB'⟩, -, -⟩ := mem_leviOne_last.1 (a⁻¹).2
    have e1 : blk P X (1 : GAd σ J) = 1 := by
      have := blk_of hPX (h1X 1 (by rw [map_one, Units.val_one, Matrix.one_mul]))
      rw [this, Units.val_one]
    refine ⟨?_, ?_⟩
    · rw [← blk_mul hPX _ hB', ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, e1]
    · rw [← blk_mul hPX _ hB, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, e1]
  let πu : A → GL (Fin (r + 1)) (AF F ⊗[F] E) := fun a =>
    ⟨blk P X (a : GAd σ J), blk P X ((a⁻¹ : A) : GAd σ J), (hinv a).1, (hinv a).2⟩
  have hπK : ∀ a : A, πu a ∈ K := by
    intro a
    obtain ⟨-, -, ⟨B, hBK, hB⟩⟩ := mem_leviOne_last.1 a.2
    have : πu a = B := Units.ext (blk_of hPX hB)
    rw [this]; exact hBK
  let π : A → K := fun a => ⟨πu a, hπK a⟩
  have hlvA : ∀ β : K, lv β ∈ A := fun β =>
    mem_leviOne_last.2 ⟨⟨β, hlv.onC β⟩, ⟨cTUnit (sigR (AF F) σ) (β : GL (Fin (r + 1)) (AF F ⊗[F] E)), hlv.onD β⟩,
      ⟨β, β.2, hlv.onC β⟩⟩
  let mm : K → A := fun β => ⟨lv β, hlvA β⟩
  have hTA : T ≤ A := by
    intro x hx
    obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.1 hx
    have hX' : (matHom _ σ J x).1 * adMat F X = adMat F X := hxX
    have hY' : (matHom _ σ J x).1 * adMat F Y = adMat F Y := hxY
    exact mem_leviOne_last.2 ⟨⟨1, by rw [hX', Units.val_one, Matrix.mul_one]⟩, ⟨1, by rw [hY', Units.val_one, Matrix.mul_one]⟩,
      ⟨1, one_mem _, by rw [hX', Units.val_one, Matrix.mul_one]⟩⟩
  have hTiff : ∀ a : A, (a : GAd σ J) ∈ T ↔ π a = 1 := by
    intro a
    constructor
    · intro hx
      exact Subtype.ext (Units.ext (blk_of hPX (h1X _ (Subgroup.mem_inf.1 hx).1)))
    · intro h1
      have hb : blk P X (a : GAd σ J) = 1 := by
        have := congrArg (fun x : K => (x : GL (Fin (r + 1)) (AF F ⊗[F] E)).1) h1
        exact this
      obtain ⟨⟨B, hB⟩, ⟨B', hB'⟩, -⟩ := mem_leviOne_last.1 a.2
      have hB1 : B.1 = 1 := (blk_of hPX hB).symm.trans hb
      have hfX : (matHom _ σ J (a : GAd σ J)).1 * adMat F X = adMat F X := by rw [hB, hB1, Matrix.mul_one]
      have hfXi : (a : GAd σ J)⁻¹ ∈ GlobalTheory.SphEis.fixG σ J X :=
        inv_mem (show (a : GAd σ J) ∈ GlobalTheory.SphEis.fixG σ J X from hfX)
      have hform := form_mul_of_mul_cols (B := 1)
        (show (matHom _ σ J (a : GAd σ J)⁻¹).1 * adMat F X = adMat F X * 1 by rw [Matrix.mul_one]; exact hfXi)
      rw [inv_inv, cT_one_sq, Matrix.one_mul] at hform
      have e1 : blk Q Y (a : GAd σ J) = B'.1 := blk_of hQY hB'
      rw [blk, hform, ← adMat_mul', hQY, adMat_one'] at e1
      have hfY : (matHom _ σ J (a : GAd σ J)).1 * adMat F Y = adMat F Y := by rw [hB', ← e1, Matrix.mul_one]
      exact Subgroup.mem_inf.2 ⟨hfX, hfY⟩
  have hπc : Continuous π := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun a : A => adMat F P * (matHom _ σ J (a : GAd σ J)).1 * adMat F X
      exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp continuous_subtype_val)).matrix_mul continuous_const
    · show Continuous fun a : A => adMat F P * (matHom _ σ J ((a⁻¹ : A) : GAd σ J)).1 * adMat F X
      exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp (continuous_subtype_val.comp continuous_inv))).matrix_mul
        continuous_const
  have hmc : Continuous mm := (hlv.cont.comp continuous_subtype_val).subtype_mk _
  have hmm : ∀ a b, mm (a * b) = mm a * mm b := fun a b => Subtype.ext (map_mul lv _ _)
  have hππ : ∀ a b, π (a * b) = π a * π b := by
    intro a b
    obtain ⟨⟨B, hB⟩, -, -⟩ := mem_leviOne_last.1 b.2
    exact Subtype.ext (Units.ext (blk_mul hPX (a : GAd σ J) hB))
  have hπm : ∀ β, π (mm β) = β := fun β => Subtype.ext (Units.ext (blk_of hPX (hlv.onC β)))
  have hc : ∀ τ ∈ T, ∀ β, τ * (mm β : GAd σ J) = mm β * τ := fun τ hτ β =>
    (GlobalTheory.SphEis.lv_comm_of_fix_cols F E σ n J (r + 1) m X Y Z J₀ hF lv hlv β τ hτ).symm
  obtain ⟨φ, hφ⟩ := GlobalTheory.LeviSplit.exists_prod_equiv A T mm π hmc hπc hmm hππ hπm hTA hTiff hc
  refine ⟨φ, fun p => ?_⟩
  rw [hφ p]
  change (p.1 : GAd σ J) * lv p.2 ∈ ratPts σ J ↔ _
  constructor
  · intro h
    have hp1 : (matHom _ σ J (p.1 : GAd σ J)).1 * adMat F X = adMat F X := (Subgroup.mem_inf.1 p.1.2).1
    have hg : (matHom _ σ J ((p.1 : GAd σ J) * lv p.2)).1 * adMat F X =
        adMat F X * (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1 := by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hlv.onC, ← Matrix.mul_assoc, hp1]
    have hb := blk_of hPX hg
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h)
    have hM : (matHom _ σ J ((p.1 : GAd σ J) * lv p.2)).1 = adMat F γ.1 := (congrArg Units.val hγ).symm
    rw [blk, hM, ← adMat_mul', ← adMat_mul'] at hb
    have hrng : (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) :
        GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range := by
      rcases subsingleton_or_nontrivial (AF F ⊗[F] E) with _ | _
      · exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩
      · have hd : (P * γ.1 * X).det ≠ 0 := fun h0 => by
          have hu : IsUnit (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1.det :=
            (Matrix.isUnit_iff_isUnit_det _).1 (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).isUnit
          rw [← hb, show (adMat F (P * γ.1 * X)).det = inclR (F := F) (AF F) (P * γ.1 * X).det from
            (RingHom.map_det _ _).symm, h0, map_zero] at hu
          exact not_isUnit_zero hu
        exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext hb⟩
    obtain ⟨δ, hδ⟩ := hrng
    refine ⟨?_, ⟨δ, hδ⟩⟩
    have h2 : lv p.2 ∈ ratPts σ J := by rw [← hδ]; exact hlv.rat δ
    have := mul_mem h (inv_mem h2)
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨h1, ⟨δ, hδ⟩⟩
    refine mul_mem h1 ?_
    rw [← hδ]; exact hlv.rat δ

end GlobalTheory.SphEis.LeviLast
end
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardParabolicLeviNormOne_lastColumn_prodEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∃ φ : (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) × ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ≃ₜ* GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∀ p, ((φ p : GAd σ J) ∈ ratPts σ J ↔ (p.1 : GAd σ J) ∈ ratPts σ J ∧ (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range) := by
  atlas_forward_decl GlobalTheory.SphEis.LeviLast.leviOne_last_prod
end
