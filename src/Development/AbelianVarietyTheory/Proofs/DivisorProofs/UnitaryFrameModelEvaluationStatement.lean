import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticBlockBasisOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPair

section
namespace GlobalTheory.AbelianSumIdentityFourth

open Matrix

theorem main : ∀ {A : Type} [inst : CommRing A] {n q : ℕ} (X Y : Matrix (Fin n) (Fin q) A) (RX RY : Matrix (Fin q) (Fin n) A) (a b a' b' : Fin q → A), RY * X = (1 : Matrix (Fin q) (Fin q) A) → RY * Y = (0 : Matrix (Fin q) (Fin q) A) → RX * X = (0 : Matrix (Fin q) (Fin q) A) → RX * Y = (1 : Matrix (Fin q) (Fin q) A) → (∀ (i : Fin q), a i + a' i + a i * a' i = (0 : A)) → (∀ (i : Fin q), b i + b' i + b i * b' i = (0 : A)) → ((1 : Matrix (Fin n) (Fin n) A) + X * Matrix.diagonal a * RY + Y * Matrix.diagonal b * RX) * ((1 : Matrix (Fin n) (Fin n) A) + X * Matrix.diagonal a' * RY + Y * Matrix.diagonal b' * RX) = (1 : Matrix (Fin n) (Fin n) A) := by
  intro A _ n q X Y RX RY a b a' b' h1 h2 h3 h4 ha hb
  have e1 : ∀ {m : Type} (M : Matrix (Fin q) m A), RY * (X * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e2 : ∀ {m : Type} (M : Matrix (Fin q) m A), RY * (Y * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.zero_mul]
  have e3 : ∀ {m : Type} (M : Matrix (Fin q) m A), RX * (X * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, h3, Matrix.zero_mul]
  have e4 : ∀ {m : Type} (M : Matrix (Fin q) m A), RX * (Y * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  have hDa : Matrix.diagonal a + Matrix.diagonal a' + Matrix.diagonal a * Matrix.diagonal a' = 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal_apply, ha i]
    · simp [Matrix.diagonal_apply, hij]
  have hDb : Matrix.diagonal b + Matrix.diagonal b' + Matrix.diagonal b * Matrix.diagonal b' = 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal_apply, hb i]
    · simp [Matrix.diagonal_apply, hij]
  have kx : X * (Matrix.diagonal a * RY) + X * (Matrix.diagonal a' * RY)
      + X * (Matrix.diagonal a * (Matrix.diagonal a' * RY)) = 0 := by
    have := congrArg (fun M => X * (M * RY)) hDa
    simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero] using this
  have ky : Y * (Matrix.diagonal b * RX) + Y * (Matrix.diagonal b' * RX)
      + Y * (Matrix.diagonal b * (Matrix.diagonal b' * RX)) = 0 := by
    have := congrArg (fun M => Y * (M * RX)) hDb
    simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero] using this
  calc _ = 1 + (X * (Matrix.diagonal a * RY) + X * (Matrix.diagonal a' * RY)
          + X * (Matrix.diagonal a * (Matrix.diagonal a' * RY)))
        + (Y * (Matrix.diagonal b * RX) + Y * (Matrix.diagonal b' * RX)
          + Y * (Matrix.diagonal b * (Matrix.diagonal b' * RX))) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul,
          e1, e2, e3, e4, Matrix.zero_mul, Matrix.mul_zero, add_zero]
        abel
    _ = 1 := by rw [kx, ky, add_zero, add_zero]

end GlobalTheory.AbelianSumIdentityFourth
end

section
namespace GlobalTheory.DiagonalKeyIdentity

open Matrix

theorem diag_key {A : Type} [CommRing A] {q : ℕ} (a b : Fin q → A)
    (h : ∀ i, a i + b i + a i * b i = 0) :
    diagonal a + diagonal b + diagonal a * diagonal b = (0 : Matrix (Fin q) (Fin q) A) := by
  rw [diagonal_mul_diagonal, diagonal_add, diagonal_add, ← diagonal_zero]
  congr 1
  funext i
  exact h i

theorem main : ∀ {A : Type} [inst : CommRing A] {n q : ℕ} (J : Matrix (Fin n) (Fin n) A) (X Xc Y Yc : Matrix (Fin n) (Fin q) A) (a b : Fin q → A), Matrix.transpose X * J * Xc = (0 : Matrix (Fin q) (Fin q) A) → Matrix.transpose X * J * Yc = (1 : Matrix (Fin q) (Fin q) A) → Matrix.transpose Y * J * Xc = (1 : Matrix (Fin q) (Fin q) A) → Matrix.transpose Y * J * Yc = (0 : Matrix (Fin q) (Fin q) A) → (∀ (i : Fin q), a i + b i + a i * b i = (0 : A)) → ((1 : Matrix (Fin n) (Fin n) A) + J * Yc * Matrix.diagonal a * Matrix.transpose X + J * Xc * Matrix.diagonal b * Matrix.transpose Y) * J * ((1 : Matrix (Fin n) (Fin n) A) + Xc * Matrix.diagonal a * (Matrix.transpose Y * J) + Yc * Matrix.diagonal b * (Matrix.transpose X * J)) = J := by
  intro A _ n q J X Xc Y Yc a b h1 h2 h3 h4 hab
  have k1 := diag_key a b hab
  have k2 : diagonal b + diagonal a + diagonal b * diagonal a = (0 : Matrix (Fin q) (Fin q) A) := by
    apply diag_key b a; intro i; rw [add_comm (b i), mul_comm (b i)]; exact hab i
  have g1 : ∀ {m : ℕ} (Z : Matrix (Fin q) (Fin m) A), Xᵀ * (J * (Xc * Z)) = 0 := by
    intro m Z; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.zero_mul]
  have g2 : ∀ {m : ℕ} (Z : Matrix (Fin q) (Fin m) A), Xᵀ * (J * (Yc * Z)) = Z := by
    intro m Z; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have g3 : ∀ {m : ℕ} (Z : Matrix (Fin q) (Fin m) A), Yᵀ * (J * (Xc * Z)) = Z := by
    intro m Z; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  have g4 : ∀ {m : ℕ} (Z : Matrix (Fin q) (Fin m) A), Yᵀ * (J * (Yc * Z)) = 0 := by
    intro m Z; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h4, Matrix.zero_mul]
  calc _ = J + J * (Xc * ((diagonal b + diagonal a + diagonal b * diagonal a) * (Yᵀ * J)))
        + J * (Yc * ((diagonal a + diagonal b + diagonal a * diagonal b) * (Xᵀ * J))) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_one,
            Matrix.one_mul, g1, g2, g3, g4, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
          abel
    _ = J := by rw [k1, k2]; simp

end GlobalTheory.DiagonalKeyIdentity
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.FrameTorus

open Matrix

section Gen

variable {A : Type} [CommRing A] {n q : ℕ}

theorem mul_core (X Y : Matrix (Fin n) (Fin q) A) (RX RY : Matrix (Fin q) (Fin n) A) (a b a' b' : Fin q → A)
    (h1 : RY * X = 1) (h2 : RY * Y = 0) (h3 : RX * X = 0) (h4 : RX * Y = 1)
    (ha : ∀ i, a i + a' i + a i * a' i = 0) (hb : ∀ i, b i + b' i + b i * b' i = 0) :
    (1 + X * diagonal a * RY + Y * diagonal b * RX) * (1 + X * diagonal a' * RY + Y * diagonal b' * RX) = 1 := by
  first
  | exact @_root_.GlobalTheory.AbelianSumIdentityFourth.main
  | exact _root_.GlobalTheory.AbelianSumIdentityFourth.main
  | (apply _root_.GlobalTheory.AbelianSumIdentityFourth.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbelianSumIdentityFourth.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbelianSumIdentityFourth.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbelianSumIdentityFourth.main ..)

end Gen

section Gen2

variable {A : Type} [CommRing A] {n q : ℕ}

theorem unitary_core (J : Matrix (Fin n) (Fin n) A) (X Xc Y Yc : Matrix (Fin n) (Fin q) A) (a b : Fin q → A)
    (h1 : Xᵀ * J * Xc = 0) (h2 : Xᵀ * J * Yc = 1) (h3 : Yᵀ * J * Xc = 1) (h4 : Yᵀ * J * Yc = 0)
    (hab : ∀ i, a i + b i + a i * b i = 0) :
    (1 + J * Yc * diagonal a * Xᵀ + J * Xc * diagonal b * Yᵀ) * J *
      (1 + Xc * diagonal a * (Yᵀ * J) + Yc * diagonal b * (Xᵀ * J)) = J := by
  first
  | exact @_root_.GlobalTheory.DiagonalKeyIdentity.main
  | exact _root_.GlobalTheory.DiagonalKeyIdentity.main
  | (apply _root_.GlobalTheory.DiagonalKeyIdentity.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DiagonalKeyIdentity.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DiagonalKeyIdentity.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DiagonalKeyIdentity.main ..)

theorem unitary_gen (c : A →+* A) (J : Matrix (Fin n) (Fin n) A) (X Xc Y Yc : Matrix (Fin n) (Fin q) A)
    (RX RY : Matrix (Fin q) (Fin n) A) (a b : Fin q → A)
    (hRYt : RYᵀ = J * Yc) (hRXt : RXᵀ = J * Xc) (hXc : X.map c = Xc) (hYc : Y.map c = Yc)
    (hRYc : RY.map c = Yᵀ * J) (hRXc : RX.map c = Xᵀ * J) (hac : ∀ i, c (a i) = a i) (hbc : ∀ i, c (b i) = b i)
    (h1 : Xᵀ * J * Xc = 0) (h2 : Xᵀ * J * Yc = 1) (h3 : Yᵀ * J * Xc = 1) (h4 : Yᵀ * J * Yc = 0)
    (hab : ∀ i, a i + b i + a i * b i = 0) :
    (1 + X * diagonal a * RY + Y * diagonal b * RX)ᵀ * J * (1 + X * diagonal a * RY + Y * diagonal b * RX).map c = J := by
  have hT : (1 + X * diagonal a * RY + Y * diagonal b * RX)ᵀ = 1 + J * Yc * diagonal a * Xᵀ + J * Xc * diagonal b * Yᵀ := by
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.diagonal_transpose, hRYt, hRXt,
      Matrix.mul_assoc]
  have hC : (1 + X * diagonal a * RY + Y * diagonal b * RX).map c =
      1 + Xc * diagonal a * (Yᵀ * J) + Yc * diagonal b * (Xᵀ * J) := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c),
      Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero c),
      Matrix.diagonal_map (map_zero c), hXc, hYc, hRYc, hRXc]
    simp only [hac, hbc]
  rw [hT, hC]
  exact unitary_core J X Xc Y Yc a b h1 h2 h3 h4 hab

end Gen2

section Conc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem realAd_mul' (a b : ℝ) : realAd F a * realAd F b = realAd F (a * b) := by
  unfold realAd
  simp only [LinearMap.inl_apply, map_mul]
  refine Prod.ext ?_ ?_
  · show _ * _ = _
    rw [← map_mul]
  · exact mul_zero _

theorem realAd_add' (s t : ℝ) : realAd F (s + t) = realAd F s + realAd F t := by
  simp only [realAd, map_add]
  rfl

theorem realAd_zero' : realAd F 0 = 0 := by
  simp only [realAd, map_zero]
  rfl

theorem realAd_key {t : ℝ} (ht : t ≠ 0) :
    realAd F (t - 1) + realAd F (t⁻¹ - 1) + realAd F (t - 1) * realAd F (t⁻¹ - 1) = 0 := by
  rw [realAd_mul', ← realAd_add', ← realAd_add']
  have : t - 1 + (t⁻¹ - 1) + (t - 1) * (t⁻¹ - 1) = 0 := by field_simp; ring
  rw [this, realAd_zero']

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

def colMat {n p : ℕ} (u : Fin p → Fin n → E) : Matrix (Fin n) (Fin p) E := Matrix.of fun k i => u i k

theorem colMat_form (σ : E →ₐ[F] E) {n p p' : ℕ} (J : Matrix (Fin n) (Fin n) E) (u : Fin p → Fin n → E)
    (v : Fin p' → Fin n → E) (i : Fin p) (j : Fin p') :
    ((colMat u)ᵀ * J * (colMat v).map (σ : E →+* E)) i j = form σ J (u i) (v j) := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, form, dotProduct, Matrix.mulVec, colMat]

theorem tr_eq {n p p' : ℕ} (s : E →+* E) (J : Matrix (Fin n) (Fin n) E) (U : Matrix (Fin n) (Fin p) E)
    (V : Matrix (Fin n) (Fin p') E) : (V.map s)ᵀ * Jᵀ * U = (Uᵀ * J * V.map s)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end Conc

theorem exists_isTorusU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s → ∀ (q : ℕ) (x y : Fin q → Fin n → E),
    IsFrameU σ X.J x y → ∀ t : Fin q → ℝ, (∀ i, 0 < t i) → ∃ a : UA σ X.J, IsTorusU x y t a := by
  intro F E _ _ _ _ _ σ B n X r s hB hX q x y hF t ht
  have hσσ := sigma_sigma hB.cm
  set J := X.J with hJdef
  set sg : E →+* E := (σ : E →+* E) with hsg
  set ι : E →+* AE F E := inclR (F := F) (AF F) with hι
  set c : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hc
  have hcι : ∀ e, c (ι e) = ι (sg e) := fun e => cA_inclR σ e
  have hconj : ∀ {p p' : ℕ} (M : Matrix (Fin p) (Fin p') E), (M.map ι).map c = (M.map sg).map ι := by
    intro p p' M; ext i j; simp only [Matrix.map_apply]; exact hcι _
  set Xe := colMat x with hXe
  set Ye := colMat y with hYe
  have hXX : Xeᵀ * J * Xe.map sg = 0 := by ext i j; rw [colMat_form]; exact hF.1 i j
  have hYY : Yeᵀ * J * Ye.map sg = 0 := by ext i j; rw [colMat_form]; exact hF.2.1 i j
  have hXY : Xeᵀ * J * Ye.map sg = 1 := by ext i j; rw [colMat_form, hF.2.2 i j, Matrix.one_apply]
  have hJt : Jᵀ.map sg = J := by ext i j; exact hX.herm i j
  have hss : ∀ {p p' : ℕ} (M : Matrix (Fin p) (Fin p') E), (M.map sg).map sg = M := by
    intro p p' M; ext i j; simp [hsg, hσσ]
  have hYX : Yeᵀ * J * Xe.map sg = 1 := by
    have e : Yeᵀ * J * Xe.map sg = ((Xeᵀ * J * Ye.map sg)ᵀ).map sg := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.map_mul, hJt,
        Matrix.transpose_map, hss, Matrix.mul_assoc]
    rw [e, hXY, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]

  set RYe : Matrix (Fin q) (Fin n) E := (Ye.map sg)ᵀ * Jᵀ with hRYe
  set RXe : Matrix (Fin q) (Fin n) E := (Xe.map sg)ᵀ * Jᵀ with hRXe
  have mapι : ∀ {p p' : ℕ} (M : Matrix (Fin p) (Fin n) E) (N : Matrix (Fin n) (Fin p') E), M.map ι * N.map ι = (M * N).map ι :=
    fun M N => (Matrix.map_mul).symm
  have z0 : ∀ {p p' : ℕ}, (0 : Matrix (Fin p) (Fin p') E).map ι = 0 := by intros; exact Matrix.map_zero _ (map_zero _)
  have o1 : ∀ {p : ℕ}, (1 : Matrix (Fin p) (Fin p) E).map ι = 1 := by intros; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : RYe.map ι * Xe.map ι = 1 := by rw [mapι, hRYe, tr_eq, hXY, Matrix.transpose_one, o1]
  have h2 : RYe.map ι * Ye.map ι = 0 := by rw [mapι, hRYe, tr_eq, hYY, Matrix.transpose_zero, z0]
  have h3 : RXe.map ι * Xe.map ι = 0 := by rw [mapι, hRXe, tr_eq, hXX, Matrix.transpose_zero, z0]
  have h4 : RXe.map ι * Ye.map ι = 1 := by rw [mapι, hRXe, tr_eq, hYX, Matrix.transpose_one, o1]
  set al : (Fin q → ℝ) → Fin q → AE F E := fun t i => algebraMap (AF F) (AE F E) (realAd F (t i - 1)) with hal
  have key : ∀ u : Fin q → ℝ, (∀ i, u i ≠ 0) → ∀ i, al u i + al (fun i => (u i)⁻¹) i + al u i * al (fun i => (u i)⁻¹) i = 0 := by
    intro u hu i
    simp only [hal, ← map_add, ← map_mul, realAd_key (hu i), map_zero]
  set M : (Fin q → ℝ) → Matrix (Fin n) (Fin n) (AE F E) := fun u =>
    1 + Xe.map ι * diagonal (al u) * RYe.map ι + Ye.map ι * diagonal (al (fun i => (u i)⁻¹)) * RXe.map ι with hM
  have ht0 : ∀ i, t i ≠ 0 := fun i => (ht i).ne'
  have ht0' : ∀ i, (fun i => (t i)⁻¹) i ≠ 0 := fun i => inv_ne_zero (ht0 i)
  have hinv : M t * M (fun i => (t i)⁻¹) = 1 :=
    mul_core _ _ _ _ _ _ _ _ h1 h2 h3 h4 (key t ht0) (key _ ht0')

  have hmem : (⟨M t, M (fun i => (t i)⁻¹), hinv, (Matrix.mul_eq_one_comm_of_card_eq (Fin n) (Fin n) (AE F E) rfl).mp hinv⟩ : GL (Fin n) (AE F E)) ∈
      UG (cA σ) (incM F X.J) := by
    show (M t)ᵀ * J.map ι * (M t).map c = J.map ι
    refine unitary_gen c (J.map ι) (Xe.map ι) ((Xe.map sg).map ι) (Ye.map ι) ((Ye.map sg).map ι) (RXe.map ι) (RYe.map ι)
      (al t) (al (fun i => (t i)⁻¹)) ?_ ?_ (hconj Xe) (hconj Ye) ?_ ?_ (fun i => (cA σ).commutes _) (fun i => (cA σ).commutes _)
      ?_ ?_ ?_ ?_ (key t ht0)
    · rw [← Matrix.transpose_map, hRYe, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
        Matrix.map_mul]
    · rw [← Matrix.transpose_map, hRXe, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
        Matrix.map_mul]
    · rw [hconj, hRYe, Matrix.map_mul, hJt, Matrix.transpose_map, hss, Matrix.map_mul, Matrix.transpose_map]
    · rw [hconj, hRXe, Matrix.map_mul, hJt, Matrix.transpose_map, hss, Matrix.map_mul, Matrix.transpose_map]
    · rw [← Matrix.transpose_map, mapι, mapι, hXX, z0]
    · rw [← Matrix.transpose_map, mapι, mapι, hXY, o1]
    · rw [← Matrix.transpose_map, mapι, mapι, hYX, o1]
    · rw [← Matrix.transpose_map, mapι, mapι, hYY, z0]

  have hM1 : M t - 1 = Xe.map ι * diagonal (al t) * RYe.map ι + Ye.map ι * diagonal (al (fun i => (t i)⁻¹)) * RXe.map ι := by
    simp only [hM]; abel
  have col : ∀ (N : Matrix (Fin n) (Fin n) (AE F E)) {p : ℕ} (Z : Matrix (Fin n) (Fin p) (AE F E)) (i : Fin p),
      N *ᵥ (fun k => Z k i) = fun k => (N * Z) k i := by
    intro N p Z i; funext k; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  refine ⟨⟨_, hmem⟩, fun i => ?_, fun i => ?_, fun z hzx hzy => ?_⟩
  · have hx : incV F (x i) = fun k => (Xe.map ι) k i := rfl
    have e : (M t - 1) * Xe.map ι = Xe.map ι * diagonal (al t) := by
      rw [hM1]; simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3, Matrix.mul_one, Matrix.mul_zero, add_zero]
    show (M t - 1) *ᵥ incV F (x i) = _
    rw [hx, col, e]
    funext k
    simp [Matrix.mul_diagonal, Algebra.smul_def, hal, mul_comm]
  · have hy : incV F (y i) = fun k => (Ye.map ι) k i := rfl
    have e : (M t - 1) * Ye.map ι = Ye.map ι * diagonal (al (fun i => (t i)⁻¹)) := by
      rw [hM1]; simp only [Matrix.add_mul, Matrix.mul_assoc, h2, h4, Matrix.mul_one, Matrix.mul_zero, zero_add]
    show (M t - 1) *ᵥ incV F (y i) = _
    rw [hy, col, e]
    funext k
    simp [Matrix.mul_diagonal, Algebra.smul_def, hal, mul_comm]
  · set Ze := colMat (fun _ : Fin 1 => z) with hZe
    have hz : incV F z = fun k => (Ze.map ι) k 0 := rfl
    have hYZ : RYe.map ι * Ze.map ι = 0 := by
      have e0 : Zeᵀ * J * Ye.map sg = 0 := by ext i j; rw [colMat_form]; exact hzy j
      rw [mapι, hRYe, tr_eq, e0, Matrix.transpose_zero, z0]
    have hXZ : RXe.map ι * Ze.map ι = 0 := by
      have e0 : Zeᵀ * J * Xe.map sg = 0 := by ext i j; rw [colMat_form]; exact hzx j
      rw [mapι, hRXe, tr_eq, e0, Matrix.transpose_zero, z0]
    have e : (M t - 1) * Ze.map ι = 0 := by
      rw [hM1]; simp only [Matrix.add_mul, Matrix.mul_assoc, hYZ, hXZ, Matrix.mul_zero, add_zero]
    show (M t - 1) *ᵥ incV F z = 0
    rw [hz, col, e]
    rfl

end GlobalTheory.FrameTorus
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_torus_element_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s → ∀ (q : ℕ) (x y : Fin q → Fin n → E),
    IsFrameU σ X.J x y → ∀ t : Fin q → ℝ, (∀ i, 0 < t i) → ∃ a : UA σ X.J, IsTorusU x y t a := by
  atlas_forward_decl GlobalTheory.FrameTorus.exists_isTorusU
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKTorus.FrameBlock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tAd_one : tAd F 1 = 1 := by
  have hr : realAd F 0 = 0 := by
    simp only [realAd, map_zero]
    rfl
  rw [tAd, sub_self, hr, add_zero]

theorem eq_zero_of_tAd_mul_eq {r s : ℝ} (hrs : r ≠ s) (u : F)
    (h : tAd F r * algebraMap F (AF F) u = tAd F s * algebraMap F (AF F) u) : u = 0 := by
  have hadd : ∀ a b : AF F, evI F (a + b) = evI F a + evI F b := fun a b =>
    map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have hmul : ∀ a b : AF F, evI F (a * b) = evI F a * evI F b := fun a b =>
    map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have hone : evI F 1 = 1 := map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have hreal : ∀ t : ℝ, evI F (realAd F t) = algebraMap ℝ _ t := fun t => by simp [evI, realAd]
  have halg : evI F (algebraMap F (AF F) u) = mixedEmbedding F u := by
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl
  have ht : ∀ t : ℝ, evI F (tAd F t) = algebraMap ℝ _ t := fun t => by
    rw [tAd, hadd, hone, hreal, map_sub, map_one, add_sub_cancel]
  have h1 := congrArg (evI F) h
  rw [hmul, hmul, ht, ht, halg, ← Algebra.smul_def, ← Algebra.smul_def, ← sub_eq_zero, ← sub_smul,
    smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) hrs
  · exact mixedEmbedding_injective F (h1.trans (map_zero _).symm)

end GlobalTheory.ThKTorus.FrameBlock

open GlobalTheory.ThKTorus.FrameBlock GlobalTheory.ThKTorus.FrameCoords

theorem GlobalTheory.ThKTorus.frameCo_vecMulVec_mem_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (q : ℕ) (x y : Fin q → Fin n → E) (M₁ : Model σ X W)
    (blk : Fin q → Finset (Fin n × Fin d)), M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk →
    (∀ t : Fin q → ℝ, (∀ i, 0 < t i) → ∃ a : UA σ X.J, IsTorusU x y t a) →
    ∀ (i : Fin q) (z : Fin d → AE F E), ∃ z' : Fin n × Fin d → AF F, (∀ j, j ∉ blk i → z' j = 0) ∧
      M₁.co.e (Matrix.vecMulVec (incV F (x i)) z) = (0, z') := by
  intro F E _ _ _ _ _ σ B n d X W q x y M₁ blk hG hF hT i
  classical
  let t : Fin q → ℝ := Function.update (fun _ => 1) i 2
  have hti : t i = 2 := by simp [t]
  have htk : ∀ k, k ≠ i → t k = 1 := fun k hk => by simp [t, hk]
  have ht : ∀ k, 0 < t k := fun k => by
    by_cases hk : k = i
    · rw [hk, hti]; norm_num
    · rw [htk k hk]; norm_num
  obtain ⟨a, ha⟩ := hT t ht
  have hprod : ∀ s : Fin q → ℝ, (∀ k, k ≠ i → s k = 1) → ∀ j : Fin n × Fin d,
      (∏ k, if j ∈ blk k then tAd F (s k) else 1) = tAd F (if j ∈ blk i then s i else 1) := by
    intro s hs j
    rw [Finset.prod_eq_single i (fun k _ hk => by rw [hs k hk, tAd_one, ite_self])
      (fun h => absurd (Finset.mem_univ i) h)]
    split_ifs
    · rfl
    · exact tAd_one.symm

  have hrat : ∀ z₀ : Fin d → E, (M₁.co.e (Matrix.vecMulVec (incV F (x i)) (incV F z₀))).1 = 0 ∧
      ∀ j, j ∉ blk i → (M₁.co.e (Matrix.vecMulVec (incV F (x i)) (incV F z₀))).2 j = 0 := by
    intro z₀
    obtain ⟨u, v, huv⟩ := hG.rat (Matrix.vecMulVec (x i) z₀)
    rw [incM_vecMulVec] at huv
    set w := Matrix.vecMulVec (incV F (x i)) (incV F z₀) with hw
    have h1 : mat a * w = tAd F 2 • w := by
      rw [hw, mul_vecMulVec_eq, mulVec_eq_tAd _ _ _ (ha.1 i), hti]
      ext r l
      simp [Matrix.vecMulVec_apply, smul_mul_assoc]
    have h2 : w = M₁.co.e.symm (fun j => algebraMap F (AF F) (u j), 0) +
        M₁.co.e.symm (0, fun j => algebraMap F (AF F) (v j)) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, ← huv, LinearEquiv.symm_apply_apply]
    have h3 : M₁.co.e (mat a * w) = (blkScale blk (fun k => (t k)⁻¹) fun j => algebraMap F (AF F) (u j),
        blkScale blk t fun j => algebraMap F (AF F) (v j)) := by
      conv_lhs => rw [h2]
      rw [Matrix.mul_add, map_add, (hF.2 t a ht ha _).1, (hF.2 t a ht ha _).2, Prod.mk_add_mk, add_zero, zero_add]
    rw [h1, map_smul, huv] at h3
    rw [huv]
    refine ⟨funext fun j => ?_, fun j hj => ?_⟩
    · have h4 := congrFun (congrArg Prod.fst h3) j
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, blkScale] at h4
      rw [hprod _ (fun k hk => by rw [htk k hk, inv_one]), hti] at h4
      have := eq_zero_of_tAd_mul_eq (by split_ifs <;> norm_num) _ h4
      simp [this]
    · have h4 := congrFun (congrArg Prod.snd h3) j
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, blkScale] at h4
      rw [hprod _ htk, if_neg hj] at h4
      have := eq_zero_of_tAd_mul_eq (by norm_num) _ h4
      simp [this]

  let P : (Fin d → AE F E) → Prop := fun z => (M₁.co.e (Matrix.vecMulVec (incV F (x i)) z)).1 = 0 ∧
      ∀ j, j ∉ blk i → (M₁.co.e (Matrix.vecMulVec (incV F (x i)) z)).2 j = 0
  have hP0 : P 0 := by
    have e : Matrix.vecMulVec (incV F (x i)) (0 : Fin d → AE F E) = 0 := by
      ext r l
      rw [Matrix.vecMulVec_apply, Pi.zero_apply, mul_zero, Matrix.zero_apply]
    refine ⟨?_, fun j _ => ?_⟩
    · rw [e, map_zero]; rfl
    · rw [e, map_zero]; rfl
  have hPadd : ∀ z z', P z → P z' → P (z + z') := by
    intro z z' h h'
    have e : Matrix.vecMulVec (incV F (x i)) (z + z') =
        Matrix.vecMulVec (incV F (x i)) z + Matrix.vecMulVec (incV F (x i)) z' := by
      ext r l
      simp [Matrix.vecMulVec_apply, mul_add]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [e, map_add, Prod.fst_add, h.1, h'.1, add_zero]
    · rw [e, map_add, Prod.snd_add, Pi.add_apply, h.2 j hj, h'.2 j hj, add_zero]
  have hPsmul : ∀ (c : AF F) z, P z → P (c • z) := by
    intro c z h
    have e : Matrix.vecMulVec (incV F (x i)) (c • z) = c • Matrix.vecMulVec (incV F (x i)) z := by
      ext r l
      simp [Matrix.vecMulVec_apply]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [e, map_smul, Prod.smul_fst, h.1, smul_zero]
    · rw [e, map_smul, Prod.smul_snd, Pi.smul_apply, h.2 j hj, smul_zero]
  have hsingle : ∀ (l : Fin d) (c : AE F E), P (Pi.single l c) := by
    intro l c
    induction c using TensorProduct.induction_on with
    | zero => rw [Pi.single_zero]; exact hP0
    | add b c hb hc => rw [Pi.single_add]; exact hPadd _ _ hb hc
    | tmul b e =>
      have e1 : (Pi.single l (b ⊗ₜ[F] e) : Fin d → AE F E) = b • incV F (Pi.single l e) := by
        funext k
        by_cases hk : k = l
        · subst hk
          simp [incV, inclR, TensorProduct.smul_tmul']
        · simp [incV, hk]
      rw [e1]
      exact hPsmul _ _ (hrat _)
  intro z
  have hz : P z := by
    rw [← Finset.univ_sum_single z]
    exact Finset.sum_induction _ P hPadd hP0 fun l _ => hsingle l _
  exact ⟨_, hz.2, Prod.ext hz.1 rfl⟩
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_torus_lattice_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (q : ℕ) (x y : Fin q → Fin n → E) (M₁ : Model σ X W)
    (blk : Fin q → Finset (Fin n × Fin d)), M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk →
    (∀ t : Fin q → ℝ, (∀ i, 0 < t i) → ∃ a : UA σ X.J, IsTorusU x y t a) →
    ∀ (i : Fin q) (z : Fin d → AE F E), ∃ z' : Fin n × Fin d → AF F, (∀ j, j ∉ blk i → z' j = 0) ∧
      M₁.co.e (Matrix.vecMulVec (incV F (x i)) z) = (0, z') := by
  atlas_forward_decl GlobalTheory.ThKTorus.frameCo_vecMulVec_mem_block
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.TorusSupportAvg

section Generic

variable {K V Ω : Type} [AddCommGroup K] [AddCommGroup V]

def IsCharAvg (ψ : AddChar K ℂ) (G : V →+ (Ω → K)) (h : Ω → ℂ) : Prop :=
  ∃ (N : ℕ) (a : Fin N → ℂ) (w : Fin N → V), ∑ m, a m = 1 ∧ ∀ Y, ∑ m, a m * ψ (G (w m) Y) = h Y

theorem isCharAvg_one (ψ : AddChar K ℂ) (G : V →+ (Ω → K)) : IsCharAvg ψ G 1 :=
  ⟨1, fun _ => 1, fun _ => 0, by simp, fun Y => by simp⟩

theorem isCharAvg_mul {ψ : AddChar K ℂ} {G : V →+ (Ω → K)} {h₁ h₂ : Ω → ℂ}
    (h1 : IsCharAvg ψ G h₁) (h2 : IsCharAvg ψ G h₂) : IsCharAvg ψ G (h₁ * h₂) := by
  obtain ⟨N₁, a₁, w₁, hs₁, hv₁⟩ := h1
  obtain ⟨N₂, a₂, w₂, hs₂, hv₂⟩ := h2
  refine ⟨N₁ * N₂, fun m => a₁ (finProdFinEquiv.symm m).1 * a₂ (finProdFinEquiv.symm m).2,
    fun m => w₁ (finProdFinEquiv.symm m).1 + w₂ (finProdFinEquiv.symm m).2, ?_, ?_⟩
  · rw [finProdFinEquiv.symm.sum_comp (fun p => a₁ p.1 * a₂ p.2), Fintype.sum_prod_type,
      ← Finset.sum_mul_sum, hs₁, hs₂, one_mul]
  · intro Y
    rw [finProdFinEquiv.symm.sum_comp (fun p => a₁ p.1 * a₂ p.2 * ψ (G (w₁ p.1 + w₂ p.2) Y)),
      Fintype.sum_prod_type, Pi.mul_apply, ← hv₁, ← hv₂, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, Pi.add_apply, AddChar.map_add_eq_mul]
    ring

theorem isCharAvg_prod {ψ : AddChar K ℂ} {G : V →+ (Ω → K)} {ι : Type} (s : Finset ι) (h : ι → Ω → ℂ)
    (hs : ∀ j ∈ s, IsCharAvg ψ G (h j)) : IsCharAvg ψ G (∏ j ∈ s, h j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCharAvg_one ψ G
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact isCharAvg_mul (hs j (Finset.mem_insert_self j s))
      (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))

theorem isCharAvg_poly (ψ : AddChar K ℂ) (G : V →+ (Ω → K)) (P : Polynomial ℂ) (hP : P.eval 1 = 1) (w₀ : V) :
    IsCharAvg ψ G (fun Y => P.eval (ψ (G w₀ Y))) := by
  refine ⟨P.natDegree + 1, fun m => P.coeff m, fun m => (m : ℕ) • w₀, ?_, ?_⟩
  · rw [Fin.sum_univ_eq_sum_range (fun i => P.coeff i), ← hP, Polynomial.eval_eq_sum_range]
    simp
  · intro Y
    dsimp only
    rw [Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun i => P.coeff i * ψ (G w₀ Y) ^ i)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_nsmul, Pi.smul_apply, AddChar.map_nsmul_eq_pow]

end Generic

def killPoly (Z : Finset ℂ) : Polynomial ℂ :=
  ∏ ζ ∈ Z.filter (· ≠ 1), (Polynomial.C (1 - ζ)⁻¹ * (Polynomial.X - Polynomial.C ζ))

theorem killPoly_eval_one (Z : Finset ℂ) : (killPoly Z).eval 1 = 1 := by
  unfold killPoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_one fun ζ hζ => ?_
  have : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm (Finset.mem_filter.1 hζ).2)
  simp [this]

theorem killPoly_eval_eq_zero {Z : Finset ℂ} {z : ℂ} (hz : z ∈ Z) (h1 : z ≠ 1) : (killPoly Z).eval z = 0 := by
  unfold killPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_filter.2 ⟨hz, h1⟩) (by simp)

theorem finite_image_of_isLocallyConstant {Ω : Type} [TopologicalSpace Ω] {g : Ω → ℂ} (hg : IsLocallyConstant g)
    {S : Set Ω} (hS : IsCompact S) : (g '' S).Finite := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  rw [Set.image_eq_range]
  exact (hg.comp_continuous continuous_subtype_val).range_finite

theorem rank_ne_of_vecMul_eq_zero {K : Type} [Field K] {n d : ℕ} {c : Fin n → K} (hc : c ≠ 0)
    {Y : Matrix (Fin n) (Fin d) K} (h : Matrix.vecMul c Y = 0) : Y.rank ≠ n := by
  rw [← Matrix.rank_transpose, Matrix.rank]
  have hker : c ∈ LinearMap.ker Yᵀ.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, h]
  have hne : LinearMap.ker Yᵀ.mulVecLin ≠ ⊥ := by
    intro hb; rw [hb, Submodule.mem_bot] at hker; exact hc hker
  have hpos : 0 < Module.finrank K (LinearMap.ker Yᵀ.mulVecLin) := by
    rw [Nat.pos_iff_ne_zero]; exact fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
  have hrn := LinearMap.finrank_range_add_finrank_ker Yᵀ.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  omega

end GlobalTheory.TorusSupportAvg

namespace GlobalTheory.TorusSupportAvg

theorem exists_charAvg_mul_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ (n d : ℕ) (c : Fin n → Fv F v), c ≠ 0 → ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
    (∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → f Y = 0) →
    ∃ (N : ℕ) (a : Fin N → ℂ) (w : Fin N → Fin d → Fv F v), ∑ m, a m = 1 ∧
      ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (∑ m, a m * ψ₀ (∑ k, ∑ l, Y k l * c k * w m l)) * f Y = 0 := by
  intro F _ _ v ψ₀ hψ hne n d c hc f hf hrank
  classical
  have hlc : IsLocallyConstant ψ₀ :=
    @SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.isLocallyConstant_addChar _ _ (GlobalTheory.LocalData.complRel v) _ (GlobalTheory.LocalData.isLocalField v) ψ₀ hψ
  obtain ⟨hloc, hcs⟩ : IsLocallyConstant f ∧ HasCompactSupport f := hf
  let G : (Fin d → Fv F v) →+ (Matrix (Fin n) (Fin d) (Fv F v) → Fv F v) :=
    AddMonoidHom.mk' (fun w Y => ∑ k, ∑ l, Y k l * c k * w l) (by
      intro w₁ w₂; funext Y; simp [mul_add, Finset.sum_add_distrib])
  have hG : ∀ w Y, G w Y = ∑ k, ∑ l, Y k l * c k * w l := fun _ _ => rfl
  have hGc : ∀ w, Continuous (G w) := by
    intro w
    show Continuous fun Y : Matrix (Fin n) (Fin d) (Fv F v) => ∑ k, ∑ l, Y k l * c k * w l
    exact continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ =>
      ((continuous_id.matrix_elem k l).mul continuous_const).mul continuous_const

  set S := Function.support f with hSdef
  have hSc : IsCompact S := by
    have hcl : IsClosed S := by
      have := (hloc.isClopen_fiber 0).isOpen.isClosed_compl
      convert this using 1
      ext x; simp [S, Function.mem_support]
    exact hcs.of_isClosed_subset hcl (subset_tsupport f)

  obtain ⟨t₀, ht₀⟩ : ∃ t, ψ₀ t ≠ 1 := by
    by_contra h; push_neg at h; exact hne (by ext x; simp [h x])
  have hex : ∀ Y ∈ S, ∃ w, ψ₀ (G w Y) ≠ 1 := by
    intro Y hY
    have hr : Y.rank = n := by by_contra h; exact hY (hrank Y h)
    have hv : Matrix.vecMul c Y ≠ 0 := fun h => rank_ne_of_vecMul_eq_zero hc h hr
    obtain ⟨l, hl⟩ : ∃ l, Matrix.vecMul c Y l ≠ 0 := by
      by_contra h; push_neg at h; exact hv (funext h)
    refine ⟨Pi.single l (t₀ / Matrix.vecMul c Y l), ?_⟩
    have : G (Pi.single l (t₀ / Matrix.vecMul c Y l)) Y = t₀ := by
      rw [hG]
      simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← Finset.sum_mul]
      have e : ∑ k, Y k l * c k = Matrix.vecMul c Y l := by
        simp only [Matrix.vecMul, dotProduct]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [e]; field_simp
    rw [this]; exact ht₀
  choose! wch hwch using hex
  have hopen : ∀ Y, IsOpen {Y' | ψ₀ (G (wch Y) Y') ≠ 1} := fun Y =>
    isOpen_compl_singleton.preimage (hψ.comp (hGc _))
  obtain ⟨t, htS, hcov⟩ := hSc.elim_nhds_subcover (fun Y => {Y' | ψ₀ (G (wch Y) Y') ≠ 1})
    (fun Y hY => (hopen Y).mem_nhds (hwch Y hY))
  have hfin : ∀ j, ((fun Y => ψ₀ (G (wch j) Y)) '' S).Finite := fun j =>
    finite_image_of_isLocallyConstant (hlc.comp_continuous (hGc _)) hSc
  have hrep := isCharAvg_prod (ψ := ψ₀) (G := G) t
    (fun j Y => (killPoly (hfin j).toFinset).eval (ψ₀ (G (wch j) Y)))
    (fun j _ => isCharAvg_poly ψ₀ G _ (killPoly_eval_one _) (wch j))
  obtain ⟨N, a, w, hs, hval⟩ := hrep
  refine ⟨N, a, w, hs, fun Y => ?_⟩
  have hv := hval Y
  simp only [hG] at hv
  rw [hv]
  by_cases hY : f Y = 0
  · rw [hY, mul_zero]
  · have hYS : Y ∈ S := hY
    obtain ⟨j, hj, hjY⟩ : ∃ j ∈ t, ψ₀ (G (wch j) Y) ≠ 1 := by
      have := hcov hYS
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
      obtain ⟨j, hj, h⟩ := this
      exact ⟨j, hj, h⟩
    rw [Finset.prod_apply, Finset.prod_eq_zero hj, zero_mul]
    exact killPoly_eval_eq_zero ((hfin j).mem_toFinset.2 ⟨Y, hYS, rfl⟩) hjY

end GlobalTheory.TorusSupportAvg
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_deficient_schwartz_average : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ (n d : ℕ) (c : Fin n → Fv F v), c ≠ 0 → ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
    (∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → f Y = 0) →
    ∃ (N : ℕ) (a : Fin N → ℂ) (w : Fin N → Fin d → Fv F v), ∑ m, a m = 1 ∧
      ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (∑ m, a m * ψ₀ (∑ k, ∑ l, Y k l * c k * w m l)) * f Y = 0 := by
  atlas_forward_decl GlobalTheory.TorusSupportAvg.exists_charAvg_mul_eq_zero
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.HeisMultLin

theorem at_neg_hTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl F} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (x u : Matrix (Fin m) (Fin n) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (cA σ) (incM F JA) (incM F JB) x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

theorem heis_mult_lin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (c : Fin n → AE F E)
    (ι : ((Fin n × Fin d → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F B.v₁) → ℂ)),
    M.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ w : Fin d → Fv F B.v₁, ∃ z : Fin d → AE F E, At (evFin F B.v₁) z ∧
      (∀ l, piW (B.τ₁.comp σ) (z l) = 0) ∧
      ∀ φ ∈ SB (Fin n × Fin d → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F B.v₁),
        Acts (evFin F B.v₁) (M.co.rho B.ψ (Matrix.vecMulVec c z)) φ φ₁ →
        ∀ Y : Matrix (Fin n) (Fin d) (Fv F B.v₁),
          ι φ₁ Y = psiLoc B.ψ B.v₁ (∑ k, ∑ l, Y k l * piW B.τ₁ (c k) * w l) * ι φ Y := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP c ι hι w
  have hcm : IsCMExt F E σ := hP.base.cm
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdX : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.herm.sig w0)
    have e : (X.J.map (B.emb w0).1).det = (B.emb w0).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.skew.sig w0)
    have e : (W.J.map (B.emb w0).1).det = (B.emb w0).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  set A := X.J.map B.τ₁ with hAdef
  set Bm := W.J.map B.τ₁ with hBdef
  have hA : IsUnit A.det := by
    have e : A.det = (B.τ₁ : E →+* Fv F B.v₁) X.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((B.τ₁ : E →+* Fv F B.v₁).injective (by rw [map_zero]; exact h))
  have hB : IsUnit Bmᵀ.det := by
    have e : Bm.det = (B.τ₁ : E →+* Fv F B.v₁) W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((B.τ₁ : E →+* Fv F B.v₁).injective (by rw [map_zero]; exact h))
  obtain ⟨Z, hZat, hZ0, hZ1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm B.v₁ B.τ₁
    (Matrix.of fun (l : Fin d) (_ : Unit) => -w l) (0 : Matrix (Fin d) Unit (Fv F B.v₁))
  have hZa : ∀ a : AF F, evFin F B.v₁ a = 0 → ∀ l, a • Z l () = 0 := fun a ha l => by
    have := congrFun (congrFun (hZat a ha) l) ()
    simpa using this
  have hZτ : ∀ l, piW B.τ₁ (Z l ()) = -w l := fun l => by
    have := congrFun (congrFun hZ0 l) ()
    simpa using this
  have hZσ : ∀ l, piW (B.τ₁.comp σ) (Z l ()) = 0 := fun l => by
    have := congrFun (congrFun hZ1 l) ()
    simpa using this
  refine ⟨fun l => Z l (), ?_, hZσ, ?_⟩
  · intro a ha
    funext l
    simpa using hZa a ha l
  intro φ hφ φ₁ hφ₁ hact Y
  set u := Matrix.vecMulVec c (fun l => Z l ()) with hudef
  have huat : At (evFin F B.v₁) u := by
    intro a ha
    funext k l
    simp only [hudef, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    rw [← mul_smul_comm, hZa a ha l, mul_zero]
  have hu1 : u.map (piW (B.τ₁.comp σ)) = 0 := by
    funext k l
    simp [hudef, Matrix.vecMulVec_apply, map_mul, hZσ]
  have hu0 : ∀ k l, u.map (piW B.τ₁) k l = piW B.τ₁ (c k) * -w l := fun k l => by
    simp [hudef, Matrix.vecMulVec_apply, map_mul, hZτ]
  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  obtain ⟨x, hxat, hx0, hx1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm B.v₁ B.τ₁ (0 : Matrix (Fin n) (Fin d) (Fv F B.v₁))
    (-(A⁻¹ * Y * (Bmᵀ)⁻¹))
  have hco : -(A * x.map (piW (B.τ₁.comp σ)) * Bmᵀ) = Y := by
    rw [hx1]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hm := hL.mult u huat hu1 φ hφ φ₁ hφ₁ hact x hxat hx0
  rw [hco] at hm
  rw [hm]
  congr 1
  have hsymp : B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
      GlobalTheory.LatVac.psiAt B.ψ B.v₁
        (-(∑ k, ∑ j, (-(A * x.map (piW (B.τ₁.comp σ)) * Bmᵀ)) k j * u.map (piW B.τ₁) k j)) := by
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm B.v₁ B.τ₁ _ (at_neg_hTens _ _ x u hxat)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm B.τ₁ X.J W.J hP.herm.herm hP.skew.skew x u hx0 hu1]
    rfl
  rw [hsymp, hco, GlobalTheory.LatVac.psiAt_apply]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hu0]
  ring

end GlobalTheory.HeisMultLin
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_linear_bar_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (c : Fin n → AE F E)
    (ι : ((Fin n × Fin d → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F B.v₁) → ℂ)),
    M.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ w : Fin d → Fv F B.v₁, ∃ z : Fin d → AE F E, At (evFin F B.v₁) z ∧
      (∀ l, piW (B.τ₁.comp σ) (z l) = 0) ∧
      ∀ φ ∈ SB (Fin n × Fin d → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F B.v₁),
        Acts (evFin F B.v₁) (M.co.rho B.ψ (Matrix.vecMulVec c z)) φ φ₁ →
        ∀ Y : Matrix (Fin n) (Fin d) (Fv F B.v₁),
          ι φ₁ Y = psiLoc B.ψ B.v₁ (∑ k, ∑ l, Y k l * piW B.τ₁ (c k) * w l) * ι φ Y := by
  atlas_forward_decl GlobalTheory.HeisMultLin.heis_mult_lin
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKSoKill

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

open Classical in

theorem pure_update_zero (v : Pl F) (f : SInf F κ) (φ : ∀ w : Pl F, (κ → Fv F w) → ℂ)
    (hfin : ∀ x : κ → AF F, (Function.mulSupport fun w => φ w fun i => evFin F w (x i)).Finite) :
    pure f (Function.update φ v 0) = 0 := by
  funext x
  rw [GlobalTheory.ThK.LocalOps.pure_split v f φ (Function.update φ v 0) x (hfin x)
    (fun w hw => Function.update_of_ne hw _ _), Function.update_self, Pi.zero_apply, zero_mul, Pi.zero_apply]

open Classical in

theorem pure_update_sum (v : Pl F) (f : SInf F κ) (φ : ∀ w : Pl F, (κ → Fv F w) → ℂ)
    (hfin : ∀ x : κ → AF F, (Function.mulSupport fun w => φ w fun i => evFin F w (x i)).Finite)
    {N : ℕ} (a : Fin N → ℂ) (g : Fin N → (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v (∑ m, a m • g m)) = ∑ m, a m • pure f (Function.update φ v (g m)) := by
  funext x
  rw [GlobalTheory.ThK.LocalOps.pure_split v f φ _ x (hfin x) (fun w hw => Function.update_of_ne hw _ _),
    Function.update_self, Finset.sum_apply, Finset.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := GlobalTheory.ThK.LocalOps.pure_split v f φ (Function.update φ v (g m)) x (hfin x)
    (fun w hw => Function.update_of_ne hw _ _)
  rw [Function.update_self] at h
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h, mul_assoc]

end GlobalTheory.ThKSoKill

namespace GlobalTheory.ThKSoKill

theorem at_vecMulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (v : Pl F) (c : Fin n → AE F E) (z : Fin d → AE F E) (hz : At (evFin F v) z) :
    At (evFin F v) (Matrix.vecMulVec c z) := by
  intro u hu
  ext i j
  have h := congrFun (hz u hu) j
  simp only [Pi.smul_apply, Pi.zero_apply] at h
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  rw [← mul_smul_comm, h, mul_zero]

open Classical in

theorem so_kill : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (c : Fin n → AE F E),
    (fun k => piW B.τ₁ (c k)) ≠ 0 →
    (∀ z : Fin d → AE F E, At (evFin F B.v₁) z → (∀ l, piW (B.τ₁.comp σ) (z l) = 0) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), Λ (M.co.rho B.ψ (Matrix.vecMulVec c z) Ψ) = Λ Ψ) →
    ∀ Φ ∈ M.So B.ψ B.τ₁, Λ Φ = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Λ c hc hinv Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero => exact map_zero Λ
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]
  | mem x hx =>
    obtain ⟨f, φ, hSB, hcof, ⟨hSB1, ι, hι, hrank⟩, rfl⟩ := hx
    have hstd := (hcof.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    have hfin := fun x => GlobalTheory.PureFactor.mulSupport_finite φ hstd x
    have hpure := GlobalTheory.ConeMeasV.pure_mem_schA hP.good f φ hSB hcof
    obtain ⟨N, a, w, ha1, hkill⟩ := GlobalTheory.T.rank_deficient_schwartz_average F B.v₁ (GlobalTheory.LatVac.psiAt B.ψ B.v₁)
      (GlobalTheory.SchrSB.continuous_psiAt B.ψ hP.base.std.1 B.v₁) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hP.base.std B.v₁)
      n d (fun k => piW B.τ₁ (c k)) hc (ι (φ B.v₁)) (hι.bij.mapsTo hSB1) hrank
    have hmult := fun m => GlobalTheory.T.pair_linear_bar_vector F E σ B n d X W M χX χW om r s r' s' hP c ι hι (w m)
    choose z hzat hzpi hzmul using hmult
    have hAE := GlobalTheory.ThK.LocalOps.actsEx hKP.base
    have hex : ∀ m, ∃ φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F B.v₁) ∧
        Acts (evFin F B.v₁) (M.co.rho B.ψ (Matrix.vecMulVec c (z m))) (φ B.v₁) φ₁ := fun m =>
      ((hAE F E σ B n d X W M χX χW om r s r' s' hP B.v₁).2.1 _ (at_vecMulVec B.v₁ c (z m) (hzat m)) _ hSB1).exists
    choose φ₁ hφ₁SB hφ₁ using hex

    have hsumSB : ∑ m, a m • φ₁ m ∈ SB (Fin n × Fin d → Fv F B.v₁) :=
      Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hφ₁SB m)
    have hsum0 : ∑ m, a m • φ₁ m = 0 := by
      refine hι.bij.injOn hsumSB (Submodule.zero_mem _) ?_
      rw [map_zero, map_sum]
      funext Y
      rw [Finset.sum_apply, Pi.zero_apply]
      have hY := hkill Y
      rw [Finset.sum_mul] at hY
      rw [← hY]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, Pi.smul_apply, smul_eq_mul, hzmul m (φ B.v₁) hSB1 (φ₁ m) (hφ₁SB m) (hφ₁ m) Y,
        GlobalTheory.LatVac.psiAt_apply, mul_assoc]

    have hact : ∀ m, M.co.rho B.ψ (Matrix.vecMulVec c (z m)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pure f (Function.update φ B.v₁ (φ₁ m)) :=
      fun m => GlobalTheory.ThK.LocalOps.acts_pure B.v₁ _ f φ (φ₁ m) hpure hfin (hφ₁ m)
    calc Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = ∑ m, a m • Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by rw [← Finset.sum_smul, ha1, one_smul]
      _ = ∑ m, a m • Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ B.v₁ (φ₁ m))) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← hact m, hinv (z m) (hzat m) (hzpi m) _ hpure]
      _ = Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ B.v₁ (∑ m, a m • φ₁ m))) := by
          rw [pure_update_sum B.v₁ f φ hfin a φ₁, map_sum]
          simp only [map_smul]
      _ = 0 := by rw [hsum0, pure_update_zero B.v₁ f φ hfin, map_zero]

end GlobalTheory.ThKSoKill
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_functional_nonvanishing : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (c : Fin n → AE F E),
    (fun k => piW B.τ₁ (c k)) ≠ 0 →
    (∀ z : Fin d → AE F E, At (evFin F B.v₁) z → (∀ l, piW (B.τ₁.comp σ) (z l) = 0) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), Λ (M.co.rho B.ψ (Matrix.vecMulVec c z) Ψ) = Λ Ψ) →
    ∀ Φ ∈ M.So B.ψ B.τ₁, Λ Φ = 0 := by
  atlas_forward_decl GlobalTheory.ThKSoKill.so_kill
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem piW_mat_inv_mulVec_incV_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) (x : Fin n → E), x ≠ 0 →
    (fun k => piW B.τ₁ ((mat g⁻¹ *ᵥ incV F x) k)) ≠ 0 := by
  intro F E _ _ _ _ _ σ B n J g x hx h
  apply hx
  set φ := piW B.τ₁ with hφ
  have hinc : (fun k => φ (incV F x k)) = fun k => B.τ₁ (x k) := by
    funext k
    exact GlobalTheory.HTensSplitPair.piW_inclR_eq B.τ₁ (x k)
  have hmv : (fun k => φ ((mat g⁻¹ *ᵥ incV F x) k)) = (mat g⁻¹).map φ *ᵥ (fun k => B.τ₁ (x k)) := by
    funext k
    rw [RingHom.map_mulVec, ← hinc]
    rfl
  have hone : mat g * mat g⁻¹ = 1 := by
    unfold mat
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  have hy : (fun k => B.τ₁ (x k)) = 0 := by
    have := congrArg (fun v => (mat g).map φ *ᵥ v) (hmv.symm.trans h)
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hone, Matrix.mulVec_zero] at this
    rw [Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec] at this
    exact this
  funext k
  have := congrFun hy k
  simpa using (map_eq_zero_iff B.τ₁ B.τ₁.toRingHom.injective).1 this

end GlobalTheory.ThKTorus
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_inverse_infinite_nonzero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) (x : Fin n → E), x ≠ 0 →
    (fun k => piW B.τ₁ ((mat g⁻¹ *ᵥ incV F x) k)) ≠ 0 := by
  atlas_forward_decl GlobalTheory.ThKTorus.piW_mat_inv_mulVec_incV_ne_zero
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem vanish_of_block_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ Φ ∈ M.So B.ψ B.τ₁, ∀ (g : UA σ X.J) (h : UA σ W.J) (ξ : Fin n × Fin d → F), (∃ i, ∀ j ∈ blk i, ξ j = 0) →
      e (om (g, h) Φ) (fun j => algebraMap F (AF F) (ξ j)) = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP q x y hfr M₁ blk e hG hco hev Φ hΦ g h ξ hξ
  obtain ⟨i, hi⟩ := hξ
  have htor := GlobalTheory.T.unitary_torus_element_exists F E σ B n X r s hP.base hP.herm q x y hfr
  have hblk := GlobalTheory.T.frame_torus_lattice_action F E σ B n d X W q x y M₁ blk hG hco htor i
  have hW := IsUWeilPair.isUSplitting hP.weil
  set ξ' : Fin n × Fin d → AF F := fun j => algebraMap F (AF F) (ξ j) with hξ'
  let Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => e (om (g, h) Ψ) ξ'
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hxi : x i ≠ 0 := by
    intro h0
    have := hfr.2.2 i i
    simp [h0, form] at this
  have hc := GlobalTheory.T.unitary_inverse_infinite_nonzero F E σ B n X.J g (x i) hxi
  refine GlobalTheory.T.pair_functional_nonvanishing hKP F E σ B n d X W M χX χW om r s r' s' hP Λ (mat g⁻¹ *ᵥ incV F (x i)) hc ?_ Φ hΦ
  intro z _ _ Ψ hΨ
  show e (om (g, h) (M.co.rho B.ψ _ Ψ)) ξ' = e (om (g, h) Ψ) ξ'
  rw [hW.impl (g, h) _ Ψ hΨ]
  have hgg : mat g * mat g⁻¹ = 1 := by simp [mat]
  have hgen : ∀ (A : Matrix (Fin n) (Fin n) (AE F E)) (Bm : Matrix (Fin d) (Fin d) (AE F E))
      (u : Fin n → AE F E) (w : Fin d → AE F E), A * Matrix.vecMulVec u w * Bmᵀ = Matrix.vecMulVec (A *ᵥ u) (Bm *ᵥ w) := by
    intro A Bm u w
    ext k l
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hact : actAB (cA σ) (g, h) (Matrix.vecMulVec (mat g⁻¹ *ᵥ incV F (x i)) z) =
      Matrix.vecMulVec (incV F (x i)) (mat h *ᵥ z) := by
    change mat g * _ * (mat h)ᵀ = _
    rw [hgen, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  rw [hact]
  obtain ⟨z', hz', hze⟩ := hblk (mat h *ᵥ z)
  have hΨ2 : om (g, h) Ψ ∈ schA F _ := hW.pres _ _ hΨ
  have hheis := hev.Heisenberg₂ (Matrix.vecMulVec (incV F (x i)) (mat h *ᵥ z)) _ hΨ2
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp [incM, Matrix.map_one]
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by
    simp [incM, Matrix.map_one]
  rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at hheis
  rw [hheis]
  have hdot : ξ' ⬝ᵥ z' = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ∈ blk i
    · simp [hξ', hi j hj]
    · simp [hz' j hj]
  simp only [Darboux.rho, hze, schr, hdot, zero_dotProduct, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThKTorus
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_frame_model_evaluation : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ Φ ∈ M.So B.ψ B.τ₁, ∀ (g : UA σ X.J) (h : UA σ W.J) (ξ : Fin n × Fin d → F), (∃ i, ∀ j ∈ blk i, ξ j = 0) →
      e (om (g, h) Φ) (fun j => algebraMap F (AF F) (ξ j)) = 0 := by
  first | exact @GlobalTheory.ThKTorus.vanish_of_block_zero | exact GlobalTheory.ThKTorus.vanish_of_block_zero | (intros; apply GlobalTheory.ThKTorus.vanish_of_block_zero <;> assumption)
end
