import Formalism.LocalToGlobal.GlobalTheory.PassageAtBaseSymmetricLevels
import Formalism.LocalToGlobal.GlobalTheory.DivPassageP
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

set_option linter.style.haveILetI false

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.DivPassage2

open Formalism.L2.Indef Formalism.L2.GlobalTheoryTheory.DivPassage

section Chars

variable {K : Type} [Field K] {Γ : Type} [Group Γ] [Finite Γ]






end Chars

section TP

variable {K : Type} [Field K] {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}

theorem sum_mulVec' {ι : Type} (s : Finset ι) (M : ι → Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (∑ i ∈ s, M i) *ᵥ x = ∑ i ∈ s, M i *ᵥ x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]

def tsumP (ρ : Γ →* Matrix (Fin n) (Fin n) K) (H : Subgroup Γ) (χ : H →* Kˣ) : Matrix (Fin n) (Fin n) K :=
  haveI : Fintype H := Fintype.ofFinite H
  ∑ h : H, (((χ h)⁻¹ : Kˣ) : K) • ρ (h : Γ)

theorem typeProj_eq (ρ : Γ →* Matrix (Fin n) (Fin n) K) (H : Subgroup Γ) (χ : H →* Kˣ) :
    typeProj ρ H χ = ((Nat.card H : K)⁻¹) • tsumP ρ H χ := rfl

theorem unit_aux (a b : Kˣ) : (a : K) * (((a * b)⁻¹ : Kˣ) : K) = ((b⁻¹ : Kˣ) : K) := by
  have e : (a : K) * (((a * b)⁻¹ : Kˣ) : K) = ((a * (a * b)⁻¹ : Kˣ) : K) := (Units.val_mul _ _).symm
  rw [e, mul_inv_rev, ← mul_assoc, mul_comm a, mul_assoc, mul_inv_cancel, mul_one]

theorem rho_mul_tsum (ρ : Γ →* Matrix (Fin n) (Fin n) K) (H : Subgroup Γ) (χ : H →* Kˣ) (h : H) :
    ρ (h : Γ) * tsumP ρ H χ = ((χ h : Kˣ) : K) • tsumP ρ H χ := by
  letI : Fintype H := Fintype.ofFinite H
  simp only [tsumP, Finset.mul_sum, Finset.smul_sum, Matrix.mul_smul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun u => ?_)
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, unit_aux]

theorem tsum_mul_tsum (ρ : Γ →* Matrix (Fin n) (Fin n) K) (H : Subgroup Γ) (χ : H →* Kˣ) :
    tsumP ρ H χ * tsumP ρ H χ = (Nat.card H : K) • tsumP ρ H χ := by
  letI : Fintype H := Fintype.ofFinite H
  have e : tsumP ρ H χ * tsumP ρ H χ = ∑ h : H, (((χ h)⁻¹ : Kˣ) : K) • (ρ (h : Γ) * tsumP ρ H χ) := by
    show (∑ h : H, (((χ h)⁻¹ : Kˣ) : K) • ρ (h : Γ)) * tsumP ρ H χ = _
    rw [Finset.sum_mul]
    simp only [Matrix.smul_mul]
  rw [e]
  simp only [rho_mul_tsum, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K]

theorem typeProj_mul_self [CharZero K] (ρ : Γ →* Matrix (Fin n) (Fin n) K) (H : Subgroup Γ) (χ : H →* Kˣ) :
    typeProj ρ H χ * typeProj ρ H χ = typeProj ρ H χ := by
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  rw [typeProj_eq, Matrix.smul_mul, Matrix.mul_smul, tsum_mul_tsum, smul_smul, smul_smul]
  congr 1
  field_simp



variable [NumberField K]



end TP

section Norms

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)

def tmat (v : InfinitePlace K) (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) ℂ :=
  (X v)⁻¹ * M.map v.embedding * X v

theorem toMatrix_mulVecLin (M : Matrix (Fin n) (Fin n) K) :
    LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) M.mulVecLin = M := by
  rw [LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

theorem opNormAt_eq (v : InfinitePlace K) (M : Matrix (Fin n) (Fin n) K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin n)) X v M.mulVecLin =
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (tmat X v M))‖ := by
  simp only [Formalism.HN.opNormAt, tmat, toMatrix_mulVecLin]

theorem fcoord_mulVec (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (M : Matrix (Fin n) (Fin n) K)
    (x : Fin n → K) :
    fcoord (Pi.basisFun K (Fin n)) X v (M *ᵥ x) = tmat X v M *ᵥ fcoord (Pi.basisFun K (Fin n)) X v x := by
  have e := Formalism.HN.PlaceOperatorNorms.fcoord_map (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin n)) X hX v
    M.mulVecLin x
  rw [toMatrix_mulVecLin] at e
  exact e

theorem tmat_mul (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (M N : Matrix (Fin n) (Fin n) K) :
    tmat X v (M * N) = tmat X v M * tmat X v N := by
  simp only [tmat, Matrix.map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (X v) ((X v)⁻¹), Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mul]

theorem maj_eq (v : InfinitePlace K) (x y : Fin n → K) :
    majAt (Pi.basisFun K (Fin n)) X v x y =
      star (fcoord (Pi.basisFun K (Fin n)) X v x) ⬝ᵥ fcoord (Pi.basisFun K (Fin n)) X v y := rfl

theorem fcoord_single (v : InfinitePlace K) (i : Fin n) :
    fcoord (Pi.basisFun K (Fin n)) X v (Pi.basisFun K (Fin n) i) = (X v)⁻¹ *ᵥ Pi.single i 1 := by
  rw [fcoord, Formalism.L2.GlobalTheoryTheory.HLatOps.vecAt_basis]

theorem mat_eq_of_form (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (A C : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ x y : Fin n → K, star (fcoord (Pi.basisFun K (Fin n)) X v x) ⬝ᵥ (A *ᵥ fcoord (Pi.basisFun K (Fin n)) X v y) =
      star (fcoord (Pi.basisFun K (Fin n)) X v x) ⬝ᵥ (C *ᵥ fcoord (Pi.basisFun K (Fin n)) X v y)) : A = C := by
  set Y := (X v)⁻¹ with hY
  have hYu : IsUnit Y := by
    rw [hY, Matrix.isUnit_iff_isUnit_det, Matrix.det_nonsing_inv]
    exact (hX v).ringInverse
  have hYH : IsUnit Yᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hYu).star
  have key : ∀ (B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n),
      star (Y *ᵥ Pi.single i 1) ⬝ᵥ (B *ᵥ (Y *ᵥ Pi.single j 1)) = (Yᴴ * B * Y) i j := by
    intro B i j
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_single_one, Matrix.mul_assoc]
    simp [Pi.single_apply, dotProduct, Matrix.col_apply]
  have hm : Yᴴ * A * Y = Yᴴ * C * Y := by
    ext i j
    have := h (Pi.basisFun K (Fin n) i) (Pi.basisFun K (Fin n) j)
    rw [fcoord_single, fcoord_single] at this
    rw [← key, ← key, this]
  have h1 : Yᴴ * A = Yᴴ * C := hYu.mul_right_cancel hm
  exact hYH.mul_left_cancel h1

theorem tmat_adj (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (M N : Matrix (Fin n) (Fin n) K)
    (h : ∀ x y, majAt (Pi.basisFun K (Fin n)) X v (M *ᵥ x) y = majAt (Pi.basisFun K (Fin n)) X v x (N *ᵥ y)) :
    (tmat X v M)ᴴ = tmat X v N := by
  apply mat_eq_of_form X hX v
  intro x y
  have e := h x y
  rw [maj_eq, maj_eq, fcoord_mulVec X hX, fcoord_mulVec X hX, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at e
  exact e


def Contr (T : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ u, cnorm (T *ᵥ u) ≤ cnorm u

theorem contr_mul {T T' : Matrix (Fin n) (Fin n) ℂ} (h : Contr T) (h' : Contr T') : Contr (T * T') := by
  intro u
  rw [← Matrix.mulVec_mulVec]
  exact le_trans (h _) (h' u)


theorem contr_proj {P : Matrix (Fin n) (Fin n) ℂ} (hH : Pᴴ = P) (hP : P * P = P) : Contr P := by
  intro u
  set w := P *ᵥ u
  set q := u - w
  have hPq : P *ᵥ q = 0 := by
    simp only [q, w, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP, sub_self]
  have c1 : star w ⬝ᵥ q = 0 := by
    simp only [w, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH, hPq, dotProduct_zero]
  have c2 : star q ⬝ᵥ w = 0 := by
    have : star q ⬝ᵥ w = star (star w ⬝ᵥ q) := by
      simp only [dotProduct, star_sum, star_mul', Pi.star_apply, star_star]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this, c1, star_zero]
  have hu : u = w + q := by simp [q]
  have e : ((Formalism.HermitianLatticesTheory.cnorm u ^ 2 : ℝ) : ℂ) = ((Formalism.HermitianLatticesTheory.cnorm w ^ 2 : ℝ) : ℂ) + ((Formalism.HermitianLatticesTheory.cnorm q ^ 2 : ℝ) : ℂ) := by
    rw [Formalism.L2.GlobalTheoryTheory.HLatOps.cnorm_sq_eq, Formalism.L2.GlobalTheoryTheory.HLatOps.cnorm_sq_eq, Formalism.L2.GlobalTheoryTheory.HLatOps.cnorm_sq_eq]
    conv_lhs => rw [hu]
    rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, c1, c2]
    ring
  have e' : Formalism.HermitianLatticesTheory.cnorm u ^ 2 = Formalism.HermitianLatticesTheory.cnorm w ^ 2 + Formalism.HermitianLatticesTheory.cnorm q ^ 2 := by exact_mod_cast e
  have h0 := Formalism.L2.GlobalTheoryTheory.HLatOps.cnorm_nonneg w
  have h1 := Formalism.L2.GlobalTheoryTheory.HLatOps.cnorm_nonneg u
  nlinarith [sq_nonneg (Formalism.HermitianLatticesTheory.cnorm q)]

theorem opN_le_one {T : Matrix (Fin n) (Fin n) ℂ} (h : Contr T) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin T)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  have e1 : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin T)) a‖ = cnorm (T *ᵥ WithLp.ofLp a) := by
    rw [Formalism.HN.PlaceOperatorNorms.cnorm_eq]; try rfl
  have e2 : ‖a‖ = cnorm (WithLp.ofLp a) := by rw [Formalism.HN.PlaceOperatorNorms.cnorm_eq]; try rfl
  rw [e1, e2, one_mul]
  exact h _

end Norms

section Adj

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}
  (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)

theorem maj_add_left (v : InfinitePlace K) (x x' y : Fin n → K) :
    majAt (Pi.basisFun K (Fin n)) X v (x + x') y =
      majAt (Pi.basisFun K (Fin n)) X v x y + majAt (Pi.basisFun K (Fin n)) X v x' y :=
  (Formalism.L2.GlobalTheoryTheory.HLatOps.isSesq_maj (Pi.basisFun K (Fin n)) X v).1 x x' y

theorem maj_add_right (v : InfinitePlace K) (x y y' : Fin n → K) :
    majAt (Pi.basisFun K (Fin n)) X v x (y + y') =
      majAt (Pi.basisFun K (Fin n)) X v x y + majAt (Pi.basisFun K (Fin n)) X v x y' :=
  (Formalism.L2.GlobalTheoryTheory.HLatOps.isSesq_maj (Pi.basisFun K (Fin n)) X v).2.1 x y y'

theorem maj_smul_left (v : InfinitePlace K) (a : K) (x y : Fin n → K) :
    majAt (Pi.basisFun K (Fin n)) X v (a • x) y =
      starRingEnd ℂ (v.embedding a) * majAt (Pi.basisFun K (Fin n)) X v x y :=
  (Formalism.L2.GlobalTheoryTheory.HLatOps.isSesq_maj (Pi.basisFun K (Fin n)) X v).2.2.1 a x y

theorem maj_smul_right (v : InfinitePlace K) (a : K) (x y : Fin n → K) :
    majAt (Pi.basisFun K (Fin n)) X v x (a • y) = v.embedding a * majAt (Pi.basisFun K (Fin n)) X v x y :=
  (Formalism.L2.GlobalTheoryTheory.HLatOps.isSesq_maj (Pi.basisFun K (Fin n)) X v).2.2.2 a x y

theorem maj_zero_left (v : InfinitePlace K) (y : Fin n → K) : majAt (Pi.basisFun K (Fin n)) X v 0 y = 0 := by
  have := maj_smul_left X v 0 0 y
  simpa using this

theorem maj_zero_right (v : InfinitePlace K) (x : Fin n → K) : majAt (Pi.basisFun K (Fin n)) X v x 0 = 0 := by
  have := maj_smul_right X v 0 x 0
  simpa using this

theorem maj_sum_left (v : InfinitePlace K) {ι : Type} (s : Finset ι) (f : ι → Fin n → K) (y : Fin n → K) :
    majAt (Pi.basisFun K (Fin n)) X v (∑ i ∈ s, f i) y = ∑ i ∈ s, majAt (Pi.basisFun K (Fin n)) X v (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [maj_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, maj_add_left, ih]

theorem maj_sum_right (v : InfinitePlace K) {ι : Type} (s : Finset ι) (f : ι → Fin n → K) (x : Fin n → K) :
    majAt (Pi.basisFun K (Fin n)) X v x (∑ i ∈ s, f i) = ∑ i ∈ s, majAt (Pi.basisFun K (Fin n)) X v x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [maj_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, maj_add_right, ih]

theorem maj_move (ρ : Γ →* Matrix (Fin n) (Fin n) K)
    (hI : ∀ (g : Γ) v (x y : Fin n → K), majAt (Pi.basisFun K (Fin n)) X v (ρ g *ᵥ x) (ρ g *ᵥ y) =
      majAt (Pi.basisFun K (Fin n)) X v x y) (g : Γ) (v : InfinitePlace K) (x y : Fin n → K) :
    majAt (Pi.basisFun K (Fin n)) X v (ρ g *ᵥ x) y = majAt (Pi.basisFun K (Fin n)) X v x (ρ g⁻¹ *ᵥ y) := by
  have e := hI g v x (ρ g⁻¹ *ᵥ y)
  rwa [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec] at e



end Adj

section Lat

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

theorem mem_range_idem {n : ℕ} {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) {y : Fin n → K} :
    y ∈ LinearMap.range P.mulVecLin ↔ P *ᵥ y = y := by
  constructor
  · rintro ⟨x, rfl⟩
    show P *ᵥ (P *ᵥ x) = P *ᵥ x
    rw [Matrix.mulVec_mulVec, hP]
  · intro h
    exact ⟨y, h⟩

theorem mem_range_mul {n : ℕ} (P Q : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (P * Q) *ᵥ x ∈ LinearMap.range P.mulVecLin :=
  ⟨Q *ᵥ x, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]⟩

theorem range_mul_le {n : ℕ} (P Q : Matrix (Fin n) (Fin n) K) :
    LinearMap.range (P * Q).mulVecLin ≤ LinearMap.range P.mulVecLin := by
  rintro y ⟨x, rfl⟩
  exact mem_range_mul P Q x

theorem es_fix (hO1 : ∀ s, A.es s * A.es s = A.es s) (P : Matrix (Fin A.Dg) (Fin A.Dg) K) (s : A.S)
    (hc : A.es s * P = P * A.es s) {x : Fin A.Dg → K} (hx : x ∈ LinearMap.range (P * A.es s).mulVecLin) :
    A.es s *ᵥ x = x := by
  obtain ⟨z, rfl⟩ := hx
  show A.es s *ᵥ ((P * A.es s) *ᵥ z) = (P * A.es s) *ᵥ z
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hc, Matrix.mul_assoc, hO1 s]

theorem parts_orth
    (hA : ∀ s v (x y : Fin A.Dg → K), majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v (A.es s *ᵥ x) y =
      majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x (A.es s *ᵥ y))
    (hO1 : ∀ s, A.es s * A.es s = A.es s) (hO2 : ∀ s t, s ≠ t → A.es s * A.es t = 0)
    (P : Matrix (Fin A.Dg) (Fin A.Dg) K) (hc : ∀ s, A.es s * P = P * A.es s) (s t : A.S) (hst : s ≠ t) :
    Formalism.BranchingDeterminantCap.OrthAt (Pi.basisFun K (Fin A.Dg)) A.Xg (A.partLat (P * A.es s)) (A.partLat (P * A.es t)) := by
  intro v x hx y hy
  rw [← es_fix A hO1 P s (hc s) hx.2, ← es_fix A hO1 P t (hc t) hy.2, hA, Matrix.mulVec_mulVec, hO2 s t hst,
    Matrix.zero_mulVec]
  exact maj_zero_right A.Xg v x

theorem parts_sand (hE : ∑ s, A.es s = 1)
    (hI : ∀ s, ∀ x ∈ A.Rg, ((A.G : ℕ) : 𝓞 K) • (A.es s *ᵥ x) ∈ A.Rg)
    (hO1 : ∀ s, A.es s * A.es s = A.es s) (P : Matrix (Fin A.Dg) (Fin A.Dg) K)
    (hPP : P * P = P) (hc : ∀ s, A.es s * P = P * A.es s) :
    ∀ x ∈ A.partLat P, ((A.G : ℕ) : 𝓞 K) • x ∈ ⨆ s, A.partLat (P * A.es s) := by
  intro x hx
  have hPx : P *ᵥ x = x := (mem_range_idem hPP).1 hx.2
  have hsum : x = ∑ s, A.es s *ᵥ x := by
    rw [← sum_mulVec', hE, Matrix.one_mulVec]
  rw [hsum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  refine Submodule.mem_iSup_of_mem s ⟨hI s x hx.1, ?_⟩
  have hr : A.es s *ᵥ x ∈ LinearMap.range (P * A.es s).mulVecLin := by
    refine ⟨A.es s *ᵥ x, ?_⟩
    show (P * A.es s) *ᵥ (A.es s *ᵥ x) = A.es s *ᵥ x
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hO1 s, ← hc s, ← Matrix.mulVec_mulVec, hPx]
  exact ((LinearMap.range (P * A.es s).mulVecLin).restrictScalars (𝓞 K)).smul_mem _ hr

theorem rk_partLat (hL : A.LatG) (P : Matrix (Fin A.Dg) (Fin A.Dg) K) :
    Formalism.HN.rkK (A.partLat P) = finrank K (LinearMap.range P.mulVecLin) := by
  unfold Formalism.HN.rkK
  rw [A.span_partLat hL P]

theorem rkK_bot {n : ℕ} : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) (Fin n → K)) = 0 := by
  unfold Formalism.HN.rkK
  rw [Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot]

theorem degD_rk_zero {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (L : Submodule (𝓞 K) (Fin n → K))
    (h : Formalism.HN.rkK L = 0) : Formalism.BranchingDeterminantCap.degD (Pi.basisFun K (Fin n)) X L = 0 := by
  unfold Formalism.BranchingDeterminantCap.degD
  rw [h]; simp

end Lat

section Gen

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

theorem xs_inj_gen (u u' : ∀ s : A.S, Fin (A.nS s) → Matrix (Fin A.Dg) (Fin A.Dg) K) (hF : A.FramesG)
    (a0 : ∀ v (x y : Fin A.Dg → K), majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v (A.ep0 *ᵥ x) y =
      majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x (A.ep0 *ᵥ y))
    (a1 : ∀ v (x y : Fin A.Dg → K), majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v (A.ep1 *ᵥ x) y =
      majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x (A.ep1 *ᵥ y))
    (hA : ∀ s v (x y : Fin A.Dg → K), majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v (A.es s *ᵥ x) y =
      majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x (A.es s *ᵥ y))
    (hadj : ∀ s i v (x y : Fin A.Dg → K), majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v (u s i *ᵥ x) y =
      majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x (u' s i *ᵥ y))
    (hDM : ∀ s, finrank K (LinearMap.range (A.ep1 * A.es s).mulVecLin) =
      A.nS s * finrank K (LinearMap.range (A.ep0 * A.es s).mulVecLin))
    (hXI : ∀ s (a : Fin (A.nS s) → Fin A.Dg → K), (∀ i, a i ∈ LinearMap.range (A.ep0 * A.es s).mulVecLin) →
      ∑ i, (A.ep1 * A.es s * u s i * A.ep0) *ᵥ a i = 0 → a = 0)
    (s : A.S) (c : Fin A.Dg → K) (hc : c ∈ LinearMap.range (A.ep1 * A.es s).mulVecLin)
    (h0 : ∀ i, (A.ep0 * u' s i * A.es s * A.ep1) *ᵥ c = 0) : c = 0 := by
  set W0 := LinearMap.range (A.ep0 * A.es s).mulVecLin with hW0
  set W1 := LinearMap.range (A.ep1 * A.es s).mulVecLin with hW1
  let Ψ : (Fin (A.nS s) → W0) →ₗ[K] (Fin A.Dg → K) :=
    ∑ i, (A.ep1 * A.es s * u s i * A.ep0).mulVecLin ∘ₗ W0.subtype ∘ₗ LinearMap.proj i
  have hΨa : ∀ a, Ψ a = ∑ i, (A.ep1 * A.es s * u s i * A.ep0) *ᵥ (a i : Fin A.Dg → K) := by
    intro a
    simp only [Ψ, LinearMap.sum_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply,
      LinearMap.proj_apply, Submodule.subtype_apply]
  have hΨ : ∀ a, Ψ a ∈ W1 := by
    intro a
    rw [hΨa]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mul_assoc]
    exact mem_range_mul _ _ _
  let Φ : (Fin (A.nS s) → W0) →ₗ[K] W1 := Ψ.codRestrict W1 hΨ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h1 : Ψ a = 0 := by
      have := congrArg Subtype.val ha
      simpa [Φ] using this
    rw [hΨa] at h1
    have h2 := hXI s (fun i => (a i : Fin A.Dg → K)) (fun i => (a i).2) h1
    funext i
    exact Subtype.ext (congrFun h2 i)
  have hdim : finrank K (Fin (A.nS s) → W0) = finrank K W1 := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hW1, hDM s]
  have hsurj : Function.Surjective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  obtain ⟨a, ha⟩ := hsurj ⟨c, hc⟩
  have hca : c = ∑ i, (A.ep1 * A.es s * u s i * A.ep0) *ᵥ (a i : Fin A.Dg → K) := by
    have := congrArg Subtype.val ha
    rw [← hΨa]
    exact this.symm
  have hadj' : ∀ i (x y : Fin A.Dg → K) v, majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v
      ((A.ep1 * A.es s * u s i * A.ep0) *ᵥ x) y =
      majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x ((A.ep0 * u' s i * A.es s * A.ep1) *ᵥ y) := by
    intro i x y v
    simp only [← Matrix.mulVec_mulVec]
    rw [a1, hA, hadj, a0]
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hcc : majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v c c = 0 := by
    nth_rewrite 1 [hca]
    rw [maj_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hadj', h0 i, maj_zero_right]
  have hn : normAt (Pi.basisFun K (Fin A.Dg)) A.Xg v c = 0 := by
    rw [Formalism.L2.GlobalTheoryTheory.HLatOps.normAt_eq_sqrt, hcc, Complex.zero_re, Real.sqrt_zero]
  exact Formalism.L2.GlobalTheoryTheory.HLatOps.normAt_eq_zero _ _ v (hF v) hn

theorem transfer_gen [IsTotallyComplex K] (u u' : ∀ s : A.S, Fin (A.nS s) → Matrix (Fin A.Dg) (Fin A.Dg) K)
    (hF : A.FramesG) (hL : A.LatG) (hRows : A.RowsG) (hGp : 0 < A.G)
    (i0 : A.ep0 * A.ep0 = A.ep0) (i1 : A.ep1 * A.ep1 = A.ep1)
    (c0 : ∀ s, A.es s * A.ep0 = A.ep0 * A.es s) (c1 : ∀ s, A.es s * A.ep1 = A.ep1 * A.es s)
    (n0 : ∀ x ∈ A.Rg, ((A.G : ℕ) : 𝓞 K) • (A.ep0 *ᵥ x) ∈ A.Rg)
    (n1 : ∀ x ∈ A.Rg, ((A.G : ℕ) : 𝓞 K) • (A.ep1 *ᵥ x) ∈ A.Rg)
    (a0 : ∀ v (x y : Fin A.Dg → K), majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v (A.ep0 *ᵥ x) y =
      majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x (A.ep0 *ᵥ y))
    (a1 : ∀ v (x y : Fin A.Dg → K), majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v (A.ep1 *ᵥ x) y =
      majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x (A.ep1 *ᵥ y))
    (hO1 : ∀ s, A.es s * A.es s = A.es s) (hO2 : ∀ s t, s ≠ t → A.es s * A.es t = 0)
    (hE : ∑ s, A.es s = 1) (hI : ∀ s, ∀ x ∈ A.Rg, ((A.G : ℕ) : 𝓞 K) • (A.es s *ᵥ x) ∈ A.Rg)
    (hA : ∀ s v (x y : Fin A.Dg → K), majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v (A.es s *ᵥ x) y =
      majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x (A.es s *ᵥ y))
    (hu : ∀ s i, ∀ x ∈ A.Rg, u s i *ᵥ x ∈ A.Rg) (hu' : ∀ s i, ∀ x ∈ A.Rg, u' s i *ᵥ x ∈ A.Rg)
    (huc : ∀ s i v, Contr (tmat A.Xg v (u s i))) (hu'c : ∀ s i v, Contr (tmat A.Xg v (u' s i)))
    (hadj : ∀ s i v (x y : Fin A.Dg → K), majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v (u s i *ᵥ x) y =
      majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x (u' s i *ᵥ y))
    (hcu' : ∀ s i, A.es s * u' s i = u' s i * A.es s)
    (hDM : ∀ s, finrank K (LinearMap.range (A.ep1 * A.es s).mulVecLin) =
      A.nS s * finrank K (LinearMap.range (A.ep0 * A.es s).mulVecLin))
    (hXI : ∀ s (a : Fin (A.nS s) → Fin A.Dg → K), (∀ i, a i ∈ LinearMap.range (A.ep0 * A.es s).mulVecLin) →
      ∑ i, (A.ep1 * A.es s * u s i * A.ep0) *ᵥ a i = 0 → a = 0)
    (hNS : ∀ s, A.nS s ^ 2 ≤ A.G) :
    A.Ranks ∧ A.Deg0 ∧ A.Deg1 ∧ A.MaxT := by
  have hGr : (1 : ℝ) ≤ (A.G : ℝ) := by exact_mod_cast hGp
  have hlogG : 0 ≤ Real.log (A.G : ℝ) := Real.log_nonneg hGr
  have le0 : ∀ s, A.partLat (A.ep0 * A.es s) ≤ A.partLat A.ep0 := fun s y hy => ⟨hy.1, range_mul_le _ _ hy.2⟩
  have le1 : ∀ s, A.partLat (A.ep1 * A.es s) ≤ A.partLat A.ep1 := fun s y hy => ⟨hy.1, range_mul_le _ _ hy.2⟩
  have OS0 := Formalism.BranchingDeterminantCap.orthSandwich K (Fin A.Dg → K) (Fin A.Dg) (Pi.basisFun K (Fin A.Dg)) A.Xg hF A.S
    (fun s => A.partLat (A.ep0 * A.es s)) (A.partLat A.ep0) A.G (A.partLat_fg hL _) hGp
    (parts_orth A hA hO1 hO2 _ c0) le0 (parts_sand A hE hI hO1 _ i0 c0)
  have OS1 := Formalism.BranchingDeterminantCap.orthSandwich K (Fin A.Dg → K) (Fin A.Dg) (Pi.basisFun K (Fin A.Dg)) A.Xg hF A.S
    (fun s => A.partLat (A.ep1 * A.es s)) (A.partLat A.ep1) A.G (A.partLat_fg hL _) hGp
    (parts_orth A hA hO1 hO2 _ c1) le1 (parts_sand A hE hI hO1 _ i1 c1)
  have hrkB : ∀ s, Formalism.HN.rkK (A.partLat (A.ep1 * A.es s)) = A.nS s * Formalism.HN.rkK (A.partLat (A.ep0 * A.es s)) := by
    intro s
    rw [rk_partLat A hL, rk_partLat A hL]
    exact hDM s

  have hcP : ∀ P : Matrix (Fin A.Dg) (Fin A.Dg) K, P * P = P →
      (∀ v (x y : Fin A.Dg → K), majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v (P *ᵥ x) y =
        majAt (Pi.basisFun K (Fin A.Dg)) A.Xg v x (P *ᵥ y)) → ∀ v, Contr (tmat A.Xg v P) := by
    intro P hPP hPa v
    apply contr_proj
    · exact tmat_adj A.Xg hF v P P (hPa v)
    · rw [← tmat_mul A.Xg hF, hPP]
  have hnx : ∀ s i v, Formalism.HN.opNormAt (Pi.basisFun K (Fin A.Dg)) A.Xg (Pi.basisFun K (Fin A.Dg)) A.Xg v
      (A.ep1 * A.es s * u s i * A.ep0).mulVecLin ≤ 1 := by
    intro s i v
    rw [opNormAt_eq]
    apply opN_le_one
    rw [tmat_mul A.Xg hF, tmat_mul A.Xg hF, tmat_mul A.Xg hF]
    exact contr_mul (contr_mul (contr_mul (hcP _ i1 a1 v) (hcP _ (hO1 s) (hA s) v)) (huc s i v)) (hcP _ i0 a0 v)
  have hnxs : ∀ s i v, Formalism.HN.opNormAt (Pi.basisFun K (Fin A.Dg)) A.Xg (Pi.basisFun K (Fin A.Dg)) A.Xg v
      (A.ep0 * u' s i * A.es s * A.ep1).mulVecLin ≤ 1 := by
    intro s i v
    rw [opNormAt_eq]
    apply opN_le_one
    rw [tmat_mul A.Xg hF, tmat_mul A.Xg hF, tmat_mul A.Xg hF]
    exact contr_mul (contr_mul (contr_mul (hcP _ i0 a0 v) (hu'c s i v)) (hcP _ (hO1 s) (hA s) v)) (hcP _ i1 a1 v)

  have hx3 : ∀ s i, ∀ a ∈ A.partLat (A.ep0 * A.es s),
      ((A.G : 𝓞 K) ^ 3) • (A.ep1 * A.es s * u s i * A.ep0).mulVecLin a ∈ A.partLat (A.ep1 * A.es s) := by
    intro s i a ha
    have ha0 : A.ep0 *ᵥ a = a := (mem_range_idem i0).1 (range_mul_le _ _ ha.2)
    have hxa : (A.ep1 * A.es s * u s i * A.ep0).mulVecLin a = A.ep1 *ᵥ (A.es s *ᵥ (u s i *ᵥ a)) := by
      rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, ha0, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    refine ⟨?_, ?_⟩
    · rw [hxa]
      have h3 := n1 _ (hI s _ (hu s i a ha.1))
      have e : ((A.G : 𝓞 K) ^ 3) • (A.ep1 *ᵥ (A.es s *ᵥ (u s i *ᵥ a))) =
          (A.G : 𝓞 K) • ((A.G : 𝓞 K) • (A.ep1 *ᵥ ((A.G : 𝓞 K) • (A.es s *ᵥ (u s i *ᵥ a))))) := by
        rw [Matrix.mulVec_smul, smul_smul, smul_smul]
        congr 1
        ring
      rw [e]
      exact A.Rg.smul_mem _ h3
    · have hm : (A.ep1 * A.es s * u s i * A.ep0).mulVecLin a ∈ LinearMap.range (A.ep1 * A.es s).mulVecLin := by
        rw [Matrix.mulVecLin_apply, Matrix.mul_assoc]
        exact mem_range_mul _ _ _
      exact ((LinearMap.range (A.ep1 * A.es s).mulVecLin).restrictScalars (𝓞 K)).smul_mem _ hm
  have hxs3 : ∀ s i, ∀ c ∈ A.partLat (A.ep1 * A.es s),
      ((A.G : 𝓞 K) ^ 3) • (A.ep0 * u' s i * A.es s * A.ep1).mulVecLin c ∈ A.partLat (A.ep0 * A.es s) := by
    intro s i c hc
    have hc1 : A.ep1 *ᵥ c = c := (mem_range_idem i1).1 (range_mul_le _ _ hc.2)
    have hxc : (A.ep0 * u' s i * A.es s * A.ep1).mulVecLin c = A.ep0 *ᵥ (u' s i *ᵥ (A.es s *ᵥ c)) := by
      rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, hc1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    refine ⟨?_, ?_⟩
    · rw [hxc]
      have h4 := n0 _ (hu' s i _ (hI s c hc.1))
      have e : ((A.G : 𝓞 K) ^ 3) • (A.ep0 *ᵥ (u' s i *ᵥ (A.es s *ᵥ c))) =
          (A.G : 𝓞 K) • ((A.G : 𝓞 K) • (A.ep0 *ᵥ (u' s i *ᵥ ((A.G : 𝓞 K) • (A.es s *ᵥ c))))) := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, smul_smul]
        congr 1
        ring
      rw [e]
      exact A.Rg.smul_mem _ h4
    · have hmat : A.ep0 * u' s i * A.es s * A.ep1 = (A.ep0 * A.es s) * (u' s i * A.ep1) := by
        rw [Matrix.mul_assoc (A.ep0 * u' s i), Matrix.mul_assoc A.ep0, ← Matrix.mul_assoc (u' s i), ← hcu' s i,
          Matrix.mul_assoc (A.es s), ← Matrix.mul_assoc A.ep0]
      have hm : (A.ep0 * u' s i * A.es s * A.ep1).mulVecLin c ∈ LinearMap.range (A.ep0 * A.es s).mulVecLin := by
        rw [Matrix.mulVecLin_apply, hmat]
        exact mem_range_mul _ _ _
      exact ((LinearMap.range (A.ep0 * A.es s).mulVecLin).restrictScalars (𝓞 K)).smul_mem _ hm
  have hxsinj : ∀ s, ∀ c ∈ A.partLat (A.ep1 * A.es s),
      (∀ i, (A.ep0 * u' s i * A.es s * A.ep1).mulVecLin c = 0) → c = 0 :=
    fun s c hc h => xs_inj_gen A u u' hF a0 a1 hA hadj hDM hXI s c hc.2 h

  have hdeg : ∀ s, (A.nS s : ℝ) * Formalism.BranchingDeterminantCap.degD (Pi.basisFun K (Fin A.Dg)) A.Xg (A.partLat (A.ep0 * A.es s)) -
      13 / 2 * Real.log A.G * ((A.nS s : ℝ) * Formalism.HN.rkK (A.partLat (A.ep0 * A.es s))) ≤
      Formalism.BranchingDeterminantCap.degD (Pi.basisFun K (Fin A.Dg)) A.Xg (A.partLat (A.ep1 * A.es s)) := by
    intro s
    by_cases hz : A.nS s = 0 ∨ A.partLat (A.ep0 * A.es s) = ⊥
    · have hr0 : (A.nS s : ℝ) * (Formalism.HN.rkK (A.partLat (A.ep0 * A.es s)) : ℝ) = 0 := by
        rcases hz with h | h
        · rw [h]; simp
        · rw [h, rkK_bot]; simp
      have hB0 : Formalism.HN.rkK (A.partLat (A.ep1 * A.es s)) = 0 := by
        rw [hrkB]
        rcases hz with h | h
        · rw [h, zero_mul]
        · rw [h, rkK_bot, mul_zero]
      have hA0 : (A.nS s : ℝ) * Formalism.BranchingDeterminantCap.degD (Pi.basisFun K (Fin A.Dg)) A.Xg (A.partLat (A.ep0 * A.es s)) = 0 := by
        rcases hz with h | h
        · rw [h]; simp
        · rw [degD_rk_zero _ _ (by rw [h]; exact rkK_bot), mul_zero]
      rw [degD_rk_zero _ _ hB0, hA0, hr0]
      simp
    · rw [not_or] at hz
      obtain ⟨hn, hne⟩ := hz
      have hnpos : 0 < A.nS s := Nat.pos_of_ne_zero hn
      have T := Formalism.BranchingDeterminantCap.transferPart K (Fin A.Dg → K) (Fin A.Dg) (Pi.basisFun K (Fin A.Dg)) A.Xg hF
        (A.partLat (A.ep0 * A.es s)) (A.partLat (A.ep1 * A.es s)) (A.nS s) A.G
        (fun i => (A.ep1 * A.es s * u s i * A.ep0).mulVecLin) (fun i => (A.ep0 * u' s i * A.es s * A.ep1).mulVecLin)
        (A.partLat_fg hL _) (A.partLat_fg hL _) hne hnpos hGp (hx3 s) (hxs3 s) (hnx s) (hnxs s)
        (fun a ha h => hXI s a (fun i => (ha i).2) h) (hxsinj s) (hrkB s)
      have hlogn : Real.log (A.nS s : ℝ) ≤ 1 / 2 * Real.log A.G := by
        have h1 : ((A.nS s : ℝ)) ^ 2 ≤ (A.G : ℝ) := by exact_mod_cast hNS s
        have hp : (0 : ℝ) < (A.nS s : ℝ) ^ 2 := by positivity
        have h2 : Real.log (((A.nS s : ℝ)) ^ 2) ≤ Real.log A.G := Real.log_le_log hp h1
        rw [Real.log_pow] at h2
        push_cast at h2
        linarith
      have hrk0 : (0 : ℝ) ≤ (A.nS s : ℝ) * (Formalism.HN.rkK (A.partLat (A.ep0 * A.es s)) : ℝ) := by positivity
      have t1 := (abs_le.mp T).1
      have t2 := mul_le_mul_of_nonneg_right hlogn hrk0
      nlinarith
  unfold LevelAmb.Ranks LevelAmb.Deg0 LevelAmb.Deg1 LevelAmb.MaxT LevelAmb.latticeAtBaseLevel LevelAmb.latticeAtSharpLevel LevelAmb.Rs
  refine ⟨⟨OS0.1, ?_⟩, OS0.2.2, ?_, ?_⟩
  · rw [OS1.1]
    exact Finset.sum_congr rfl fun s _ => hrkB s
  · have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hdeg s)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
    have hr : (Formalism.HN.rkK (A.partLat A.ep1) : ℝ) =
        ∑ s, (A.nS s : ℝ) * (Formalism.HN.rkK (A.partLat (A.ep0 * A.es s)) : ℝ) := by
      rw [OS1.1]
      push_cast
      exact Finset.sum_congr rfl fun s _ => by rw [hrkB s]; push_cast; ring
    have hpos : 0 ≤ Real.log (A.G : ℝ) * (Formalism.HN.rkK (A.partLat A.ep1) : ℝ) :=
      mul_nonneg hlogG (Nat.cast_nonneg _)
    have h3 := OS1.2.1
    rw [hr] at hpos ⊢
    nlinarith
  · exact Formalism.BranchingDeterminantCap.transferMuMax K (Fin A.Dg → K) (Fin A.Dg) (Pi.basisFun K (Fin A.Dg)) A.Xg hF A.S
      (fun s => A.partLat (A.ep0 * A.es s)) (fun s => A.partLat (A.ep1 * A.es s)) (A.partLat A.ep1)
      (A.partLat A.ep0) A.G A.nS (fun s i => (A.ep0 * u' s i * A.es s * A.ep1).mulVecLin)
      (A.partLat_fg hL _) (A.partLat_fg hL _) hRows.2 hGp hNS
      (parts_orth A hA hO1 hO2 _ c1) le1 (parts_sand A hE hI hO1 _ i1 c1) le0 (fun s i c hc => hxs3 s i c hc)
      hnxs hxsinj

theorem rows_gen (hL : A.LatG) {D : ℕ} (ι : Matrix (Fin A.Dg) (Fin D) K) (P : Matrix (Fin A.Dg) (Fin A.Dg) K)
    (hD : 0 < D) (hinj : Function.Injective ι.mulVec) (hr : LinearMap.range ι.mulVecLin = LinearMap.range P.mulVecLin) :
    A.partLat P ≠ ⊥ := by
  intro hb
  have hspan := A.span_partLat hL P
  rw [hb, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
  obtain ⟨x, hx⟩ : ∃ x : Fin D → K, x ≠ 0 := ⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hD⟩)⟩
  have hmem : ι *ᵥ x ∈ LinearMap.range P.mulVecLin := by
    rw [← hr]
    exact ⟨_, rfl⟩
  rw [← hspan, Submodule.mem_bot] at hmem
  exact hx (hinj (by rw [hmem, Matrix.mulVec_zero]))

end Gen







section Triv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def trivRep (D : ℕ) (X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (R : Submodule (𝓞 K) (Fin D → K)) :
    RepDat K Unit D D where
  Dg := D
  Xg := X
  Rg := R
  ρ := 1
  S := Unit
  fS := inferInstance
  es := fun _ => 1
  nS := fun _ => 1
  nbar := 1
  γ := fun _ _ => 1
  ι0 := 1
  ι1 := 1


end Triv

end Formalism.L2.GlobalTheoryTheory.DivPassage2
