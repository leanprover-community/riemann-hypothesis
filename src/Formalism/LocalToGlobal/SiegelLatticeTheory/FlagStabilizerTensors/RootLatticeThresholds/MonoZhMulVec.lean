import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotGeo
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis

section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]

def Ymat (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) : Matrix n n ℂ :=
  1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J

theorem rankUpdate_mul (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (hΓ : IsUnit (Wᴴ * J * W).det) :
    Ymat J W M * W = W * (1 + M) := by
  have hinv : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  unfold Ymat
  calc (1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J) * W
        = W + W * M * ((Wᴴ * J * W)⁻¹ * (Wᴴ * J * W)) := by
          simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = W * (1 + M) := by rw [hinv, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one]

theorem Ymat_sub (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (x : n → ℂ) :
    Ymat J W M *ᵥ x - x = W *ᵥ (M *ᵥ ((Wᴴ * J * W)⁻¹ *ᵥ ((Wᴴ * J) *ᵥ x))) := by
  unfold Ymat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem Ymat_unitary (J : Matrix n n ℂ) (hJ : Jᴴ = J) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ)
    (hΓ : IsUnit (Wᴴ * J * W).det) (hM : (1 + M)ᴴ * (Wᴴ * J * W) * (1 + M) = Wᴴ * J * W) :
    (Ymat J W M)ᴴ * J * Ymat J W M = J := by
  have hGh : (Wᴴ * J * W)ᴴ = Wᴴ * J * W := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ,
      Matrix.mul_assoc]
  have hGi1 : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  have hGi2 : (Wᴴ * J * W) * (Wᴴ * J * W)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΓ
  have hGih : ((Wᴴ * J * W)⁻¹)ᴴ = (Wᴴ * J * W)⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  unfold Ymat
  set G := Wᴴ * J * W with hG
  set Gi := G⁻¹ with hGi

  have hK : G * M + Mᴴ * G + Mᴴ * G * M = 0 := by
    have h' := hM
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one] at h'
    have e : (1 + Mᴴ) * G * (1 + M) = G + (G * M + Mᴴ * G + Mᴴ * G * M) := by noncomm_ring
    rw [e] at h'
    exact add_eq_left.1 h'
  have hbr : M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi = 0 := by
    calc M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi
        = Gi * G * M * Gi + Gi * Mᴴ * (G * Gi) + Gi * Mᴴ * G * M * Gi := by
          rw [hGi1, hGi2]
          noncomm_ring
      _ = Gi * (G * M + Mᴴ * G + Mᴴ * G * M) * Gi := by noncomm_ring
      _ = 0 := by rw [hK]; noncomm_ring
  have key : J * W * (M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi) * Wᴴ * J = 0 := by
    rw [hbr]
    simp
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJ, hGih]
  refine Eq.trans ?_ (add_zero J)
  rw [← key]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hG]
  abel

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {m : ℕ}

def IsUB (blk : Fin m → ℕ) (C : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (∀ i, C i i = 1) ∧ ∀ i j, C i j ≠ 0 → i ≤ j ∧ blk i = blk j

theorem IsUB.zero_of_lt {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) {i j : Fin m} (hij : j < i) :
    C i j = 0 := by
  by_contra hne
  exact absurd hij (not_lt.mpr (h.2 i j hne).1)

theorem IsUB.zero_of_blk {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) {i j : Fin m}
    (hij : blk i ≠ blk j) : C i j = 0 := by
  by_contra hne
  exact hij (h.2 i j hne).2

theorem IsUB.det_eq_one {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) : C.det = 1 := by
  have hup : C.BlockTriangular id := by
    intro i j hij
    exact h.zero_of_lt hij
  rw [Matrix.det_of_upperTriangular hup]
  exact Finset.prod_eq_one fun i _ => h.1 i

theorem IsUB.inv {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) : IsUB blk C⁻¹ := by
  have hup : C.BlockTriangular id := by
    intro i j hij
    exact h.zero_of_lt hij
  have hb1 : C.BlockTriangular blk := by
    intro i j hij
    exact h.zero_of_blk hij.ne'
  have hb2 : C.BlockTriangular (fun i => OrderDual.toDual (blk i)) := by
    intro i j hij
    exact h.zero_of_blk (OrderDual.toDual_lt_toDual.mp hij).ne
  have hdet : IsUnit C.det := by
    rw [h.det_eq_one]
    exact isUnit_one
  letI : Invertible C := C.invertibleOfIsUnitDet hdet
  have iup := Matrix.blockTriangular_inv_of_blockTriangular hup
  have ib1 := Matrix.blockTriangular_inv_of_blockTriangular hb1
  have ib2 := Matrix.blockTriangular_inv_of_blockTriangular hb2
  refine ⟨fun i => ?_, fun i j hij => ⟨?_, ?_⟩⟩
  · have h1 : (C * C⁻¹) i i = 1 := by
      rw [Matrix.mul_nonsing_inv _ hdet, one_apply_eq]
    rw [mul_apply, Finset.sum_eq_single i] at h1
    · rwa [h.1, one_mul] at h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [h.zero_of_lt hlt, zero_mul]
      · rw [iup hlt, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · by_contra hlt
    exact hij (iup (not_le.mp hlt))
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hij (ib2 (OrderDual.toDual_lt_toDual.mpr hlt))
    · exact hij (ib1 hlt)

section Mono

variable (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hZ

theorem Z_ne' (i : Fin m) : Z i (π i) ≠ 0 := (hZ i (π i)).mpr (hπ i).symm

def Zi : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun b c => if b = π c then (Z c b)⁻¹ else 0

theorem Z_mul_Zi : Z * Zi π Z = 1 := by
  ext i k
  simp only [mul_apply, Zi, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, one_apply]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    exact mul_inv_cancel₀ (Z_ne' π hπ Z hZ i)
  · rw [if_neg hik]
    have h0 : Z i (π k) = 0 := by
      by_contra hne
      have h1 := (hZ i (π k)).mp hne
      rw [hπ] at h1
      exact hik h1
    rw [h0, zero_mul]

theorem Z_inv_eq : Z⁻¹ = Zi π Z := Matrix.inv_eq_right_inv (Z_mul_Zi π hπ Z hZ)

theorem isUnit_Z : IsUnit Z.det := Matrix.isUnit_det_of_right_inverse (Z_mul_Zi π hπ Z hZ)

theorem conj_apply (X : Matrix (Fin m) (Fin m) ℂ) (j i : Fin m) :
    (Z * X * Z⁻¹) j i = Z j (π j) * X (π j) (π i) * (Z i (π i))⁻¹ := by
  rw [Z_inv_eq π hπ Z hZ]
  simp only [mul_apply, Zi, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  rw [Finset.sum_eq_single (π j)]
  · intro l _ hl
    have h0 : Z j l = 0 := by
      by_contra hne
      apply hl
      rw [(hZ j l).mp hne, hπ]
    rw [h0, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ _) hj

end Mono

section Pair

variable {blk : Fin m → ℕ} (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a)
  (hanti : ∀ a b, blk a = blk b → a < b → π b < π a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hblk hanti hZ

theorem isUB_A {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUB blk C) : IsUB blk (Z * C⁻¹ * Z⁻¹)ᴴ := by
  have hD := hC.inv
  have hM : ∀ j i, (Z * C⁻¹ * Z⁻¹) j i = Z j (π j) * C⁻¹ (π j) (π i) * (Z i (π i))⁻¹ :=
    fun j i => conj_apply π hπ Z hZ _ j i
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [conjTranspose_apply, hM, hD.1, mul_one, mul_inv_cancel₀ (Z_ne' π hπ Z hZ i),
      star_one]
  · rw [conjTranspose_apply, hM] at hij
    have h1 : C⁻¹ (π j) (π i) ≠ 0 := by
      intro h0
      apply hij
      rw [h0]
      simp
    obtain ⟨hle, hb⟩ := hD.2 _ _ h1
    refine ⟨?_, by simpa [hblk] using hb.symm⟩
    rcases hle.lt_or_eq with hlt | heq
    · have h2 := hanti _ _ hb hlt
      rw [hπ, hπ] at h2
      exact h2.le
    · have h2 := congrArg π heq
      rw [hπ, hπ] at h2
      exact h2.symm.le

theorem A_Z_C {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUB blk C) : (Z * C⁻¹ * Z⁻¹)ᴴᴴ * Z * C = Z := by
  rw [conjTranspose_conjTranspose]
  have hZu := isUnit_Z π hπ Z hZ
  have hCu : IsUnit C.det := by
    rw [hC.det_eq_one]
    exact isUnit_one
  rw [mul_assoc (Z * C⁻¹) Z⁻¹ Z, Matrix.nonsing_inv_mul _ hZu, mul_one, mul_assoc,
    Matrix.nonsing_inv_mul _ hCu, mul_one]

end Pair

theorem gram_last {blk : Fin (m + 1) → ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hA : IsUB blk A)
    (Γ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hΓ : ∀ i j, (i ≠ Fin.last m ∨ j ≠ Fin.last m) → Γ i j = 0) :
    Aᴴ * Γ * A = Γ := by
  have hrow : ∀ j, A (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    by_cases hj : j = Fin.last m
    · rw [if_pos hj, hj]
      exact hA.1 _
    · rw [if_neg hj]
      exact hA.zero_of_lt (lt_of_le_of_ne (Fin.le_last j) hj)
  ext i j
  simp only [mul_apply, conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [Finset.sum_eq_single (Fin.last m)]
    · rw [hrow i, hrow j]
      by_cases hi : i = Fin.last m
      · by_cases hj : j = Fin.last m
        · subst hi
          subst hj
          simp
        · rw [if_neg hj, hΓ i j (Or.inr hj)]
          simp
      · rw [if_neg hi, hΓ i j (Or.inl hi)]
        simp
    · intro k _ hk
      rw [hΓ k (Fin.last m) (Or.inl hk), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro l _ hl
    rw [Finset.sum_eq_zero (fun k _ => by rw [hΓ k l (Or.inr hl), mul_zero]), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {r : ℕ}

def lastDiag (t : ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then t else 0

theorem lastDiag_mulVec (t : ℂ) (α : Fin (r + 1) → ℂ) :
    lastDiag t *ᵥ α = Pi.single (Fin.last r) (t * α (Fin.last r)) := by
  ext i
  by_cases hi : i = Fin.last r
  · subst hi
    simp [lastDiag, Matrix.mulVec, dotProduct]
  · simp [lastDiag, Matrix.mulVec, dotProduct, hi]

theorem gram_isUnit (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0) :
    IsUnit (Matrix.fromBlocks (lastDiag (-(T : ℂ))) Z Zᴴ (lastDiag (-(T' : ℂ)))).det := by
  rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv0, hv⟩
  apply hv0
  have hZi : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hZ
  have hZhi : (Zᴴ)⁻¹ * Zᴴ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hZ.star)
  rw [Matrix.fromBlocks_mulVec] at hv
  have h1 : lastDiag (-(T : ℂ)) *ᵥ (v ∘ Sum.inl) + Z *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inl, Pi.zero_apply] using congrFun hv (Sum.inl i)
  have h2 : Zᴴ *ᵥ (v ∘ Sum.inl) + lastDiag (-(T' : ℂ)) *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inr, Pi.zero_apply] using congrFun hv (Sum.inr i)
  rw [lastDiag_mulVec] at h1 h2
  have h1' : Z *ᵥ (v ∘ Sum.inr) = Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_right h1, ← Pi.single_neg]
    congr 1
    ring
  have h2' : Zᴴ *ᵥ (v ∘ Sum.inl) = Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_left h2, ← Pi.single_neg]
    congr 1
    ring
  have hy : v ∘ Sum.inr = Z⁻¹ *ᵥ Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [← h1', Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
  have hx : v ∘ Sum.inl = (Zᴴ)⁻¹ *ᵥ Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [← h2', Matrix.mulVec_mulVec, hZhi, Matrix.one_mulVec]
  have hsingle : ∀ (N : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : ℂ) (i : Fin (r + 1)),
      (N *ᵥ Pi.single (Fin.last r) c) i = N i (Fin.last r) * c := by
    intro N c i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hinv : (Zᴴ)⁻¹ (Fin.last r) (Fin.last r) = starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) := by
    rw [← Matrix.conjTranspose_nonsing_inv]
    rfl
  have hyl := congrFun hy (Fin.last r)
  have hxl := congrFun hx (Fin.last r)
  rw [hsingle] at hyl hxl
  rw [hinv] at hxl
  have hprod : (v ∘ Sum.inl) (Fin.last r) *
      (1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))))
        = 0 := by
    linear_combination hxl + (starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) * (T' : ℂ)) * hyl
  have hx0 : (v ∘ Sum.inl) (Fin.last r) = 0 := (mul_eq_zero.mp hprod).resolve_right hG
  have hy0 : (v ∘ Sum.inr) (Fin.last r) = 0 := by rw [hyl, hx0]; ring
  rw [hx0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hy
  rw [hy0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hx
  funext s
  cases s with
  | inl i => exact congrFun hx i
  | inr i => exact congrFun hy i

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

section Tri

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem shear_mp (i : ι) (ε : ℂ) (hε : MeasurePreserving (fun x : ℂ => ε * x) volume volume)
    (h : (ι → ℂ) → ℂ) (hm : Measurable h) (hi : ∀ c x, h (Function.update c i x) = h c) :
    MeasurePreserving (fun c : ι → ℂ => Function.update c i (ε * c i + h c)) volume volume := by
  let p : ι → Prop := fun j => j ≠ i
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) p
  have he : MeasurePreserving e (volume : Measure (ι → ℂ))
      ((volume : Measure ({j // p j} → ℂ)).prod (volume : Measure ({j // ¬ p j} → ℂ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure ℂ)) p
  have he2 : ∀ (q : ({j // p j} → ℂ) × ({j // ¬ p j} → ℂ)) x,
      e.symm q x = if hx : p x then q.1 ⟨x, hx⟩ else q.2 ⟨x, hx⟩ := fun q x => rfl
  let h' : ({j // p j} → ℂ) → ℂ := fun y => h (e.symm (y, fun _ => 0))
  have hh'm : Measurable h' := hm.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hh : ∀ c, h c = h' (e c).1 := by
    intro c
    have : e.symm ((e c).1, fun _ => 0) = Function.update c i 0 := by
      funext x
      rw [he2]
      by_cases hx : x = i
      · subst hx; simp [p]
      · rw [dif_pos hx, Function.update_of_ne hx]; rfl
    simp only [h', this, hi]
  let g : ({j // p j} → ℂ) → ({j // ¬ p j} → ℂ) → ({j // ¬ p j} → ℂ) := fun y x j => ε * x j + h' y
  have hS : MeasurePreserving (fun q : ({j // p j} → ℂ) × ({j // ¬ p j} → ℂ) => (id q.1, g q.1 q.2))
      ((volume : Measure ({j // p j} → ℂ)).prod (volume : Measure ({j // ¬ p j} → ℂ)))
      ((volume : Measure ({j // p j} → ℂ)).prod (volume : Measure ({j // ¬ p j} → ℂ))) := by
    refine MeasurePreserving.skew_product (MeasurePreserving.id _) ?_ (ae_of_all _ fun y => ?_)
    · exact measurable_pi_lambda _ fun j =>
        (measurable_const.mul ((measurable_pi_apply j).comp measurable_snd)).add (hh'm.comp measurable_fst)
    · exact (measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure ℂ))
        (fun _ => (measurePreserving_add_right volume (h' y)).comp hε)).map_eq
  have heq : (fun c : ι → ℂ => Function.update c i (ε * c i + h c)) =
      e.symm ∘ (fun q => (id q.1, g q.1 q.2)) ∘ e := by
    funext c x
    simp only [Function.comp_apply]
    rw [he2]
    by_cases hx : x = i
    · subst hx
      rw [dif_neg (by simp [p]), Function.update_self]
      simp only [g]; rw [hh c]; rfl
    · rw [dif_pos hx, Function.update_of_ne hx]
      rfl
  rw [heq]
  exact he.symm.comp (hS.comp he)

theorem tri_mp (ρ : ι → ℕ) (ε : ι → ℂ) (hε : ∀ p, MeasurePreserving (fun x : ℂ => ε p * x) volume volume)
    (g : ι → (ι → ℂ) → ℂ) (hgm : ∀ p, Measurable (g p))
    (hg : ∀ p c c', (∀ q, ρ q < ρ p → c q = c' q) → g p c = g p c') :
    MeasurePreserving (fun c p => ε p * c p + g p c) volume volume := by
  let F : Finset ι → (ι → ℂ) → (ι → ℂ) := fun s c p => if p ∈ s then ε p * c p + g p c else c p
  have key : ∀ s, MeasurePreserving (F s) volume volume := by
    intro s
    induction s using Finset.induction_on_max_value ρ with
    | empty =>
      have : F ∅ = id := by funext c p; simp [F]
      rw [this]; exact MeasurePreserving.id _
    | insert a s has hmax ih =>
      have hT := shear_mp a (ε a) (hε a) (g a) (hgm a) (fun c x => hg a _ _ fun q hq => by
        rw [Function.update_of_ne]; intro h; rw [h] at hq; exact lt_irrefl _ hq)
      have : F (insert a s) = F s ∘ fun c => Function.update c a (ε a * c a + g a c) := by
        funext c p
        simp only [F, Function.comp_apply, Finset.mem_insert]
        by_cases hp : p = a
        · subst hp; simp [has]
        · rw [Function.update_of_ne hp]
          by_cases hs : p ∈ s
          · rw [if_pos (Or.inr hs), if_pos hs]
            congr 1
            refine hg p _ _ fun q hq => ?_
            rw [Function.update_of_ne]
            intro hqa; rw [hqa] at hq; exact absurd (hmax p hs) (not_le.2 hq)
          · rw [if_neg (by simp [hp, hs]), if_neg hs]
      rw [this]; exact ih.comp hT
  have : (fun c p => ε p * c p + g p c) = F Finset.univ := by funext c p; simp [F]
  rw [this]; exact key _

theorem tri_mp' (ρ : ι → ℕ) (ε : ι → ℂ) (hε : ∀ p, MeasurePreserving (fun x : ℂ => ε p * x) volume volume)
    (f : (ι → ℂ) → (ι → ℂ)) (hfm : Measurable f) (G : ι → (ι → ℂ) → (ι → ℂ) → ℂ)
    (hf : ∀ c p, f c p = ε p * c p + G p c (f c))
    (hG : ∀ p c d c' d', (∀ q, ρ q < ρ p → c q = c' q ∧ d q = d' q) → G p c d = G p c' d') :
    MeasurePreserving f volume volume := by
  have low : ∀ L c c', (∀ q, ρ q < L → c q = c' q) → ∀ q, ρ q < L → f c q = f c' q := by
    intro L
    induction L using Nat.strong_induction_on with
    | _ L ih =>
      intro c c' hc q hq
      rw [hf c q, hf c' q, hc q hq]
      congr 1
      refine hG q _ _ _ _ fun q' hq' => ⟨hc q' (by omega), ?_⟩
      exact ih (ρ q) hq c c' (fun q'' h'' => hc q'' (by omega)) q' hq'
  have hfg : f = fun c p => ε p * c p + (f c p - ε p * c p) := by funext c p; ring
  rw [hfg]
  refine tri_mp ρ ε hε (fun p c => f c p - ε p * c p)
    (fun p => ((measurable_pi_apply p).comp hfm).sub (measurable_const.mul (measurable_pi_apply p))) ?_
  intro p c c' hc
  have e1 : f c p - ε p * c p = G p c (f c) := by rw [hf c p]; ring
  have e2 : f c' p - ε p * c' p = G p c' (f c') := by rw [hf c' p]; ring
  simp only [e1, e2]
  exact hG p _ _ _ _ fun q hq => ⟨hc q hq, low (ρ p) c c' hc q hq⟩

end Tri

variable {D : D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def extC (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) (a b : Fin (D.R.rS + 1)) : ℂ :=
  if h : a < b ∧ blkOf w.1 a.1 = blkOf w.1 b.1 then c ⟨(a, b), h⟩ else 0

def coordMul (w : Point D.host.E (D.R.rS + 1)) (c d : FreeE w → ℂ) : FreeE w → ℂ :=
  fun p => c p + d p + ∑ m, extC w c p.1.1 m * extC w d m p.1.2

def gapE (w : Point D.host.E (D.R.rS + 1)) (p : FreeE w) : ℕ := p.1.2.val - p.1.1.val

theorem extC_measurable (w : Point D.host.E (D.R.rS + 1)) (a b : Fin (D.R.rS + 1)) :
    Measurable fun c : FreeE w → ℂ => extC w c a b := by
  unfold extC
  by_cases h : a < b ∧ blkOf w.1 a.1 = blkOf w.1 b.1
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const

theorem extC_of_not_lt (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) (a b : Fin (D.R.rS + 1)) (h : ¬ a < b) :
    extC w c a b = 0 := by
  unfold extC
  rw [dif_neg (fun h' => h h'.1)]

theorem extC_congr (w : Point D.host.E (D.R.rS + 1)) (c c' : FreeE w → ℂ) (a b : Fin (D.R.rS + 1)) (L : ℕ)
    (hL : b.val - a.val < L) (hc : ∀ q, gapE w q < L → c q = c' q) : extC w c a b = extC w c' a b := by
  unfold extC
  split_ifs with h
  · exact hc ⟨(a, b), h⟩ hL
  · rfl

theorem nV_one (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ NV X u v := by
  show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)))
  have : uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) = 1 := by simp [uMat]
  rw [this]; exact ⟨Formalism.L2.SG.Pf.inFl_one _, fun y _ => by simp⟩

theorem nV_mul (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (s t : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ NV X u v) (ht : t ∈ NV X u v) : s * t ∈ NV X u v := by
  show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (s * t))
  have : uMat (s * t) = uMat s * uMat t := by simp [uMat]
  rw [this]
  exact ⟨Formalism.L2.SG.Pf.inFl_mul hs.1 ht.1,
    fun y hy => Formalism.L2.SG.Pf.fl_mul (Formalism.L2.SG.Pf.fl_map_le hs.1.1 D.R.rS) (hs.2 y hy) (ht.2 y hy)⟩

theorem nV_inv (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (s : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ NV X u v) : s⁻¹ ∈ NV X u v := by
  show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat s⁻¹)
  have : uMat s⁻¹ * uMat s = 1 := by simp [uMat]
  exact ⟨Formalism.L2.SG.Pf.inFl_inv this hs.1,
    fun y hy => Formalism.L2.SG.Pf.fl_inv this (Formalism.L2.SG.Pf.fl_le_map hs.1.1 D.R.rS) (hs.2 y hy)⟩

theorem stV_one (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ StV X u u' γ v := by
  refine ⟨nV_one X u v, ?_⟩
  simp only [mul_one, inv_mul_cancel]
  exact nV_one X u' v

theorem stV_mul (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F)
    (s t : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ StV X u u' γ v) (ht : t ∈ StV X u u' γ v) :
    s * t ∈ StV X u u' γ v := by
  refine ⟨nV_mul X u v s t hs.1 ht.1, ?_⟩
  have e : (γ v)⁻¹ * (s * t) * γ v = ((γ v)⁻¹ * s * γ v) * ((γ v)⁻¹ * t * γ v) := by group
  rw [e]
  exact nV_mul X u' v _ _ hs.2 ht.2

theorem stV_inv (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F)
    (s : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ StV X u u' γ v) : s⁻¹ ∈ StV X u u' γ v := by
  refine ⟨nV_inv X u v s hs.1, ?_⟩
  have e : (γ v)⁻¹ * s⁻¹ * γ v = ((γ v)⁻¹ * s * γ v)⁻¹ := by group
  rw [e]
  exact nV_inv X u' v _ hs.2

theorem hJ_smul_r {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) (c : ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (c • y) = c * Formalism.L2.SG.HidaSetting.hJ ε x y := by
  simp [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem stCoordV_one (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) : stCoordV X u' w γ v 1 = 0 := by
  funext p
  rcases p with ⟨⟨a, b⟩, hab, hbl⟩
  simp only [stCoordV, mul_one, inv_mul_cancel]
  have h1 : uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) = 1 := by simp [uMat]
  rw [h1, Matrix.one_mulVec]
  apply mul_eq_zero_of_right
  simp only [frm, famSc]
  rw [hJ_smul_r]
  apply mul_eq_zero_of_right
  induction b using Fin.lastCases with
  | last =>
    rw [fam_last, Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hermitian_f_z_zero, map_zero]
  | cast b' =>
    rw [fam_castSucc, Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hE_f_e, if_neg, map_zero]
    intro h
    have h2 := congrArg Fin.val h
    simp only at h2
    rw [Fin.lt_def] at hab
    simp at hab
    omega

def StVLaw (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F,
    ∀ y ∈ StV X u u' (gamW X u u' w) v, ∀ y' ∈ StV X u u' (gamW X u u' w) v,
      stCoordV X u' w (gamW X u u' w) v (y * y') =
        coordMul w (stCoordV X u' w (gamW X u u' w) v y) (stCoordV X u' w (gamW X u u' w) v y')

section LawLoc

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_T_e (e f : Fin r → Fin n → ℂ) (z' : Fin n → ℂ)
    (hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ ε (f a) (e b) = if b = a then 1 else 0)
    (hfz' : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) z' = 0) (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : Formalism.L2.SG.HidaSetting.InS e z' T) (a c : Fin r) :
    Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ e c) = (if c = a then 1 else 0) +
      (if a.castSucc < c.castSucc then Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ e c) else 0) := by
  have h := flag_expand ε e f z' hfe hfz' T hT c.castSucc
  rw [fam_castSucc] at h
  have h2 := congrArg (Formalism.L2.SG.HidaSetting.hJ ε (f a)) h
  rw [hJ_add_r', hJ_sum_r', hfe] at h2
  rw [Finset.sum_eq_single a] at h2
  · rw [hfe, if_pos rfl, mul_one] at h2
    exact h2
  · intro d _ hda; rw [hfe, if_neg hda, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem flag_mul_coef (e f : Fin r → Fin n → ℂ) (z' : Fin n → ℂ)
    (hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ ε (f a) (e b) = if b = a then 1 else 0)
    (hfz' : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) z' = 0) (T T' : Matrix (Fin n) (Fin n) ℂ)
    (hT : Formalism.L2.SG.HidaSetting.InS e z' T) (hT' : Formalism.L2.SG.HidaSetting.InS e z' T') (a : Fin r) (b : Fin (r + 1))
    (hab : a.castSucc < b) :
    Formalism.L2.SG.HidaSetting.hJ ε (f a) ((T * T') *ᵥ fam e z' b) =
      Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ fam e z' b) + Formalism.L2.SG.HidaSetting.hJ ε (f a) (T' *ᵥ fam e z' b) +
      ∑ c : Fin r, if a.castSucc < c.castSucc ∧ c.castSucc < b then
        Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ e c) * Formalism.L2.SG.HidaSetting.hJ ε (f c) (T' *ᵥ fam e z' b) else 0 := by
  have h := flag_expand ε e f z' hfe hfz' T' hT' b
  have h1 := congrArg (fun x => T *ᵥ x) h
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul] at h1
  rw [← Matrix.mulVec_mulVec, h1, hJ_add_r', hJ_sum_r', add_assoc]
  congr 1
  have hterm : ∀ c : Fin r, (if c.castSucc < b then Formalism.L2.SG.HidaSetting.hJ ε (f c) (T' *ᵥ fam e z' b) else 0) *
      Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ e c) =
      (if c = a then Formalism.L2.SG.HidaSetting.hJ ε (f a) (T' *ᵥ fam e z' b) else 0) +
      (if a.castSucc < c.castSucc ∧ c.castSucc < b then
        Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ e c) * Formalism.L2.SG.HidaSetting.hJ ε (f c) (T' *ᵥ fam e z' b) else 0) := by
    intro c
    have hc := hJ_T_e ε e f z' hfe hfz' T hT a c
    by_cases hca : c = a
    · subst hca
      rw [if_neg (lt_irrefl _), add_zero, if_pos rfl] at hc
      rw [if_pos hab, hc, if_pos rfl, if_neg (fun h => lt_irrefl _ h.1)]; ring
    · rw [if_neg hca, zero_add] at hc
      rw [if_neg hca, zero_add]
      by_cases hac : a.castSucc < c.castSucc
      · by_cases hcb : c.castSucc < b
        · rw [if_pos hcb, if_pos ⟨hac, hcb⟩]; ring
        · rw [if_neg hcb, if_neg (fun h => hcb h.2), zero_mul]
      · rw [if_neg hac] at hc
        rw [hc, mul_zero, if_neg (fun h => hac h.1)]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end LawLoc

theorem blkOf_mono {K : Type*} : ∀ (bs : List (K × ℕ)) (i j : ℕ), i ≤ j → blkOf bs i ≤ blkOf bs j
  | [], _, _, _ => by simp [blkOf]
  | (t, s) :: bs, i, j, h => by
    simp only [blkOf]
    split_ifs with h1 h2 h2
    · exact le_refl _
    · omega
    · omega
    · have := blkOf_mono bs (i - s) (j - s) (by omega); omega

theorem rdE_pos_c : (0 : ℝ) < D.host.rdE :=
  Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))) _

theorem stCoordV_apply (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (y : Formalism.REAL.UJ (X.B.I.ε v)) (p : FreeE w) :
    stCoordV X u' w γ v y p = ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) * ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.1))⁻¹) *
      Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR ⟨p.1.1.1, by have := p.2.1; omega⟩))
        (uMat ((γ v)⁻¹ * y * γ v) *ᵥ
          fam (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) p.1.2) := by
  simp only [stCoordV, frm, famSc, Matrix.mulVec_smul, hJ_smul_r]
  ring

theorem stVLaw_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StVLaw X u u' := by
  classical
  intro w _ v y hy y' hy'
  set γ := gamW X u u' w
  set e : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)
  set f : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a)
  set z' := Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')
  have hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (f a) (e b) = if b = a then 1 else 0 := by
    intro a b
    rw [Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hE_f_e]
    split_ifs <;> simp
  have hfz' : ∀ a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (f a) z' = 0 := by
    intro a
    rw [Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hermitian_f_z_zero, map_zero]
  have hT : Formalism.L2.SG.HidaSetting.InS e z' (uMat ((γ v)⁻¹ * y * γ v)) := hy.2.1
  have hT' : Formalism.L2.SG.HidaSetting.InS e z' (uMat ((γ v)⁻¹ * y' * γ v)) := hy'.2.1
  have hprod : uMat ((γ v)⁻¹ * (y * y') * γ v) = uMat ((γ v)⁻¹ * y * γ v) * uMat ((γ v)⁻¹ * y' * γ v) := by
    have e1 : (γ v)⁻¹ * (y * y') * γ v = ((γ v)⁻¹ * y * γ v) * ((γ v)⁻¹ * y' * γ v) := by group
    rw [e1]; simp [uMat]
  have hx : (D.host.rdE : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (rdE_pos_c (D := D)).ne'
  let S : ℕ → ℕ → ℂ := fun a b => (D.host.rdE : ℂ) ^ (D.R.rS - a) * ((D.host.rdE : ℂ) ^ (D.R.rS - b))⁻¹
  have hS : ∀ a c b, S a c * S c b = S a b := by
    intro a c b
    simp only [S]
    rw [mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hx)]
  funext p
  have hab : p.1.1 < p.1.2 := p.2.1
  have hbl : blkOf w.1 p.1.1.1 = blkOf w.1 p.1.2.1 := p.2.2
  obtain ⟨a', ha'⟩ : ∃ a' : Fin D.R.rS, a'.castSucc = p.1.1 :=
    ⟨⟨p.1.1.val, by have h : p.1.1.val < p.1.2.val := hab; have := p.1.2.2; omega⟩, Fin.ext rfl⟩
  have hfa : (⟨p.1.1.1, by have h : p.1.1.val < p.1.2.val := hab; have := p.1.2.2; omega⟩ : Fin D.R.rS) = a' :=
    Fin.ext (congrArg Fin.val ha').symm
  simp only [coordMul]
  rw [stCoordV_apply X u' w γ v (y * y'), stCoordV_apply X u' w γ v y, stCoordV_apply X u' w γ v y', hprod]
  simp only [hfa]
  have hF := flag_mul_coef (X.B.I.ε v) e f z' hfe hfz' _ _ hT hT' a' p.1.2 (by rw [ha']; exact hab)
  rw [ha'] at hF
  rw [hF, Fin.sum_univ_castSucc, extC_of_not_lt w _ (Fin.last _) p.1.2 (fun h => absurd (Fin.le_last _) (not_le.2 h)),
    mul_zero, add_zero, mul_add, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : p.1.1 < c.castSucc ∧ c.castSucc < p.1.2
  · rw [if_pos hc]
    have hb1 : blkOf w.1 p.1.1.1 = blkOf w.1 c.castSucc.1 := by
      have h1 := blkOf_mono w.1 p.1.1.1 c.castSucc.1 (le_of_lt hc.1)
      have h2 := blkOf_mono w.1 c.castSucc.1 p.1.2.1 (le_of_lt hc.2)
      omega
    have hb2 : blkOf w.1 c.castSucc.1 = blkOf w.1 p.1.2.1 := by rw [← hb1]; exact hbl
    have hfc : (⟨c.castSucc.val, by have h : c.castSucc.val < p.1.2.val := hc.2; have := p.1.2.2; omega⟩ : Fin D.R.rS) = c :=
      Fin.ext rfl
    unfold extC
    rw [dif_pos ⟨hc.1, hb1⟩, dif_pos ⟨hc.2, hb2⟩]
    refine Eq.trans ?_ (congrArg₂ (· * ·) (stCoordV_apply X u' w γ v y _).symm (stCoordV_apply X u' w γ v y' _).symm)
    dsimp only
    simp only [hfa, hfc, fam_castSucc]
    have h3 := hS p.1.1.1 c.castSucc.1 p.1.2.1
    simp only [S] at h3
    rw [← h3]
    simp only [e, f, z']
    ring
  · rw [if_neg hc, mul_zero]
    by_cases hac : p.1.1 < c.castSucc
    · have hcb : ¬ c.castSucc < p.1.2 := fun h => hc ⟨hac, h⟩
      rw [extC_of_not_lt w _ _ _ hcb, mul_zero]
    · rw [extC_of_not_lt w _ _ _ hac, zero_mul]

def StVChart (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F,
    ∃ φ : (FreeE w → ℂ) → Formalism.REAL.UJ (X.B.I.ε v), Continuous φ ∧
      (∀ c, φ c ∈ StV X u u' (gamW X u u' w) v) ∧
      (∀ y ∈ StV X u u' (gamW X u u' w) v, φ (stCoordV X u' w (gamW X u u' w) v y) = y) ∧
      (∀ c, stCoordV X u' w (gamW X u u' w) v (φ c) = c)

theorem mp_one_mul : MeasurePreserving (fun x : ℂ => (1 : ℂ) * x) volume volume := by
  have e : (fun x : ℂ => (1 : ℂ) * x) = id := funext fun x => one_mul x
  rw [e]
  exact MeasurePreserving.id _

theorem mp_neg_one_mul : MeasurePreserving (fun x : ℂ => (-1 : ℂ) * x) volume volume := by
  have e : (fun x : ℂ => (-1 : ℂ) * x) = fun x => -x := funext fun x => by ring
  rw [e]
  exact Measure.measurePreserving_neg volume

theorem stVGeo_of (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hC : StVChart X u u')
    (hLw : StVLaw X u u') : StVGeo X u u' := by
  classical
  intro w hw v
  obtain ⟨φ, hφ, hφS, hφκ, hκφ⟩ := hC w hw v
  have law := hLw w hw v
  set γ := gamW X u u' w with hγ
  set κ := stCoordV X u' w γ v with hκ
  refine ⟨⟨stV_one X u u' γ v, fun s hs t ht => stV_mul X u u' γ v s t hs ht,
    fun s hs => stV_inv X u u' γ v s hs⟩, φ, hφ, hφS, hφκ, hκφ, ?_, ?_⟩
  ·
    intro s hs
    have e1 : (fun c => κ (s * φ c)) = fun c p => (1 : ℂ) * c p +
        (κ s p + ∑ m, extC w (κ s) p.1.1 m * extC w c m p.1.2) := by
      funext c p
      rw [law s hs (φ c) (hφS c), hκφ c, coordMul]
      ring
    rw [e1]
    refine tri_mp (gapE w) (fun _ => 1) (fun _ => mp_one_mul) _ (fun p => measurable_const.add
      (Finset.measurable_sum _ fun m _ => measurable_const.mul (extC_measurable w m p.1.2))) ?_
    intro p c c' hc
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases ham : p.1.1 < m
    · rw [extC_congr w c c' m p.1.2 (gapE w p) ?_ hc]
      have := p.2.1
      rw [Fin.lt_def] at ham this
      simp only [gapE]
      omega
    · rw [extC_of_not_lt w _ _ _ ham, zero_mul, zero_mul]
  ·
    have hκ1 : κ 1 = 0 := stCoordV_one X u' w γ v
    refine tri_mp' (gapE w) (fun _ => -1) (fun _ => mp_neg_one_mul) (fun c => κ (φ c)⁻¹)
      ((stCoordV_continuous X u' w γ v).comp hφ.inv).measurable
      (fun p c d => - ∑ m, extC w d p.1.1 m * extC w c m p.1.2) ?_ ?_
    · intro c p
      have h := law (φ c)⁻¹ (stV_inv X u u' γ v _ (hφS c)) (φ c) (hφS c)
      rw [inv_mul_cancel, hκ1, hκφ c] at h
      have hp := congrFun h p
      simp only [coordMul, Pi.zero_apply] at hp
      linear_combination -hp
    · intro p c d c' d' hcd
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      have hp := p.2.1
      rw [Fin.lt_def] at hp
      by_cases ham : p.1.1 < m
      · by_cases hmb : m < p.1.2
        · rw [Fin.lt_def] at ham hmb
          rw [extC_congr w d d' p.1.1 m (gapE w p) (by simp only [gapE]; omega) (fun q hq => (hcd q hq).2),
            extC_congr w c c' m p.1.2 (gapE w p) (by simp only [gapE]; omega) (fun q hq => (hcd q hq).1)]
        · rw [extC_of_not_lt w c m p.1.2 hmb, extC_of_not_lt w c' m p.1.2 hmb, mul_zero, mul_zero]
      · rw [extC_of_not_lt w d _ _ ham, extC_of_not_lt w d' _ _ ham, zero_mul, zero_mul]

theorem stVGeo_of_chart (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hC : StVChart X u u') :
    StVGeo X u u' := stVGeo_of X u u' hC (stVLaw_holds X u u')


def StVKer (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F, ∀ y ∈ StV X u u' (gamW X u u' w) v,
    stCoordV X u' w (gamW X u u' w) v y = 0 → y = 1

def StVSec (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F,
    ∃ φ : (FreeE w → ℂ) → Formalism.REAL.UJ (X.B.I.ε v), Continuous φ ∧
      (∀ c, φ c ∈ StV X u u' (gamW X u u' w) v) ∧ (∀ c, stCoordV X u' w (gamW X u u' w) v (φ c) = c)

theorem stVChart_of (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hK : StVKer X u u')
    (hS : StVSec X u u') : StVChart X u u' := by
  intro w hw v
  obtain ⟨φ, hφ, hφS, hκφ⟩ := hS w hw v
  refine ⟨φ, hφ, hφS, fun y hy => ?_, hκφ⟩
  have law := stVLaw_holds X u u' w hw v
  have hinj : ∀ y ∈ StV X u u' (gamW X u u' w) v, ∀ y' ∈ StV X u u' (gamW X u u' w) v,
      stCoordV X u' w (gamW X u u' w) v y = stCoordV X u' w (gamW X u u' w) v y' → y = y' := by
    intro y hy y' hy' he
    have hi := stV_inv X u u' (gamW X u u' w) v y' hy'
    have h1 := law y'⁻¹ hi y hy
    have h2 := law y'⁻¹ hi y' hy'
    rw [inv_mul_cancel, stCoordV_one, ← he] at h2
    rw [← h2] at h1
    have := hK w hw v (y'⁻¹ * y) (stV_mul X u u' _ v _ _ hi hy) h1
    rw [inv_mul_eq_one] at this
    exact this.symm
  exact hinj _ (hφS _) y hy (hκφ _)

theorem stVGeo_of_ker_sec (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hK : StVKer X u u')
    (hS : StVSec X u u') : StVGeo X u u' := stVGeo_of_chart X u u' (stVChart_of X u u' hK hS)

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

variable {D : D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem blkOf_ptPar {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (x : ℕ), x < (bs.map Prod.snd).sum →
    blkOf bs (ptPar bs x) = blkOf bs x
  | [], x, hx => by simp at hx
  | (t, s) :: bs, x, hx => by
    simp only [List.map_cons, List.sum_cons] at hx
    rw [ptPar_cons]
    by_cases hxs : x < s
    · rw [if_pos hxs]; simp only [blkOf]; rw [if_pos (by omega), if_pos hxs]
    · rw [if_neg hxs]; simp only [blkOf]
      rw [if_neg (by omega), if_neg hxs, show s + ptPar bs (x - s) - s = ptPar bs (x - s) by omega,
        blkOf_ptPar bs (x - s) (by omega)]

theorem ptPar_lt_of_blk {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (x y : ℕ), x < (bs.map Prod.snd).sum →
    y < (bs.map Prod.snd).sum → blkOf bs x < blkOf bs y → ptPar bs x < ptPar bs y
  | [], x, _, hx, _, _ => by simp at hx
  | (t, s) :: bs, x, y, hx, hy, h => by
    simp only [List.map_cons, List.sum_cons] at hx hy
    simp only [blkOf] at h
    rw [ptPar_cons, ptPar_cons]
    by_cases hxs : x < s
    · by_cases hys : y < s
      · rw [if_pos hxs, if_pos hys] at h; omega
      · rw [if_pos hxs, if_neg hys]; omega
    · by_cases hys : y < s
      · rw [if_neg hxs, if_pos hys] at h; omega
      · rw [if_neg hxs, if_neg hys] at h ⊢
        have := ptPar_lt_of_blk bs (x - s) (y - s) (by omega) (by omega) (by omega)
        omega

def StVFix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F, ∀ y ∈ StV X u u' (gamW X u u' w) v,
    (∀ a, uMat y *ᵥ fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) a =
      fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) a) →
    (∀ b, uMat y *ᵥ (uMat (gamW X u u' w v) *ᵥ
        fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) b) =
      uMat (gamW X u u' w v) *ᵥ
        fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) b) →
    y = 1

private theorem flag_fix_lemma {n r : ℕ} (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ ε (f a) (e b) = if b = a then 1 else 0)
    (hfz : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) z = 0) (hfz' : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) z' = 0)
    (S Si G T : Matrix (Fin n) (Fin n) ℂ) (hSi : Formalism.L2.SG.HidaSetting.InS e z Si)
    (hT : Formalism.L2.SG.HidaSetting.InS e z' T)
    (hadj : ∀ x y, Formalism.L2.SG.HidaSetting.hJ ε x (S *ᵥ y) = Formalism.L2.SG.HidaSetting.hJ ε (Si *ᵥ x) y)
    (hrel : S * G = G * T) (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hZ : ∀ c b, Zhat ε (fam e z) (fam e z') G c b ≠ 0 ↔ c = π b)
    (hfree : ∀ (c : Fin r) (b : Fin (r + 1)), c.castSucc < b →
      π c.castSucc < π b ∨ Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) = 0) :
    (∀ b, T *ᵥ fam e z' b = fam e z' b) ∧ (∀ a, Si *ᵥ fam e z a = fam e z a) := by
  have hA := relA_loc ε e f z z' hfe hfz hfz' S Si G T hSi hT hadj hrel
  have hTc : ∀ (c : Fin r) (b : Fin (r + 1)), c.castSucc < b →
      Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) = 0 := by
    intro c b hcb
    rcases hfree c b hcb with hlt | h0
    · have h := hA (π c.castSucc) b
      have hL : (∑ c' : Fin r, if c'.castSucc < π c.castSucc then
          conj (Formalism.L2.SG.HidaSetting.hJ ε (f c') (Si *ᵥ fam e z (π c.castSucc))) * Zhat ε (fam e z) (fam e z') G c'.castSucc b
          else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro c' _
        split_ifs with h1
        · have hz : Zhat ε (fam e z) (fam e z') G c'.castSucc b = 0 := by
            by_contra hne
            rw [(hZ _ _).1 hne] at h1
            exact lt_irrefl _ (lt_trans h1 hlt)
          rw [hz, mul_zero]
        · rfl
      have hR : (∑ c' : Fin r, if c'.castSucc < b then
          Formalism.L2.SG.HidaSetting.hJ ε (f c') (T *ᵥ fam e z' b) * Zhat ε (fam e z) (fam e z') G (π c.castSucc) c'.castSucc else 0) =
          Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) * Zhat ε (fam e z) (fam e z') G (π c.castSucc) c.castSucc := by
        rw [Finset.sum_eq_single c]
        · rw [if_pos hcb]
        · intro c' _ hc'
          split_ifs
          · have hz : Zhat ε (fam e z) (fam e z') G (π c.castSucc) c'.castSucc = 0 := by
              by_contra hne
              have h2 := (hZ _ _).1 hne
              have h3 : c.castSucc = c'.castSucc := by rw [← hπ c.castSucc, h2, hπ]
              exact hc' (Fin.castSucc_injective _ h3).symm
            rw [hz, mul_zero]
          · rfl
        · intro h; exact absurd (Finset.mem_univ c) h
      rw [hL, hR] at h
      exact (mul_eq_zero.1 h.symm).resolve_right ((hZ _ _).2 rfl)
    · exact h0
  have hSc : ∀ (c : Fin r) (a : Fin (r + 1)), c.castSucc < a →
      Formalism.L2.SG.HidaSetting.hJ ε (f c) (Si *ᵥ fam e z a) = 0 := by
    intro c a hca
    have h := hA a (π c.castSucc)
    have hR : (∑ c' : Fin r, if c'.castSucc < π c.castSucc then
        Formalism.L2.SG.HidaSetting.hJ ε (f c') (T *ᵥ fam e z' (π c.castSucc)) * Zhat ε (fam e z) (fam e z') G a c'.castSucc else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro c' _
      split_ifs with h1
      · rw [hTc c' _ h1, zero_mul]
      · rfl
    have hL : (∑ c' : Fin r, if c'.castSucc < a then
        conj (Formalism.L2.SG.HidaSetting.hJ ε (f c') (Si *ᵥ fam e z a)) * Zhat ε (fam e z) (fam e z') G c'.castSucc (π c.castSucc) else 0) =
        conj (Formalism.L2.SG.HidaSetting.hJ ε (f c) (Si *ᵥ fam e z a)) * Zhat ε (fam e z) (fam e z') G c.castSucc (π c.castSucc) := by
      rw [Finset.sum_eq_single c]
      · rw [if_pos hca]
      · intro c' _ hc'
        split_ifs
        · have hz : Zhat ε (fam e z) (fam e z') G c'.castSucc (π c.castSucc) = 0 := by
            by_contra hne
            have h2 := (hZ _ _).1 hne
            rw [hπ] at h2
            exact hc' (Fin.castSucc_injective _ h2)
          rw [hz, mul_zero]
        · rfl
      · intro h; exact absurd (Finset.mem_univ c) h
    rw [hL, hR] at h
    have h4 := (mul_eq_zero.1 h).resolve_right ((hZ _ _).2 (hπ _).symm)
    simpa using h4
  refine ⟨fun b => ?_, fun a => ?_⟩
  · rw [flag_expand ε e f z' hfe hfz' T hT b]
    conv_rhs => rw [← add_zero (fam e z' b)]
    congr 1
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with h1
    · rw [hTc c b h1, zero_smul]
    · rw [zero_smul]
  · rw [flag_expand ε e f z hfe hfz Si hSi a]
    conv_rhs => rw [← add_zero (fam e z a)]
    congr 1
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with h1
    · rw [hSc c a h1, zero_smul]
    · rw [zero_smul]

theorem stVKer_of_fix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hFx : StVFix X u u') :
    StVKer X u u' := by
  intro w hw v y hy h0
  have hγ : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dif_pos hw.1]
    exact hw.1.choose_spec
  have hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR b)) = if b = a then 1 else 0 := by
    intro a b
    change Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.fY a)))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.eX b))) = _
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v (X.fY a) (X.eX b), Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X a b]
    split_ifs <;> simp
  have hfz : ∀ (u₀ : D.what₂.Word) a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v)
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u₀)) = 0 := by
    intro u₀ a
    change Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.fY a)))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.zu u₀))) = 0
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v (X.fY a) (X.zu u₀), (X.zu_orth u₀ a).2, map_zero]
  have hy' := hy
  obtain ⟨hyN, hyN'⟩ := hy'
  have hSi : Formalism.L2.SG.HidaSetting.InS (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) (uMat y⁻¹) := by
    obtain ⟨h1, _⟩ := nV_inv X u v y hyN
    exact h1
  have hT : Formalism.L2.SG.HidaSetting.InS (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v)) := by
    obtain ⟨h1, _⟩ := hyN'
    exact h1
  have hrel : uMat y * uMat (gamW X u u' w v) =
      uMat (gamW X u u' w v) * uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) := by
    rw [← Formalism.L2.SG.PoincareInHH.Cut.uMat_mul, ← Formalism.L2.SG.PoincareInHH.Cut.uMat_mul]
    congr 1
    group
  have hlen : ∀ b : Fin (D.R.rS + 1), b.1 < (w.1.map Prod.snd).sum := fun b => by
    rw [w.2.2]; exact b.2
  let π : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
    ⟨ptPar w.1 b.1, by have h := ptPar_lt w.1 b.1 (hlen b); rwa [w.2.2] at h⟩
  have hπ : ∀ a, π (π a) = a := fun a => Fin.ext (ptPar_invol w.1 a.1 (hlen a))
  have hZ : ∀ c b, Zhat (X.B.I.ε v) (fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u))) (fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u'))) (uMat (gamW X u u' w v)) c b ≠ 0 ↔ c = π b := by
    intro c b
    have h1 := congrFun (congrFun (hγ v) c) b
    simp only [RealObj.ZhatO, ZX, frm, famSc_one, ptC, Matrix.map_apply, ptMat] at h1
    rw [ptEntry_eq w.1 c.1 b.1 (hlen b)] at h1
    have hsgn : ((-1 : ℂ) ^ (D.R.rS - b.1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    constructor
    · intro hne
      by_contra hcb
      have hv : c.1 ≠ ptPar w.1 b.1 := fun h => hcb (Fin.ext h)
      rw [if_neg hv, map_zero, map_zero] at h1
      exact hne ((mul_eq_zero.1 h1).resolve_left hsgn)
    · intro hcb hz
      have hv : c.1 = ptPar w.1 b.1 := congrArg Fin.val hcb
      rw [if_pos hv, hz, mul_zero] at h1
      exact ptSc_ne w.1 (fun x hx => w.2.1 x hx) b.1 (hlen b) (by simpa using h1.symm)
  have hfree : ∀ (c : Fin D.R.rS) (b : Fin (D.R.rS + 1)), c.castSucc < b →
      π c.castSucc < π b ∨ Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR c))
        (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) *ᵥ
          fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) b) = 0 := by
    intro c b hcb
    by_cases hbl : blkOf w.1 c.castSucc.1 = blkOf w.1 b.1
    · right
      have hp := congrFun h0 ⟨(c.castSucc, b), hcb, hbl⟩
      simp only [stCoordV, frm, famSc, Matrix.mulVec_smul, hJ_smul_r, Fin.val_castSucc,
        Fin.eta] at hp
      have hrd : (D.host.rdE : ℂ) ≠ 0 := by exact_mod_cast (rdE_pos_c (D := D)).ne'
      rcases mul_eq_zero.1 hp with h | h
      · exact absurd h (pow_ne_zero _ hrd)
      · rcases mul_eq_zero.1 h with h' | h'
        · exact absurd h' (inv_ne_zero (pow_ne_zero _ hrd))
        · exact h'
    · left
      have hle : blkOf w.1 c.castSucc.1 ≤ blkOf w.1 b.1 := blkOf_mono w.1 _ _ (le_of_lt hcb)
      exact ptPar_lt_of_blk w.1 _ _ (hlen _) (hlen _) (lt_of_le_of_ne hle hbl)
  obtain ⟨hTfix, hSfix⟩ := flag_fix_lemma (X.B.I.ε v) (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
    (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u))
    (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) hfe (hfz u) (hfz u') (uMat y) (uMat y⁻¹)
    (uMat (gamW X u u' w v)) (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v)) hSi hT
    (fun x x' => Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj y x x') hrel π hπ hZ hfree
  have hyy : uMat y * uMat y⁻¹ = 1 := by
    have h := Formalism.L2.SG.PoincareInHH.Cut.uMat_inv_mul y⁻¹
    rwa [inv_inv] at h
  refine hFx w hw v y hy (fun a => ?_) (fun b => ?_)
  · rw [← hSfix a, Matrix.mulVec_mulVec, hyy, Matrix.one_mulVec, hSfix a]
  · rw [Matrix.mulVec_mulVec, hrel, ← Matrix.mulVec_mulVec, hTfix b]

theorem stVGeo_of_fix_sec (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hFx : StVFix X u u')
    (hS : StVSec X u u') : StVGeo X u u' :=
  stVGeo_of_ker_sec X u u' (stVKer_of_fix X u u' hFx) hS

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

section FixLoc

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_sub_r' (x a b : Fin n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (a - b) = Formalism.L2.SG.HidaSetting.hJ ε x a - Formalism.L2.SG.HidaSetting.hJ ε x b := by
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_sub, dotProduct_sub]

theorem mem_spanLt_r (e : Fin r → Fin n → ℂ) (x : Fin n → ℂ) (hx : x ∈ Formalism.L2.SG.HidaSetting.spanLt e r) :
    ∃ α : Fin r → ℂ, ∑ a, α a • e a = x := by
  have hset : e '' {b : Fin r | b.1 < r} = Set.range e := by
    rw [← Set.image_univ]
    congr 1
    ext b
    simp [b.isLt]
  unfold Formalism.L2.SG.HidaSetting.spanLt at hx
  rw [hset] at hx
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx

theorem fix_loc (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (G Gi Y T : Matrix (Fin n) (Fin n) ℂ)
    (hGGi : G * Gi = 1) (hG : ∀ x x', Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ x) (G *ᵥ x') = Formalism.L2.SG.HidaSetting.hJ ε x x')
    (hee : ∀ a b, Formalism.L2.SG.HidaSetting.hJ ε (e a) (e b) = 0) (hez : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) z = 0)
    (hez' : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) z' = 0)
    (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hP1 : ∀ c b, RealObj.Zhat ε (fam e z) (fam e z') G c b ≠ 0 ↔ c = π b)
    (hYN : ∀ x, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) x = 0) → (Y - 1) *ᵥ x ∈ Formalism.L2.SG.HidaSetting.spanLt e r)
    (hTN : ∀ x, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) x = 0) → (T - 1) *ᵥ x ∈ Formalism.L2.SG.HidaSetting.spanLt e r)
    (hYG : Y * G = G * T)
    (hYF : ∀ a, Y *ᵥ fam e z a = fam e z a) (hYGF : ∀ b, Y *ᵥ (G *ᵥ fam e z' b) = G *ᵥ fam e z' b) :
    Y = 1 := by
  set Z := RealObj.Zhat ε (fam e z) (fam e z') G with hZdef
  have hZne : ∀ b, Z (π b) b ≠ 0 := fun b => (hP1 _ _).2 rfl
  have hZ0 : ∀ c b, c ≠ π b → Z c b = 0 := fun c b h => by by_contra h'; exact h ((hP1 c b).1 h')
  have hπi : Function.Injective π := fun a b h => by rw [← hπ a, h, hπ b]
  have hZe : ∀ i c, Formalism.L2.SG.HidaSetting.hJ ε (fam e z i) (G *ᵥ e c) = Z i c.castSucc := by
    intro i c; simp only [hZdef, RealObj.Zhat, fam_castSucc]
  have hZf : ∀ i j, Formalism.L2.SG.HidaSetting.hJ ε (fam e z i) (G *ᵥ fam e z' j) = Z i j := fun i j => rfl
  have hef : ∀ (w : Fin n → ℂ), (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) w = 0) →
      ∀ a (i : Fin (r + 1)), Formalism.L2.SG.HidaSetting.hJ ε (e a) (fam (fun c => e c) w i) = 0 := by
    intro w hw a i
    induction i using Fin.lastCases with
    | last => rw [fam_last]; exact hw a
    | cast c => rw [fam_castSucc]; exact hee a c
  have hfe' : ∀ i a, Formalism.L2.SG.HidaSetting.hJ ε (fam e z i) (e a) = 0 := by
    intro i a
    rw [hJ_cj', hef z hez a i, map_zero]
  have hGi : ∀ x, G *ᵥ (Gi *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hGGi, Matrix.one_mulVec]

  have hQ : ∀ q, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) q = 0) → (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e a) q = 0) →
      Y *ᵥ q = q := by
    intro q h1 h2
    obtain ⟨α, hα⟩ := mem_spanLt_r e _ (hYN q h1)
    have h3 : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) (Gi *ᵥ q) = 0 := by
      intro a; rw [← hG, hGi]; exact h2 a
    obtain ⟨β, hβ⟩ := mem_spanLt_r e _ (hTN _ h3)
    have hD : (Y - 1) *ᵥ q = ∑ b, β b • (G *ᵥ e b) := by
      have e1 : Y *ᵥ q = G *ᵥ (T *ᵥ (Gi *ᵥ q)) := by
        rw [Matrix.mulVec_mulVec (Gi *ᵥ q) G T, ← hYG, ← Matrix.mulVec_mulVec, hGi]
      have : (Y - 1) *ᵥ q = G *ᵥ ((T - 1) *ᵥ (Gi *ᵥ q)) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, e1, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hGi]
      rw [this, ← hβ, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    have hβ0 : ∀ b, β b = 0 := by
      intro b
      have h := congrArg (Formalism.L2.SG.HidaSetting.hJ ε (fam e z (π b.castSucc))) (hα.trans hD)
      rw [hJ_sum_r', hJ_sum_r'] at h
      simp only [hfe', mul_zero, Finset.sum_const_zero, hZe] at h
      rw [Finset.sum_eq_single b] at h
      · rcases mul_eq_zero.1 h.symm with h1 | h1
        · exact h1
        · exact absurd h1 (hZne _)
      · intro c _ hcb
        rw [hZ0 (π b.castSucc) c.castSucc (fun h' => hcb (Fin.castSucc_injective _ (hπi h')).symm), mul_zero]
      · intro h'; exact absurd (Finset.mem_univ b) h'
    have : (Y - 1) *ᵥ q = 0 := by rw [hD]; simp [hβ0]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this

  have hall : ∀ x, Y *ᵥ x = x := by
    intro x
    let s1 : Fin n → ℂ := ∑ a : Fin r,
      (Formalism.L2.SG.HidaSetting.hJ ε (e a) x / Z a.castSucc (π a.castSucc)) • (G *ᵥ fam e z' (π a.castSucc))
    let s2 : Fin n → ℂ := ∑ c : Fin r,
      (Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e c) x / conj (Z (π c.castSucc) c.castSucc)) • fam e z (π c.castSucc)
    have hs1 : Y *ᵥ s1 = s1 := by
      simp only [s1, Matrix.mulVec_sum, Matrix.mulVec_smul, hYGF]
    have hs2 : Y *ᵥ s2 = s2 := by
      simp only [s2, Matrix.mulVec_sum, Matrix.mulVec_smul, hYF]
    have hq1 : ∀ d, Formalism.L2.SG.HidaSetting.hJ ε (e d) (x - s1 - s2) = 0 := by
      intro d
      rw [hJ_sub_r', hJ_sub_r', hJ_sum_r', hJ_sum_r']
      have hz2 : ∀ c : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (e d) (fam e z (π c.castSucc)) = 0 :=
        fun c => hef z hez d _
      simp only [hz2, mul_zero, Finset.sum_const_zero, sub_zero]
      have hd : ∀ a : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (e d) (G *ᵥ fam e z' (π a.castSucc)) =
          Z d.castSucc (π a.castSucc) := by
        intro a; rw [← hZf, fam_castSucc]
      simp only [hd]
      rw [Finset.sum_eq_single d, div_mul_cancel₀ _ ((hP1 _ _).2 (hπ _).symm), sub_self]
      · intro a _ had
        rw [hZ0 d.castSucc (π a.castSucc) (fun h' => had (Fin.castSucc_injective _ (by rw [hπ] at h'; exact h'.symm))), mul_zero]
      · intro h'; exact absurd (Finset.mem_univ d) h'
    have hq2 : ∀ d, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e d) (x - s1 - s2) = 0 := by
      intro d
      rw [hJ_sub_r', hJ_sub_r', hJ_sum_r', hJ_sum_r']
      have hz1 : ∀ a : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e d) (G *ᵥ fam e z' (π a.castSucc)) = 0 :=
        fun a => by rw [hG]; exact hef z' hez' d _
      have hd2 : ∀ c : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e d) (fam e z (π c.castSucc)) =
          conj (Z (π c.castSucc) d.castSucc) := fun c => by rw [hJ_cj', hZe]
      simp only [hz1, mul_zero, Finset.sum_const_zero, sub_zero, hd2]
      rw [Finset.sum_eq_single d, div_mul_cancel₀ _ ((map_ne_zero (starRingEnd ℂ)).2 (hZne _)), sub_self]
      · intro c _ hcd
        rw [hZ0 (π c.castSucc) d.castSucc (fun h' => hcd (Fin.castSucc_injective _ (hπi h'))), map_zero, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ d) h'
    have hq := hQ _ hq1 hq2
    calc Y *ᵥ x = Y *ᵥ ((x - s1 - s2) + s1 + s2) := by congr 1; abel
      _ = (x - s1 - s2) + s1 + s2 := by rw [Matrix.mulVec_add, Matrix.mulVec_add, hq, hs1, hs2]
      _ = x := by abel
  exact Matrix.toLin'.injective (LinearMap.ext fun x => by rw [Matrix.toLin'_apply, hall x, Matrix.toLin'_one]; rfl)

end FixLoc

section FixGlob

variable {D : D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stVFix_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StVFix X u u' := by
  classical
  intro w hw v y hy hF hGF
  set γ := gamW X u u' w with hγdef
  have hγ : IsPtRep X u u' w γ := by
    rw [hγdef, gamW, dif_pos hw.1]; exact hw.1.choose_spec
  set e : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)
  set z := Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)
  set z' := Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')
  have hee : ∀ a b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (e a) (e b) = 0 := by
    intro a b; rw [Formalism.L2.SG.Pf.Level.hJ_rv]
    convert congrArg (X.B.I.φ v) (Formalism.L2.SG.Pf.UnipB.hE_ee X a b) using 1; simp
  have hez : ∀ (u : D.what₂.Word) a,
      Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (e a) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) = 0 := by
    intro u a; rw [Formalism.L2.SG.Pf.Level.hJ_rv]
    convert congrArg (X.B.I.φ v) (Formalism.L2.SG.Pf.UnipB.hE_ez X u a) using 1; simp
  have hGGi : uMat (γ v) * uMat (γ v)⁻¹ = 1 := by simp [uMat]
  have hG : ∀ x x', Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat (γ v) *ᵥ x) (uMat (γ v) *ᵥ x') =
      Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) x x' := by
    intro x x'
    rw [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj (γ v), Matrix.mulVec_mulVec,
      Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul', Matrix.one_mulVec]
  have hYG : uMat y * uMat (γ v) = uMat (γ v) * uMat ((γ v)⁻¹ * y * γ v) := by
    have e1 : y * γ v = γ v * ((γ v)⁻¹ * y * γ v) := by group
    have e2 : uMat (y * γ v) = uMat (γ v * ((γ v)⁻¹ * y * γ v)) := by rw [e1]
    simpa [uMat] using e2
  have hZ : ZX X u u' 1 γ v = RealObj.Zhat (X.B.I.ε v) (fam e z) (fam e z') (uMat (γ v)) := by
    simp only [ZX, frm, famSc_one]; rfl
  have hO := hγ v
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hZe : ∀ c b : Fin (D.R.rS + 1), RealObj.Zhat (X.B.I.ε v) (fam e z) (fam e z') (uMat (γ v)) c b =
      (-1 : ℂ) ^ (D.R.rS - b.1) * X.B.I.φ v (X.ιE.symm (if c.val = ptPar w.1 b.val then ptSc w.1 b.val else 0)) := by
    intro c b
    have h1 := congrFun (congrFun hO c) b
    simp only [RealObj.ZhatO, ptC, Matrix.map_apply, ptMat, hZ] at h1
    rw [← ptEntry_eq w.1 c.val b.val (by rw [hsum]; exact b.2), ← h1, ← mul_assoc, ← mul_pow]
    norm_num
  have hne : ∀ b : ℕ, b < D.R.rS + 1 → X.B.I.φ v (X.ιE.symm (ptSc w.1 b)) ≠ 0 := by
    intro b hb
    rw [map_ne_zero, map_ne_zero]
    exact ptSc_ne w.1 w.2.1 b (by rw [hsum]; exact hb)
  let π : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
    ⟨ptPar w.1 b.val, lt_of_lt_of_eq (ptPar_lt w.1 b.val (by rw [hsum]; exact b.2)) hsum⟩
  have hπ : ∀ a, π (π a) = a := fun a => Fin.ext (ptPar_invol w.1 a.val (by rw [hsum]; exact a.2))
  have hP1 : ∀ c b, RealObj.Zhat (X.B.I.ε v) (fam e z) (fam e z') (uMat (γ v)) c b ≠ 0 ↔ c = π b := by
    intro c b
    rw [hZe]
    by_cases h : c.val = ptPar w.1 b.val
    · rw [if_pos h]
      refine ⟨fun _ => Fin.ext h, fun _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (hne b.val b.2)⟩
    · rw [if_neg h, map_zero, map_zero, mul_zero]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd (congrArg Fin.val h') h⟩
  have hY1 := fix_loc (X.B.I.ε v) e z z' (uMat (γ v)) (uMat (γ v)⁻¹) (uMat y) (uMat ((γ v)⁻¹ * y * γ v))
    hGGi hG hee (hez u) (hez u') π hπ hP1 hy.1.2 hy.2.2 hYG hF hGF
  apply Subtype.ext
  apply Units.ext
  simpa [uMat] using hY1

theorem stVGeo_of_sec (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hS : StVSec X u u') :
    StVGeo X u u' := by
  exact stVGeo_of_fix_sec X u u' (stVFix_holds X u u') hS

end FixGlob

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ)

def Wfg : Matrix (Fin N) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ := Matrix.of fun p k => Sum.elim F G k p

theorem gram_Wfg : (Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G =
    Matrix.fromBlocks (Matrix.of fun a b => hJ ε (F a) (F b)) (Matrix.of fun a b => hJ ε (F a) (G b))
      (Matrix.of fun a b => hJ ε (G a) (F b)) (Matrix.of fun a b => hJ ε (G a) (G b)) := by
  ext k l
  rw [Matrix.mul_assoc]
  rcases k with a | a <;> rcases l with b | b <;>
    simp [hJ, Matrix.mul_apply, mulVec, dotProduct, Wfg, conjTranspose_apply]

theorem wjx (x : Fin N → ℂ) : ((Wfg F G)ᴴ * Formalism.REAL.Jm ε) *ᵥ x = Sum.elim (fun a => hJ ε (F a) x) (fun b => hJ ε (G b) x) := by
  funext k
  rw [← mulVec_mulVec]
  rcases k with a | b <;> simp [hJ, mulVec, dotProduct, Wfg, conjTranspose_apply]

theorem Wfg_mulVec (v : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    Wfg F G *ᵥ v = ∑ a, v (Sum.inl a) • F a + ∑ b, v (Sum.inr b) • G b := by
  funext p
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Finset.sum_apply, mul_comm]

section Main

variable (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1)) (blk : Fin (r + 1) → ℕ)

def Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun a b => hJ ε (F a) (G b)

def Am (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  (Zm ε F G * C⁻¹ * (Zm ε F G)⁻¹)ᴴ

def Mm (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.fromBlocks (Am ε F G C - 1) 0 0 (C - 1)

def Yc (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Ymat (Formalism.REAL.Jm ε) (Wfg F G) (Mm ε F G C)

variable (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

theorem Jm_herm : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

include hFF hGG hπ hZ in
theorem gram_eq : (Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G =
    Matrix.fromBlocks (lastDiag (-(T : ℂ))) (Zm ε F G) (Zm ε F G)ᴴ (lastDiag (-(T' : ℂ))) := by
  rw [gram_Wfg]
  refine fromBlocks_inj.2 ⟨?_, rfl, ?_, ?_⟩
  · ext a b
    simp [hFF]
  · ext a b
    simp only [of_apply, conjTranspose_apply, Zm]
    unfold hJ Formalism.REAL.Jm
    simp only [mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp <;> ring
  · ext a b
    simp [hGG]

include hFF hGG hπ hZ hgap in
theorem gram_unit : IsUnit ((Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G).det := by
  rw [gram_eq ε F G T T' π hFF hGG hπ hZ]
  exact gram_isUnit _ (isUnit_Z π hπ _ hZ) T T' hgap

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_unitary {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) :
    (Yc ε F G C)ᴴ * Formalism.REAL.Jm ε * Yc ε F G C = Formalism.REAL.Jm ε := by
  have hA := isUB_A π hπ hblk hanti (Zm ε F G) hZ hC
  have hAZC : (Am ε F G C)ᴴ * Zm ε F G * C = Zm ε F G := A_Z_C π hπ hblk hanti _ hZ hC
  have hL : ∀ t : ℂ, ∀ i j : Fin (r + 1), i ≠ Fin.last r ∨ j ≠ Fin.last r → lastDiag t i j = 0 := by
    intro t i j h
    simp only [lastDiag, of_apply]
    rw [if_neg]
    tauto
  unfold Yc
  refine Ymat_unitary _ (Jm_herm ε) _ _ (gram_unit ε F G T T' π hFF hGG hπ hZ hgap) ?_
  rw [gram_eq ε F G T T' π hFF hGG hπ hZ]
  have h1 : (1 : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) + Mm ε F G C =
      fromBlocks (Am ε F G C) 0 0 C := by
    rw [Mm, ← fromBlocks_one, fromBlocks_add]
    simp
  rw [h1, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, zero_mul, mul_zero, add_zero, zero_add]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
  · exact gram_last hA _ (hL _)
  · exact hAZC
  · have h2 := congrArg conjTranspose hAZC
    simpa [conjTranspose_mul, Matrix.mul_assoc] using h2
  · exact gram_last hC _ (hL _)

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ) (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1))
  (blk : Fin (r + 1) → ℕ)
  (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

include hFF hGG hπ hZ hgap in
theorem Yc_G {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (b : Fin (r + 1)) :
    Yc ε F G C *ᵥ G b = ∑ b', C b' b • G b' := by
  have hΓ := gram_unit (ε := ε) (F := F) (G := G) (T := T) (T' := T') (π := π) (hFF := hFF)
    (hGG := hGG) (hπ := hπ) (hZ := hZ) (hgap := hgap)
  have hW : Yc ε F G C * Wfg F G = Wfg F G * (1 + Mm ε F G C) := rankUpdate_mul _ _ _ hΓ
  have hGcol : G b = Wfg F G *ᵥ Pi.single (Sum.inr b) 1 := by
    funext p
    rw [Matrix.mulVec_single]
    simp [Wfg]
  rw [hGcol, Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, Matrix.mulVec_single]
  funext p
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Mm, Matrix.one_apply, Finset.sum_apply, mul_comm]

include hFF hGG hπ hZ hgap in
theorem Yc_F {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (a : Fin (r + 1)) :
    Yc ε F G C *ᵥ F a = ∑ a', Am ε F G C a' a • F a' := by
  have hΓ := gram_unit (ε := ε) (F := F) (G := G) (T := T) (T' := T') (π := π) (hFF := hFF)
    (hGG := hGG) (hπ := hπ) (hZ := hZ) (hgap := hgap)
  have hW : Yc ε F G C * Wfg F G = Wfg F G * (1 + Mm ε F G C) := rankUpdate_mul _ _ _ hΓ
  have hFcol : F a = Wfg F G *ᵥ Pi.single (Sum.inl a) 1 := by
    funext p
    rw [Matrix.mulVec_single]
    simp [Wfg]
  rw [hFcol, Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, Matrix.mulVec_single]
  funext p
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Mm, Matrix.one_apply, Finset.sum_apply, mul_comm]

theorem rowLast {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (k : Fin (r + 1)) :
    C (Fin.last r) k = if k = Fin.last r then 1 else 0 := by
  obtain ⟨hdiag, hup⟩ := hC
  split_ifs with hk
  · rw [hk]
    exact hdiag _
  · by_contra h
    have h1 := (hup _ _ h).1
    exact hk (le_antisymm (Fin.le_last k) h1)

include hπ hblk hanti in
theorem colMin {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (b : Fin (r + 1)) :
    C b (π (Fin.last r)) = if b = π (Fin.last r) then 1 else 0 := by
  obtain ⟨hdiag, hup⟩ := hC
  split_ifs with hb
  · rw [hb]
    exact hdiag _
  · by_contra h
    obtain ⟨hle, hbl⟩ := hup _ _ h
    have hlt : b < π (Fin.last r) := lt_of_le_of_ne hle hb
    have h2 := hanti b (π (Fin.last r)) hbl hlt
    rw [hπ] at h2
    exact absurd (Fin.le_last (π b)) (not_le.mpr h2)

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ) (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1))
  (blk : Fin (r + 1) → ℕ)
  (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

def kap (x : Fin N → ℂ) : Fin (r + 1) ⊕ Fin (r + 1) → ℂ :=
  ((Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G)⁻¹ *ᵥ (((Wfg F G)ᴴ * Formalism.REAL.Jm ε) *ᵥ x)

include hFF hGG hπ hZ hgap in
theorem kap_eq (x : Fin N → ℂ) :
    Matrix.fromBlocks (lastDiag (-(T : ℂ))) (Zm ε F G) (Zm ε F G)ᴴ (lastDiag (-(T' : ℂ))) *ᵥ kap ε F G x =
      Sum.elim (fun a => hJ ε (F a) x) (fun b => hJ ε (G b) x) := by
  rw [← gram_eq ε F G T T' π hFF hGG hπ hZ, kap, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (gram_unit ε F G T T' π hFF hGG hπ hZ hgap), Matrix.one_mulVec, wjx]

theorem Yc_sub (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : Fin N → ℂ) :
    Yc ε F G C *ᵥ x - x = ∑ a, ((Am ε F G C - 1) *ᵥ (kap ε F G x ∘ Sum.inl)) a • F a +
      ∑ b, ((C - 1) *ᵥ (kap ε F G x ∘ Sum.inr)) b • G b := by
  unfold Yc
  rw [Ymat_sub, Wfg_mulVec]
  unfold Mm
  rw [Matrix.fromBlocks_mulVec]
  simp [kap]

include hπ hZ in
theorem monoZ_mulVec (v : Fin (r + 1) → ℂ) (a : Fin (r + 1)) : (Zm ε F G *ᵥ v) a = Zm ε F G a (π a) * v (π a) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π a)]
  · intro j _ hj
    have : Zm ε F G a j = 0 := by by_contra h; exact hj (by rw [(hZ a j).1 h, hπ])
    rw [this, zero_mul]
  · simp

include hπ hZ in
theorem monoZh_mulVec (v : Fin (r + 1) → ℂ) (b : Fin (r + 1)) :
    ((Zm ε F G)ᴴ *ᵥ v) b = starRingEnd ℂ (Zm ε F G (π b) b) * v (π b) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π b)]
  · simp [Matrix.conjTranspose_apply]
  · intro j _ hj
    have : Zm ε F G j b = 0 := by by_contra h; exact hj ((hZ j b).1 h)
    simp [Matrix.conjTranspose_apply, this]
  · simp

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_perpF {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (x : Fin N → ℂ)
    (hx : ∀ a, a ≠ Fin.last r → hJ ε (F a) x = 0) :
    Yc ε F G C *ᵥ x - x ∈ Submodule.span ℂ (F '' {a | a ≠ Fin.last r}) := by
  have hk := kap_eq ε F G T T' π hFF hGG hπ hZ hgap x
  rw [Matrix.fromBlocks_mulVec] at hk
  set κ := kap ε F G x
  have hG0 : ∀ j, j ≠ π (Fin.last r) → κ (Sum.inr j) = 0 := by
    intro j hj
    have ha : π j ≠ Fin.last r := fun h => hj (by rw [← h, hπ])
    have h1 := congrFun hk (Sum.inl (π j))
    simp only [Sum.elim_inl, Pi.add_apply] at h1
    rw [hx _ ha, lastDiag_mulVec, Pi.single_apply, if_neg ha, zero_add, monoZ_mulVec ε F G π hπ hZ, hπ] at h1
    have hz : Zm ε F G (π j) j ≠ 0 := (hZ _ _).2 rfl
    exact (mul_eq_zero.1 h1).resolve_left hz
  rw [Yc_sub]
  have h2 : ∑ b, ((C - 1) *ᵥ (κ ∘ Sum.inr)) b • G b = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ((C - 1) *ᵥ (κ ∘ Sum.inr)) b = 0 := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π (Fin.last r))]
      · rw [Matrix.sub_apply, colMin π blk hπ hblk hanti hC, Matrix.one_apply]
        split_ifs <;> simp
      · intro j _ hj; simp [hG0 j hj]
      · simp
    rw [this, zero_smul]
  rw [h2, add_zero]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a = Fin.last r
  · subst ha
    have : ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) (Fin.last r) = 0 := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hA : IsUB blk (Am ε F G C) := isUB_A π hπ hblk hanti _ hZ hC
      rw [Matrix.sub_apply, rowLast blk hA, Matrix.one_apply]
      by_cases hk : k = Fin.last r
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    rw [this, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_perpG {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (x : Fin N → ℂ)
    (hx : ∀ b, b ≠ Fin.last r → hJ ε (G b) x = 0) :
    Yc ε F G C *ᵥ x - x ∈ Submodule.span ℂ (G '' {b | b ≠ Fin.last r}) := by
  have hk := kap_eq ε F G T T' π hFF hGG hπ hZ hgap x
  rw [Matrix.fromBlocks_mulVec] at hk
  set κ := kap ε F G x
  have hF0 : ∀ i, i ≠ π (Fin.last r) → κ (Sum.inl i) = 0 := by
    intro i hi
    have hb : π i ≠ Fin.last r := fun h => hi (by rw [← h, hπ])
    have h1 := congrFun hk (Sum.inr (π i))
    simp only [Sum.elim_inr, Pi.add_apply] at h1
    rw [hx _ hb, lastDiag_mulVec, Pi.single_apply, if_neg hb, add_zero, monoZh_mulVec ε F G π hπ hZ, hπ] at h1
    have hz : starRingEnd ℂ (Zm ε F G i (π i)) ≠ 0 := by
      rw [map_ne_zero]; exact (hZ _ _).2 (hπ i).symm
    exact (mul_eq_zero.1 h1).resolve_left hz
  rw [Yc_sub]
  have hA : IsUB blk (Am ε F G C) := isUB_A π hπ hblk hanti _ hZ hC
  have h2 : ∑ a, ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) a • F a = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) a = 0 := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π (Fin.last r))]
      · rw [Matrix.sub_apply, colMin π blk hπ hblk hanti hA, Matrix.one_apply]
        split_ifs <;> simp
      · intro j _ hj; simp [hF0 j hj]
      · simp
    rw [this, zero_smul]
  rw [h2, zero_add]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : b = Fin.last r
  · subst hb
    have : ((C - 1) *ᵥ (κ ∘ Sum.inr)) (Fin.last r) = 0 := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Matrix.sub_apply, rowLast blk hC, Matrix.one_apply]
      by_cases hk : k = Fin.last r
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    rw [this, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
