import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormaliserUnipSymCharPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfNormalizesSymmetricLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent

section
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

noncomputable section
namespace GlobalTheory.ScalConj

theorem single_conj_apply {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (a b i j : Fin n) :
    (A * (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) * B) i j = A i a * B b j := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]

def conjInt {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K) :
    Subalgebra O (Matrix (Fin n) (Fin n) O) where
  carrier := {X | ∃ Y : Matrix (Fin n) (Fin n) O,
    Y.map O.subtype = (m : Matrix (Fin n) (Fin n) K) * X.map O.subtype * ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
  mul_mem' := by
    rintro X X' ⟨Y, hY⟩ ⟨Y', hY'⟩
    refine ⟨Y * Y', ?_⟩
    rw [Matrix.map_mul, Matrix.map_mul, hY, hY']
    have : ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (m : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul m
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), this, Matrix.one_mul]
  add_mem' := by
    rintro X X' ⟨Y, hY⟩ ⟨Y', hY'⟩
    refine ⟨Y + Y', ?_⟩
    rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hY, hY', Matrix.mul_add, Matrix.add_mul]
  algebraMap_mem' := by
    intro r
    refine ⟨algebraMap O _ r, ?_⟩
    have h : (algebraMap O (Matrix (Fin n) (Fin n) O) r).map O.subtype = (r : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.algebraMap_matrix_apply]
      · simp [Matrix.algebraMap_matrix_apply, h, Matrix.one_apply_ne h]
    rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv]

theorem single_map_subtype {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (a b : Fin n) :
    (Matrix.single a b (1 : O)).map O.subtype = (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem entry_mul_inv_entry_mem {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K)
    (T : Set (GL (Fin n) O))
    (hT : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤)
    (hc : ∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) (i a b j : Fin n) :
    (m : Matrix (Fin n) (Fin n) K) i a * ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b j ∈ O := by
  have hle : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) ≤ conjInt O m := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx'⟩ := hc x hx
    exact ⟨x', congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hx'⟩
  rw [hT] at hle
  obtain ⟨Y, hY⟩ := hle (Algebra.mem_top : Matrix.single a b (1 : O) ∈ (⊤ : Subalgebra O (Matrix (Fin n) (Fin n) O)))
  have h := congrFun (congrFun hY i) j
  rw [single_map_subtype, single_conj_apply] at h
  rw [← h]
  exact (Y i j).2

theorem isScal_of_conj (K : Type) [Field K] (O : ValuationSubring K) (n : ℕ) (m : GL (Fin n) K)
    (T : Set (GL (Fin n) O))
    (hT : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤)
    (hc : ∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) : IsScal O m := by
  have H := entry_mul_inv_entry_mem O m T hT hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  set M : Matrix (Fin n) (Fin n) K := (m : Matrix (Fin n) (Fin n) K) with hM
  set N : Matrix (Fin n) (Fin n) K := ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hN
  have hMN : M * N = 1 := Units.mul_inv m
  obtain ⟨⟨i0, a0⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => O.valuation (M p.1 p.2)) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  set c := M i0 a0 with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    have hz : ∀ i a, M i a = 0 := fun i a => by
      have h1 := hmax (i, a) (Finset.mem_univ _)
      simp only [h0, map_zero] at h1
      exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    have h1 := congrFun (congrFun hMN ⟨0, hn⟩) ⟨0, hn⟩
    simp [Matrix.mul_apply, hz] at h1
  have hv : 0 < O.valuation c := (Valuation.pos_iff _).2 hc0
  have hy : ∀ i a, c⁻¹ * M i a ∈ O := fun i a => by
    rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
    exact (inv_mul_le_one₀ hv).2 (hmax (i, a) (Finset.mem_univ _))
  have hz : ∀ b j, c * N b j ∈ O := fun b j => H i0 a0 b j
  let Y : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hy i j⟩
  let Z : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hz i j⟩
  have hYm : Y.map O.subtype = c⁻¹ • M := by ext i j; rfl
  have hZm : Z.map O.subtype = c • N := by ext i j; rfl
  have inj : Function.Injective fun X : Matrix (Fin n) (Fin n) O => X.map O.subtype :=
    Matrix.map_injective (Subtype.val_injective)
  have key : ∀ {A B : Matrix (Fin n) (Fin n) K}, A * B = 1 → (c⁻¹ • A) * (c • B) = 1 := fun {A B} h => by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, h]
  have hNM : N * M = 1 := Units.inv_mul m
  have e1 : Y * Z = 1 := inj (by
    show (Y * Z).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hYm, hZm, key hMN])
  have e2 : Z * Y = 1 := inj (by
    show (Z * Y).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hYm, hZm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hc0, one_smul, hNM])
  refine ⟨Units.mk0 c hc0, ⟨Y, Z, e1, e2⟩, ?_⟩
  show M = c • (Y.map O.subtype)
  rw [hYm, smul_smul, mul_inv_cancel₀ hc0, one_smul]

end GlobalTheory.ScalConj
end
end

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isScalarMulIntegral_of_conj_integral_generators : ∀ (K : Type) [Field K] (O : ValuationSubring K) (n : ℕ) (m : GL (Fin n) K) (T : Set (GL (Fin n) O)), Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤ → (∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) → IsScal O m := by
  atlas_forward_decl GlobalTheory.ScalConj.isScal_of_conj
end

section
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

theorem adjoin_range_GL_eq_top (R : Type) [CommRing R] (n : ℕ) :
    Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ) = ⊤ := by
  set S := Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ)
  have hoff : ∀ i j : Fin n, i ≠ j → Matrix.single i j (1:R) ∈ S := by
    intro i j hij
    have hu : IsUnit (Matrix.transvection i j (1:R)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transvection_of_ne _ _ hij]; exact isUnit_one)
    have hmem : Matrix.transvection i j (1:R) ∈ S :=
      Algebra.subset_adjoin ⟨hu.unit, Set.mem_univ _, rfl⟩
    have : Matrix.single i j (1:R) = Matrix.transvection i j 1 - 1 := by
      simp [Matrix.transvection]
    rw [this]; exact S.sub_mem hmem S.one_mem
  have hall : ∀ i j : Fin n, Matrix.single i j (1:R) ∈ S := by
    intro i j
    by_cases hij : i = j
    · subst hij
      by_cases h : ∃ k, k ≠ i
      · obtain ⟨k, hk⟩ := h
        have : Matrix.single i i (1:R) = Matrix.single i k 1 * Matrix.single k i 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        rw [this]; exact S.mul_mem (hoff _ _ (Ne.symm hk)) (hoff _ _ hk)
      · push_neg at h
        have : Matrix.single i i (1:R) = 1 := by
          ext a b
          rw [h a, h b]; simp
        rw [this]; exact S.one_mem
    · exact hoff i j hij
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  have : Matrix.single i j (M i j) = M i j • Matrix.single i j 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]; exact S.smul_mem (hall i j) _

end GlobalTheory
end

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_range_GL_eq_top_matrix : ∀ (R : Type) [CommRing R] (n : ℕ), Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ) = ⊤ := by
  atlas_forward_decl GlobalTheory.adjoin_range_GL_eq_top
end

section
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

noncomputable section

namespace GlobalTheory.UnitaryGen
variable {R : Type} [CommRing R] (s : R →+* R)

theorem refl_unitary (hs : ∀ x, s (s x) = x) {n : ℕ} (d : Fin n → R) (hd : ∀ k, s (d k) = d k)
    (c : R) (v : Fin n → R) (hc : c + s c + c * s c * ∑ k, s (v k) * d k * v k = 0) :
    cT s (1 + c • vecMulVec v (fun k => s (v k) * d k)) * diagonal d *
      (1 + c • vecMulVec v (fun k => s (v k) * d k)) = diagonal d := by
  ext a b
  set r := 1 + c • vecMulVec v (fun k => s (v k) * d k) with hr
  have e1 : ∀ k, cT s r a k * d k = (1 : Matrix (Fin n) (Fin n) R) a k * d k +
      (s c * (v a * d a)) * (s (v k) * d k) := by
    intro k
    simp only [hr, cT, transpose_apply, map_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      map_add, map_mul, hs, hd]
    by_cases h : k = a
    · subst h; simp only [one_apply_eq, map_one]; ring
    · rw [one_apply_ne h, one_apply_ne (Ne.symm h), map_zero]; ring
  have e2 : ∀ k, r k b = (1 : Matrix (Fin n) (Fin n) R) k b + c * v k * (s (v b) * d b) := by
    intro k
    simp only [hr, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]; ring
  rw [mul_apply]
  simp only [mul_diagonal]
  rw [Finset.sum_congr rfl (fun k _ => by rw [e1, e2])]
  have e3 : ∀ k, ((1 : Matrix (Fin n) (Fin n) R) a k * d k + (s c * (v a * d a)) * (s (v k) * d k)) *
      ((1 : Matrix (Fin n) (Fin n) R) k b + c * v k * (s (v b) * d b)) =
      (1 : Matrix (Fin n) (Fin n) R) a k * (d k * (1 : Matrix (Fin n) (Fin n) R) k b) +
      (1 : Matrix (Fin n) (Fin n) R) a k * (d k * (c * v k * (s (v b) * d b))) +
      (1 : Matrix (Fin n) (Fin n) R) k b * ((s c * (v a * d a)) * (s (v k) * d k)) +
      (s c * (v a * d a) * c * (s (v b) * d b)) * (s (v k) * d k * v k) := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => e3 k)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hab : a = b
  · subst hab; simp; linear_combination (v a * d a * (s (v a) * d a)) * hc
  · simp [hab]; linear_combination (v a * d a * (s (v b) * d b)) * hc

abbrev uAlg {n : ℕ} (J : Matrix (Fin n) (Fin n) R) : Subalgebra R (Matrix (Fin n) (Fin n) R) :=
  Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' (UJ s J : Set (GL (Fin n) R)))

theorem mem_uAlg_of_unitary {n : ℕ} {J : Matrix (Fin n) (Fin n) R} (hJ : IsUnit J.det)
    {M : Matrix (Fin n) (Fin n) R} (hM : cT s M * J * M = J) : M ∈ uAlg s J := by
  have hdet : IsUnit M.det := by
    have h := congrArg Matrix.det hM
    rw [det_mul] at h
    exact isUnit_of_mul_isUnit_right (h ▸ hJ)
  exact Algebra.subset_adjoin ⟨nonsingInvUnit M hdet, hM, rfl⟩

theorem isUnit_det_diagonal {n : ℕ} {d : Fin n → R} (hdu : ∀ k, IsUnit (d k)) : IsUnit (diagonal d).det := by
  rw [det_diagonal, isUnit_iff_exists_inv]
  exact ⟨∏ k, ((hdu k).unit⁻¹ : Rˣ), by rw [← Finset.prod_mul_distrib]; simp⟩

theorem vec_mem (hs : ∀ x, s (s x) = x) {ζ : R} (hζ : ζ * s ζ = 1) (hζ1 : IsUnit (ζ - 1)) {n : ℕ}
    {d : Fin n → R} (hdu : ∀ k, IsUnit (d k)) (hd : ∀ k, s (d k) = d k) (v : Fin n → R)
    (hN : IsUnit (∑ k, s (v k) * d k * v k)) :
    vecMulVec v (fun k => s (v k) * d k) ∈ uAlg s (diagonal d) := by
  set N := ∑ k, s (v k) * d k * v k with hNdef
  have hsN : s N = N := by
    rw [hNdef, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_mul, hs, hd]; ring
  set Ni : R := ((hN.unit⁻¹ : Rˣ) : R) with hNidef
  have hNi : Ni * N = 1 := hN.val_inv_mul
  have hsNi' : s Ni * N = 1 := by rw [← hsN, ← map_mul, hNi, map_one]
  have hsNi : s Ni = Ni := by
    calc s Ni = s Ni * (N * Ni) := by rw [mul_comm N, hNi, mul_one]
      _ = (s Ni * N) * Ni := by ring
      _ = Ni := by rw [hsNi', one_mul]
  set c := (ζ - 1) * Ni with hcdef
  have hc : c + s c + c * s c * N = 0 := by
    rw [hcdef, map_mul, hsNi, map_sub, map_one]
    linear_combination ((ζ - 1) * (s ζ - 1) * Ni) * hNi + Ni * hζ
  have hcu : IsUnit c := hζ1.mul (Units.isUnit _)
  have hr := mem_uAlg_of_unitary s (isUnit_det_diagonal hdu) (refl_unitary s hs d hd c v hc)
  have hX : vecMulVec v (fun k => s (v k) * d k) =
      ((hcu.unit⁻¹ : Rˣ) : R) • ((1 + c • vecMulVec v (fun k => s (v k) * d k)) - 1) := by
    rw [add_sub_cancel_left, smul_smul, hcu.val_inv_mul, one_smul]
  rw [hX]
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ hr (Subalgebra.one_mem _)) _

theorem single_mem_of_isUnit {n : ℕ} {J : Matrix (Fin n) (Fin n) R} (i j : Fin n) {u : R} (hu : IsUnit u)
    (h : single i j u ∈ uAlg s J) : single i j (1 : R) ∈ uAlg s J := by
  have : single i j (1 : R) = ((hu.unit⁻¹ : Rˣ) : R) • single i j u := by
    rw [smul_single, smul_eq_mul, hu.val_inv_mul]
  rw [this]; exact Subalgebra.smul_mem _ h _

theorem ind_mem (hs : ∀ x, s (s x) = x) {ζ : R} (hζ : ζ * s ζ = 1) (hζ1 : IsUnit (ζ - 1)) {n : ℕ}
    {d : Fin n → R} (hdu : ∀ k, IsUnit (d k)) (hd : ∀ k, s (d k) = d k) (S : Finset (Fin n))
    (hN : IsUnit (∑ k ∈ S, d k)) :
    vecMulVec (fun k => if k ∈ S then (1 : R) else 0) (fun k => if k ∈ S then d k else 0) ∈ uAlg s (diagonal d) := by
  have h := vec_mem s hs hζ hζ1 hdu hd (fun k => if k ∈ S then (1 : R) else 0) (by
    convert hN using 1
    rw [← Finset.univ_inter S, ← Finset.sum_ite_mem]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp_all)
  convert h using 2
  funext k
  split_ifs <;> simp

theorem single_mem_diag (hs : ∀ x, s (s x) = x) [IsLocalRing R] {ζ : R} (hζ : ζ * s ζ = 1) (hζ1 : IsUnit (ζ - 1))
    {n : ℕ} (hn : 3 ≤ n) {d : Fin n → R} (hdu : ∀ k, IsUnit (d k)) (hd : ∀ k, s (d k) = d k) (i j : Fin n) :
    single i j (1 : R) ∈ uAlg s (diagonal d) := by
  have hii : ∀ i, single i i (1 : R) ∈ uAlg s (diagonal d) := by
    intro i
    have h := ind_mem s hs hζ hζ1 hdu hd {i} (by simpa using hdu i)
    refine single_mem_of_isUnit s i i (hdu i) ?_
    convert h using 1
    ext a b
    by_cases ha : a = i <;> by_cases hb : b = i <;> simp [vecMulVec_apply, single_apply, ha, hb] <;> intros <;> simp_all
  have hS : ∀ S : Finset (Fin n), i ∈ S → j ∈ S → IsUnit (∑ k ∈ S, d k) →
      single i j (1 : R) ∈ uAlg s (diagonal d) := by
    intro S hi hj hN
    have h := ind_mem s hs hζ hζ1 hdu hd S hN
    have h2 := Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hii i) h) (hii j)
    rw [single_mul_mul_single] at h2
    refine single_mem_of_isUnit s i j ?_ h2
    simpa [vecMulVec_apply, hi, hj] using hdu j
  by_cases hij : i = j
  · subst hij; exact hii i
  by_cases hu : IsUnit (d i + d j)
  · exact hS {i, j} (by simp) (by simp) (by rwa [Finset.sum_pair hij])
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {i, j}) (t := Finset.univ) (by
    rw [Finset.card_univ, Fintype.card_fin]; exact lt_of_le_of_lt Finset.card_le_two (by omega))
  refine hS {l, i, j} (by simp) (by simp) ?_
  rw [Finset.sum_insert hl, Finset.sum_pair hij]
  by_contra h
  have h1 : d l + (d i + d j) + -(d i + d j) ∈ nonunits R :=
    IsLocalRing.nonunits_add h (by rw [mem_nonunits_iff, IsUnit.neg_iff]; exact hu)
  rw [add_neg_cancel_right] at h1
  exact h1 (hdu l)

theorem eq_top_of_single {n : ℕ} {A : Subalgebra R (Matrix (Fin n) (Fin n) R)}
    (h : ∀ i j, single i j (1 : R) ∈ A) : A = ⊤ := by
  refine eq_top_iff.2 fun M _ => ?_
  rw [matrix_eq_sum_single M]
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => ?_
  have : single i j (M i j) = M i j • single i j (1 : R) := by rw [smul_single, smul_eq_mul, mul_one]
  rw [this]; exact Subalgebra.smul_mem _ (h i j) _

theorem isUnit_det_cT {n : ℕ} {Q : Matrix (Fin n) (Fin n) R} (hQ : IsUnit Q.det) : IsUnit (cT s Q).det := by
  rw [cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hQ.map s

theorem uAlg_conj {n : ℕ} {J Q : Matrix (Fin n) (Fin n) R} (hQ : IsUnit Q.det) (hJ : IsUnit J.det)
    {M : Matrix (Fin n) (Fin n) R} (hM : M ∈ uAlg s J) : Q⁻¹ * M * Q ∈ uAlg s (cT s Q * J * Q) := by
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQ
  refine Algebra.adjoin_induction (p := fun M _ => Q⁻¹ * M * Q ∈ uAlg s (cT s Q * J * Q)) ?_ ?_ ?_ ?_ hM
  · rintro x ⟨g, hg, rfl⟩
    refine mem_uAlg_of_unitary s ?_ ?_
    · rw [det_mul, det_mul]
      exact ((isUnit_det_cT s hQ).mul hJ).mul hQ
    · have hg' : cT s (g : Matrix (Fin n) (Fin n) R) * J * (g : Matrix (Fin n) (Fin n) R) = J := hg
      have hc1 : cT s (Q⁻¹) * cT s Q = 1 := by rw [← cT_mul, hQQ, cT_one]
      calc cT s (Q⁻¹ * (g : Matrix (Fin n) (Fin n) R) * Q) * (cT s Q * J * Q) * (Q⁻¹ * (g : Matrix (Fin n) (Fin n) R) * Q)
          = cT s Q * (cT s (g : Matrix (Fin n) (Fin n) R) * (cT s (Q⁻¹) * cT s Q) * J * (Q * Q⁻¹) *
              (g : Matrix (Fin n) (Fin n) R)) * Q := by
            rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
        _ = cT s Q * J * Q := by rw [hc1, hQQ, Matrix.mul_one, Matrix.mul_one, hg']
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQQ', ← Algebra.algebraMap_eq_smul_one]
    exact Subalgebra.algebraMap_mem _ r
  · intro x y _ _ hx hy
    rw [Matrix.mul_add, Matrix.add_mul]; exact Subalgebra.add_mem _ hx hy
  · intro x y _ _ hx hy
    have : Q⁻¹ * (x * y) * Q = (Q⁻¹ * x * Q) * (Q⁻¹ * y * Q) := by
      calc Q⁻¹ * (x * y) * Q = Q⁻¹ * x * (Q * Q⁻¹) * y * Q := by rw [hQQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = (Q⁻¹ * x * Q) * (Q⁻¹ * y * Q) := by simp only [Matrix.mul_assoc]
    rw [this]; exact Subalgebra.mul_mem _ hx hy

theorem adjoin_unitary_eq_top : ∀ (R : Type) [CommRing R] [IsLocalRing R] (s : R →+* R), (∀ x, s (s x) = x) →
    (∃ δ : R, IsUnit (δ - s δ)) → ∀ n : ℕ, 3 ≤ n → ∀ G : Matrix (Fin n) (Fin n) R, cT s G = G → IsUnit G →
    Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' (UJ s G : Set (GL (Fin n) R))) = ⊤ := by
  intro R _ _ s hs ⟨δ, hδ⟩ n hn G hG hGu
  obtain ⟨δ', hδ'u, hδ'⟩ : ∃ δ', IsUnit δ' ∧ IsUnit (δ' - s δ') := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self δ with h | h
    · exact ⟨δ, h, hδ⟩
    · refine ⟨1 - δ, h, ?_⟩
      have : 1 - δ - s (1 - δ) = -(δ - s δ) := by rw [map_sub, map_one]; ring
      rw [this, IsUnit.neg_iff]; exact hδ
  have hsu : IsUnit (s δ') := hδ'u.map s
  set i : R := ((hsu.unit⁻¹ : Rˣ) : R) with hidef
  have h1 : i * s δ' = 1 := hsu.val_inv_mul
  have h2 : s i * δ' = 1 := by have := congrArg s h1; rwa [map_mul, hs, map_one] at this
  have hζ : δ' * i * s (δ' * i) = 1 := by
    rw [map_mul]; linear_combination (δ' * s i) * h1 + h2
  have hζ1 : IsUnit (δ' * i - 1) := by
    have : δ' * i - 1 = (δ' - s δ') * i := by linear_combination h1
    rw [this]; exact hδ'.mul (Units.isUnit _)

  have hw : ∃ w, w + s w = 1 := by
    set ui : R := ((hδ.unit⁻¹ : Rˣ) : R)
    have e1 : ui * (δ - s δ) = 1 := hδ.val_inv_mul
    have e2 : s ui * (s δ - δ) = 1 := by have := congrArg s e1; rwa [map_mul, map_sub, hs, map_one] at this
    have e3 : s ui = -ui := by
      calc s ui = s ui * ((δ - s δ) * ui) := by rw [mul_comm (δ - s δ), e1, mul_one]
        _ = -(s ui * (s δ - δ)) * ui := by ring
        _ = -ui := by rw [e2]; ring
    refine ⟨δ * ui, ?_⟩
    rw [map_mul, e3]; linear_combination e1
  have hGab : ∀ a b, s (G a b) = G b a := fun a b => congrFun (congrFun hG b) a
  have hdetG : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hGu
  obtain ⟨P, d, hP, hdu, hd, hGe⟩ := GlobalTheory.UnramifiedHermitian.exists_eq_diagonal_of_isUnit_or s hs
    (fun x _ => IsLocalRing.isUnit_or_isUnit_one_sub_self x) hw hGab hdetG
  set Q := P.map s with hQdef
  have hcQ : cT s Q = Pᵀ := by
    ext a b; simp [cT, hQdef, hs]
  have hQ : IsUnit Q.det := by
    rw [hQdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hP.map s
  have hGQ : cT s Q * diagonal d * Q = G := by rw [hcQ, hGe]
  have htop := eq_top_of_single (single_mem_diag s hs hζ hζ1 hn hdu hd)
  refine eq_top_of_single (A := uAlg s G) fun a b => ?_
  have hm := uAlg_conj s hQ (isUnit_det_diagonal hdu) (M := Q * single a b (1 : R) * Q⁻¹) (by rw [htop]; trivial)
  rw [hGQ] at hm
  have : Q⁻¹ * (Q * single a b (1 : R) * Q⁻¹) * Q = single a b 1 := by
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hQ, Matrix.mul_one]
  rwa [this] at hm

end GlobalTheory.UnitaryGen

end
end

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_unitaryGroup_hermitian_local_eq_top : ∀ (R : Type) [CommRing R] [IsLocalRing R] (s : R →+* R), (∀ x, s (s x) = x) → (∃ δ : R, IsUnit (δ - s δ)) → ∀ n : ℕ, 3 ≤ n → ∀ G : Matrix (Fin n) (Fin n) R, cT s G = G → IsUnit G → Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' (UJ s G : Set (GL (Fin n) R))) = ⊤ := by
  atlas_forward_decl GlobalTheory.UnitaryGen.adjoin_unitary_eq_top
end

section
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

noncomputable section

namespace GlobalTheory.LevNorm.PlaceSys

theorem gU_intM_mul {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O) : ∀ i j, (M * N) i j ∈ O := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)

theorem gU_glO {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (M N : Matrix (Fin n) (Fin n) K)
    (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O) (h : M * N = 1) :
    ∃ y : GL (Fin n) O, ((bc O.subtype y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := by
  have h' : N * M = 1 := mul_eq_one_comm.1 h
  have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype :=
    Matrix.map_injective fun x y hxy => Subtype.ext hxy
  refine ⟨⟨Matrix.of fun i j => ⟨M i j, hM i j⟩, Matrix.of fun i j => ⟨N i j, hN i j⟩, inj ?_, inj ?_⟩, rfl⟩
  · show Matrix.map _ O.subtype = Matrix.map _ O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact h
  · show Matrix.map _ O.subtype = Matrix.map _ O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact h'

theorem gU_val_inv {R : Type} [CommRing R] {n : ℕ} (g : GL (Fin n) R) (L : Matrix (Fin n) (Fin n) R)
    (h : L * (g : Matrix (Fin n) (Fin n) R) = 1) : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = L := by
  calc ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
      = L * (g : Matrix (Fin n) (Fin n) R) * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
        rw [h, Matrix.one_mul]
    _ = L := by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem gU_cT_smul {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (w : A) (M : Matrix (Fin n) (Fin n) A) :
    cT σ (w • M) = σ w • cT σ M := by
  ext i j; simp [cT]

theorem gU_mapMatrix_smul {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (w : A)
    (M : Matrix (Fin n) (Fin n) A) : φ.mapMatrix (w • M) = φ w • φ.mapMatrix M := by
  ext i j; simp

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q}
  (Z : PlaceSys A S P k r) {σ : A →+* A}

theorem gU_inv_comp {Q Q' : P} {s : Z.K Q →+* Z.K Q'} (hs : ∀ a, s (Z.p Q a) = Z.p Q' (σ a))
    (hsO : ∀ x ∈ Z.O Q, s x ∈ Z.O Q') {n : ℕ} (G : GL (Fin n) S) (u : GL (Fin n) A)
    (hu : u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (d : Z.K Q) (W : Matrix (Fin n) (Fin n) (Z.K Q)) (hW : ∀ i j, W i j ∈ Z.O Q)
    (h : (Z.p Q).mapMatrix (u : Matrix (Fin n) (Fin n) A) = d • W) :
    ∃ I : Matrix (Fin n) (Fin n) (Z.K Q'), (∀ i j, I i j ∈ Z.O Q') ∧
      (Z.p Q').mapMatrix ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = s d • I := by
  set Gm : Matrix (Fin n) (Fin n) A := ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) with hGm
  set Gi : Matrix (Fin n) (Fin n) A := ((bc S.subtype G⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) with hGi
  have hu' : cT σ (u : Matrix (Fin n) (Fin n) A) * Gm * u = Gm := hu
  have hGG : Gi * Gm = 1 := by
    rw [hGi, hGm, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have key : ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = Gi * cT σ (u : Matrix (Fin n) (Fin n) A) * Gm := by
    apply gU_val_inv
    calc Gi * cT σ (u : Matrix (Fin n) (Fin n) A) * Gm * u = Gi * (cT σ (u : Matrix (Fin n) (Fin n) A) * Gm * u) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu', hGG]
  have hcT : (Z.p Q').mapMatrix (cT σ (u : Matrix (Fin n) (Fin n) A)) = s d • (W.map s)ᵀ := by
    ext i j
    have := congrFun (congrFun h j) i
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
    simp only [cT, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← hs, this, map_mul]
  refine ⟨(Z.p Q').mapMatrix Gi * (W.map s)ᵀ * (Z.p Q').mapMatrix Gm, ?_, ?_⟩
  · have hG1 : ∀ (g : GL (Fin n) S) i j,
        (Z.p Q').mapMatrix ((bc S.subtype g : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j ∈ Z.O Q' :=
      fun g i j => (Z.int _).1 ((g : Matrix (Fin n) (Fin n) S) i j).2 Q'
    exact gU_intM_mul _ (gU_intM_mul _ (hG1 _) fun i j => hsO _ (hW j i)) (hG1 _)
  · rw [key, map_mul, map_mul, hcT, Matrix.mul_smul, Matrix.smul_mul]

theorem gU_scal_conj {Q Q' : P} {s : Z.K Q →+* Z.K Q'} (hs : ∀ a, s (Z.p Q a) = Z.p Q' (σ a))
    (hsO : ∀ x ∈ Z.O Q, s x ∈ Z.O Q') {n : ℕ} (G : GL (Fin n) S) (m : GL (Fin n) A)
    (hm : m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) (c : (Z.K Q)ˣ)
    (x : GL (Fin n) (Z.O Q))
    (hc : (Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A) =
      (c : Z.K Q) • ((bc (Z.O Q).subtype x : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q))) :
    ∃ y : GL (Fin n) (Z.O Q'), (Z.p Q').mapMatrix (m : Matrix (Fin n) (Fin n) A) =
      (s c)⁻¹ • ((bc (Z.O Q').subtype y : GL (Fin n) (Z.K Q')) : Matrix (Fin n) (Fin n) (Z.K Q')) := by
  set X := ((bc (Z.O Q).subtype x : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hX
  set Xi := ((bc (Z.O Q).subtype x⁻¹ : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hXi
  have hXint : ∀ i j, X i j ∈ Z.O Q := fun i j => ((x : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hXiint : ∀ i j, Xi i j ∈ Z.O Q := fun i j => (((x⁻¹ : GL (Fin n) (Z.O Q)) : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hXX : Xi * X = 1 := by rw [hXi, hX, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hinv : (Z.p Q).mapMatrix ((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = (c : Z.K Q)⁻¹ • Xi := by
    show ((bc (Z.p Q) m⁻¹ : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) = _
    rw [map_inv]
    apply gU_val_inv
    show _ * (Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A) = 1
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul, hXX]
  obtain ⟨I1, hI1, e1⟩ := gU_inv_comp Z hs hsO G m hm c X hXint hc
  obtain ⟨I2, hI2, e2⟩ := gU_inv_comp Z hs hsO G m⁻¹ (inv_mem hm) ((c : Z.K Q)⁻¹) Xi hXiint hinv
  rw [inv_inv, map_inv₀] at e2
  have hsc : s c ≠ 0 := (map_ne_zero s).2 c.ne_zero
  have h2 : I2 = s c • (Z.p Q').mapMatrix (m : Matrix (Fin n) (Fin n) A) := by
    rw [e2, smul_smul, mul_inv_cancel₀ hsc, one_smul]
  have h1 : I1 = (s c)⁻¹ • (Z.p Q').mapMatrix ((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
    rw [e1, smul_smul, inv_mul_cancel₀ hsc, one_smul]
  have hprod : I2 * I1 = 1 := by
    rw [h1, h2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hsc, one_smul, ← map_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  obtain ⟨y, hy⟩ := gU_glO _ I2 I1 hI2 hI1 hprod
  exact ⟨y, by rw [hy]; exact e2⟩

end GlobalTheory.LevNorm.PlaceSys

namespace GlobalTheory.LevNorm.PlaceSys

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q}
  (Z : PlaceSys A S P k r) {σ : A →+* A}

theorem gU_good_self (hS : ∀ a ∈ S, σ a ∈ S) {Q : P} (hQ : σ (Z.e Q) = Z.e Q) {n : ℕ} (G : GL (Fin n) S)
    (m : GL (Fin n) A) (hm : m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (h : IsScal (Z.O Q) (bc (Z.p Q) m)) :
    ∃ y : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y = bc (Z.p Q) m := by
  obtain ⟨s, hs, hsO⟩ := Z.exists_conj hS hQ
  obtain ⟨c, x, hc⟩ := h
  have hc' : (Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A) =
      (c : Z.K Q) • ((bc (Z.O Q).subtype x : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) := hc
  obtain ⟨y, hy⟩ := gU_scal_conj Z hs hsO G m hm c x hc'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact ⟨1, Subsingleton.elim _ _⟩
  set X := ((bc (Z.O Q).subtype x : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hX
  set Xi := ((bc (Z.O Q).subtype x⁻¹ : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hXi
  set Y := ((bc (Z.O Q).subtype y : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hY
  set Yi := ((bc (Z.O Q).subtype y⁻¹ : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hYi
  have hXint : ∀ i j, X i j ∈ Z.O Q := fun i j => ((x : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hXiint : ∀ i j, Xi i j ∈ Z.O Q := fun i j => (((x⁻¹ : GL (Fin n) (Z.O Q)) : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hYint : ∀ i j, Y i j ∈ Z.O Q := fun i j => ((y : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hYiint : ∀ i j, Yi i j ∈ Z.O Q := fun i j => (((y⁻¹ : GL (Fin n) (Z.O Q)) : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hXXi : X * Xi = 1 := by rw [hXi, hX, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hYYi : Y * Yi = 1 := by rw [hYi, hY, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hsc : s c ≠ 0 := (map_ne_zero s).2 c.ne_zero
  set t : Z.K Q := (c : Z.K Q) * s c with ht
  have ht0 : t ≠ 0 := mul_ne_zero c.ne_zero hsc
  have hYX : t • X = Y := by
    have e : (c : Z.K Q) • X = (s c)⁻¹ • Y := hc'.symm.trans hy
    calc t • X = s c • ((c : Z.K Q) • X) := by rw [smul_smul, ht, mul_comm]
      _ = s c • ((s c)⁻¹ • Y) := by rw [e]
      _ = Y := by rw [smul_smul, mul_inv_cancel₀ hsc, one_smul]
  have hXY : t⁻¹ • Y = X := by rw [← hYX, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  let i0 : Fin n := ⟨0, hn⟩
  have htO : t ∈ Z.O Q := by
    have e : (Y * Xi) i0 i0 = t := by
      rw [← hYX, Matrix.smul_mul, hXXi, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [← e]; exact gU_intM_mul _ hYint hXiint i0 i0
  have htiO : t⁻¹ ∈ Z.O Q := by
    have e : (X * Yi) i0 i0 = t⁻¹ := by
      rw [← hXY, Matrix.smul_mul, hYYi, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [← e]; exact gU_intM_mul _ hXint hYiint i0 i0
  have hcO : (c : Z.K Q) ∈ Z.O Q ∧ (c : Z.K Q)⁻¹ ∈ Z.O Q := by
    rcases (Z.O Q).mem_or_inv_mem (c : Z.K Q) with h1 | h1
    · refine ⟨h1, ?_⟩
      have e : (c : Z.K Q)⁻¹ = s c * t⁻¹ := by
        rw [ht, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hsc, one_mul]
      rw [e]; exact mul_mem (hsO _ h1) htiO
    · refine ⟨?_, h1⟩
      have e : (c : Z.K Q) = t * (s c)⁻¹ := by rw [ht, mul_assoc, mul_inv_cancel₀ hsc, mul_one]
      have h2 : (s c)⁻¹ ∈ Z.O Q := by rw [← map_inv₀]; exact hsO _ h1
      rw [e]; exact mul_mem htO h2
  obtain ⟨y', hy'⟩ := gU_glO _ ((c : Z.K Q) • X) ((c : Z.K Q)⁻¹ • Xi) (fun i j => mul_mem hcO.1 (hXint i j))
    (fun i j => mul_mem hcO.2 (hXiint i j))
    (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ c.ne_zero, one_smul, hXXi])
  exact ⟨y', Units.ext (hy'.trans hc'.symm)⟩

theorem gU_comp_sigma (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) (Q : P) :
    ∃ R, σ (Z.e R) = Z.e Q ∧ ∃ t : Z.K R →+* Z.K Q, ∀ a, t (Z.p R a) = Z.p Q (σ a) := by
  obtain ⟨R, hR⟩ := Z.exists_bar hσ Q
  have h : σ (Z.e R) = Z.e Q := by rw [← hR, hσ]
  obtain ⟨t, ht, -⟩ := Z.exists_conj hS h
  exact ⟨R, h, t, ht⟩

end GlobalTheory.LevNorm.PlaceSys

namespace GlobalTheory.LevNorm.PlaceSys

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q}
  (Z : PlaceSys A S P k r) {σ : A →+* A}

theorem gU_step (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) {n : ℕ} (G : GL (Fin n) S)
    (m : GL (Fin n) A) (hm : m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (hscal : ∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m)) {a a' : P} (ha : σ (Z.e a) = Z.e a') (hne : a ≠ a') :
    ∃ (z : A) (m₁ : GL (Fin n) A), z * σ z = 1 ∧
      (m : Matrix (Fin n) (Fin n) A) = z • (m₁ : Matrix (Fin n) (Fin n) A) ∧
      m₁ ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧
      (∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m₁)) ∧ (∀ Q, Q ≠ a → Q ≠ a' → bc (Z.p Q) m₁ = bc (Z.p Q) m) ∧
      (∃ y : GL (Fin n) (Z.O a), bc (Z.O a).subtype y = bc (Z.p a) m₁) ∧
      (∃ y : GL (Fin n) (Z.O a'), bc (Z.O a').subtype y = bc (Z.p a') m₁) := by
  obtain ⟨s, hs, hsO⟩ := Z.exists_conj hS ha
  obtain ⟨c, x, hc⟩ := hscal a
  have hc' : (Z.p a).mapMatrix (m : Matrix (Fin n) (Fin n) A) =
      (c : Z.K a) • ((bc (Z.O a).subtype x : GL (Fin n) (Z.K a)) : Matrix (Fin n) (Fin n) (Z.K a)) := hc
  obtain ⟨y, hy⟩ := gU_scal_conj Z hs hsO G m hm c x hc'
  have hsc : s c ≠ 0 := (map_ne_zero s).2 c.ne_zero
  obtain ⟨α, hα1, hα2⟩ := Z.exists_single a ((c : Z.K a) - 1)
  obtain ⟨β, hβ1, hβ2⟩ := Z.exists_single a' ((s c)⁻¹ - 1)
  set z : A := 1 + α + β with hz
  have pa : Z.p a z = c := by rw [hz, map_add, map_add, map_one, hα1, hβ2 a hne]; ring
  have pa' : Z.p a' z = (s c)⁻¹ := by rw [hz, map_add, map_add, map_one, hα2 a' (Ne.symm hne), hβ1]; ring
  have po : ∀ Q, Q ≠ a → Q ≠ a' → Z.p Q z = 1 := fun Q h1 h2 => by
    rw [hz, map_add, map_add, map_one, hα2 Q h1, hβ2 Q h2]; ring
  have σinj : ∀ u v, σ u = σ v → u = v := fun u v h => by rw [← hσ u, h, hσ]
  have einj := Z.e_injective
  have hzz : z * σ z = 1 := by
    refine Z.ext' fun Q => ?_
    obtain ⟨R, hR, t, ht⟩ := gU_comp_sigma Z hσ hS Q
    rw [map_mul, ← ht, map_one]
    by_cases hQa : Q = a
    · subst hQa
      have hRa' : R = a' := einj (σinj _ _ (by rw [hR, ← ha, hσ]))
      subst hRa'
      obtain ⟨w, hw⟩ := Z.surj Q c
      have e : t (s c) = c := by rw [← hw, hs, ht, hσ]
      rw [pa, pa', map_inv₀, e, mul_inv_cancel₀ c.ne_zero]
    · by_cases hQa' : Q = a'
      · subst hQa'
        have hRa : R = a := einj (σinj _ _ (by rw [hR, ha]))
        subst hRa
        obtain ⟨w, hw⟩ := Z.surj R c
        have e : t c = s c := by rw [← hw, hs, ht]
        rw [pa', pa, e, inv_mul_cancel₀ hsc]
      · have hR1 : R ≠ a := fun h => hQa' (einj (by rw [← hR, h, ha]))
        have hR2 : R ≠ a' := fun h => hQa (einj (by rw [← hR, h, ← ha, hσ]))
        rw [po Q hQa hQa', po R hR1 hR2, map_one, mul_one]
  have hzz' : σ z * z = 1 := by rw [mul_comm]; exact hzz
  let m₁ : GL (Fin n) A := ⟨σ z • (m : Matrix (Fin n) (Fin n) A), z • ((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A),
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hzz', one_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hzz, one_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one]⟩
  have hm₁ : (m₁ : Matrix (Fin n) (Fin n) A) = σ z • (m : Matrix (Fin n) (Fin n) A) := rfl
  have pm : ∀ Q, (Z.p Q).mapMatrix (m₁ : Matrix (Fin n) (Fin n) A) =
      Z.p Q (σ z) • (Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A) := fun Q => by
    rw [hm₁]; exact gU_mapMatrix_smul _ _ _
  have pσ : ∀ Q, Z.p Q z * Z.p Q (σ z) = 1 := fun Q => by rw [← map_mul, hzz, map_one]
  refine ⟨z, m₁, hzz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm₁, smul_smul, hzz, one_smul]
  · show cT σ (m₁ : Matrix (Fin n) (Fin n) A) * _ * (m₁ : Matrix (Fin n) (Fin n) A) = _
    have hm' : cT σ (m : Matrix (Fin n) (Fin n) A) * ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *
        (m : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := hm
    rw [hm₁, gU_cT_smul, hσ, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hzz, one_smul, hm']
  · intro Q
    obtain ⟨cQ, xQ, hQ⟩ := hscal Q
    have h0 : Z.p Q (σ z) ≠ 0 := right_ne_zero_of_mul_eq_one (pσ Q)
    refine ⟨Units.mk0 _ h0 * cQ, xQ, ?_⟩
    show (Z.p Q).mapMatrix (m₁ : Matrix (Fin n) (Fin n) A) = _
    rw [pm, Units.val_mul, Units.val_mk0, ← smul_smul]
    exact congrArg _ hQ
  · intro Q h1 h2
    apply Units.ext
    show (Z.p Q).mapMatrix (m₁ : Matrix (Fin n) (Fin n) A) = (Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A)
    have e : Z.p Q (σ z) = 1 := by have := pσ Q; rwa [po Q h1 h2, one_mul] at this
    rw [pm, e, one_smul]
  · refine ⟨x, Units.ext ?_⟩
    show _ = (Z.p a).mapMatrix (m₁ : Matrix (Fin n) (Fin n) A)
    have e : Z.p a (σ z) = (c : Z.K a)⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pa]; exact pσ a)).symm
    rw [pm, e, hc', smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]
  · refine ⟨y, Units.ext ?_⟩
    show _ = (Z.p a').mapMatrix (m₁ : Matrix (Fin n) (Fin n) A)
    have e : Z.p a' (σ z) = s c :=
      (inv_eq_of_mul_eq_one_right (by rw [← pa']; exact pσ a')).symm.trans (inv_inv _)
    rw [pm, e, hy, smul_smul, mul_inv_cancel₀ hsc, one_smul]

theorem gU_ind (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) {n : ℕ} (G : GL (Fin n) S) (T : Finset P) :
    ∀ (m : GL (Fin n) A), m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) →
      (∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m)) →
      (∀ Q, Q ∉ T → ∃ y : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y = bc (Z.p Q) m) →
      ∃ (z : A) (x : GL (Fin n) S), z * σ z = 1 ∧
        (m : Matrix (Fin n) (Fin n) A) = z • ((bc S.subtype x : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro m _ _ hg
    obtain ⟨x, hx⟩ := Z.gl_int (fun Q => hg Q (by simp))
    exact ⟨1, x, by rw [map_one, mul_one], by rw [hx, one_smul]⟩
  | @insert a T haT ih =>
    intro m hm hscal hg
    by_cases ha : ∃ y : GL (Fin n) (Z.O a), bc (Z.O a).subtype y = bc (Z.p a) m
    · exact ih m hm hscal fun Q hQ => by
        by_cases h : Q = a
        · subst h; exact ha
        · exact hg Q (by simp [h, hQ])
    · obtain ⟨a', ha'⟩ := Z.exists_bar hσ a
      by_cases hne : a = a'
      · exact absurd (gU_good_self Z hS (by rw [ha', ← hne]) G m hm (hscal a)) ha
      · obtain ⟨z, m₁, hzz, hmz, hm₁, hs₁, heq, hga, hga'⟩ := gU_step Z hσ hS G m hm hscal ha' hne
        obtain ⟨z₂, x, hz₂, hx⟩ := ih m₁ hm₁ hs₁ fun Q hQ => by
          by_cases h1 : Q = a
          · subst h1; exact hga
          by_cases h2 : Q = a'
          · subst h2; exact hga'
          rw [heq Q h1 h2]; exact hg Q (by simp [h1, hQ])
        refine ⟨z * z₂, x, ?_, ?_⟩
        · rw [map_mul, mul_mul_mul_comm, hzz, hz₂, one_mul]
        · rw [hmz, hx, smul_smul]

end GlobalTheory.LevNorm.PlaceSys

namespace GlobalTheory.LevNorm.PlaceSys

theorem unitary_locScal_glue : ∀ {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A), (∀ a, σ (σ a) = a) → (∀ a ∈ S, σ a ∈ S) → ∀ (n : ℕ) (G : GL (Fin n) S) (m : GL (Fin n) A), m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) → (∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m) ∨ ∃ Q', σ (Z.e Q') = Z.e Q ∧ IsScal (Z.O Q') (bc (Z.p Q') m)) → ∃ (z : A) (x : GL (Fin n) S), z * σ z = 1 ∧ (m : Matrix (Fin n) (Fin n) A) = z • ((bc S.subtype x : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  intro A _ S P k _ r Z σ hσ hS n G m hm hloc
  have hscal : ∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m) := fun Q => by
    rcases hloc Q with h | ⟨Q', hQ', h⟩
    · exact h
    · obtain ⟨s, hs, hsO⟩ := Z.exists_conj hS hQ'
      obtain ⟨c, x, hc⟩ := h
      obtain ⟨y, hy⟩ := gU_scal_conj Z hs hsO G m hm c x hc
      have hsc : s c ≠ 0 := (map_ne_zero s).2 c.ne_zero
      exact ⟨(Units.mk0 _ hsc)⁻¹, y, by rw [Units.val_inv_eq_inv_val, Units.val_mk0]; exact hy⟩
  have hfin : {Q | ¬ ∃ y : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y = bc (Z.p Q) m}.Finite := by
    refine (Set.finite_iUnion (fun ij : Fin n × Fin n => (Z.fin ((m : Matrix (Fin n) (Fin n) A) ij.1 ij.2)).union
      (Z.fin (((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ij.1 ij.2)))).subset ?_
    intro Q hQ
    by_contra hc
    apply hQ
    have h1 : ∀ i j, Z.p Q ((m : Matrix (Fin n) (Fin n) A) i j) ∈ Z.O Q := fun i j =>
      by_contra fun h => hc (Set.mem_iUnion.2 ⟨(i, j), Or.inl h⟩)
    have h2 : ∀ i j, Z.p Q (((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) ∈ Z.O Q := fun i j =>
      by_contra fun h => hc (Set.mem_iUnion.2 ⟨(i, j), Or.inr h⟩)
    obtain ⟨y, hy⟩ := gU_glO _ ((Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A))
      ((Z.p Q).mapMatrix ((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) h1 h2
      (by rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
    exact ⟨y, Units.ext hy⟩
  exact gU_ind Z hσ hS G hfin.toFinset m hm hscal fun Q hQ => by
    by_contra h
    exact hQ (hfin.mem_toFinset.2 h)

end GlobalTheory.LevNorm.PlaceSys
end
end

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_scalarMulIntegral_local_to_global : ∀ {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A), (∀ a, σ (σ a) = a) → (∀ a ∈ S, σ a ∈ S) → ∀ (n : ℕ) (G : GL (Fin n) S) (m : GL (Fin n) A), m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) → (∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m) ∨ ∃ Q', σ (Z.e Q') = Z.e Q ∧ IsScal (Z.O Q') (bc (Z.p Q') m)) → ∃ (z : A) (x : GL (Fin n) S), z * σ z = 1 ∧ (m : Matrix (Fin n) (Fin n) A) = z • ((bc S.subtype x : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  atlas_forward_decl GlobalTheory.LevNorm.PlaceSys.unitary_locScal_glue
end

section
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

section Idem

variable {R : Type} [CommRing R] {n : ℕ}

theorem matrix_mul_orthogonal_three_idempotents_smul (a b c : R) (hab : a * b = 0) (hac : a * c = 0) (hbc : b * c = 0) (ha : a * a = a)
    (hb : b * b = b) (hc : c * c = c) (M₁ M₂ M₃ N₁ N₂ N₃ : Matrix (Fin n) (Fin n) R) :
    (a • M₁ + b • M₂ + c • M₃) * (a • N₁ + b • N₂ + c • N₃) = a • (M₁ * N₁) + b • (M₂ * N₂) + c • (M₃ * N₃) := by
  have hba : b * a = 0 := by rw [mul_comm]; exact hab
  have hca : c * a = 0 := by rw [mul_comm]; exact hac
  have hcb : c * b = 0 := by rw [mul_comm]; exact hbc
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hab, hac, hbc, hba, hca, hcb,
    ha, hb, hc, zero_smul, add_zero, zero_add]

theorem cT_smul' (τ : R →+* R) (a : R) (M : Matrix (Fin n) (Fin n) R) : cT τ (a • M) = τ a • cT τ M := by
  ext i j; simp [cT]

theorem cT_add' (τ : R →+* R) (M N : Matrix (Fin n) (Fin n) R) : cT τ (M + N) = cT τ M + cT τ N := by
  ext i j; simp [cT]

theorem cT_cT' (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) (M : Matrix (Fin n) (Fin n) R) : cT τ (cT τ M) = M := by
  ext i j; simp [cT, hτ]

theorem map_idem3 (a b c : R) (X Y : Matrix (Fin n) (Fin n) R) {T : Type} [CommRing T] (f : R →+* T) :
    (a • X + b • Y + c • (1 : Matrix (Fin n) (Fin n) R)).map f
      = f a • X.map f + f b • Y.map f + f c • (1 : Matrix (Fin n) (Fin n) T) := by
  ext i j; simp [Matrix.one_apply]; split_ifs <;> simp

theorem idem_split_inv (τ : R →+* R) (a b : R) (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (G Gi X Xi : Matrix (Fin n) (Fin n) R) (hG : G * Gi = 1) (hGi : Gi * G = 1) (hX : X * Xi = 1) :
    (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) *
      (a • Xi + b • (Gi * cT τ X * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
  have hac : a * (1 - a - b) = 0 := by linear_combination -ha - hab
  have hbc : b * (1 - a - b) = 0 := by linear_combination -hb - hab
  have hc : (1 - a - b) * (1 - a - b) = 1 - a - b := by linear_combination ha + hb + 2 * hab
  rw [matrix_mul_orthogonal_three_idempotents_smul a b _ hab hac hbc ha hb hc]
  have h1 : Gi * cT τ Xi * G * (Gi * cT τ X * G) = 1 := by
    calc _ = Gi * (cT τ Xi * (G * Gi) * cT τ X) * G := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG, Matrix.mul_one, ← cT_mul, hX, cT_one, Matrix.mul_one, hGi]
  rw [hX, h1, Matrix.mul_one, ← add_smul, ← add_smul, show a + b + (1 - a - b) = 1 by ring, one_smul]

theorem idem_split_unitary (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) (a b : R) (ha : a * a = a) (hb : b * b = b)
    (hab : a * b = 0) (hτa : τ a = b)
    (G Gi X Xi : Matrix (Fin n) (Fin n) R) (hG : G * Gi = 1) (hXi : Xi * X = 1) (hGh : cT τ G = G) :
    cT τ (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) * G *
      (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) = G := by
  have hac : a * (1 - a - b) = 0 := by linear_combination -ha - hab
  have hbc : b * (1 - a - b) = 0 := by linear_combination -hb - hab
  have hc : (1 - a - b) * (1 - a - b) = 1 - a - b := by linear_combination ha + hb + 2 * hab
  have hτb : τ b = a := by rw [← hτa, hτ]
  have hτc : τ (1 - a - b) = 1 - a - b := by rw [map_sub, map_sub, map_one, hτa, hτb]; ring
  have hGc : cT τ Gi * G = 1 := by
    have : cT τ Gi * cT τ G = 1 := by rw [← cT_mul, hG, cT_one]
    rwa [hGh] at this
  have hct : cT τ (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R))
      = a • (G * (Xi * cT τ Gi)) + b • cT τ X + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [cT_add', cT_add', cT_smul', cT_smul', cT_smul', hτa, hτb, hτc, cT_one, cT_mul, cT_mul, hGh, cT_cT' τ hτ]
    abel
  have hGs : G = a • G + b • G + (1 - a - b) • G := by
    rw [← add_smul, ← add_smul, show a + b + (1 - a - b) = 1 by ring, one_smul]
  rw [hct, show (a • (G * (Xi * cT τ Gi)) + b • cT τ X + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) * G
      = a • (G * (Xi * cT τ Gi) * G) + b • (cT τ X * G) + (1 - a - b) • (1 * G) by
    simp only [Matrix.add_mul, Matrix.smul_mul]]
  rw [matrix_mul_orthogonal_three_idempotents_smul a b _ hab hac hbc ha hb hc]
  have e1 : G * (Xi * cT τ Gi) * G * X = G := by
    calc _ = G * (Xi * (cT τ Gi * G) * X) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hGc, Matrix.mul_one, hXi, Matrix.mul_one]
  have e2 : cT τ X * G * (Gi * cT τ Xi * G) = G := by
    calc _ = cT τ X * (G * Gi) * cT τ Xi * G := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hG, Matrix.mul_one, ← cT_mul, hXi, cT_one, Matrix.one_mul]
  rw [e1, e2, Matrix.one_mul, Matrix.mul_one, ← hGs]

end Idem

end GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

theorem exists_unitary_int_of_component {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type}
    [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a)
    (hS : ∀ a ∈ S, σ a ∈ S) (n : ℕ) (G : GL (Fin n) S)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
      = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (Q Q' : P) (hQ : σ (Z.e Q) = Z.e Q') (hne : Q ≠ Q') (y : GL (Fin n) (Z.O Q)) :
    ∃ u : GL (Fin n) S, bc S.subtype u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧
      bc (Z.pO Q) u = y ∧ ∀ Q'', Q'' ≠ Q → Q'' ≠ Q' → bc (Z.pO Q'') u = 1 := by
  obtain ⟨x, hx1, hx2⟩ := Z.gl_single Q (bc (Z.O Q).subtype y)
  obtain ⟨X, hX⟩ := Z.gl_int (x := x) fun R => by
    by_cases h : R = Q
    · subst h; exact ⟨y, hx1.symm⟩
    · exact ⟨1, by rw [map_one, hx2 R h]⟩
  have hcomp : ∀ R, bc (Z.O R).subtype (bc (Z.pO R) X) = bc (Z.p R) x := fun R => by
    rw [← hX]; rfl
  have binj : ∀ R, Function.Injective (bc (n := Fin n) (Z.O R).subtype) := fun R g h e =>
    Units.ext (Matrix.map_injective Subtype.val_injective (congrArg Units.val e))
  have hXQ : bc (Z.pO Q) X = y := binj Q (by rw [hcomp, hx1])
  have hXR : ∀ R, R ≠ Q → bc (Z.pO R) X = 1 := fun R h => binj R (by rw [hcomp, hx2 R h, map_one])
  let τ : S →+* S := σ.restrict S S hS
  have hτv : ∀ s : S, (τ s : A) = σ s := fun s => rfl
  have hτ : ∀ s, τ (τ s) = s := fun s => Subtype.ext (by rw [hτv, hτv, hσ])
  let a : S := ⟨Z.e Q, Z.e_mem Q⟩
  let b : S := ⟨Z.e Q', Z.e_mem Q'⟩
  have ha : a * a = a := Subtype.ext (Z.e_idem Q)
  have hb : b * b = b := Subtype.ext (Z.e_idem Q')
  have hab : a * b = 0 := Subtype.ext (by
    show Z.e Q * Z.e Q' = 0
    refine Z.ext _ fun R => ?_
    rw [map_mul]
    by_cases h : R = Q
    · subst h; rw [Z.e_ne Q' R hne, mul_zero]
    · rw [Z.e_ne Q R h, zero_mul])
  have hτa : τ a = b := Subtype.ext hQ
  have hmap : ∀ M : Matrix (Fin n) (Fin n) S, (cT τ M).map S.subtype = cT σ (M.map S.subtype) := fun M => by
    ext i j; rfl
  have hGh : cT τ (G : Matrix (Fin n) (Fin n) S) = G :=
    Matrix.map_injective (f := (S.subtype : S → A)) S.subtype_injective ((hmap _).trans hG)
  let uM : Matrix (Fin n) (Fin n) S := a • (X : Matrix (Fin n) (Fin n) S) +
    b • (((G⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * cT τ ((X⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * G) +
    (1 - a - b) • (1 : Matrix (Fin n) (Fin n) S)
  let vM : Matrix (Fin n) (Fin n) S := a • ((X⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) +
    b • (((G⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * cT τ (X : Matrix (Fin n) (Fin n) S) * G) +
    (1 - a - b) • (1 : Matrix (Fin n) (Fin n) S)
  let u : GL (Fin n) S := ⟨uM, vM,
    idem_split_inv τ a b ha hb hab _ _ _ _ (Units.mul_inv G) (Units.inv_mul G) (Units.mul_inv X),
    idem_split_inv τ a b ha hb hab _ _ _ _ (Units.mul_inv G) (Units.inv_mul G) (Units.inv_mul X)⟩
  have hcompU : ∀ R, ((bc (Z.pO R) u : GL (Fin n) (Z.O R)) : Matrix (Fin n) (Fin n) (Z.O R)) =
      Z.pO R a • (X : Matrix (Fin n) (Fin n) S).map (Z.pO R) + Z.pO R b • _ + Z.pO R (1 - a - b) • 1 :=
    fun R => map_idem3 _ _ _ _ _ _
  refine ⟨u, ?_, ?_, ?_⟩
  · show cT σ (uM.map S.subtype) * (G : Matrix (Fin n) (Fin n) S).map S.subtype * uM.map S.subtype
      = (G : Matrix (Fin n) (Fin n) S).map S.subtype
    rw [← hmap, ← Matrix.map_mul, ← Matrix.map_mul,
      idem_split_unitary τ hτ a b ha hb hab hτa _ _ _ _ (Units.mul_inv G) (Units.inv_mul X) hGh]
  · have hpa : Z.pO Q a = 1 := Subtype.ext (Z.e_self Q)
    have hpb : Z.pO Q b = 0 := Subtype.ext (Z.e_ne Q' Q hne)
    refine Units.ext ?_
    rw [hcompU, map_sub, map_sub, map_one, hpa, hpb]
    simp only [one_smul, zero_smul, add_zero, sub_self]
    exact congrArg Units.val hXQ
  · intro R h1 h2
    have hpa : Z.pO R a = 0 := Subtype.ext (Z.e_ne Q R h1)
    have hpb : Z.pO R b = 0 := Subtype.ext (Z.e_ne Q' R h2)
    refine Units.ext ?_
    rw [hcompU, map_sub, map_sub, map_one, hpa, hpb]
    simp

end GlobalTheory.LevNorm
end

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_integral_of_splitPlace_component : ∀ {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A), (∀ a, σ (σ a) = a) → (∀ a ∈ S, σ a ∈ S) → ∀ (n : ℕ) (G : GL (Fin n) S), cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) → ∀ Q Q' : P, σ (Z.e Q) = Z.e Q' → Q ≠ Q' → ∀ y : GL (Fin n) (Z.O Q), ∃ u : GL (Fin n) S, bc S.subtype u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧ bc (Z.pO Q) u = y ∧ ∀ Q'', Q'' ≠ Q → Q'' ≠ Q' → bc (Z.pO Q'') u = 1 := by
  atlas_forward_decl GlobalTheory.LevNorm.exists_unitary_int_of_component
end

section
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

theorem exists_normOne_residues {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)]
    {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S)
    (T : Finset P) (hT : ∀ Q ∈ T, ∀ Q' ∈ T, σ (Z.e Q) ≠ Z.e Q') (c : ∀ Q, (k Q)ˣ) :
    ∃ z : S, (z : A) * σ z = 1 ∧ (∀ Q ∈ T, r Q z = c Q) ∧
      ∀ b : A, (∀ Q ∈ T, Z.p Q b ∈ Z.O Q ∧ Z.p Q (σ b) ∈ Z.O Q) → (1 - (z : A)) * b ∈ S := by
  classical

  have comp : ∀ (f : P → A) Q0, Z.p Q0 (∑ Q ∈ T, Z.e Q * f Q) = if Q0 ∈ T then Z.p Q0 (f Q0) else 0 := by
    intro f Q0
    rw [map_sum]
    by_cases h : Q0 ∈ T
    · rw [if_pos h, Finset.sum_eq_single_of_mem Q0 h
        (fun Q _ hQ => by rw [map_mul, Z.e_ne Q Q0 (Ne.symm hQ), zero_mul]), map_mul, Z.e_self, one_mul]
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun Q hQ => by
        rw [map_mul, Z.e_ne Q Q0 (by rintro rfl; exact h hQ), zero_mul]
  have smem : ∀ f : P → A, (∀ Q, f Q ∈ S) → (∑ Q ∈ T, Z.e Q * f Q) ∈ S := fun f hf =>
    Subring.sum_mem _ fun Q _ => Subring.mul_mem _ (Z.e_mem Q) (hf Q)

  choose s hs using fun Q => Z.r_surj Q (c Q : k Q)
  have hval : ∀ Q, (Z.O Q).valuation (Z.p Q (s Q)) = 1 := fun Q => by
    have hm : Z.p Q (s Q) ∈ Z.O Q := (Z.int _).1 (s Q).2 Q
    refine le_antisymm (((Z.O Q).valuation_le_one_iff _).2 hm) (not_lt.1 fun hc => ?_)
    have := (Z.r_ker Q (s Q)).2 hc
    rw [hs Q] at this
    exact (c Q).ne_zero this
  have hne : ∀ Q, Z.p Q (s Q) ≠ 0 := fun Q e => by
    have := hval Q; rw [e, map_zero] at this; exact zero_ne_one this
  have hinv : ∀ Q, (Z.p Q (s Q))⁻¹ ∈ Z.O Q := fun Q => by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hval Q, inv_one]
  choose t ht using fun Q => Z.pO_surj Q ⟨_, hinv Q⟩
  have hpt : ∀ Q, Z.p Q (t Q) = (Z.p Q (s Q))⁻¹ := fun Q => by
    rw [← Z.pO_coe, ht Q]

  obtain ⟨E, hEd⟩ : ∃ E, E = ∑ Q ∈ T, Z.e Q * 1 := ⟨_, rfl⟩
  obtain ⟨a, had⟩ : ∃ a, a = ∑ Q ∈ T, Z.e Q * (s Q : A) := ⟨_, rfl⟩
  obtain ⟨bb, hbd⟩ : ∃ bb, bb = ∑ Q ∈ T, Z.e Q * (t Q : A) := ⟨_, rfl⟩
  have pE : ∀ Q0, Z.p Q0 E = if Q0 ∈ T then 1 else 0 := fun Q0 => by
    rw [hEd, comp, map_one]
  have pa : ∀ Q0, Z.p Q0 a = if Q0 ∈ T then Z.p Q0 (s Q0) else 0 := fun Q0 => by rw [had, comp]
  have pb : ∀ Q0, Z.p Q0 bb = if Q0 ∈ T then Z.p Q0 (t Q0) else 0 := fun Q0 => by rw [hbd, comp]
  have pF : ∀ Q0 ∈ T, Z.p Q0 (σ E) = 0 := fun Q0 hQ0 => by
    rw [hEd, map_sum, map_sum]
    refine Finset.sum_eq_zero fun Q hQ => ?_
    obtain ⟨Q3, h3⟩ := Z.exists_bar hσ Q
    rw [map_mul, map_one, mul_one, h3, Z.e_ne Q3 Q0 (fun h => hT Q hQ Q0 hQ0 (by rw [h3, h]))]
  have Emem : E ∈ S := hEd ▸ smem _ fun _ => one_mem _
  have amem : a ∈ S := had ▸ smem _ fun Q => (s Q).2
  have bmem : bb ∈ S := hbd ▸ smem _ fun Q => (t Q).2
  have hE : E * E = E := Z.ext' fun Q0 => by rw [map_mul, pE]; split_ifs <;> simp
  have hEF : E * σ E = 0 := Z.ext' fun Q0 => by
    rw [map_mul, map_zero]
    by_cases h : Q0 ∈ T
    · rw [pF Q0 h, mul_zero]
    · rw [pE, if_neg h, zero_mul]
  have ha : E * a = a := Z.ext' fun Q0 => by rw [map_mul, pE, pa]; split_ifs <;> simp
  have hb : E * bb = bb := Z.ext' fun Q0 => by rw [map_mul, pE, pb]; split_ifs <;> simp
  have hab : a * bb = E := Z.ext' fun Q0 => by
    rw [map_mul, pE, pa, pb]
    split_ifs
    · rw [hpt, mul_inv_cancel₀ (hne Q0)]
    · simp
  set F := σ E with hFd
  set x := σ a with hxd
  set y := σ bb with hyd
  have hF : F * F = F := by rw [hFd, ← map_mul, hE]
  have hFx : F * x = x := by rw [hFd, hxd, ← map_mul, ha]
  have hFy : F * y = y := by rw [hFd, hyd, ← map_mul, hb]
  have hxy : x * y = F := by rw [hFd, hxd, hyd, ← map_mul, hab]
  have hEx : E * x = 0 := by rw [← hFx, ← mul_assoc, hEF, zero_mul]
  have hEy : E * y = 0 := by rw [← hFy, ← mul_assoc, hEF, zero_mul]
  have hFa : F * a = 0 := by rw [← ha, ← mul_assoc, mul_comm F E, hEF, zero_mul]
  have hFb : F * bb = 0 := by rw [← hb, ← mul_assoc, mul_comm F E, hEF, zero_mul]
  have hax : a * x = 0 := by
    calc a * x = (E * a) * (F * x) := by rw [ha, hFx]
      _ = (E * F) * (a * x) := by ring
      _ = 0 := by rw [hEF, zero_mul]
  have hby : bb * y = 0 := by
    calc bb * y = (E * bb) * (F * y) := by rw [hb, hFy]
      _ = (E * F) * (bb * y) := by ring
      _ = 0 := by rw [hEF, zero_mul]
  have zmem : 1 - E - F + a + y ∈ S :=
    add_mem (add_mem (sub_mem (sub_mem (one_mem _) Emem) (hS _ Emem)) amem) (hS _ bmem)
  refine ⟨⟨1 - E - F + a + y, zmem⟩, ?_, ?_, ?_⟩
  · show (1 - E - F + a + y) * σ (1 - E - F + a + y) = 1
    have hσF : σ F = E := hσ E
    have hσy : σ y = bb := hσ bb
    rw [map_add, map_add, map_sub, map_sub, map_one, hσF, hσy]
    linear_combination hE + hF + 2 * hEF - hEx - hb - hFx - hFb - ha - hFy - hFa - hEy + hax + hab + hxy + hby
  · intro Q hQ
    rw [← hs Q]
    refine Z.r_congr Q ?_
    show Z.p Q (1 - E - F + a + y) = Z.p Q (s Q)
    have hy0 : Z.p Q y = 0 := by rw [← hFy, map_mul, pF Q hQ, zero_mul]
    rw [map_add, map_add, map_sub, map_sub, map_one, pE, if_pos hQ, pF Q hQ, pa, if_pos hQ, hy0]
    ring
  · intro w hw
    show (1 - (1 - E - F + a + y)) * w ∈ S
    have key : (1 - (1 - E - F + a + y)) * w = (E - a) * w + σ ((E - bb) * σ w) := by
      rw [map_mul, map_sub, hσ w]; ring
    rw [key]
    refine add_mem ((Z.int _).2 fun Q0 => ?_) (hS _ ((Z.int _).2 fun Q0 => ?_))
    · rw [map_mul, map_sub, pE, pa]
      by_cases h : Q0 ∈ T
      · rw [if_pos h, if_pos h]
        exact Subring.mul_mem _ (sub_mem (one_mem _) ((Z.int _).1 (s Q0).2 Q0)) (hw Q0 h).1
      · rw [if_neg h, if_neg h, sub_zero, zero_mul]; exact zero_mem _
    · rw [map_mul, map_sub, pE, pb]
      by_cases h : Q0 ∈ T
      · rw [if_pos h, if_pos h]
        exact Subring.mul_mem _ (sub_mem (one_mem _) ((Z.int _).1 (t Q0).2 Q0)) (hw Q0 h).2
      · rw [if_neg h, if_neg h, sub_zero, zero_mul]; exact zero_mem _

end GlobalTheory.LevNorm
end

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normOne_with_residues_at_splitPlaces : ∀ {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A), (∀ a, σ (σ a) = a) → (∀ a ∈ S, σ a ∈ S) → ∀ (T : Finset P), (∀ Q ∈ T, ∀ Q' ∈ T, σ (Z.e Q) ≠ Z.e Q') → ∀ c : ∀ Q, (k Q)ˣ, ∃ z : S, (z : A) * σ z = 1 ∧ (∀ Q ∈ T, r Q z = c Q) ∧ ∀ b : A, (∀ Q ∈ T, Z.p Q b ∈ Z.O Q ∧ Z.p Q (σ b) ∈ Z.O Q) → (1 - (z : A)) * b ∈ S := by
  atlas_forward_decl GlobalTheory.LevNorm.exists_normOne_residues
end

section
noncomputable section

open Matrix Formalism.UG Formalism.L2.DIV

namespace GlobalTheory.LevNorm

theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {n : ℕ} (f : R →+* R') (g : R' →+* R'')
    (x : GL (Fin n) R) : bc g (bc f x) = bc (g.comp f) x := Units.ext rfl

theorem bc_injective {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ} {f : R →+* R'} (hf : Function.Injective f) :
    Function.Injective (bc (n := Fin n) f) := fun _ _ h =>
  Units.ext (Matrix.map_injective hf (congrArg Units.val h))

theorem bc_surjective {R k : Type} [CommRing R] [IsLocalRing R] [Field k] {n : ℕ} {f : R →+* k} (hf : Function.Surjective f) :
    Function.Surjective (bc (n := Fin n) f) := fun y => by
  choose j hj using hf
  have e : f.mapMatrix ((y : Matrix (Fin n) (Fin n) k).map j) = y := by ext a b; exact hj _
  haveI : IsLocalHom f := IsLocalHom.of_surjective f fun a => ⟨j a, hj a⟩
  have hu : IsUnit ((y : Matrix (Fin n) (Fin n) k).map j) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← isUnit_map_iff f, RingHom.map_det, e, ← Matrix.isUnit_iff_isUnit_det]
    exact y.isUnit
  exact ⟨hu.unit, Units.ext e⟩

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] (r : ∀ Q, S →+* k Q)
  (σ : A →+* A) {n : ℕ} (ρ κ : ℕ) (G : GL (Fin n) S) (T : Finset P) (ψ : ∀ Q, AddChar (k Q) ℂ) (a : ∀ Q, Fin n → Fin n → k Q)

def InLev (x : GL (Fin n) S) : Prop :=
  bc S.subtype x ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧ ∀ Q ∈ T, bc (r Q) x ∈ unipSym (k Q) n ρ κ

def levChr (x : GL (Fin n) S) : ℂ := ∏ Q ∈ T, ψ Q (edgeVal ρ κ (a Q) (bc (r Q) x))

def Keeps (m : GL (Fin n) A) : Prop :=
  ∀ x, InLev r σ ρ κ G T x → ∃ x', bc S.subtype x' = m * bc S.subtype x * m⁻¹ ∧ InLev r σ ρ κ G T x' ∧
    levChr r ρ κ T ψ a x' = levChr r ρ κ T ψ a x

variable {r σ ρ κ G T ψ a} (Z : PlaceSys A S P k r)

theorem bc_pO (Q : P) (x : GL (Fin n) S) : bc (Z.O Q).subtype (bc (Z.pO Q) x) = bc (Z.p Q) (bc S.subtype x) := Units.ext rfl

theorem bc_res {Q : P} {f : Z.O Q →+* k Q} (hf : ∀ s, f (Z.pO Q s) = r Q s) (x : GL (Fin n) S) :
    bc f (bc (Z.pO Q) x) = bc (r Q) x := by
  rw [bc_bc, show f.comp (Z.pO Q) = r Q from RingHom.ext hf]

theorem bc_r_one {Q : P} {x : GL (Fin n) S} (h : bc (Z.pO Q) x = 1) : bc (r Q) x = 1 := by
  obtain ⟨f, -, hf⟩ := Z.exists_res Q
  rw [← bc_res Z hf, h, map_one]

theorem pO_conj_one {Q : P} {m : GL (Fin n) A} {x x' : GL (Fin n) S} (e : bc S.subtype x' = m * bc S.subtype x * m⁻¹)
    (h : bc (Z.pO Q) x = 1) : bc (Z.pO Q) x' = 1 := by
  apply bc_injective (Z.O Q).subtype_injective
  rw [bc_pO, e, map_mul, map_mul, ← bc_pO, h, map_one, mul_one, ← map_mul, mul_inv_cancel, map_one]

theorem loc_split (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    {Q Q' : P} (h : σ (Z.e Q) = Z.e Q') (hne : Q ≠ Q') (hQ' : Q' ∉ T) {f : Z.O Q →+* k Q} (hf : ∀ s, f (Z.pO Q s) = r Q s)
    {m : GL (Fin n) A} (hm : Keeps r σ ρ κ G T ψ a m) (y : GL (Fin n) (Z.O Q)) (hy : Q ∈ T → bc f y ∈ unipSym (k Q) n ρ κ) :
    ∃ y' : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y' = bc (Z.p Q) m * bc (Z.O Q).subtype y * (bc (Z.p Q) m)⁻¹ ∧
      (Q ∈ T → bc f y' ∈ unipSym (k Q) n ρ κ ∧ ψ Q (edgeVal ρ κ (a Q) (bc f y')) = ψ Q (edgeVal ρ κ (a Q) (bc f y))) := by
  obtain ⟨u, hu, rfl, h1⟩ := GlobalTheory.T.exists_unitary_integral_of_splitPlace_component Z σ hσ hS n G hG Q Q' h hne y
  have h2 : ∀ Q'' ∈ T, Q'' ≠ Q → bc (Z.pO Q'') u = 1 := fun Q'' hT e => h1 Q'' e fun e' => hQ' (e' ▸ hT)
  obtain ⟨x', e, hx', hc⟩ := hm u ⟨hu, fun Q'' hT => by
    by_cases e : Q'' = Q
    · subst e; rw [← bc_res Z hf]; exact hy hT
    · rw [bc_r_one Z (h2 _ hT e)]; exact one_mem _⟩
  refine ⟨bc (Z.pO Q) x', by rw [bc_pO, bc_pO, e, map_mul, map_mul, map_inv], fun hT => ?_⟩
  rw [bc_res Z hf, bc_res Z hf]
  refine ⟨hx'.2 Q hT, ?_⟩
  unfold levChr at hc
  rwa [Finset.prod_eq_single_of_mem Q hT, Finset.prod_eq_single_of_mem Q hT] at hc
  · intro Q'' hT' e'
    rw [bc_r_one Z (h2 _ hT' e'), edgeVal_one, AddChar.map_zero_eq_one]
  · intro Q'' hT' e'
    rw [bc_r_one Z (pO_conj_one Z e (h2 _ hT' e')), edgeVal_one, AddChar.map_zero_eq_one]

theorem map_cT {Q Q' : P} {s : Z.K Q →+* Z.K Q'} (hs : ∀ a, s (Z.p Q a) = Z.p Q' (σ a)) (M : Matrix (Fin n) (Fin n) A) :
    (Z.p Q').mapMatrix (cT σ M) = (((Z.p Q).mapMatrix M).map s)ᵀ := by
  ext i j
  exact (hs _).symm

theorem loc_inert (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) (hn : 3 ≤ n)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    {Q : P} (h : σ (Z.e Q) = Z.e Q) (hQ : Q ∉ T) (δ : S) (hδ : r Q (δ - ⟨σ δ, hS _ δ.2⟩) ≠ 0)
    {m : GL (Fin n) A} (hm : Keeps r σ ρ κ G T ψ a m) : IsScal (Z.O Q) (bc (Z.p Q) m) := by
  obtain ⟨s, hs, hsO⟩ := Z.exists_conj hS h
  obtain ⟨f, hf0, hf⟩ := Z.exists_res Q
  let t : Z.O Q →+* Z.O Q := (s.comp (Z.O Q).subtype).codRestrict (Z.O Q) fun x => hsO _ x.2
  have ht : ∀ x : S, t (Z.pO Q x) = Z.pO Q ⟨σ x, hS _ x.2⟩ := fun x => Subtype.ext (hs _)
  have htt : ∀ x, t (t x) = x := fun x => by
    obtain ⟨x, rfl⟩ := Z.pO_surj Q x
    rw [ht, ht]
    exact congrArg _ (Subtype.ext (hσ _))
  haveI : IsLocalHom f := IsLocalHom.of_surjective f hf0
  have hδ' : IsUnit (Z.pO Q δ - t (Z.pO Q δ)) := by
    rw [ht, ← map_sub, ← isUnit_map_iff f, hf]
    exact hδ.isUnit
  have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) (Z.O Q) => M.map (Z.O Q).subtype :=
    Matrix.map_injective (Z.O Q).subtype_injective
  have hgen := GlobalTheory.T.adjoin_unitaryGroup_hermitian_local_eq_top (Z.O Q) t htt ⟨_, hδ'⟩ n hn ((bc (Z.pO Q) G : GL (Fin n) (Z.O Q)) : Matrix (Fin n) (Fin n) (Z.O Q))
    (inj ((map_cT Z hs _).symm.trans (congrArg (Z.p Q).mapMatrix hG))) (Units.isUnit _)
  refine GlobalTheory.T.isScalarMulIntegral_of_conj_integral_generators _ _ n _ _ hgen fun y hy => ?_
  obtain ⟨x, hx1, hx2⟩ := Z.gl_single Q (bc (Z.O Q).subtype y)
  obtain ⟨u, rfl⟩ := Z.gl_int (x := x) fun Q' => by
    by_cases e : Q' = Q
    · subst e; exact ⟨y, hx1.symm⟩
    · exact ⟨1, by rw [hx2 _ e, map_one]⟩
  have hu1 : bc (Z.pO Q) u = y := bc_injective (Z.O Q).subtype_injective hx1
  have hu2 : ∀ Q', Q' ≠ Q → bc (Z.pO Q') u = 1 := fun Q' e =>
    bc_injective (Z.O Q').subtype_injective (by rw [bc_pO, hx2 _ e, map_one])
  have hU : bc S.subtype u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
    refine Matrix.ext fun i j => Z.ext' fun Q' => ?_
    refine congrFun (congrFun (show (Z.p Q').mapMatrix _ = (Z.p Q').mapMatrix _ from ?_) i) j
    rw [map_mul, map_mul]
    by_cases e : Q' = Q
    · subst e
      rw [map_cT Z hs]
      have h3 : (Z.p Q').mapMatrix ((bc S.subtype u : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) =
        (Z.O Q').subtype.mapMatrix (y : Matrix (Fin n) (Fin n) (Z.O Q')) := congrArg Units.val hx1
      have h4 := congrArg (Z.O Q').subtype.mapMatrix (show cT t _ * _ * _ = _ from hy)
      rw [map_mul, map_mul] at h4
      rw [h3]
      exact h4
    · obtain ⟨Q₁, h1⟩ := Z.exists_bar hσ Q'
      have h1' : σ (Z.e Q₁) = Z.e Q' := by rw [← h1, hσ]
      obtain ⟨s', hs', -⟩ := Z.exists_conj hS h1'
      have e1 : Q₁ ≠ Q := fun e' => e (Z.e_injective (by rw [← h1', e', h]))
      have h3 : ∀ Q'', Q'' ≠ Q → (Z.p Q'').mapMatrix ((bc S.subtype u : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 :=
        fun Q'' e' => congrArg Units.val (hx2 Q'' e')
      rw [map_cT Z hs', h3 _ e, h3 _ e1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, one_mul, mul_one]
  obtain ⟨x', e, -, -⟩ := hm u ⟨hU, fun Q' hT => by
    rw [bc_r_one Z (hu2 _ fun e => hQ (e ▸ hT))]; exact one_mem _⟩
  exact ⟨bc (Z.pO Q) x', by rw [bc_pO, ← hu1, bc_pO, e, map_mul, map_mul, map_inv]⟩

theorem conj_of_smul {R : Type} [CommRing R] {z z' : R} (hz : z * z' = 1) {m x : GL (Fin n) R}
    (h : (m : Matrix (Fin n) (Fin n) R) = z • (x : Matrix (Fin n) (Fin n) R)) (y : GL (Fin n) R) :
    m * y * m⁻¹ = x * y * x⁻¹ ∧ m⁻¹ * y * m = x⁻¹ * y * x := by
  have h1 : ∀ y : GL (Fin n) R, (m * x⁻¹) * y = y * (m * x⁻¹) := fun y => Units.ext (by
    simp only [Units.val_mul, h, Matrix.smul_mul, Matrix.mul_smul, Units.mul_inv, Matrix.one_mul, Matrix.mul_one])
  obtain ⟨w, rfl⟩ : ∃ w, m = w * x := ⟨m * x⁻¹, by group⟩
  rw [mul_inv_cancel_right] at h1
  constructor
  · calc _ = w * (x * y * x⁻¹) * w⁻¹ := by group
      _ = _ := by rw [h1]; group
  · calc _ = x⁻¹ * (w⁻¹ * (y * w)) * x := by group
      _ = _ := by rw [← h1]; group

theorem normaliser_core (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (hT : ∀ Q ∈ T, ∀ Q' ∈ T, σ (Z.e Q) ≠ Z.e Q')
    (hun : ∀ Q, σ (Z.e Q) = Z.e Q → ∃ δ : S, r Q (δ - ⟨σ δ, hS _ δ.2⟩) ≠ 0)
    (hψ : ∀ Q ∈ T, ψ Q ≠ 1) (ha : ∀ Q ∈ T, ∀ i j, symEdge ρ κ i j → a Q i j ≠ 0)
    {m : GL (Fin n) A} (hU : m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (hm : Keeps r σ ρ κ G T ψ a m) (hm' : Keeps r σ ρ κ G T ψ a m⁻¹) :
    ∃ (z : A) (c : S) (x : GL (Fin n) S), z * σ z = 1 ∧ (c : A) * σ c = 1 ∧
      (∀ b : A, (∀ Q ∈ T, Z.p Q b ∈ Z.O Q ∧ Z.p Q (σ b) ∈ Z.O Q) → (1 - (c : A)) * b ∈ S) ∧
      (m : Matrix (Fin n) (Fin n) A) = z • ((bc S.subtype x : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧
      ∀ Q ∈ T, ∃ h ∈ unipSym (k Q) n ρ κ,
        ((bc (r Q) x : GL (Fin n) (k Q)) : Matrix (Fin n) (Fin n) (k Q)) = midDiag n ρ κ 1 (r Q c) * (h : Matrix (Fin n) (Fin n) (k Q)) := by
  classical
  choose bar hbar using Z.exists_bar hσ
  choose f hf0 hf using Z.exists_res
  have hb1 : ∀ Q ∈ T, Q ≠ bar Q := fun Q hQ e => hT Q hQ Q hQ (by rw [hbar, ← e])
  have hb2 : ∀ Q ∈ T, bar Q ∉ T := fun Q hQ e => hT Q hQ _ e (hbar Q)
  have hscT : ∀ Q ∈ T, IsScal (Z.O Q) (bc (Z.p Q) m) := fun Q hQ =>
    GlobalTheory.T.isScalarMul_integral_of_normalizes_symmetricLevel _ _ _ (f Q) (hf0 Q) n ρ κ hn hρ (ψ Q) (hψ Q hQ) (a Q) (ha Q hQ) _
      (fun y hy => by
        obtain ⟨y', h1, h2⟩ := loc_split Z hσ hS hG (hbar Q) (hb1 Q hQ) (hb2 Q hQ) (hf Q) hm y fun _ => hy
        exact ⟨y', h1, (h2 hQ).2⟩)
      (fun y hy => by
        obtain ⟨y', h1, -⟩ := loc_split Z hσ hS hG (hbar Q) (hb1 Q hQ) (hb2 Q hQ) (hf Q) hm' y fun _ => hy
        exact ⟨y', by rwa [map_inv, inv_inv] at h1⟩)
  obtain ⟨z₁, x₁, hz₁, hx₁⟩ := GlobalTheory.T.unitary_scalarMulIntegral_local_to_global Z σ hσ hS n G m hU fun Q => by
    by_cases hQ : Q ∈ T
    · exact Or.inl (hscT Q hQ)
    by_cases hQ' : bar Q ∈ T
    · exact Or.inr ⟨bar Q, by rw [← hbar, hσ], hscT _ hQ'⟩
    left
    by_cases e : Q = bar Q
    · have h1 : σ (Z.e Q) = Z.e Q := by rw [hbar, ← e]
      obtain ⟨δ, hδ⟩ := hun Q h1
      exact loc_inert Z hσ hS (by omega) hG h1 hQ δ hδ hm
    · refine GlobalTheory.T.isScalarMulIntegral_of_conj_integral_generators _ _ n _ _ (GlobalTheory.T.adjoin_range_GL_eq_top_matrix _ n) fun y _ => ?_
      obtain ⟨y', h1, -⟩ := loc_split Z hσ hS hG (hbar Q) e hQ' (hf Q) hm y fun h => absurd h hQ
      exact ⟨y', h1⟩
  have red : ∀ x : GL (Fin n) S, Keeps r σ ρ κ G T ψ a (bc S.subtype x) → ∀ Q ∈ T, ∀ h ∈ unipSym (k Q) n ρ κ,
      bc (r Q) x * h * (bc (r Q) x)⁻¹ ∈ unipSym (k Q) n ρ κ ∧
        ψ Q (edgeVal ρ κ (a Q) (bc (r Q) x * h * (bc (r Q) x)⁻¹)) = ψ Q (edgeVal ρ κ (a Q) h) := by
    intro x hx Q hQ h hh
    obtain ⟨y, rfl⟩ := bc_surjective (hf0 Q) h
    obtain ⟨y', h1, h2⟩ := loc_split Z hσ hS hG (hbar Q) (hb1 Q hQ) (hb2 Q hQ) (hf Q) hx y fun _ => hh
    have h3 : y' = bc (Z.pO Q) x * y * (bc (Z.pO Q) x)⁻¹ :=
      bc_injective (Z.O Q).subtype_injective (by rw [h1, map_mul, map_mul, map_inv, bc_pO])
    have h4 := h2 hQ
    rwa [h3, map_mul, map_mul, map_inv, bc_res Z (hf Q)] at h4
  have k1 : Keeps r σ ρ κ G T ψ a (bc S.subtype x₁) := fun x hx => by
    obtain ⟨x', h1, h2⟩ := hm x hx
    exact ⟨x', by rw [h1, (conj_of_smul hz₁ hx₁ _).1], h2⟩
  have k2 : Keeps r σ ρ κ G T ψ a (bc S.subtype x₁⁻¹) := fun x hx => by
    obtain ⟨x', h1, h2⟩ := hm' x hx
    exact ⟨x', by rw [h1, map_inv, inv_inv, inv_inv, (conj_of_smul hz₁ hx₁ _).2], h2⟩
  have fin : ∀ Q, ∃ s c : (k Q)ˣ, Q ∈ T → ∃ h ∈ unipSym (k Q) n ρ κ,
      ((bc (r Q) x₁ : GL (Fin n) (k Q)) : Matrix (Fin n) (Fin n) (k Q)) =
        midDiag n ρ κ (s : k Q) (c : k Q) * (h : Matrix (Fin n) (Fin n) (k Q)) := fun Q => by
    by_cases hQ : Q ∈ T
    · obtain ⟨s, c, h⟩ := GlobalTheory.T.normaliser_unipSym_char_pattern (k Q) n ρ κ hn hρ hκ (ψ Q) (hψ Q hQ) (a Q) (ha Q hQ) _ (red x₁ k1 Q hQ) fun h hh => by
        have := (red _ k2 Q hQ h hh).1
        rwa [map_inv, inv_inv] at this
      exact ⟨s, c, fun _ => h⟩
    · exact ⟨1, 1, fun h => absurd h hQ⟩
  choose s c hsc using fin
  obtain ⟨z₂, hz₂, hr₂, -⟩ := GlobalTheory.T.exists_normOne_with_residues_at_splitPlaces Z σ hσ hS T hT s
  obtain ⟨c', hc', hrc, hsup⟩ := GlobalTheory.T.exists_normOne_with_residues_at_splitPlaces Z σ hσ hS T hT fun Q => (s Q)⁻¹ * c Q
  let w : S := ⟨σ z₂, hS _ z₂.2⟩
  have hw : z₂ * w = 1 := Subtype.ext hz₂
  have hw' : w * z₂ = 1 := by rw [mul_comm, hw]
  refine ⟨z₁ * z₂, c', ⟨w • x₁.1, z₂ • (x₁⁻¹).1, ?_, ?_⟩, ?_, hc', hsup, ?_, fun Q hQ => ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hw', Units.mul_inv, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hw, Units.inv_mul, one_smul]
  · rw [map_mul, mul_mul_mul_comm, hz₁, hz₂, one_mul]
  · rw [hx₁]
    ext i j
    show z₁ * _ = z₁ * z₂ * (σ z₂ * (x₁.1 i j : A))
    rw [mul_assoc, ← mul_assoc (z₂ : A), hz₂, one_mul]
    rfl
  · obtain ⟨h, hh, e⟩ := hsc Q hQ
    refine ⟨h, hh, ?_⟩
    have h1 : r Q w = ((s Q)⁻¹ : (k Q)ˣ) := by
      have := congrArg (r Q) hw
      rw [map_mul, map_one, hr₂ Q hQ] at this
      exact (Units.inv_eq_of_mul_eq_one_right this).symm
    ext i j
    have e' := congrFun (congrFun e i) j
    show r Q (w * x₁.1 i j) = _
    rw [map_mul, show r Q (x₁.1 i j) = _ from e', h1, hrc Q hQ]
    simp only [midDiag, Matrix.diagonal_mul]
    split_ifs
    · rw [Units.val_mul, mul_assoc]
    · rw [← mul_assoc, Units.inv_mul]

end GlobalTheory.LevNorm

end
end
