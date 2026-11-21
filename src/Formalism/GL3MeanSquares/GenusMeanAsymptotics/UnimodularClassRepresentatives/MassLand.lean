import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandA
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandG
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt

section
open Module Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.QuadAdj

variable {F : Type*} [Field F] (c : F)

theorem monic_pol : (X ^ 2 - C c : F[X]).Monic := monic_X_pow_sub_C c two_ne_zero

theorem natDegree_pol : (X ^ 2 - C c : F[X]).natDegree = 2 := natDegree_X_pow_sub_C

theorem root_mul_root :
    AdjoinRoot.root (X ^ 2 - C c) * AdjoinRoot.root (X ^ 2 - C c) = AdjoinRoot.of (X ^ 2 - C c) c := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C c)
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  linear_combination h

theorem exists_rep (y : AdjoinRoot (X ^ 2 - C c)) :
    ∃ a b : F, y = AdjoinRoot.of _ a + AdjoinRoot.of _ b * AdjoinRoot.root _ := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective y
  have h1 : AdjoinRoot.mk (X ^ 2 - C c) f = AdjoinRoot.mk (X ^ 2 - C c) (f %ₘ (X ^ 2 - C c)) := by
    rw [AdjoinRoot.mk_eq_mk, modByMonic_eq_sub_mul_div]
    exact ⟨f /ₘ (X ^ 2 - C c), by ring⟩
  have h2 : (f %ₘ (X ^ 2 - C c)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt f (monic_pol c) (by
      intro h
      have := natDegree_pol c
      rw [h, natDegree_one] at this
      omega)
    rw [natDegree_pol] at this
    omega
  obtain ⟨b, a, hab⟩ := exists_eq_X_add_C_of_natDegree_le_one h2
  refine ⟨a, b, ?_⟩
  rw [h1, hab, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, add_comm]

theorem rep_eq_zero {a b : F}
    (h : AdjoinRoot.of (X ^ 2 - C c) a + AdjoinRoot.of _ b * AdjoinRoot.root _ = 0) :
    a = 0 ∧ b = 0 := by
  have h1 : AdjoinRoot.mk (X ^ 2 - C c) (C b * X + C a) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, add_comm]
    exact h
  by_contra hne
  have h0 : (C b * X + C a : F[X]) ≠ 0 := by
    intro h0
    apply hne
    have ha := congrArg (fun p => coeff p 0) h0
    have hb := congrArg (fun p => coeff p 1) h0
    simp at ha hb
    exact ⟨ha, hb⟩
  refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_pol c) h0 ?_ h1
  rw [natDegree_pol]
  exact lt_of_le_of_lt natDegree_linear_le one_lt_two

theorem rep_inj {a b a' b' : F}
    (h : AdjoinRoot.of (X ^ 2 - C c) a + AdjoinRoot.of _ b * AdjoinRoot.root _ =
      AdjoinRoot.of _ a' + AdjoinRoot.of _ b' * AdjoinRoot.root _) : a = a' ∧ b = b' := by
  have := rep_eq_zero c (a := a - a') (b := b - b') (by
    rw [map_sub, map_sub]; linear_combination h)
  exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩

instance finite_adj : Module.Finite F (AdjoinRoot (X ^ 2 - C c)) := (monic_pol c).finite_adjoinRoot

theorem finrank_adj : finrank F (AdjoinRoot (X ^ 2 - C c)) = 2 := by
  rw [(AdjoinRoot.powerBasis' (monic_pol c)).finrank, AdjoinRoot.powerBasis'_dim, natDegree_pol]

def conjHom : AdjoinRoot (X ^ 2 - C c) →ₐ[F] AdjoinRoot (X ^ 2 - C c) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId F _) (-AdjoinRoot.root _) (by
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    have h := root_mul_root c
    show (-AdjoinRoot.root _) ^ 2 - AdjoinRoot.of _ c = 0
    linear_combination h)

theorem conjHom_root : conjHom c (AdjoinRoot.root _) = -AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

def conj : AdjoinRoot (X ^ 2 - C c) ≃ₐ[F] AdjoinRoot (X ^ 2 - C c) :=
  AlgEquiv.ofAlgHom (conjHom c) (conjHom c)
    (AdjoinRoot.algHom_ext (by
      rw [AlgHom.comp_apply, conjHom_root, map_neg, conjHom_root, neg_neg, AlgHom.id_apply]))
    (AdjoinRoot.algHom_ext (by
      rw [AlgHom.comp_apply, conjHom_root, map_neg, conjHom_root, neg_neg, AlgHom.id_apply]))

theorem conj_root : conj c (AdjoinRoot.root _) = -AdjoinRoot.root _ := conjHom_root c

section

variable [Fact (Irreducible (X ^ 2 - C c : F[X]))]

theorem gal_root (τ : AdjoinRoot (X ^ 2 - C c) ≃ₐ[F] AdjoinRoot (X ^ 2 - C c)) :
    τ (AdjoinRoot.root _) = AdjoinRoot.root _ ∨ τ (AdjoinRoot.root _) = -AdjoinRoot.root _ := by
  have h := congrArg τ (root_mul_root c)
  have hc : τ (AdjoinRoot.of _ c) = AdjoinRoot.of _ c := τ.commutes c
  rw [map_mul, hc, ← root_mul_root c] at h
  have h2 : (τ (AdjoinRoot.root _) - AdjoinRoot.root (X ^ 2 - C c)) *
      (τ (AdjoinRoot.root _) + AdjoinRoot.root _) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact Or.inl (sub_eq_zero.1 h3)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h3)

theorem gal_cases (τ : AdjoinRoot (X ^ 2 - C c) ≃ₐ[F] AdjoinRoot (X ^ 2 - C c)) :
    τ = 1 ∨ τ = conj c := by
  rcases gal_root c τ with h | h
  · left
    apply AlgEquiv.coe_toAlgHom_injective
    exact AdjoinRoot.algHom_ext h
  · right
    apply AlgEquiv.coe_toAlgHom_injective
    exact AdjoinRoot.algHom_ext (h.trans (conj_root c).symm)

variable [CharZero F]

instance isGalois_adj : IsGalois F (AdjoinRoot (X ^ 2 - C c)) := by
  have : Algebra.IsQuadraticExtension F (AdjoinRoot (X ^ 2 - C c)) := ⟨finrank_adj c⟩
  infer_instance

end

end Formalism.HermitianLattices.Ext.L3.QuadAdj
end
end

section
open NumberField Module Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def skewSq (w : K) (hw : star w = -w) : cmF K :=
  ⟨w * w, (mem_cmF_iff K _).2 (by rw [star_mul', hw]; ring)⟩

abbrev polE (d : cmF K) : (cmF K)[X] := X ^ 2 - C d

abbrev Ed (d : cmF K) : Type := AdjoinRoot (polE d)

abbrev polKE (d δ : cmF K) : (Ed d)[X] := X ^ 2 - C (algebraMap (cmF K) (Ed d) δ)

abbrev KEd (d δ : cmF K) : Type := AdjoinRoot (polKE d δ)

section

variable (d δ : cmF K) [Fact (Irreducible (polE d))] [Fact (Irreducible (polKE d δ))]

instance numberField_Ed : NumberField (Ed d) :=
  NumberField.of_module_finite (cmF K) (Ed d)

instance numberField_KEd : NumberField (KEd d δ) :=
  NumberField.of_module_finite (Ed d) (KEd d δ)

instance finiteDimensional_KEd : FiniteDimensional (Ed d) (KEd d δ) :=
  QuadAdj.finite_adj _

instance isScalarTower_KEd : IsScalarTower (cmF K) (Ed d) (KEd d δ) :=
  inferInstance

instance isGalois_KEd : IsGalois (Ed d) (KEd d δ) :=
  QuadAdj.isGalois_adj _

end

def reF (x : K) : cmF K :=
  ⟨(x + star x) / 2, (mem_cmF_iff K _).2 (by rw [star_div₀, star_add, star_star, star_ofNat]; ring)⟩

def imF (w : K) (hw : star w = -w) (x : K) : cmF K :=
  ⟨(x - star x) / (2 * w), (mem_cmF_iff K _).2 (by
    rw [star_div₀, star_sub, star_star, star_mul', hw, star_ofNat]; ring)⟩

theorem reF_add (x y : K) : reF (x + y) = reF x + reF y := by
  apply Subtype.ext
  show (x + y + star (x + y)) / 2 = (x + star x) / 2 + (y + star y) / 2
  rw [star_add]; ring

theorem imF_add (w : K) (hw : star w = -w) (x y : K) :
    imF w hw (x + y) = imF w hw x + imF w hw y := by
  apply Subtype.ext
  show (x + y - star (x + y)) / (2 * w) = (x - star x) / (2 * w) + (y - star y) / (2 * w)
  rw [star_add]; ring

theorem reF_coe (a : cmF K) : reF (a : K) = a := by
  apply Subtype.ext
  show ((a : K) + star (a : K)) / 2 = a
  rw [star_coe_cmF]; ring

theorem imF_coe (w : K) (hw : star w = -w) (a : cmF K) : imF w hw (a : K) = 0 := by
  apply Subtype.ext
  show ((a : K) - star (a : K)) / (2 * w) = 0
  rw [star_coe_cmF, sub_self, zero_div]

theorem reF_star (x : K) : reF (star x) = reF x := by
  apply Subtype.ext
  show (star x + star (star x)) / 2 = (x + star x) / 2
  rw [star_star, add_comm]

theorem imF_star (w : K) (hw : star w = -w) (x : K) : imF w hw (star x) = -imF w hw x := by
  apply Subtype.ext
  show (star x - star (star x)) / (2 * w) = -((x - star x) / (2 * w))
  rw [star_star]; ring

theorem reF_mul (w : K) (hw0 : w ≠ 0) (hw : star w = -w) (x y : K) :
    reF (x * y) = reF x * reF y + skewSq w hw * (imF w hw x * imF w hw y) := by
  apply Subtype.ext
  show (x * y + star (x * y)) / 2 = (x + star x) / 2 * ((y + star y) / 2) +
    w * w * ((x - star x) / (2 * w) * ((y - star y) / (2 * w)))
  rw [star_mul']
  field_simp
  ring

theorem imF_mul (w : K) (hw0 : w ≠ 0) (hw : star w = -w) (x y : K) :
    imF w hw (x * y) = reF x * imF w hw y + imF w hw x * reF y := by
  apply Subtype.ext
  show (x * y - star (x * y)) / (2 * w) = (x + star x) / 2 * ((y - star y) / (2 * w)) +
    (x - star x) / (2 * w) * ((y + star y) / 2)
  rw [star_mul']
  field_simp
  ring

theorem skew_ne_zero_of_irreducible (w : K) (hw : star w = -w) (d : cmF K)
    [Fact (Irreducible (polE d))] [Fact (Irreducible (polKE d (skewSq w hw)))] : w ≠ 0 := by
  rintro rfl
  have hr := QuadAdj.root_mul_root (algebraMap (cmF K) (Ed d) (skewSq 0 hw))
  have h0 : skewSq (0 : K) hw = 0 := Subtype.ext (mul_zero _)
  have hz : algebraMap (cmF K) (Ed d) (skewSq 0 hw) = 0 := by rw [h0, map_zero]
  have hr0 := mul_self_eq_zero.1 (hr.trans ((congrArg (AdjoinRoot.of _) hz).trans (map_zero _)))
  have := QuadAdj.rep_eq_zero (algebraMap (cmF K) (Ed d) (skewSq 0 hw)) (a := 0) (b := 1) (by
    rw [map_zero, map_one, hr0]; ring)
  exact one_ne_zero this.2

section

variable (w : K) (hw0 : w ≠ 0) (hw : star w = -w) (d : cmF K) [Fact (Irreducible (polE d))]
  [Fact (Irreducible (polKE d (skewSq w hw)))]

def ιK : K →ₐ[cmF K] KEd d (skewSq w hw) where
  toFun x := algebraMap (cmF K) (KEd d (skewSq w hw))
      ⟨(x + star x) / 2, (mem_cmF_iff K _).2 (by rw [star_div₀, star_add, star_star, star_ofNat]; ring)⟩ +
    algebraMap (cmF K) (KEd d (skewSq w hw))
      ⟨(x - star x) / (2 * w), (mem_cmF_iff K _).2 (by
        rw [star_div₀, star_sub, star_star, star_mul', hw, star_ofNat]; ring)⟩ *
      AdjoinRoot.root (polKE d (skewSq w hw))
  map_one' := by
    show algebraMap (cmF K) (KEd d (skewSq w hw)) (reF 1) +
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw 1) * AdjoinRoot.root _ = 1
    have h1 : (1 : K) = ((1 : cmF K) : K) := rfl
    rw [h1, reF_coe, imF_coe, map_one, map_zero, zero_mul, add_zero]
  map_mul' x y := by
    show algebraMap (cmF K) (KEd d (skewSq w hw)) (reF (x * y)) +
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw (x * y)) * AdjoinRoot.root _ =
      (algebraMap (cmF K) (KEd d (skewSq w hw)) (reF x) +
        algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw x) * AdjoinRoot.root _) *
      (algebraMap (cmF K) (KEd d (skewSq w hw)) (reF y) +
        algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw y) * AdjoinRoot.root _)
    have hw0' := skew_ne_zero_of_irreducible w hw d
    have hr : AdjoinRoot.root (polKE d (skewSq w hw)) * AdjoinRoot.root (polKE d (skewSq w hw)) =
        algebraMap (cmF K) (KEd d (skewSq w hw)) (skewSq w hw) :=
      QuadAdj.root_mul_root (algebraMap (cmF K) (Ed d) (skewSq w hw))
    rw [reF_mul w hw0' hw, imF_mul w hw0' hw]
    simp only [map_add, map_mul]
    linear_combination (-(algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw x) *
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw y))) * hr
  map_zero' := by
    show algebraMap (cmF K) (KEd d (skewSq w hw)) (reF 0) +
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw 0) * AdjoinRoot.root _ = 0
    have h1 : (0 : K) = ((0 : cmF K) : K) := rfl
    rw [h1, reF_coe, imF_coe, map_zero, zero_mul, add_zero]
  map_add' x y := by
    show algebraMap (cmF K) (KEd d (skewSq w hw)) (reF (x + y)) +
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw (x + y)) * AdjoinRoot.root _ =
      (algebraMap (cmF K) (KEd d (skewSq w hw)) (reF x) +
        algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw x) * AdjoinRoot.root _) +
      (algebraMap (cmF K) (KEd d (skewSq w hw)) (reF y) +
        algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw y) * AdjoinRoot.root _)
    rw [reF_add, imF_add, map_add, map_add]
    ring
  commutes' r := by
    show algebraMap (cmF K) (KEd d (skewSq w hw)) (reF (r : K)) +
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw (r : K)) * AdjoinRoot.root _ =
      algebraMap (cmF K) (KEd d (skewSq w hw)) r
    rw [reF_coe, imF_coe, map_zero, zero_mul, add_zero]

theorem ιK_apply (x : K) : ιK w hw d x = algebraMap (cmF K) (KEd d (skewSq w hw)) (reF x) +
    algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw x) *
      AdjoinRoot.root (polKE d (skewSq w hw)) := rfl

theorem gal_KEd_algebraMap (τ : KEd d (skewSq w hw) ≃ₐ[Ed d] KEd d (skewSq w hw)) (a : cmF K) :
    τ (algebraMap (cmF K) (KEd d (skewSq w hw)) a) = algebraMap (cmF K) (KEd d (skewSq w hw)) a :=
  τ.commutes (algebraMap (cmF K) (Ed d) a)

theorem gal_KEd_ιK_of_neg (τ : KEd d (skewSq w hw) ≃ₐ[Ed d] KEd d (skewSq w hw))
    (h : τ (AdjoinRoot.root (polKE d (skewSq w hw))) = -AdjoinRoot.root (polKE d (skewSq w hw)))
    (x : K) : τ (ιK w hw d x) = ιK w hw d (star x) := by
  rw [ιK_apply, ιK_apply, map_add, map_mul, gal_KEd_algebraMap, gal_KEd_algebraMap, h, reF_star,
    imF_star, map_neg]
  ring

theorem gal_KEd_ιK (τ : KEd d (skewSq w hw) ≃ₐ[Ed d] KEd d (skewSq w hw)) :
    (∀ x : K, τ (ιK w hw d x) = ιK w hw d x) ∨ ∀ x : K, τ (ιK w hw d x) = ιK w hw d (star x) := by
  rcases QuadAdj.gal_root (algebraMap (cmF K) (Ed d) (skewSq w hw)) τ with h | h
  · left
    intro x
    rw [ιK_apply, map_add, map_mul, gal_KEd_algebraMap, gal_KEd_algebraMap, h]
  · right
    exact gal_KEd_ιK_of_neg w hw d τ h

end

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem gram_eq_conjTranspose_mul {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (b b' : Basis (Fin n) K V) :
    gram h b = (b'.toMatrix b).conjTranspose * gram h b' * b'.toMatrix b := by
  ext i j
  simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Basis.toMatrix_apply]
  conv_lhs => rw [← b'.sum_repr (b i), ← b'.sum_repr (b j)]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem gram_det_change {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {n : ℕ}
    (h : V →ₗ⋆[K] V →ₗ[K] K) (b b' : Basis (Fin n) K V) :
    (gram h b).det = star (b'.det b) * b'.det b * (gram h b').det := by
  rw [gram_eq_conjTranspose_mul h b b', Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Basis.det_apply]
  ring

end Formalism.HermitianLattices.Ext.L3
end
end

section
open Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LandL

theorem det_mem_subring {K : Type*} [Field K] (A : Subring K) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, M i j ∈ A) : M.det ∈ A := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => h _ _) _

theorem gram_det_unit {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (A : Subring K) (hA : ∀ x ∈ A, star x ∈ A) (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
    (g : Basis (Fin n) K V)
    (hdual : ∀ x : V, (∀ y : V, (∀ i, g.repr y i ∈ A) → h y x ∈ A) ↔ ∀ i, g.repr x i ∈ A)
    (h0 : (gram h g).det ≠ 0) : (gram h g).det ∈ A ∧ ((gram h g).det)⁻¹ ∈ A := by
  classical
  have hg : ∀ j i, g.repr (g j) i ∈ A := by
    intro j i
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact A.one_mem
    · exact A.zero_mem
  refine ⟨det_mem_subring A _ fun i j => (hdual (g j)).2 (hg j) (g i) (hg i), ?_⟩
  set G := gram h g with hG
  have hmul : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.2 h0)
  have key : ∀ y j, h y (∑ i, G⁻¹ i j • g i) = star (g.repr y j) := by
    intro y j
    conv_lhs => rw [← g.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_smul, starRingEnd_apply]
    have h2 : ∀ k, ∑ i, star (g.repr y k) * (G⁻¹ i j * h (g k) (g i))
        = star (g.repr y k) * (1 : Matrix (Fin n) (Fin n) K) k j := by
      intro k
      rw [← hmul, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hG]
      simp only [gram, Matrix.of_apply]
      ring
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h3 : ∀ k, ∑ i, G⁻¹ i j * (star (g.repr y k) * h (g k) (g i))
        = star (g.repr y k) * (1 : Matrix (Fin n) (Fin n) K) k j := by
      intro k
      rw [← h2 k]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [Finset.sum_congr rfl fun k _ => h3 k]
    simp [Matrix.one_apply]
  have hinv : ∀ i j, G⁻¹ i j ∈ A := by
    intro i j
    have h3 := (hdual (∑ i, G⁻¹ i j • g i)).1 (fun y hy => by rw [key]; exact hA _ (hy j)) i
    rwa [Basis.repr_sum_self] at h3
  have h4 := det_mem_subring A _ hinv
  rwa [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h4

end Formalism.HermitianLattices.Ext.L3.LandL
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem hermRepUnram [Fact HermRepUnram] : HermRepUnram := Fact.out

theorem orthBasisPos : OrthBasisPos := orthBasisPos_holds

theorem landherrUnram [Fact LandherrUnram] : LandherrUnram := Fact.out

end Formalism.HermitianLattices.Ext.L3
end
end
