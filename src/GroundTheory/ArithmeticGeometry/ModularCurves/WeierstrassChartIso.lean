import Mathlib
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassCharts

section
open CategoryTheory AlgebraicGeometry DirectSum

universe u

namespace GroundTheory.Arith.Modular

section QuotientGrading

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜] (I : Ideal A)

def quotGrading (n : ℕ) : Submodule R (A ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ R I).toLinearMap

omit [GradedAlgebra 𝒜] in
lemma mk_mem_quotGrading {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I a ∈ quotGrading 𝒜 I n :=
  ⟨a, ha, rfl⟩

instance quotGrading_gradedMonoid : SetLike.GradedMonoid (quotGrading 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, by simp⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, by simp⟩

def quotComponent (n : ℕ) : 𝒜 n →+ quotGrading 𝒜 I n where
  toFun x := ⟨Ideal.Quotient.mk I x, mk_mem_quotGrading 𝒜 I x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def quotDecomposeHom : A →+ ⨁ n, quotGrading 𝒜 I n :=
  (DirectSum.map (quotComponent 𝒜 I)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

variable {𝒜 I}

lemma quotDecomposeHom_of_mem (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) :
    quotDecomposeHom 𝒜 I a = 0 := by
  ext n
  change Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a n : A) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI n ha

variable (hI : I.IsHomogeneous 𝒜)
include hI

def quotDecompose : A ⧸ I →+ ⨁ n, quotGrading 𝒜 I n :=
  QuotientAddGroup.lift I.toAddSubgroup (quotDecomposeHom 𝒜 I)
    (fun _ ha => quotDecomposeHom_of_mem hI ha)

omit hI in
lemma quotDecomposeHom_apply (a : A) : quotDecomposeHom 𝒜 I a =
    DirectSum.map (quotComponent 𝒜 I) (DirectSum.decompose 𝒜 a) := rfl

omit hI [GradedAlgebra 𝒜] in
lemma coe_comp_map_quotComponent :
    (DirectSum.coeAddMonoidHom (quotGrading 𝒜 I)).comp (DirectSum.map (quotComponent 𝒜 I)) =
      (Ideal.Quotient.mk I).toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝒜) := by
  ext n x
  simp [DirectSum.map_of, quotComponent]

omit hI in
lemma coe_quotDecomposeHom (a : A) :
    DirectSum.coeAddMonoidHom (quotGrading 𝒜 I) (quotDecomposeHom 𝒜 I a) =
      Ideal.Quotient.mk I a := by
  rw [quotDecomposeHom_apply]
  have := congrArg (fun φ => φ (DirectSum.decompose 𝒜 a)) (coe_comp_map_quotComponent (𝒜 := 𝒜) (I := I))
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
  rw [this]
  exact congrArg (Ideal.Quotient.mk I) ((DirectSum.decompose 𝒜).symm_apply_apply a)

omit hI in
lemma quotDecomposeHom_of_mem_grading {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    quotDecomposeHom 𝒜 I a = DirectSum.of (fun n => quotGrading 𝒜 I n) n
      ⟨Ideal.Quotient.mk I a, mk_mem_quotGrading 𝒜 I ha⟩ := by
  rw [quotDecomposeHom_apply, DirectSum.decompose_of_mem 𝒜 ha, DirectSum.map_of]
  rfl

@[instance_reducible]
def quotGradedAlgebra : GradedAlgebra (quotGrading 𝒜 I) where
  decompose' := quotDecompose hI
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => exact coe_quotDecomposeHom a
  right_inv d := by
    induction d using DirectSum.induction_on with
    | zero => simp
    | of n q =>
      obtain ⟨q, a, ha, rfl⟩ := q
      rw [DirectSum.coeAddMonoidHom_of]
      exact quotDecomposeHom_of_mem_grading ha
    | add d e hd he => rw [map_add, map_add, hd, he]

end QuotientGrading

section Scale

variable {R : Type u} [CommRing R] {σ : Type*} {Q : Type*} [CommRing Q] (π : MvPolynomial σ R →+* Q)
  (i : σ)

noncomputable def scale : MvPolynomial σ R →+* Localization.Away (π (MvPolynomial.X i)) :=
  MvPolynomial.eval₂Hom ((algebraMap Q _).comp (π.comp MvPolynomial.C))
    (fun j => algebraMap Q _ (π (MvPolynomial.X j)) *
      IsLocalization.Away.invSelf (S := Localization.Away (π (MvPolynomial.X i))) (π (MvPolynomial.X i)))

theorem scale_monomial (e : σ →₀ ℕ) (c : R) :
    scale π i (MvPolynomial.monomial e c) *
        algebraMap Q (Localization.Away (π (MvPolynomial.X i))) (π (MvPolynomial.X i) ^ e.degree) =
      algebraMap Q _ (π (MvPolynomial.monomial e c)) := by
  set u := IsLocalization.Away.invSelf (S := Localization.Away (π (MvPolynomial.X i)))
    (π (MvPolynomial.X i))
  have hu : algebraMap Q _ (π (MvPolynomial.X i)) * u = 1 := IsLocalization.Away.mul_invSelf _
  have hdeg : e.degree = ∑ j ∈ e.support, e j := rfl
  have hinv : (e.prod fun _ k => u ^ k) *
      algebraMap Q (Localization.Away (π (MvPolynomial.X i))) (π (MvPolynomial.X i) ^ e.degree) = 1 := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, map_pow, ← hdeg, ← mul_pow, mul_comm, hu, one_pow]
  simp only [scale, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, RingHom.comp_apply]
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul, mul_assoc, mul_assoc, hinv, mul_one, MvPolynomial.monomial_eq, map_mul,
    map_mul, map_finsuppProd, map_finsuppProd]
  simp only [map_pow]

theorem scale_homog {m : ℕ} {a : MvPolynomial σ R} (ha : a.IsHomogeneous m) :
    scale π i a * algebraMap Q (Localization.Away (π (MvPolynomial.X i))) (π (MvPolynomial.X i) ^ m) =
      algebraMap Q _ (π a) := by
  conv_lhs => rw [a.as_sum]
  conv_rhs => rw [a.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hdeg : e.degree = m := by
    have := ha (MvPolynomial.mem_support_iff.mp he)
    rwa [Finsupp.degree_eq_weight_one]
  rw [← hdeg]
  exact scale_monomial π i e _

end Scale

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Weierstrass

open MvPolynomial

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

abbrev grading (R : Type u) [CommRing R] : ℕ → Submodule R (MvPolynomial (Fin 3) R) :=
  homogeneousSubmodule (Fin 3) R

noncomputable def cubicIdeal : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {W.toProjective.polynomial}

theorem isHomogeneous_cubic : W.toProjective.polynomial.IsHomogeneous 3 := by
  have hX := isHomogeneous_X R (0 : Fin 3)
  have hY := isHomogeneous_X R (1 : Fin 3)
  have hZ := isHomogeneous_X R (2 : Fin 3)
  have hC := fun a : R => isHomogeneous_C (Fin 3) a
  simp only [WeierstrassCurve.Projective.polynomial]
  exact IsHomogeneous.sub (IsHomogeneous.add (IsHomogeneous.add ((hY.pow 2).mul hZ)
    ((((hC _).mul hX).mul hY).mul hZ)) (((hC _).mul hY).mul (hZ.pow 2)))
    (IsHomogeneous.add (IsHomogeneous.add (IsHomogeneous.add (hX.pow 3)
      (((hC _).mul (hX.pow 2)).mul hZ)) (((hC _).mul hX).mul (hZ.pow 2))) ((hC _).mul (hZ.pow 3)))

theorem cubicIdeal_isHomogeneous : (cubicIdeal W).IsHomogeneous (grading R) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ rfl
    exact ⟨3, (mem_homogeneousSubmodule 3 _).2 (isHomogeneous_cubic W)⟩)

noncomputable abbrev HomRing : Type u := MvPolynomial (Fin 3) R ⧸ cubicIdeal W

noncomputable abbrev homGrading : ℕ → Submodule R (HomRing W) := quotGrading (grading R) (cubicIdeal W)

noncomputable instance : GradedAlgebra (homGrading W) :=
  quotGradedAlgebra (cubicIdeal_isHomogeneous W)

noncomputable abbrev Curve : Scheme.{u} := Proj (homGrading W)

noncomputable abbrev var (j : Fin 3) : HomRing W := Ideal.Quotient.mk (cubicIdeal W) (X j)

theorem var_mem (j : Fin 3) : var W j ∈ homGrading W 1 :=
  mk_mem_quotGrading _ _ (isHomogeneous_X R j)

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

noncomputable abbrev π : MvPolynomial (Fin 3) R →+* HomRing W := Ideal.Quotient.mk (cubicIdeal W)

theorem π_cubic : π W W.toProjective.polynomial = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

noncomputable def scalarAway (j : Fin 3) : R →+* Away (homGrading W) (var W j) :=
  (fromZeroRingHom (homGrading W) _).comp (algebraMap R (homGrading W 0))

noncomputable def frac (j k : Fin 3) : Away (homGrading W) (var W j) :=
  Away.mk (homGrading W) (var_mem W j) 1 (var W k) (by simpa using var_mem W k)

noncomputable abbrev vinv (j : Fin 3) : Localization.Away (var W j) :=
  IsLocalization.Away.invSelf (S := Localization.Away (var W j)) (var W j)

theorem val_frac (j k : Fin 3) :
    (frac W j k).val = algebraMap (HomRing W) (Localization.Away (var W j)) (var W k) * vinv W j := by
  rw [frac, Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one, vinv,
    IsLocalization.Away.invSelf]
  congr 2
  exact Subtype.ext (pow_one _)

theorem val_scalarAway (j : Fin 3) (r : R) :
    (scalarAway W j r).val = algebraMap (HomRing W) (Localization.Away (var W j)) (algebraMap R _ r) := by
  simp [scalarAway, fromZeroRingHom]
  rfl

theorem scale_eq_zero_of_mem {j : Fin 3} : scale (π W) j W.toProjective.polynomial = 0 := by
  have h := scale_homog (π W) j (isHomogeneous_cubic W)
  rw [π_cubic, map_zero] at h
  have hu : algebraMap (HomRing W) (Localization.Away (var W j)) (var W j) * vinv W j = 1 :=
    IsLocalization.Away.mul_invSelf _
  have : scale (π W) j W.toProjective.polynomial =
      scale (π W) j W.toProjective.polynomial *
        algebraMap (HomRing W) (Localization.Away (var W j)) (var W j ^ 3) * vinv W j ^ 3 := by
    rw [map_pow, mul_assoc, ← mul_pow, hu, one_pow, mul_one]
  rw [this, h, zero_mul]

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem constantCoeff_cubic : constantCoeff W.toProjective.polynomial = 0 := by
  simp [WeierstrassCurve.Projective.polynomial]

theorem algebraMap_zero_bijective : Function.Bijective (algebraMap R (homGrading W 0)) := by
  constructor
  · intro r s h
    have h' : π W (C (r - s)) = 0 := by
      have := congrArg Subtype.val h
      simp only [SetLike.GradeZero.coe_algebraMap] at this
      rw [map_sub, map_sub, sub_eq_zero]
      exact this
    rw [Ideal.Quotient.eq_zero_iff_mem, cubicIdeal, Ideal.mem_span_singleton'] at h'
    obtain ⟨g, hg⟩ := h'
    have := congrArg constantCoeff hg
    rw [map_mul, constantCoeff_cubic, mul_zero, constantCoeff_C] at this
    exact sub_eq_zero.1 this.symm
  · rintro ⟨q, P, hP, rfl⟩
    have hP' : P.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 P).1 hP
    have h0 : P.totalDegree = 0 := by
      by_cases hP0 : P = 0
      · simp [hP0]
      · exact hP'.totalDegree hP0
    obtain ⟨r, rfl⟩ : ∃ r, P = C r := ⟨_, totalDegree_eq_zero_iff_eq_C.1 h0⟩
    exact ⟨r, Subtype.ext rfl⟩

noncomputable def zeroEquiv : R ≃+* homGrading W 0 :=
  RingEquiv.ofBijective (algebraMap R (homGrading W 0)) (algebraMap_zero_bijective W)

noncomputable def toSpec : Curve W ⟶ Spec (.of R) :=
  Proj.toSpecZero (homGrading W) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (homGrading W 0)))

instance : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R (homGrading W 0)))) := by
  have : IsIso (CommRingCat.ofHom (algebraMap R (homGrading W 0))) :=
    (zeroEquiv W).toCommRingCatIso.isIso_hom
  infer_instance

instance : IsScalarTower R (homGrading W 0) (HomRing W) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := homGrading W 0) (A := HomRing W) (fun _ => rfl)

instance : Algebra.FiniteType (homGrading W 0) (HomRing W) := by
  have : Algebra.FiniteType R (HomRing W) := inferInstance
  exact Algebra.FiniteType.of_restrictScalars_finiteType R _ _

instance : IsProper (toSpec W) := by
  unfold toSpec
  infer_instance

noncomputable def chartZι : Spec (.of (Away (homGrading W) (var W 2))) ⟶ Curve W :=
  Proj.awayι (homGrading W) (var W 2) (var_mem W 2) one_pos

noncomputable def chartYι : Spec (.of (Away (homGrading W) (var W 1))) ⟶ Curve W :=
  Proj.awayι (homGrading W) (var W 1) (var_mem W 1) one_pos

end Weierstrass

end GroundTheory.Arith.Modular
end

section
open CategoryTheory AlgebraicGeometry

universe u

namespace GroundTheory.Arith.Modular

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section General

variable {j : Fin 3} {T : Type u} [CommRing T] (ψ : MvPolynomial (Fin 3) R →+* T)
  (hψ1 : ψ (X j) = 1) (hψF : ψ W.toProjective.polynomial = 0)

noncomputable def liftHom : HomRing W →+* T :=
  Ideal.Quotient.lift (cubicIdeal W) ψ (fun a ha => by
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hψF, mul_zero])

include hψ1 in
theorem liftHom_var : liftHom W ψ hψF (var W j) = 1 := hψ1

noncomputable def awayTo : Away (homGrading W) (var W j) →+* T :=
  (Localization.awayLift (liftHom W ψ hψF) (var W j)
    (by rw [liftHom_var W ψ hψ1 hψF]; exact isUnit_one)).comp
    (algebraMap (Away (homGrading W) (var W j)) (Localization.Away (var W j)))

theorem awayTo_mk (m : ℕ) (P : MvPolynomial (Fin 3) R) (hP : π W P ∈ homGrading W (m • 1)) :
    awayTo W ψ hψ1 hψF (Away.mk (homGrading W) (var_mem W j) m (π W P) hP) = ψ P := by
  have := Localization.awayLift_mk (liftHom W ψ hψF) (var W j) (π W P) 1
    (by rw [liftHom_var W ψ hψ1 hψF, one_mul]) m
  simp only [awayTo, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  refine this.trans ?_
  rw [one_pow, mul_one]
  rfl

theorem awayTo_surjective (hsurj : Function.Surjective ψ) :
    Function.Surjective (awayTo W ψ hψ1 hψF) := by
  intro t
  obtain ⟨P, rfl⟩ := hsurj t
  refine ⟨∑ m ∈ Finset.range (P.totalDegree + 1),
    Away.mk (homGrading W) (var_mem W j) m (π W (homogeneousComponent m P))
      (mk_mem_quotGrading _ _ (by simpa using homogeneousComponent_mem m P)), ?_⟩
  rw [map_sum]
  conv_rhs => rw [← sum_homogeneousComponent P]
  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => awayTo_mk W ψ hψ1 hψF m _ _

theorem val_eq_scale (m : ℕ) (P : MvPolynomial (Fin 3) R) (hP : P.IsHomogeneous m)
    (hP' : π W P ∈ homGrading W (m • 1)) :
    (Away.mk (homGrading W) (var_mem W j) m (π W P) hP').val = scale (π W) j P := by
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  exact (scale_homog (π W) j hP).symm

noncomputable def awayEquiv (hsurj : Function.Surjective ψ)
    (θ : T →+* Away (homGrading W) (var W j))
    (hθ : ∀ P, (θ (ψ P)).val = scale (π W) j P) : Away (homGrading W) (var W j) ≃+* T :=
  RingEquiv.ofBijective (awayTo W ψ hψ1 hψF) ⟨by
    have hleft : ∀ z, θ (awayTo W ψ hψ1 hψF z) = z := by
      intro z
      obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective (homGrading W) (var_mem W j) z
      obtain ⟨P, hP, rfl⟩ := ha
      have hP1 : P.IsHomogeneous m := (mem_homogeneousSubmodule _ P).1 (by simpa using hP)
      refine (congrArg θ (awayTo_mk W ψ hψ1 hψF m P (mk_mem_quotGrading _ _ hP))).trans ?_
      apply HomogeneousLocalization.val_injective
      rw [hθ]
      exact (val_eq_scale W m P hP1 (mk_mem_quotGrading _ _ hP)).symm
    exact Function.LeftInverse.injective hleft, awayTo_surjective W ψ hψ1 hψF hsurj⟩

theorem awayEquiv_apply (hsurj : Function.Surjective ψ)
    (θ : T →+* Away (homGrading W) (var W j))
    (hθ : ∀ P, (θ (ψ P)).val = scale (π W) j P) (z : Away (homGrading W) (var W j)) :
    awayEquiv W ψ hψ1 hψF hsurj θ hθ z = awayTo W ψ hψ1 hψF z := rfl

end General

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem π_C (a : R) : π W (C a) = algebraMap R (HomRing W) a := rfl

section ChartZ

noncomputable def dehomZ : MvPolynomial (Fin 3) R →+* W.toAffine.CoordinateRing :=
  eval₂Hom (algebraMap R _) ![xC W, yC W, 1]

theorem dehomZ_X_two : dehomZ W (X 2) = 1 := by simp [dehomZ]

theorem dehomZ_cubic : dehomZ W W.toProjective.polynomial = 0 := by
  simp only [dehomZ, WeierstrassCurve.Projective.polynomial, map_sub, map_add, map_mul, map_pow,
    coe_eval₂Hom, eval₂_X, eval₂_C]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination equation_xC_yC W

theorem dehomZ_surjective : Function.Surjective (dehomZ W) := by
  intro t
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective t
  induction q using Polynomial.induction_on with
  | C a =>
    induction a using Polynomial.induction_on with
    | C r => exact ⟨C r, by simp [dehomZ]; rfl⟩
    | add p q hp hq =>
      obtain ⟨P, hP⟩ := hp
      obtain ⟨Q, hQ⟩ := hq
      exact ⟨P + Q, by rw [map_add, hP, hQ, Polynomial.C_add, map_add]⟩
    | monomial n r _ =>
      refine ⟨C r * X 0 ^ (n + 1), ?_⟩
      simp only [dehomZ, map_mul, map_pow, coe_eval₂Hom, eval₂_C, eval₂_X]
      simp only [Matrix.cons_val_zero, xC, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul,
        Polynomial.C_pow, map_mul, map_pow]
      rfl
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    exact ⟨P + Q, by rw [map_add, hP, hQ, map_add]⟩
  | monomial n a hp =>
    obtain ⟨P, hP⟩ := hp
    refine ⟨P * X 1, ?_⟩
    rw [map_mul, hP, pow_succ, ← mul_assoc, map_mul (AdjoinRoot.mk _)]
    simp [dehomZ, yC]

theorem val_scale_eq_zero_z :
    (W.toAffine.polynomial.eval₂ (Polynomial.eval₂RingHom (scalarAway W 2) (frac W 2 0))
      (frac W 2 1)).val = 0 := by
  have h0 := scale_eq_zero_of_mem W (j := 2)
  have hu : algebraMap (HomRing W) (Localization.Away (var W 2)) (var W 2) * vinv W 2 = 1 :=
    IsLocalization.Away.mul_invSelf _
  rw [← HomogeneousLocalization.algebraMap_apply, Polynomial.hom_eval₂,
    HomogeneousLocalization.algebraMap_apply, val_frac]
  simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
    RingHom.comp_apply, Polynomial.coe_eval₂RingHom, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_add, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    val_frac, val_scalarAway]
  simp only [scale, WeierstrassCurve.Projective.polynomial, map_sub, map_add, map_mul, map_pow,
    coe_eval₂Hom, eval₂_X, eval₂_C, RingHom.comp_apply, π_C] at h0
  set u := vinv W 2
  set x := algebraMap (HomRing W) (Localization.Away (var W 2)) (var W 0)
  set y := algebraMap (HomRing W) (Localization.Away (var W 2)) (var W 1)
  set s := algebraMap (HomRing W) (Localization.Away (var W 2)) (var W 2) * u
  have hs : s = 1 := hu
  linear_combination h0 - ((y * u) ^ 2 + algebraMap (HomRing W) _ (algebraMap R _ W.a₁) * (x * u) * (y * u) +
    algebraMap (HomRing W) _ (algebraMap R _ W.a₃) * (y * u) * (s + 1) -
    algebraMap (HomRing W) _ (algebraMap R _ W.a₂) * (x * u) ^ 2 -
    algebraMap (HomRing W) _ (algebraMap R _ W.a₄) * (x * u) * (s + 1) -
    algebraMap (HomRing W) _ (algebraMap R _ W.a₆) * (s ^ 2 + s + 1)) * hs

noncomputable def coordToAwayZ : W.toAffine.CoordinateRing →+* Away (homGrading W) (var W 2) :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (scalarAway W 2) (frac W 2 0)) (frac W 2 1)
    (HomogeneousLocalization.val_injective _ (by rw [val_scale_eq_zero_z, val_zero]))

theorem val_coordToAwayZ_dehomZ (P : MvPolynomial (Fin 3) R) :
    (coordToAwayZ W (dehomZ W P)).val = scale (π W) 2 P := by
  have hu : algebraMap (HomRing W) (Localization.Away (var W 2)) (var W 2) * vinv W 2 = 1 :=
    IsLocalization.Away.mul_invSelf _
  change ((algebraMap (Away (homGrading W) (var W 2)) (Localization.Away (var W 2))).comp
    ((coordToAwayZ W).comp (dehomZ W))) P = scale (π W) 2 P
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, dehomZ, coe_eval₂Hom, eval₂_C, scale]
    rw [show algebraMap R W.toAffine.CoordinateRing r = AdjoinRoot.of _ (Polynomial.C r) from rfl,
      coordToAwayZ, AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      HomogeneousLocalization.algebraMap_apply, val_scalarAway]
    rfl
  · intro k
    fin_cases k
    · simp only [RingHom.comp_apply, dehomZ, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, xC]
      rw [show AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X) =
          AdjoinRoot.of _ Polynomial.X from rfl, coordToAwayZ, AdjoinRoot.lift_of,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, HomogeneousLocalization.algebraMap_apply,
        val_frac]
    · simp only [RingHom.comp_apply, dehomZ, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, yC]
      rw [coordToAwayZ, AdjoinRoot.lift_root, HomogeneousLocalization.algebraMap_apply, val_frac]
    · simp only [RingHom.comp_apply, dehomZ, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, map_one]
      exact hu.symm

noncomputable def chartZEquiv : Away (homGrading W) (var W 2) ≃+* W.toAffine.CoordinateRing :=
  awayEquiv W (dehomZ W) (dehomZ_X_two W) (dehomZ_cubic W) (dehomZ_surjective W) (coordToAwayZ W)
    (val_coordToAwayZ_dehomZ W)

end ChartZ

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section ChartY

noncomputable def dehomY : MvPolynomial (Fin 3) R →+* InfChart W :=
  eval₂Hom (algebraMap R _) ![xI W, 1, zI W]

theorem dehomY_X_one : dehomY W (X 1) = 1 := by simp [dehomY]

theorem dehomY_cubic : dehomY W W.toProjective.polynomial = 0 := by
  simp only [dehomY, WeierstrassCurve.Projective.polynomial, map_sub, map_add, map_mul, map_pow,
    coe_eval₂Hom, eval₂_X, eval₂_C]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (-1 : InfChart W) * equation_xI_zI W

theorem dehomY_surjective : Function.Surjective (dehomY W) := by
  intro t
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective t
  induction q using Polynomial.induction_on with
  | C a =>
    induction a using Polynomial.induction_on with
    | C r => exact ⟨C r, by simp [dehomY]; rfl⟩
    | add p q hp hq =>
      obtain ⟨P, hP⟩ := hp
      obtain ⟨Q, hQ⟩ := hq
      exact ⟨P + Q, by rw [map_add, hP, hQ, Polynomial.C_add, map_add]⟩
    | monomial n r _ =>
      refine ⟨C r * X 2 ^ (n + 1), ?_⟩
      simp only [dehomY, map_mul, map_pow, coe_eval₂Hom, eval₂_C, eval₂_X]
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, zI]
      rfl
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    exact ⟨P + Q, by rw [map_add, hP, hQ, map_add]⟩
  | monomial n a hp =>
    obtain ⟨P, hP⟩ := hp
    refine ⟨P * X 0, ?_⟩
    rw [map_mul, hP, pow_succ, ← mul_assoc, map_mul (AdjoinRoot.mk _)]
    simp [dehomY, xI]

theorem val_scale_eq_zero_y :
    ((infPolynomial W).eval₂ (Polynomial.eval₂RingHom (scalarAway W 1) (frac W 1 2))
      (frac W 1 0)).val = 0 := by
  have h0 := scale_eq_zero_of_mem W (j := 1)
  have hu : algebraMap (HomRing W) (Localization.Away (var W 1)) (var W 1) * vinv W 1 = 1 :=
    IsLocalization.Away.mul_invSelf _
  rw [← HomogeneousLocalization.algebraMap_apply, Polynomial.hom_eval₂,
    HomogeneousLocalization.algebraMap_apply, val_frac]
  simp only [infPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
    RingHom.comp_apply, Polynomial.coe_eval₂RingHom, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_add, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.val_sub, val_frac, val_scalarAway]
  simp only [scale, WeierstrassCurve.Projective.polynomial, map_sub, map_add, map_mul, map_pow,
    coe_eval₂Hom, eval₂_X, eval₂_C, RingHom.comp_apply, π_C] at h0
  set u := vinv W 1
  set x := algebraMap (HomRing W) (Localization.Away (var W 1)) (var W 0)
  set z := algebraMap (HomRing W) (Localization.Away (var W 1)) (var W 2)
  set s := algebraMap (HomRing W) (Localization.Away (var W 1)) (var W 1) * u
  have hs : s = 1 := hu
  linear_combination -h0 + ((s + 1) * (z * u) +
    algebraMap (HomRing W) _ (algebraMap R _ W.a₁) * (x * u) * (z * u) +
    algebraMap (HomRing W) _ (algebraMap R _ W.a₃) * (z * u) ^ 2) * hs

noncomputable def infToAwayY : InfChart W →+* Away (homGrading W) (var W 1) :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (scalarAway W 1) (frac W 1 2)) (frac W 1 0)
    (HomogeneousLocalization.val_injective _ (by rw [val_scale_eq_zero_y, val_zero]))

theorem val_infToAwayY_dehomY (P : MvPolynomial (Fin 3) R) :
    (infToAwayY W (dehomY W P)).val = scale (π W) 1 P := by
  have hu : algebraMap (HomRing W) (Localization.Away (var W 1)) (var W 1) * vinv W 1 = 1 :=
    IsLocalization.Away.mul_invSelf _
  change ((algebraMap (Away (homGrading W) (var W 1)) (Localization.Away (var W 1))).comp
    ((infToAwayY W).comp (dehomY W))) P = scale (π W) 1 P
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, dehomY, coe_eval₂Hom, eval₂_C, scale]
    rw [show algebraMap R (InfChart W) r = AdjoinRoot.of _ (Polynomial.C r) from rfl,
      infToAwayY, AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      HomogeneousLocalization.algebraMap_apply, val_scalarAway]
    rfl
  · intro k
    fin_cases k
    · simp only [RingHom.comp_apply, dehomY, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, xI]
      rw [infToAwayY, AdjoinRoot.lift_root, HomogeneousLocalization.algebraMap_apply, val_frac]
    · simp only [RingHom.comp_apply, dehomY, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, map_one]
      exact hu.symm
    · simp only [RingHom.comp_apply, dehomY, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, zI]
      rw [infToAwayY, AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        HomogeneousLocalization.algebraMap_apply, val_frac]

noncomputable def chartYEquiv : Away (homGrading W) (var W 1) ≃+* InfChart W :=
  awayEquiv W (dehomY W) (dehomY_X_one W) (dehomY_cubic W) (dehomY_surjective W) (infToAwayY W)
    (val_infToAwayY_dehomY W)

end ChartY

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Charts

theorem awayTo_scalarAway {j : Fin 3} {T : Type u} [CommRing T] (ψ : MvPolynomial (Fin 3) R →+* T)
    (hψ1 : ψ (X j) = 1) (hψF : ψ W.toProjective.polynomial = 0) (r : R) :
    awayTo W ψ hψ1 hψF (scalarAway W j r) = ψ (C r) := by
  simp only [awayTo, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, val_scalarAway]
  rw [Localization.awayLift, IsLocalization.Away.lift_eq]
  rfl

theorem chartZEquiv_scalarAway (r : R) : chartZEquiv W (scalarAway W 2 r) = algebraMap R _ r := by
  rw [chartZEquiv, awayEquiv_apply, awayTo_scalarAway]
  simp [dehomZ]

theorem chartYEquiv_scalarAway (r : R) : chartYEquiv W (scalarAway W 1 r) = algebraMap R _ r := by
  rw [chartYEquiv, awayEquiv_apply, awayTo_scalarAway]
  simp [dehomY]

theorem chartι_toSpec (j : Fin 3) :
    Proj.awayι (homGrading W) (var W j) (var_mem W j) one_pos ≫ toSpec W =
      Spec.map (CommRingCat.ofHom (scalarAway W j)) := by
  rw [toSpec, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

noncomputable def chartZ : Spec (.of W.toAffine.CoordinateRing) ⟶ Curve W :=
  Spec.map (CommRingCat.ofHom (chartZEquiv W).toRingHom) ≫ chartZι W

noncomputable def chartY : Spec (.of (InfChart W)) ⟶ Curve W :=
  Spec.map (CommRingCat.ofHom (chartYEquiv W).toRingHom) ≫ chartYι W

instance : IsIso (Spec.map (CommRingCat.ofHom (chartZEquiv W).toRingHom)) := by
  have : IsIso (CommRingCat.ofHom (chartZEquiv W).toRingHom) :=
    (chartZEquiv W).toCommRingCatIso.isIso_hom
  infer_instance

instance : IsIso (Spec.map (CommRingCat.ofHom (chartYEquiv W).toRingHom)) := by
  have : IsIso (CommRingCat.ofHom (chartYEquiv W).toRingHom) :=
    (chartYEquiv W).toCommRingCatIso.isIso_hom
  infer_instance

instance : IsOpenImmersion (chartZι W) := by unfold chartZι; infer_instance
instance : IsOpenImmersion (chartYι W) := by unfold chartYι; infer_instance
instance : IsOpenImmersion (chartZ W) := by unfold chartZ; infer_instance
instance : IsOpenImmersion (chartY W) := by unfold chartY; infer_instance

end Charts

end Weierstrass

end GroundTheory.Arith.Modular
end
