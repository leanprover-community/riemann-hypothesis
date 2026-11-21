import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameGLTwoDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCentreLawZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.DescB.PlaneTwo GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.DescB.PlaneTwo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) in

def IsTwoPlaneFrame {n n₁ n₂ : ℕ} (Y : Spc F E n) (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) (c : E) {r : ℕ} (h1 : 1 < r)
    (Xf Yf : Matrix (Fin n) (Fin r) E) : Prop :=
  IsWittFrame σ (c • Y.J.map σ) Xf Yf ∧ (fun k => Xf k ⟨0, by omega⟩) = H₁.x ∧ (fun k => Xf k ⟨1, h1⟩) = xTwo H₁ H₂ ∧
    (fun k => Yf k ⟨0, by omega⟩) = c⁻¹ • H₁.y ∧ (fun k => Yf k ⟨1, h1⟩) = c⁻¹ • yTwo H₁ H₂

end GlobalTheory.ThK.DescB.PlaneTwo

end
end

section
noncomputable section

namespace GlobalTheory.CtTyp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def ctf {d d₁ : ℕ} {W : Spc F E d} (H' : Plane E d d₁) (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H'))
    (f : UA σ W.J → ℂ) (g : UA σ W.J) : ℂ :=
  ∫ u in 𝓕, f (u.1 * g) ∂μ

theorem absE_pos (t : (AE F E)ˣ) : 0 < (absE F E t : ℝ) := by
  have h : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h0 : absE F E t ≠ 0 := left_ne_zero_of_mul_eq_one h
  exact_mod_cast pos_iff_ne_zero.2 h0

def twAbs (χ : Chr F E) (s : ℝ) : (AE F E)ˣ →* ℂˣ where
  toFun t := Units.mk0 ((χ t : ℂ) * (((absE F E t : ℝ) ^ s : ℝ) : ℂ))
    (mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (absE_pos t) s).ne'))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Units.val_mul, Units.val_mk0]
    rw [Real.mul_rpow (absE_pos x).le (absE_pos y).le]
    push_cast
    ring

@[simp] theorem coe_twAbs (χ : Chr F E) (s : ℝ) (t : (AE F E)ˣ) :
    ((twAbs χ s t : ℂˣ) : ℂ) = (χ t : ℂ) * (((absE F E t : ℝ) ^ s : ℝ) : ℂ) := rfl

example : twAbs (1 : Chr F E) 0 = 1 := by ext t; simp

theorem norm_twAbs (χ : Chr F E) (s : ℝ) (t : (AE F E)ˣ) : ‖((twAbs χ s t : ℂˣ) : ℂ)‖ = (absE F E t : ℝ) ^ s := by
  rw [coe_twAbs, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (absE_pos t) s)]

theorem log_absE_mul (x y : (AE F E)ˣ) :
    Real.log (absE F E (x * y) : ℝ) = Real.log (absE F E x : ℝ) + Real.log (absE F E y : ℝ) := by
  rw [map_mul, NNReal.coe_mul, Real.log_mul (absE_pos x).ne' (absE_pos y).ne']

theorem log_absE_eq_zero {t : (AE F E)ˣ} : Real.log (absE F E t : ℝ) = 0 ↔ absE F E t = 1 := by
  constructor
  · intro h
    have := Real.exp_log (absE_pos t)
    rw [h, Real.exp_zero] at this
    exact_mod_cast this.symm
  · intro h; rw [h]; simp

end GlobalTheory.CtTyp
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviIdeleHom

open Matrix

section Alg

variable {R : Type*} [CommRing R] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

def levM (x y a b : n → R) (t s : R) : Matrix n n R :=
  1 + (t - 1) • vecMulVec x a + (s - 1) • vecMulVec y b

variable {x y a b : n → R}

theorem levM_mul (hax : a ⬝ᵥ x = 1) (hay : a ⬝ᵥ y = 0) (hbx : b ⬝ᵥ x = 0) (hby : b ⬝ᵥ y = 1) (t s t' s' : R) :
    levM x y a b t s * levM x y a b t' s' = levM x y a b (t * t') (s * s') := by
  have hPP : vecMulVec x a * vecMulVec x a = vecMulVec x a := by rw [vecMulVec_mul_vecMulVec, hax, one_smul]
  have hPQ : vecMulVec x a * vecMulVec y b = 0 := by
    rw [vecMulVec_mul_vecMulVec, hay, zero_smul]; ext i j; simp [vecMulVec_apply]
  have hQP : vecMulVec y b * vecMulVec x a = 0 := by
    rw [vecMulVec_mul_vecMulVec, hbx, zero_smul]; ext i j; simp [vecMulVec_apply]
  have hQQ : vecMulVec y b * vecMulVec y b = vecMulVec y b := by rw [vecMulVec_mul_vecMulVec, hby, one_smul]
  simp only [levM, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm, hPP, hPQ, hQP, hQQ,
    smul_zero, add_zero, zero_add, smul_smul]
  module

theorem levM_one : levM x y a b 1 1 = 1 := by simp [levM]

theorem levi_matrix_mulVec_first_vector (hax : a ⬝ᵥ x = 1) (hbx : b ⬝ᵥ x = 0) (t s : R) : levM x y a b t s *ᵥ x = t • x := by
  simp only [levM, add_mulVec, one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, hax, hbx, op_smul_eq_smul]
  simp only [one_smul, zero_smul, smul_zero, add_zero]
  module

theorem levM_mulVec_y (hay : a ⬝ᵥ y = 0) (hby : b ⬝ᵥ y = 1) (t s : R) : levM x y a b t s *ᵥ y = s • y := by
  simp only [levM, add_mulVec, one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, hay, hby, op_smul_eq_smul]
  simp only [one_smul, zero_smul, smul_zero, add_zero]
  module

theorem levM_mul_fix {ι : Matrix n m R} (haι : a ᵥ* ι = 0) (hbι : b ᵥ* ι = 0) (t s : R) : levM x y a b t s * ι = ι := by
  simp only [levM, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul, haι, hbι]
  have : vecMulVec x (0 : m → R) = 0 := by ext i j; simp [vecMulVec_apply]
  have h2 : vecMulVec y (0 : m → R) = 0 := by ext i j; simp [vecMulVec_apply]
  rw [this, h2, smul_zero, smul_zero, add_zero, add_zero]

theorem levM_map {S : Type*} [CommRing S] (f : R →+* S) (t s : R) :
    (levM x y a b t s).map f = levM (f ∘ x) (f ∘ y) (f ∘ a) (f ∘ b) (f t) (f s) := by
  ext i j
  simp [levM, Matrix.one_apply, vecMulVec_apply, map_add, map_mul, map_sub]

theorem levM_unitary (c : R →+* R) (hc : ∀ r, c (c r) = r) {J : Matrix n n R}
    (ha : J *ᵥ (c ∘ y) = a) (hb : J *ᵥ (c ∘ x) = -b) (hxJ : x ᵥ* J = c ∘ b) (hyJ : y ᵥ* J = -(c ∘ a))
    (hax : a ⬝ᵥ x = 1) (hay : a ⬝ᵥ y = 0) (hbx : b ⬝ᵥ x = 0) (hby : b ⬝ᵥ y = 1)
    {t s : R} (h1 : t * c s = 1) (h2 : s * c t = 1) :
    (levM x y a b t s)ᵀ * J * (levM x y a b t s).map c = J := by
  have hcc : c ∘ (c ∘ x) = x := funext fun i => hc _
  have hcc' : c ∘ (c ∘ y) = y := funext fun i => hc _
  have d1 : (c ∘ b) ⬝ᵥ (c ∘ x) = 0 := by rw [← RingHom.map_dotProduct, hbx, map_zero]
  have d2 : (c ∘ b) ⬝ᵥ (c ∘ y) = 1 := by rw [← RingHom.map_dotProduct, hby, map_one]
  have d3 : (c ∘ a) ⬝ᵥ (c ∘ x) = 1 := by rw [← RingHom.map_dotProduct, hax, map_one]
  have d4 : (c ∘ a) ⬝ᵥ (c ∘ y) = 0 := by rw [← RingHom.map_dotProduct, hay, map_zero]
  rw [levM_map, levM]
  simp only [levM, transpose_add, transpose_one, transpose_smul, transpose_vecMulVec, add_mul, mul_add, Matrix.one_mul,
    Matrix.mul_one, smul_mul_assoc, mul_smul_comm, vecMulVec_mul, mul_vecMulVec, hxJ, hyJ, ha, hb, vecMulVec_mul_vecMulVec,
    neg_dotProduct, d1, d2, d3, d4, smul_smul]
  simp only [vecMulVec_mulVec, op_smul_eq_smul, d1, d2, d3, d4, dotProduct_neg, neg_dotProduct, Matrix.vecMulVec_neg,
    Matrix.neg_vecMulVec, Matrix.smul_vecMulVec, zero_smul, one_smul, neg_zero, smul_zero, add_zero, neg_neg]
  simp only [Matrix.neg_mulVec, vecMulVec_mulVec, op_smul_eq_smul, d1, d2, d3, d4, Matrix.zero_vecMulVec, Matrix.neg_vecMulVec,
    Matrix.smul_vecMulVec, zero_smul, one_smul, neg_zero, smul_zero, add_zero, neg_neg, smul_neg]
  linear_combination (norm := module) h1 • vecMulVec a (c ∘ b) - h2 • vecMulVec b (c ∘ a)

end Alg

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.includeRight_apply]

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add u v hu hv => rw [map_add, map_add, hu, hv]

def homOf (σ : E →ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (M : (AE F E)ˣ → Matrix (Fin N) (Fin N) (AE F E))
    (hone : M 1 = 1) (hmul : ∀ t t', M (t * t') = M t * M t')
    (hunit : ∀ t, (M t)ᵀ * incM F J * (M t).map (cA σ) = incM F J) : (AE F E)ˣ →* UA σ J where
  toFun t := ⟨⟨M t, M t⁻¹, by rw [← hmul, mul_inv_cancel, hone], by rw [← hmul, inv_mul_cancel, hone]⟩, hunit t⟩
  map_one' := Subtype.ext (Units.ext hone)
  map_mul' t t' := Subtype.ext (Units.ext (hmul t t'))

end Adelic

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Matrix

theorem map_comp_mulVec {R S : Type*} [CommRing R] [CommRing S] {n m : Type*} [Fintype m] (f : R →+* S)
    (M : Matrix n m R) (v : m → R) : M.map f *ᵥ (f ∘ v) = f ∘ (M *ᵥ v) := funext fun i => (RingHom.map_mulVec f M v i).symm

theorem map_comp_vecMul {R S : Type*} [CommRing R] [CommRing S] {n m : Type*} [Fintype n] (f : R →+* S)
    (M : Matrix n m R) (v : n → R) : (f ∘ v) ᵥ* M.map f = f ∘ (v ᵥ* M) := funext fun i => (RingHom.map_vecMul f M v i).symm

theorem dual_facts {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {N N₁ : ℕ} {J : Matrix (Fin N) (Fin N) E}
    (hsk : ∀ i j, σ (J j i) = -J i j) {x y : Fin N → E} {ι : Matrix (Fin N) (Fin N₁) E}
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) :
    let aE := J *ᵥ (⇑σ ∘ y); let bE := -(J *ᵥ (⇑σ ∘ x))
    aE ⬝ᵥ x = 1 ∧ aE ⬝ᵥ y = 0 ∧ bE ⬝ᵥ x = 0 ∧ bE ⬝ᵥ y = 1 ∧ x ᵥ* J = ⇑σ ∘ bE ∧ y ᵥ* J = -(⇑σ ∘ aE) ∧
      aE ᵥ* ι = 0 ∧ bE ᵥ* ι = 0 := by
  intro aE bE
  have hconj : ∀ v : Fin N → E, ⇑σ ∘ (J *ᵥ (⇑σ ∘ v)) = -(v ᵥ* J) := by
    intro v; funext i
    simp only [Function.comp_apply, mulVec, dotProduct, vecMul, map_sum, map_mul, hσ, Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show J i j = -σ (J j i) by rw [hsk, neg_neg], map_neg, hσ]
    ring
  have hform : ∀ u v : Fin N → E, form σ J u v = (J *ᵥ (⇑σ ∘ v)) ⬝ᵥ u := fun u v => dotProduct_comm _ _
  have hyx : form σ J y x = -1 := by
    have h := congrArg σ hxy
    rw [map_one] at h
    have : σ (form σ J x y) = -form σ J y x := by
      unfold form
      change σ.toRingHom (x ⬝ᵥ J *ᵥ (⇑σ ∘ y)) = -(y ⬝ᵥ J *ᵥ (⇑σ ∘ x))
      rw [RingHom.map_dotProduct]
      change (⇑σ ∘ x) ⬝ᵥ (⇑σ ∘ (J *ᵥ (⇑σ ∘ y))) = _
      rw [hconj, dotProduct_neg, dotProduct_comm, ← dotProduct_mulVec]
    rw [this] at h
    linear_combination -h
  have hvanish : ∀ w : Fin N → E, (∀ u, (ι *ᵥ u) ⬝ᵥ w = 0) → w ᵥ* ι = 0 := by
    intro w hw; funext j
    have := hw (Pi.single j 1)
    rw [dotProduct_comm, dotProduct_mulVec, dotProduct_single, mul_one] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hform]; exact hxy
  · rw [← hform]; exact hyy
  · simp only [bE, neg_dotProduct]; rw [← hform, hxx, neg_zero]
  · simp only [bE, neg_dotProduct]; rw [← hform, hyx, neg_neg]
  · simp only [bE]
    funext i
    have := congrFun (hconj x) i
    simp only [Function.comp_apply, Pi.neg_apply, map_neg] at this ⊢
    rw [this, neg_neg]
  · simp only [aE]; rw [hconj, neg_neg]
  · exact hvanish _ fun u => (dotProduct_comm _ _).trans ((hform _ _).symm.trans (horth u).2)
  · refine hvanish _ fun u => ?_
    simp only [bE, dotProduct_neg]
    rw [dotProduct_comm]; exact neg_eq_zero.2 ((hform _ _).symm.trans (horth u).1)

end Main

section Thm

open Matrix

theorem levi_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∃ mt : (AE F E)ˣ →* UA σ G.W.J, (∀ g, Continuous fun t => mt t * g) ∧ (∀ t, IsLevi (W₁ := W₁) H' t 1 (mt t)) ∧ (∀ x : Eˣ, mt (Units.map (inclR (F := F) (AF F)).toMonoidHom x) ∈ ratU σ G.W.J) ∧ ∀ t, ∀ u ∈ unip σ G.W H', mt t * u * (mt t)⁻¹ ∈ unip σ G.W H' := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA
  have hσ : ∀ e, σ (σ e) = e := sigma_sigma hT.base.cm
  obtain ⟨hax, hay, hbx, hby, hxJ, hyJ, haι, hbι⟩ := dual_facts hσ hT.geo.hW.skew hA.xx hA.yy hA.xy hA.orth
  set aE := G.W.J *ᵥ (⇑σ ∘ H'.y) with haE
  set bE := -(G.W.J *ᵥ (⇑σ ∘ H'.x)) with hbE
  set f : E →+* AE F E := inclR (F := F) (AF F) with hf
  have hcf : ∀ {k : ℕ} (v : Fin k → E), ⇑(cA σ) ∘ (f ∘ v) = f ∘ (⇑σ ∘ v) := fun v => funext fun i => cA_inclR σ (v i)
  have hdot : ∀ v w : Fin (a + a') → E, (f ∘ v) ⬝ᵥ (f ∘ w) = f (v ⬝ᵥ w) := fun v w => (RingHom.map_dotProduct f v w).symm
  have hneg : ∀ v : Fin (a + a') → E, f ∘ (-v) = -(f ∘ v) := fun v => funext fun i => map_neg f (v i)
  have hax' : (f ∘ aE) ⬝ᵥ (f ∘ H'.x) = 1 := by rw [hdot, hax, map_one]
  have hay' : (f ∘ aE) ⬝ᵥ (f ∘ H'.y) = 0 := by rw [hdot, hay, map_zero]
  have hbx' : (f ∘ bE) ⬝ᵥ (f ∘ H'.x) = 0 := by rw [hdot, hbx, map_zero]
  have hby' : (f ∘ bE) ⬝ᵥ (f ∘ H'.y) = 1 := by rw [hdot, hby, map_one]
  have haι' : (f ∘ aE) ᵥ* incM F H'.ι = 0 := by
    change (f ∘ aE) ᵥ* H'.ι.map f = 0
    rw [map_comp_vecMul, haι]; funext i; simp
  have hbι' : (f ∘ bE) ᵥ* incM F H'.ι = 0 := by
    change (f ∘ bE) ᵥ* H'.ι.map f = 0
    rw [map_comp_vecMul, hbι]; funext i; simp
  let M : (AE F E)ˣ → Matrix (Fin (a + a')) (Fin (a + a')) (AE F E) := fun t =>
    levM (f ∘ H'.x) (f ∘ H'.y) (f ∘ aE) (f ∘ bE) t.1 (cA σ (t⁻¹).1)
  have hone : M 1 = 1 := by simp only [M, inv_one, Units.val_one, map_one]; exact levM_one
  have hmul : ∀ t t', M (t * t') = M t * M t' := by
    intro t t'
    simp only [M]
    rw [levM_mul hax' hay' hbx' hby', _root_.mul_inv_rev, Units.val_mul, Units.val_mul, map_mul, mul_comm (cA σ _)]
  have hunit : ∀ t, (M t)ᵀ * incM F G.W.J * (M t).map (cA σ) = incM F G.W.J := by
    intro t
    have ha' : G.W.J.map f *ᵥ ((cA σ).toRingHom ∘ (f ∘ H'.y)) = f ∘ aE := by
      change _ *ᵥ (⇑(cA σ) ∘ (f ∘ H'.y)) = _
      rw [hcf, map_comp_mulVec]
    have hb' : G.W.J.map f *ᵥ ((cA σ).toRingHom ∘ (f ∘ H'.x)) = -(f ∘ bE) := by
      change _ *ᵥ (⇑(cA σ) ∘ (f ∘ H'.x)) = _
      rw [hcf, map_comp_mulVec, hbE, hneg, neg_neg]
    have hxJ' : (f ∘ H'.x) ᵥ* G.W.J.map f = (cA σ).toRingHom ∘ (f ∘ bE) := by
      change _ = ⇑(cA σ) ∘ (f ∘ bE)
      rw [map_comp_vecMul, hxJ, hcf]
    have hyJ' : (f ∘ H'.y) ᵥ* G.W.J.map f = -((cA σ).toRingHom ∘ (f ∘ aE)) := by
      change _ = -(⇑(cA σ) ∘ (f ∘ aE))
      rw [map_comp_vecMul, hyJ, hcf, hneg]
    have h1 : t.1 * (cA σ).toRingHom (cA σ (t⁻¹).1) = 1 := by
      change t.1 * cA σ (cA σ (t⁻¹).1) = 1
      rw [cA_cA hσ, Units.mul_inv]
    have h2 : cA σ (t⁻¹).1 * (cA σ).toRingHom t.1 = 1 := by
      change cA σ (t⁻¹).1 * cA σ t.1 = 1
      rw [← map_mul, Units.inv_mul, map_one]
    exact levM_unitary (cA σ).toRingHom (cA_cA hσ) ha' hb' hxJ' hyJ' hax' hay' hbx' hby' h1 h2
  have hfix : ∀ (t : (AE F E)ˣ) (z : Fin d₁ → AE F E), M t *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z := by
    intro t z
    rw [mulVec_mulVec]
    exact congrArg (· *ᵥ z) (levM_mul_fix haι' hbι' _ _)
  refine ⟨homOf σ G.W.J M hone hmul hunit, ?_, ?_, ?_, ?_⟩
  · intro g
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
    have hM : ∀ p q : (AE F E)ˣ → AE F E, Continuous p → Continuous q →
        Continuous fun t => levM (f ∘ H'.x) (f ∘ H'.y) (f ∘ aE) (f ∘ bE) (p t) (q t) := by
      intro p q hp hq
      unfold levM
      exact (continuous_const.add ((hp.sub continuous_const).smul continuous_const)).add
        ((hq.sub continuous_const).smul continuous_const)
    have hc : Continuous (homOf σ G.W.J M hone hmul hunit) := by
      apply continuous_induced_rng.2
      apply Units.continuous_iff.2
      constructor
      · change Continuous fun t => M t
        exact hM _ _ Units.continuous_val (hcA.comp Units.continuous_coe_inv)
      · change Continuous fun t : (AE F E)ˣ => M t⁻¹
        simp only [M, inv_inv]
        exact hM _ _ Units.continuous_coe_inv (hcA.comp Units.continuous_val)
    exact (continuous_mul_right g).comp hc
  · intro t
    refine ⟨levi_matrix_mulVec_first_vector hax' hbx' _ _, levM_mulVec_y hay' hby' _ _, ?_⟩
    change M t * incM F H'.ι = incM F H'.ι * 1
    rw [Matrix.mul_one]
    exact levM_mul_fix haι' hbι' _ _
  · intro x
    rw [ratU, Subgroup.mem_subgroupOf]
    have hE1 := levM_mul (x := H'.x) (y := H'.y) hax hay hbx hby
    refine ⟨⟨levM H'.x H'.y aE bE x.1 (σ (x⁻¹).1), levM H'.x H'.y aE bE (x⁻¹).1 (σ x.1), ?_, ?_⟩, ?_⟩
    · rw [hE1, Units.mul_inv, ← map_mul, Units.inv_mul, map_one, levM_one]
    · rw [hE1, Units.inv_mul, ← map_mul, Units.mul_inv, map_one, levM_one]
    · apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [Matrix.GeneralLinearGroup.map_apply]
      change f (levM H'.x H'.y aE bE x.1 (σ (x⁻¹).1) i j) = M _ i j
      rw [← Matrix.map_apply (f := f), levM_map]
      show _ = levM (f ∘ H'.x) (f ∘ H'.y) (f ∘ aE) (f ∘ bE) (f x.1) (cA σ (f (x⁻¹).1)) i j
      rw [show cA σ (f (x⁻¹).1) = f (σ (x⁻¹).1) from cA_inclR σ _]
  · intro t u hu
    have hsub : unip σ G.W H' ≤ (unip σ G.W H').comap (MulAut.conj (homOf σ G.W.J M hone hmul hunit t)).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro v ⟨hvx, hvι⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      apply Subgroup.subset_closure
      refine ⟨?_, fun z => ?_⟩
      · change (M t * mat v * M t⁻¹) *ᵥ incV F H'.x = incV F H'.x
        rw [← mulVec_mulVec, ← mulVec_mulVec]
        change M t *ᵥ (mat v *ᵥ (M t⁻¹ *ᵥ (f ∘ H'.x))) = f ∘ H'.x
        rw [levi_matrix_mulVec_first_vector hax' hbx', mulVec_smul]
        change M t *ᵥ ((t⁻¹).1 • (mat v *ᵥ incV F H'.x)) = f ∘ H'.x
        rw [hvx, mulVec_smul]
        change (t⁻¹).1 • (M t *ᵥ (f ∘ H'.x)) = f ∘ H'.x
        rw [levi_matrix_mulVec_first_vector hax' hbx', smul_smul, Units.inv_mul, one_smul]
      · obtain ⟨c, hc⟩ := hvι z
        refine ⟨c * t.1, ?_⟩
        change (M t * mat v * M t⁻¹) *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + (c * t.1) • incV F H'.x
        rw [← mulVec_mulVec, ← mulVec_mulVec, hfix, hc, mulVec_add, hfix, mulVec_smul, ← smul_smul]
        change incM F H'.ι *ᵥ z + c • (M t *ᵥ (f ∘ H'.x)) = incM F H'.ι *ᵥ z + c • (t.1 • (f ∘ H'.x))
        rw [levi_matrix_mulVec_first_vector hax' hbx']
    have := hsub hu
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

end Thm

end GlobalTheory.LeviIdeleHom
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PlaneFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_conj {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

theorem det_ne_zero_of_hasSig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have h2 : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [Matrix.mul_apply]
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at h3
  intro h0
  rw [h0, Matrix.det_neg] at h3
  simp at h3
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) h3.symm

theorem form_skew {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  have hs : ∀ i j, σ (J i j) = -J j i := fun i j => hJ j i
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hs, conj_conj hσ, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PlaneFrame

namespace GlobalTheory.PlaneFrame

theorem frame_dual_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧
      Matrix.vecMulVec H'.x (W.J *ᵥ fun i => σ (H'.y i)) + H'.ι * π - Matrix.vecMulVec H'.y (W.J *ᵥ fun i => σ (H'.x i)) = 1 ∧
      IsUnit W₁.J.det := by
  intro F E _ _ _ _ _ σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH
  have hinv := conj_conj hσ
  obtain ⟨hrank, hxx, hyy, hxy, horth, hgram, -, hsplit, -, -, -⟩ := hH
  subst hrank
  have hsk := form_skew hσ hW.skew
  have hyx : form σ W.J H'.y H'.x = -1 := by rw [hsk, hxy, map_one]
  have hxι : ∀ u, form σ W.J H'.x (H'.ι *ᵥ u) = 0 := fun u => by rw [hsk, (horth u).1, map_zero, neg_zero]
  have hyι : ∀ u, form σ W.J H'.y (H'.ι *ᵥ u) = 0 := fun u => by rw [hsk, (horth u).2, map_zero, neg_zero]
  have hlin : ∀ (u : Fin d₁ → E) (a b : E) (w : Fin (d₁ + 2) → E),
      form σ W.J (H'.ι *ᵥ u + (a • H'.x + b • H'.y)) w =
        form σ W.J (H'.ι *ᵥ u) w + a * form σ W.J H'.x w + b * form σ W.J H'.y w := by
    intro u a b w
    simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]; ring
  let Φ : ((Fin d₁ → E) × E × E) →ₗ[E] (Fin (d₁ + 2) → E) :=
    H'.ι.mulVecLin.coprod ((LinearMap.toSpanSingleton E _ H'.x).coprod (LinearMap.toSpanSingleton E _ H'.y))
  have hΦ : ∀ p, Φ p = H'.ι *ᵥ p.1 + (p.2.1 • H'.x + p.2.2 • H'.y) := fun p => rfl
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hW.lat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hsplit z hz
    exact ⟨(u, a, b), by rw [hΦ]; abel⟩
  have hinj : Function.Injective Φ := by
    rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hsurj
    · simp [Module.finrank_prod]
  let eΦ := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let πl : (Fin (d₁ + 2) → E) →ₗ[E] (Fin d₁ → E) := LinearMap.fst E _ _ ∘ₗ eΦ.symm.toLinearMap
  have hπ : ∀ p, πl (Φ p) = p.1 := by
    intro p
    simp only [πl, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.fst_apply]
    rw [show Φ p = eΦ p from rfl, LinearEquiv.symm_apply_apply]
  refine ⟨LinearMap.toMatrix' πl, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, LinearMap.comp_apply, Matrix.toLin'_apply]
    have := hπ (u, 0, 0)
    rw [hΦ] at this
    simpa using this
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun z => ?_
    obtain ⟨⟨u, a, b⟩, rfl⟩ := hsurj z
    rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
      ← Matrix.mulVec_mulVec, show LinearMap.toMatrix' πl *ᵥ Φ (u, a, b) = πl (Φ (u, a, b)) from
        (Matrix.toLin'_apply _ _).symm.trans (by rw [Matrix.toLin'_toMatrix']), hπ]
    have e1 : (W.J *ᵥ fun i => σ (H'.y i)) ⬝ᵥ Φ (u, a, b) = a := by
      rw [dotProduct_comm, ← form, hΦ, hlin, (horth u).2, hxy, hyy]; ring
    have e2 : (W.J *ᵥ fun i => σ (H'.x i)) ⬝ᵥ Φ (u, a, b) = -b := by
      rw [dotProduct_comm, ← form, hΦ, hlin, (horth u).1, hxx, hyx]; ring
    rw [e1, e2, hΦ]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
    ring
  · rw [← hgram, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]

    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hJdet : W.J.det ≠ 0 := by
      intro h0
      apply det_ne_zero_of_hasSig _ (hW.sig w)
      rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
    have hJinj : Function.Injective W.J.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hJdet))
    have hσinj : Function.Injective σ := fun a b h => by rw [← hinv a, ← hinv b, h]
    have hιinj : Function.Injective H'.ι.mulVec := by
      intro u v h
      have := hinj (a₁ := (u, 0, 0)) (a₂ := (v, 0, 0)) (by rw [hΦ, hΦ]; simpa using h)
      simpa using congrArg Prod.fst this
    intro v v' hvv
    rw [← sub_eq_zero]
    have h0 : (H'.ιᵀ * W.J * H'.ι.map σ) *ᵥ (v - v') = 0 := by rw [Matrix.mulVec_sub, hvv, sub_self]
    set c : Fin d₁ → E := fun j => σ ((v - v') j) with hcdef
    have hc : H'.ι.map σ *ᵥ (v - v') = fun i => σ ((H'.ι *ᵥ c) i) := by
      ext i; simp [Matrix.mulVec, dotProduct, map_sum, c, hinv]
    have h1 : ∀ u, form σ W.J (H'.ι *ᵥ u) (H'.ι *ᵥ c) = 0 := by
      intro u
      have : form σ W.J (H'.ι *ᵥ u) (H'.ι *ᵥ c) = u ⬝ᵥ ((H'.ιᵀ * W.J * H'.ι.map σ) *ᵥ (v - v')) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc, Matrix.dotProduct_mulVec,
          Matrix.vecMul_transpose, form]
      rw [this, h0, dotProduct_zero]
    have h2 : ∀ z, form σ W.J z (H'.ι *ᵥ c) = 0 := by
      intro z
      obtain ⟨⟨u, a, b⟩, rfl⟩ := hsurj z
      rw [hΦ, hlin, h1, hxι, hyι]; ring
    have h3 : W.J *ᵥ (fun i => σ ((H'.ι *ᵥ c) i)) = 0 := by
      ext i
      have := h2 (Pi.single i 1)
      rw [form, single_dotProduct, one_mul] at this
      simpa using this
    have h4 : H'.ι *ᵥ c = 0 := by
      have := hJinj (h3.trans (Matrix.mulVec_zero _).symm)
      ext i
      exact hσinj ((congrFun this i).trans (map_zero σ).symm)
    have h5 : c = 0 := hιinj (h4.trans (Matrix.mulVec_zero _).symm)
    ext j
    have := congrFun h5 j
    simp only [c, Pi.zero_apply] at this
    simpa using hσinj (this.trans (map_zero σ).symm)

end GlobalTheory.PlaneFrame
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PlaneProj
open Matrix
variable {A : Type} [CommRing A] {m n k : Type} [Fintype m] [Fintype n] [Fintype k]

theorem mul_vmv (M : Matrix m n A) (u : n → A) (w : k → A) : M * vecMulVec u w = vecMulVec (M *ᵥ u) w := by
  ext i j; simp [vecMulVec_apply, mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem vmv_transpose (u : m → A) (w : n → A) : (vecMulVec u w)ᵀ = vecMulVec w u := by
  ext i j; simp [vecMulVec_apply, mul_comm]

theorem vmv_map (c : A →+* A) (u : m → A) (w : n → A) : (vecMulVec u w).map c = vecMulVec (c ∘ u) (c ∘ w) := by
  ext i j; simp [vecMulVec_apply]

theorem vmv_mul_vmv (a : m → A) (b : n → A) (u : n → A) (w : k → A) :
    vecMulVec a b * vecMulVec u w = (b ⬝ᵥ u) • vecMulVec a w := by
  ext i j; simp [vecMulVec_apply, mul_apply, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem vmv_mulVec (u : m → A) (w : n → A) (z : n → A) : vecMulVec u w *ᵥ z = (w ⬝ᵥ z) • u := by
  ext i; simp [vecMulVec_apply, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem proj_core {d d₁ : Type} [Fintype d] [Fintype d₁] [DecidableEq d] [DecidableEq d₁] (c : A →+* A)
    (P J : Matrix d d A) (J₁ : Matrix d₁ d₁ A) (ι : Matrix d d₁ A) (π : Matrix d₁ d A) (x y : d → A)
    (hP : Pᵀ * J * P.map c = J) (hPx : P *ᵥ x = x)
    (hframe : vecMulVec x (J *ᵥ (c ∘ y)) + ι * π - vecMulVec y (J *ᵥ (c ∘ x)) = 1)
    (hgram : ιᵀ * J * ι.map c = J₁) (hιx : (ιᵀ * J) *ᵥ (c ∘ x) = 0) (hxι : x ᵥ* (J * ι.map c) = 0)
    (hxx : x ⬝ᵥ (J *ᵥ (c ∘ x)) = 0) (hJ₁ : IsUnit J₁.det) :
    (π * P * ι)ᵀ * J₁ * (π * P * ι).map c = J₁ ∧ IsUnit (π * P * ι).det ∧
      ∀ z, P *ᵥ (ι *ᵥ z) = ι *ᵥ ((π * P * ι) *ᵥ z) + ((J *ᵥ (c ∘ y)) ⬝ᵥ (P *ᵥ (ι *ᵥ z))) • x := by
  set α : d₁ → A := (J *ᵥ (c ∘ y)) ᵥ* (P * ι) with hα
  have hcx : c ∘ x = P.map c *ᵥ (c ∘ x) := by
    funext i; rw [Function.comp_apply, ← RingHom.map_mulVec, hPx]
  have hxP : x ᵥ* Pᵀ = x := by rw [vecMul_transpose, hPx]
  have hwx : (J *ᵥ (c ∘ x)) ᵥ* (P * ι) = 0 := by
    rw [← mulVec_transpose, transpose_mul, hcx, mulVec_mulVec, mulVec_mulVec,
      show ιᵀ * Pᵀ * J * P.map c = ιᵀ * (Pᵀ * J * P.map c) by simp only [Matrix.mul_assoc], hP, hιx]
  have hιπ : ι * π = 1 - vecMulVec x (J *ᵥ (c ∘ y)) + vecMulVec y (J *ᵥ (c ∘ x)) := by
    rw [← hframe]; abel
  have hιh : ι * (π * P * ι) = P * ι - vecMulVec x α := by
    rw [show ι * (π * P * ι) = (ι * π) * (P * ι) by simp only [Matrix.mul_assoc], hιπ, Matrix.add_mul, Matrix.sub_mul,
      Matrix.one_mul, vecMulVec_mul, vecMulVec_mul, hwx]
    ext i j; simp [vecMulVec_apply, α]
  have k1 : (P * ι)ᵀ * J * (P * ι).map c = J₁ := by
    calc (P * ι)ᵀ * J * (P * ι).map c = ιᵀ * (Pᵀ * J * P.map c) * ι.map c := by
          rw [Matrix.map_mul, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J₁ := by rw [hP, hgram]
  have k2 : (P * ι)ᵀ * J * (vecMulVec x α).map c = 0 := by
    have : ((P * ι)ᵀ * J) *ᵥ (c ∘ x) = 0 := by
      rw [hcx, mulVec_mulVec, transpose_mul,
        show ιᵀ * Pᵀ * J * P.map c = ιᵀ * (Pᵀ * J * P.map c) by simp only [Matrix.mul_assoc], hP, hιx]
    rw [vmv_map, mul_vmv, this]; ext i j; simp [vecMulVec_apply]
  have k3 : (vecMulVec x α)ᵀ * J * (P * ι).map c = 0 := by
    have : x ᵥ* (J * (P * ι).map c) = 0 := by
      calc x ᵥ* (J * (P * ι).map c) = (x ᵥ* Pᵀ) ᵥ* (J * (P.map c * ι.map c)) := by rw [hxP, Matrix.map_mul]
        _ = x ᵥ* (Pᵀ * J * P.map c * ι.map c) := by rw [vecMul_vecMul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hP, hxι]
    rw [vmv_transpose, Matrix.mul_assoc, vecMulVec_mul, this]; ext i j; simp [vecMulVec_apply]
  have k4 : (vecMulVec x α)ᵀ * J * (vecMulVec x α).map c = 0 := by
    rw [vmv_transpose, vmv_map, vecMulVec_mul, vmv_mul_vmv, ← dotProduct_mulVec, hxx, zero_smul]
  have hms : (P * ι - vecMulVec x α).map c = (P * ι).map c - (vecMulVec x α).map c := by
    ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have hU : (π * P * ι)ᵀ * J₁ * (π * P * ι).map c = J₁ := by
    have e0 : (π * P * ι)ᵀ * J₁ * (π * P * ι).map c = (ι * (π * P * ι))ᵀ * J * (ι * (π * P * ι)).map c := by
      simp only [← hgram, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e0, hιh, transpose_sub, hms, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, k1, k2, k3, k4]; abel
  set h := π * P * ι with hh
  refine ⟨hU, ?_, fun z => ?_⟩
  · have e := congrArg Matrix.det hU
    rw [det_mul, det_mul, det_transpose, show h.map c = c.mapMatrix h from rfl, ← RingHom.map_det] at e
    have e' : (h.det * c h.det) * J₁.det = 1 * J₁.det := by linear_combination e
    have h1 : h.det * c h.det = 1 := hJ₁.mul_right_cancel e'
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  · have e3 : (ι * h) *ᵥ z = (P * ι) *ᵥ z - (α ⬝ᵥ z) • x := by rw [hιh, sub_mulVec, vmv_mulVec]
    have e4 : α ⬝ᵥ z = (J *ᵥ (c ∘ y)) ⬝ᵥ (P *ᵥ (ι *ᵥ z)) := by rw [hα, ← dotProduct_mulVec, mulVec_mulVec]
    rw [← mulVec_mulVec z ι h, ← mulVec_mulVec z P ι, e4] at e3
    rw [e3]; abel

end GlobalTheory.PlaneProj

namespace GlobalTheory.PlaneProj
open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR' (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] a) = (1 : AF F) ⊗ₜ[F] σ a
  simp

theorem cA_incV (σ : E →ₐ[F] E) {n : ℕ} (v : Fin n → E) :
    ⇑((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) ∘ incV F v = incV F (⇑σ ∘ v) := by
  funext i; exact cA_inclR' σ (v i)

theorem incM_map (σ : E →ₐ[F] E) {m n : Type} (M : Matrix m n E) :
    (incM F M).map ⇑((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) = incM F (M.map σ) := by
  ext i j; exact cA_inclR' σ (M i j)

theorem incM_mulVec' {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F M *ᵥ incV F v = incV F (M *ᵥ v) := by
  funext i; exact (RingHom.map_mulVec (inclR (F := F) (AF F)) M v i).symm

theorem incV_vecMul {m n : ℕ} (v : Fin m → E) (M : Matrix (Fin m) (Fin n) E) :
    incV F v ᵥ* incM F M = incV F (v ᵥ* M) := by
  funext j; exact (RingHom.map_vecMul (inclR (F := F) (AF F)) M v j).symm

theorem incV_dot {n : ℕ} (u w : Fin n → E) : incV F u ⬝ᵥ incV F w = inclR (F := F) (AF F) (u ⬝ᵥ w) := by
  simp only [incV, dotProduct, map_sum, map_mul]

theorem incM_mul {m n k : Type} [Fintype n] (M : Matrix m n E) (N : Matrix n k E) :
    incM F M * incM F N = incM F (M * N) := (Matrix.map_mul (f := inclR (F := F) (AF F))).symm

theorem incM_vmv {m n : ℕ} (u : Fin m → E) (w : Fin n → E) :
    vecMulVec (incV F u) (incV F w) = incM F (vecMulVec u w) := by
  ext i j; simp [incM, incV, vecMulVec_apply]

theorem incM_transpose {m n : Type} (M : Matrix m n E) : (incM F M)ᵀ = incM F Mᵀ := rfl

theorem incV_zero {n : ℕ} : incV F (0 : Fin n → E) = 0 := by funext i; simp [incV]

end GlobalTheory.PlaneProj

open GlobalTheory.PlaneProj Matrix in

theorem GlobalTheory.PlaneProj.exists_levi_proj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ p : UA σ W.J, mat p *ᵥ incV F H'.x = incV F H'.x → ∃ h₁ : UA σ W₁.J,
      ∀ z : Fin d₁ → AE F E, ∃ a : AE F E, mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H'.x := by
  intro F E _ _ _ _ _ σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH p hp
  obtain ⟨π, -, hfr, hJ₁⟩ := GlobalTheory.PlaneFrame.frame_dual_gram F E σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH
  have hsk := GlobalTheory.PlaneFrame.form_skew hσ hW.skew
  set c : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hc

  have eιx : (H'.ιᵀ * W.J) *ᵥ (⇑σ ∘ H'.x) = 0 := by
    funext j
    have h0 := (hH.orth (Pi.single j 1)).1
    rw [form, dotProduct_comm, dotProduct_mulVec, dotProduct_single_one] at h0
    rw [Pi.zero_apply, ← h0, ← mulVec_mulVec, mulVec_transpose]; rfl
  have exι : H'.x ᵥ* (W.J * H'.ι.map σ) = 0 := by
    funext j
    have h0 : form σ W.J H'.x (H'.ι *ᵥ Pi.single j 1) = 0 := by
      rw [hsk, (hH.orth _).1, map_zero, neg_zero]
    rw [Pi.zero_apply, ← h0, form, ← dotProduct_single_one (H'.x ᵥ* _) j, ← dotProduct_mulVec, ← mulVec_mulVec]
    congr 2
    funext i; simp [mulVec, dotProduct, Pi.single_apply]
  have hframe : vecMulVec (incV F H'.x) (incM F W.J *ᵥ (c ∘ incV F H'.y)) + incM F H'.ι * incM F π -
      vecMulVec (incV F H'.y) (incM F W.J *ᵥ (c ∘ incV F H'.x)) = 1 := by
    rw [cA_incV, cA_incV, incM_mulVec', incM_mulVec', incM_vmv, incM_vmv, incM_mul]
    have e1 : incM F (vecMulVec H'.x (W.J *ᵥ (⇑σ ∘ H'.y))) + incM F (H'.ι * π) - incM F (vecMulVec H'.y (W.J *ᵥ (⇑σ ∘ H'.x))) =
        incM F (vecMulVec H'.x (W.J *ᵥ (⇑σ ∘ H'.y)) + H'.ι * π - vecMulVec H'.y (W.J *ᵥ (⇑σ ∘ H'.x))) := by
      ext i j; simp only [incM, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, map_add, map_sub]
    rw [e1]
    have e2 : vecMulVec H'.x (W.J *ᵥ (⇑σ ∘ H'.y)) + H'.ι * π - vecMulVec H'.y (W.J *ᵥ (⇑σ ∘ H'.x)) = 1 := hfr
    rw [e2]; ext i j; simp [incM, Matrix.one_apply]
  have hgram : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map c = incM F W₁.J := by
    rw [incM_map, incM_transpose, incM_mul, incM_mul, hH.gram]
  have hιx : ((incM F H'.ι)ᵀ * incM F W.J) *ᵥ (c ∘ incV F H'.x) = 0 := by
    rw [cA_incV, incM_transpose, incM_mul, incM_mulVec', eιx, incV_zero]
  have hxι : incV F H'.x ᵥ* (incM F W.J * (incM F H'.ι).map c) = 0 := by
    rw [incM_map, incM_mul, incV_vecMul, exι, incV_zero]
  have hxx : incV F H'.x ⬝ᵥ (incM F W.J *ᵥ (c ∘ incV F H'.x)) = 0 := by
    rw [cA_incV, incM_mulVec', incV_dot]
    have : H'.x ⬝ᵥ (W.J *ᵥ (⇑σ ∘ H'.x)) = 0 := hH.xx
    rw [this, map_zero]
  have hJ₁' : IsUnit (incM F W₁.J).det := by
    rw [show incM F W₁.J = (inclR (F := F) (AF F)).mapMatrix W₁.J from rfl, ← RingHom.map_det]
    exact hJ₁.map _
  obtain ⟨hU, hdet, hz⟩ := proj_core c (mat p) (incM F W.J) (incM F W₁.J) (incM F H'.ι) (incM F π) (incV F H'.x) (incV F H'.y)
    p.2 hp hframe hgram hιx hxι hxx hJ₁'
  exact ⟨⟨Matrix.GeneralLinearGroup.mk'' _ hdet, hU⟩, fun z => ⟨_, hz z⟩⟩
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IsoPlaneProj

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_cartan (B : Base F E) {n : ℕ} (Y : Spc F E n)
    (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) : Y.J.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (B.emb w).1
  let M : Matrix (Fin n) (Fin n) ℂ := Complex.I • Y.J.map τ
  let v' : Fin n → ℂ := fun i => τ (v i)
  have hv' : v' ≠ 0 := fun h => hv (funext fun i => τ.injective (by simpa [v'] using congrFun h i))
  have hMv : M *ᵥ v' = 0 := by
    ext i
    have := congrArg τ (congrFun hJv i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this
    simp only [M, v', Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Matrix.smul_apply, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  have hx : star v' ≠ 0 := fun h => hv' (by simpa using congrArg star h)
  have := (h w).2.2 (star v') hx
  rw [star_star] at this
  change 0 < (_ ⬝ᵥ M *ᵥ v').re at this
  rw [hMv, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem frame_of_gram {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {J₁ : Matrix (Fin n₁) (Fin n₁) E} (hsk : ∀ i j, σ (J j i) = -J i j) {x y : Fin n → E} {ι : Matrix (Fin n) (Fin n₁) E}
    (hn : n = n₁ + 2) (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hgram : ιᵀ * J * ι.map σ = J₁)
    (hJ₁ : IsUnit J₁.det) :
    ∃ π : Matrix (Fin n₁) (Fin n) E, vecMulVec x (J *ᵥ (⇑σ ∘ y)) + ι * π - vecMulVec y (J *ᵥ (⇑σ ∘ x)) = 1 := by
  obtain ⟨hax, hay, hbx, hby, hxJ, hyJ, haι, hbι⟩ := GlobalTheory.LeviIdeleHom.dual_facts hσ hsk hxx hyy hxy horth
  set aE := J *ᵥ (⇑σ ∘ y) with haE
  set bE := -(J *ᵥ (⇑σ ∘ x)) with hbE
  let π : Matrix (Fin n₁) (Fin n) E := (J₁⁻¹)ᵀ * (J * ι.map σ)ᵀ
  have hπι : π * ι = 1 := by
    calc π * ι = (J₁⁻¹)ᵀ * (ιᵀ * J * ι.map σ)ᵀ := by
          simp only [π, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [hgram, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hJ₁, Matrix.transpose_one]
  have hv : ∀ w : Fin n → E, (⇑σ ∘ w) ᵥ* ι.map σ = ⇑σ ∘ (w ᵥ* ι) := fun w =>
    funext fun j => by simp [vecMul, dotProduct, map_sum]
  have hπx : π *ᵥ x = 0 := by
    have inner : (J * ι.map σ)ᵀ *ᵥ x = 0 := by
      rw [mulVec_transpose, ← vecMul_vecMul, hxJ, hv, hbι]
      funext j; simp
    simp only [π]
    rw [← mulVec_mulVec, inner, mulVec_zero]
  have hπy : π *ᵥ y = 0 := by
    have inner : (J * ι.map σ)ᵀ *ᵥ y = 0 := by
      rw [mulVec_transpose, ← vecMul_vecMul, hyJ, neg_vecMul, hv, haι]
      funext j; simp
    simp only [π]
    rw [← mulVec_mulVec, inner, mulVec_zero]
  let X : Matrix (Fin n) (Fin 2) E := Matrix.of fun i k => ![x i, y i] k
  let L : Matrix (Fin 2) (Fin n) E := Matrix.of ![aE, bE]
  have hLX : L * X = 1 := by
    ext k l
    fin_cases k <;> fin_cases l <;> simp [Matrix.mul_apply, L, X, Matrix.one_apply]
    · exact hax
    · exact hay
    · exact hbx
    · exact hby
  have hLι : L * ι = 0 := by
    ext k j
    fin_cases k <;> simp [Matrix.mul_apply, L]
    · exact congrFun haι j
    · exact congrFun hbι j
  have hπX : π * X = 0 := by
    ext k l
    fin_cases l <;> simp [Matrix.mul_apply, X]
    · exact congrFun hπx k
    · exact congrFun hπy k
  have hXL : X * L = vecMulVec x aE + vecMulVec y bE := by
    ext i j
    simp [Matrix.mul_apply, X, L, Fin.sum_univ_two, vecMulVec_apply]
  have h1 : Matrix.fromRows π L * Matrix.fromCols ι X = 1 := by
    rw [Matrix.fromRows_mul_fromCols, hπι, hπX, hLι, hLX, Matrix.fromBlocks_one]
  have e : Fin n₁ ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr hn.symm)
  have h2 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  rw [Matrix.fromCols_mul_fromRows, hXL] at h2
  refine ⟨π, ?_⟩
  rw [← h2, hbE, Matrix.vecMulVec_neg]
  abel

end GlobalTheory.IsoPlaneProj
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

open scoped Pointwise

namespace GlobalTheory.ThKOrthVInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isHermND_smul_of_skew {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hsk : ∀ k l, σ (J l k) = -J k l) (hd : J.det ≠ 0) {c : E} (hc : c ≠ 0) (hcs : σ c = -c) :
    IsHermND σ (c • J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · have h1 : σ (J i j) = -J j i := hsk j i
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hcs, hσ, h1]
    ring
  · have e : (J.map σ).det = (σ : E →+* E) J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero _).2 hd)

theorem measure_fundDom_lt_top_smul (hP : GlobalTheory.Published.SiegelSetUnitary) {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {c : E} (hc : c ≠ 0) (hJ : IsHermND σ (c • J.map σ)) {μ : Measure (UA σ J)}
    [μ.IsHaarMeasure] {D : Set (UA σ J)} (hD : IsFundamentalDomain (ratU σ J) D μ) : μ D < ⊤ := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have heq : UG (cA σ) (incM F J) = HR (AF F) σ (c • J.map σ) := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ hc
  let e : UA σ J ≃* GAd σ (c • J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  obtain ⟨S, hSc, hcov, -, hfin, -⟩ := GlobalTheory.SiegelSet.exists_cover hP hcm hJ
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ J) := ⟨by
    have h3 : (fun p : UA σ J × UA σ J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  have hH : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e he he'
  have h1 : μ (e ⁻¹' S) < ⊤ := by
    have h2 := hfin _ hH
    rwa [Measure.map_apply he.measurable hSc.measurableSet] at h2
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ J
  haveI : MeasurableMul (UA σ J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul (ratU σ J) (UA σ J) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : UA σ J => γ.1 * x).measurable⟩
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  have hcov' : D ⊆ ⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D := by
    intro x hx
    obtain ⟨γ, hγ, s, hs, hxs⟩ := hcov (e x)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    refine Set.mem_iUnion.2 ⟨⟨e.symm γ, hr⟩, Set.mem_smul_set.2 ⟨e.symm s, show e (e.symm s) ∈ S by rw [MulEquiv.apply_symm_apply]; exact hs, ?_⟩, hx⟩
    change e.symm γ * e.symm s = x
    rw [← map_mul, ← hxs, MulEquiv.symm_apply_apply]
  calc μ D ≤ μ (⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D) := measure_mono hcov'
    _ ≤ ∑' γ : ratU σ J, μ (γ • (e ⁻¹' S) ∩ D) := measure_iUnion_le _
    _ = μ (e ⁻¹' S) := (hD.measure_eq_tsum _).symm
    _ < ⊤ := h1

theorem norm_le_qht_of_le_ht {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : UA σ J → ℂ}
    (hgi : ∀ γ ∈ ratU σ J, ∀ x, g (γ * x) = g x) {C : ℝ} {k : ℕ} (hC : ∀ h, ‖g h‖ ≤ C * (ht h : ℝ) ^ k) (h : UA σ J) :
    ‖g h‖ ≤ max C 0 * (qht h : ℝ) ^ k := by
  let M : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have e1 : M * qht h ^ k = ⨅ γ : ratU σ J, M * ht (γ.1 * h) ^ k :=
    Monotone.map_ciInf_of_continuousAt (f := fun x : ℝ≥0 => M * x ^ k)
      ((continuous_const.mul (continuous_pow k)).continuousAt)
      (fun x y hxy => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hxy k) (by positivity))
      (OrderBot.bddBelow _)
  have e2 : ‖g h‖₊ ≤ M * qht h ^ k := by
    rw [e1]
    refine le_ciInf fun γ => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, ← hgi γ.1 γ.2 h]
    refine (hC _).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have e3 := NNReal.coe_le_coe.2 e2
  push_cast at e3
  exact e3

end GlobalTheory.ThKOrthVInt
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.DescB.PlaneTwo GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.TwoPlaneWitt

open Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

theorem hE_smul_map {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c s t : E)
    (x y : Fin n → E) : hE σ (c • J.map σ) (s • x) (t • y) = σ s * t * c * σ (form σ J x y) := by
  simp only [hE, form, dotProduct, mulVec, Finset.mul_sum, map_sum, map_mul, Function.comp_apply, hσ, Pi.smul_apply,
    smul_eq_mul, Matrix.smul_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    show σ (s * x i) * (c * σ (J i j)) * (t * y j) = _
    rw [map_mul]; ring

omit [NumberField F] [NumberField E] in

theorem form_mulVec {σ : E →ₐ[F] E} {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin m) E)
    (u v : Fin m → E) : form σ J (ι *ᵥ u) (ι *ᵥ v) = form σ (ιᵀ * J * ι.map σ) u v := by
  have e : (⇑σ ∘ (ι *ᵥ v)) = ι.map σ *ᵥ (⇑σ ∘ v) := funext fun i => by simp [mulVec, dotProduct, map_sum]
  show (ι *ᵥ u) ⬝ᵥ J *ᵥ (⇑σ ∘ (ι *ᵥ v)) = u ⬝ᵥ (ιᵀ * J * ι.map σ) *ᵥ (⇑σ ∘ v)
  rw [e, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u, vecMul_transpose]

omit [NumberField F] [NumberField E] in

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) : form σ J x y = -σ (form σ J y x) := by
  simp only [form, dotProduct, mulVec, Finset.mul_sum, map_sum, map_mul, Function.comp_apply, hσ, hJ,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.TwoPlaneWitt

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section
namespace GlobalTheory.PlaneFrameCons
open Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gram_entry {n r s : ℕ} (σ : E →ₐ[F] E) (M : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin r) E)
    (B : Matrix (Fin n) (Fin s) E) (i : Fin r) (j : Fin s) :
    (cT (σ : E →+* E) A * M * B) i j = hE σ M (fun k => A k i) (fun k => B k j) := by
  simp only [hE, Formalism.UG.hform, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    RingHom.coe_coe]
  rw [Finset.sum_comm]

theorem gram_mulVec_entry {n r : ℕ} (σ : E →ₐ[F] E) (M : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin r) E)
    (z : Fin n → E) (i : Fin r) :
    ((cT (σ : E →+* E) A * M) *ᵥ z) i = hE σ M (fun k => A k i) z := by
  simp only [hE, Formalism.UG.hform, cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, RingHom.coe_coe]
  rw [Finset.sum_comm]

variable [NumberField F] [NumberField E]

theorem hE_eq {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E)
    (u v : Fin n → E) : hE σ (c • J.map σ) u v = c * σ (form σ J u v) := by
  have := GlobalTheory.TwoPlaneWitt.hE_smul_map hσ J c 1 1 u v
  simpa using this

theorem exists_isWittFrame_cons : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J → ∀ c₀ : E, c₀ ≠ 0 →
      IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
        ∃ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' ∧
          (∀ k, X' k 0 = H.x k) ∧ (∀ k, Y' k 0 = c₀⁻¹ * H.y k) ∧
          ∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i := by
  intro F E _ _ _ _ _ σ hcm n n₁ W W₁ H hskew hn hxx hyy hxy horth hg c₀ hc hND₁ hND r Xf Yf hW
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  set M := c₀ • W.J.map σ with hM
  set M₁ := c₀ • W₁.J.map σ with hM₁

  have hι : ∀ u v, hE σ M (H.ι *ᵥ u) (H.ι *ᵥ v) = hE σ M₁ u v := fun u v => by
    rw [hM, hM₁, hE_eq hσ, hE_eq hσ, GlobalTheory.TwoPlaneWitt.form_mulVec, hg]
  have hcol : ∀ (A : Matrix (Fin n₁) (Fin r) E) (i : Fin r), (fun k => (H.ι * A) k i) = H.ι *ᵥ fun k => A k i :=
    fun A i => funext fun k => by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hyx : form σ W.J H.y H.x = -1 := by rw [GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ, hxy, map_one]
  have hxι : ∀ u, form σ W.J H.x (H.ι *ᵥ u) = 0 := fun u => by
    rw [GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ, (horth u).1, map_zero, neg_zero]
  have hyι : ∀ u, form σ W.J H.y (H.ι *ᵥ u) = 0 := fun u => by
    rw [GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ, (horth u).2, map_zero, neg_zero]
  let X' : Matrix (Fin n) (Fin (r + 1)) E := Matrix.of fun k => Fin.cons (H.x k) (fun i => (H.ι * Xf) k i)
  let Y' : Matrix (Fin n) (Fin (r + 1)) E := Matrix.of fun k => Fin.cons (c₀⁻¹ * H.y k) (fun i => (H.ι * Yf) k i)
  have cX0 : (fun k => X' k 0) = H.x := funext fun k => by simp [X']
  have cY0 : (fun k => Y' k 0) = c₀⁻¹ • H.y := funext fun k => by simp [Y']
  have cXs : ∀ i : Fin r, (fun k => X' k i.succ) = H.ι *ᵥ fun k => Xf k i := fun i => by
    rw [← hcol]; funext k; simp [X']
  have cYs : ∀ i : Fin r, (fun k => Y' k i.succ) = H.ι *ᵥ fun k => Yf k i := fun i => by
    rw [← hcol]; funext k; simp [Y']
  have gXX : ∀ i j, hE σ M₁ (fun k => Xf k i) (fun k => Xf k j) = 0 := fun i j => by
    rw [← gram_entry, hW.xx]; rfl
  have gYY : ∀ i j, hE σ M₁ (fun k => Yf k i) (fun k => Yf k j) = 0 := fun i j => by
    rw [← gram_entry, hW.yy]; rfl
  have gXY : ∀ i j, hE σ M₁ (fun k => Xf k i) (fun k => Yf k j) = (1 : Matrix (Fin r) (Fin r) E) i j := fun i j => by
    rw [← gram_entry, hW.xy]
  have sX : ∀ (s t : E) (a b : Fin n → E), hE σ M (s • a) (t • b) = σ s * t * c₀ * σ (form σ W.J a b) :=
    fun s t a b => GlobalTheory.TwoPlaneWitt.hE_smul_map hσ W.J c₀ s t a b
  refine ⟨X', Y', ⟨?_, ?_, ?_, ?_⟩, fun k => by simp [X'], fun k => by simp [Y'], fun k i => ⟨by simp [X'], by simp [Y']⟩⟩
  · ext i j
    rw [gram_entry]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [cX0, ← one_smul E H.x, sX]; simp [hxx]
    · rw [cX0, cXs, ← one_smul E H.x, ← one_smul E (H.ι *ᵥ _), sX]; simp [hxι]
    · rw [cX0, cXs, ← one_smul E H.x, ← one_smul E (H.ι *ᵥ _), sX]; simp [(horth _).1]
    · rw [cXs, cXs, hι, gXX]; rfl
  · ext i j
    rw [gram_entry]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [cY0, sX]; simp [hyy]
    · rw [cY0, cYs, ← one_smul E (H.ι *ᵥ _), sX]; simp [hyι]
    · rw [cY0, cYs, ← one_smul E (H.ι *ᵥ _), sX]; simp [(horth _).2]
    · rw [cYs, cYs, hι, gYY]; rfl
  · ext i j
    rw [gram_entry]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [cX0, cY0, ← one_smul E H.x, sX]; simp [hxy, hc]
    · rw [Matrix.one_apply_ne (Fin.succ_ne_zero j).symm, cX0, cYs, ← one_smul E H.x, ← one_smul E (H.ι *ᵥ _), sX]; simp [hxι]
    · rw [Matrix.one_apply_ne (Fin.succ_ne_zero i), cY0, cXs, ← one_smul E (H.ι *ᵥ _), sX]; simp [(horth _).2]
    · rw [cXs, cYs, hι, gXY]; simp [Matrix.one_apply]
  · intro z h1 h2 h3
    have σinj : ∀ a : E, σ a = 0 → a = 0 := fun a ha => by rw [← hσ a, ha, map_zero]
    have fxz : form σ W.J H.x z = 0 := by
      have e := congrFun h1 0
      rw [gram_mulVec_entry, cX0, hM, hE_eq hσ] at e
      exact σinj _ ((mul_eq_zero.1 e).resolve_left hc)
    have fyz : form σ W.J H.y z = 0 := by
      have e := congrFun h2 0
      rw [gram_mulVec_entry, cY0, ← one_smul E z, sX, Pi.zero_apply, mul_one] at e
      have hs : σ c₀⁻¹ ≠ 0 := fun h => inv_ne_zero hc (σinj _ h)
      rcases mul_eq_zero.1 e with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hs
        · exact absurd h hc
      · exact σinj _ h
    have hdet : W₁.J.det ≠ 0 := fun h => hND₁.2 (by
      rw [hM₁, Matrix.det_smul, show (W₁.J.map σ).det = σ W₁.J.det by exact (RingHom.map_det (σ : E →+* E) W₁.J).symm, h, map_zero, mul_zero])
    obtain ⟨α, β, z₁, rfl⟩ := GlobalTheory.UnipCocptForm.decomp σ W.J W₁.J H.x H.y H.ι hskew hσ hn hxx hyy hxy horth hg hdet z
    have fzx : form σ W.J (α • H.x + β • H.y + H.ι *ᵥ z₁) H.x = -β := by
      rw [GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_smul,
        GlobalTheory.UnipCocptForm.form_smul, hxx, hyx, (horth z₁).1]; ring
    have fzy : form σ W.J (α • H.x + β • H.y + H.ι *ᵥ z₁) H.y = α := by
      rw [GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_smul,
        GlobalTheory.UnipCocptForm.form_smul, hxy, hyy, (horth z₁).2]; ring
    have hβ : β = 0 := by
      have := GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ (α • H.x + β • H.y + H.ι *ᵥ z₁) H.x
      rw [fzx, fxz, map_zero, neg_zero] at this
      exact neg_eq_zero.1 this
    have hα : α = 0 := by
      have := GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ (α • H.x + β • H.y + H.ι *ᵥ z₁) H.y
      rwa [fzy, fyz, map_zero, neg_zero] at this
    subst hα hβ
    simp only [zero_smul, zero_add] at h1 h2 h3 ⊢
    have k1 : (cT (σ : E →+* E) Xf * M₁) *ᵥ z₁ = 0 := funext fun i => by
      have e := congrFun h1 i.succ
      rw [gram_mulVec_entry, cXs, hι] at e
      rw [gram_mulVec_entry, e]; rfl
    have k2 : (cT (σ : E →+* E) Yf * M₁) *ᵥ z₁ = 0 := funext fun i => by
      have e := congrFun h2 i.succ
      rw [gram_mulVec_entry, cYs, hι] at e
      rw [gram_mulVec_entry, e]; rfl
    rw [hW.aniso z₁ k1 k2 ((hι z₁ z₁).symm.trans h3), Matrix.mulVec_zero]
end GlobalTheory.PlaneFrameCons
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_plane_orthogonal_gram_restriction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J → ∀ c₀ : E, c₀ ≠ 0 →
      IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
        ∃ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' ∧
          (∀ k, X' k 0 = H.x k) ∧ (∀ k, Y' k 0 = c₀⁻¹ * H.y k) ∧
          ∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i := by
  first | exact @GlobalTheory.PlaneFrameCons.exists_isWittFrame_cons | exact GlobalTheory.PlaneFrameCons.exists_isWittFrame_cons | (intros; apply GlobalTheory.PlaneFrameCons.exists_isWittFrame_cons <;> assumption)
end
