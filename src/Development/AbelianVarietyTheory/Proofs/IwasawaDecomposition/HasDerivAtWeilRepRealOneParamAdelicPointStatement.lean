import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeisenbergSmoothVectorDerivativeCalculus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorActionUnitaryPolynomialBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakWeilRepEqUnitSmulOscillatorRealPoints

section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

noncomputable section

namespace GlobalTheory.Mem.Lift.Normal

variable {ι : Type}

theorem real_lin_smul (l : (ι → ℂ) →ₗ[ℝ] ℂ) (c : ℂ) (z : ι → ℂ) :
    l (c • z) = c.re * l z + c.im * l (I • z) := by
  have hc : c • z = c.re • z + c.im • (I • z) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  rw [hc, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem real_lin_I_I (l : (ι → ℂ) →ₗ[ℝ] ℂ) (z : ι → ℂ) : l (I • I • z) = - l z := by
  rw [smul_smul, I_mul_I, neg_one_smul, map_neg]

def linPart (l : (ι → ℂ) →ₗ[ℝ] ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := l z - I * l (I • z)
  map_add' x y := by simp only [smul_add, map_add]; ring
  map_smul' c z := by
    rw [smul_comm I c z, real_lin_smul l c z, real_lin_smul l c (I • z), real_lin_I_I, RingHom.id_apply, smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    linear_combination (c.im * l (I • z)) * I_mul_I

def antiPart (l : (ι → ℂ) →ₗ[ℝ] ℂ) : (ι → ℂ) →ₗ⋆[ℂ] ℂ where
  toFun z := l z + I * l (I • z)
  map_add' x y := by simp only [smul_add, map_add]; ring
  map_smul' c z := by
    rw [smul_comm I c z, real_lin_smul l c z, real_lin_smul l c (I • z), real_lin_I_I, smul_eq_mul]
    have : (starRingEnd ℂ) c = c.re - c.im * I := by
      apply Complex.ext <;> simp
    rw [this]
    linear_combination (c.im * l (I • z)) * I_mul_I

theorem im_add_I_re (h : ℂ) : ((h.im : ℂ) + I * ((I * h).im : ℂ)) = I * (starRingEnd ℂ) h := by
  apply Complex.ext <;> simp

theorem im_sub_I_re (h : ℂ) : ((h.im : ℂ) - I * ((I * h).im : ℂ)) = - I * h := by
  apply Complex.ext <;> simp

variable [Fintype ι] [DecidableEq ι]

def nC (X : Matrix ι ι ℂ) (i : ι × ι × Bool × Bool) : ℂ :=
  X i.1 i.2.1 * (-(1 / (4 * π))) * (if i.2.2.1 then -I else 1) * (if i.2.2.2 then I else 1)

def nP (i : ι × ι × Bool × Bool) : ι → ℂ :=
  if i.2.2.1 then I • Pi.single i.1 1 else Pi.single i.1 1

def nQ (H : Matrix ι ι ℂ) (i : ι × ι × Bool × Bool) : ι → ℂ :=
  if i.2.2.2 then I • H⁻¹ *ᵥ Pi.single i.2.1 1 else H⁻¹ *ᵥ Pi.single i.2.1 1

theorem sum_lin (X : Matrix ι ι ℂ) (A : (ι → ℂ) →ₗ[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * (v j * A (Pi.single k 1)) = A (X *ᵥ v) := by
  have hx : X *ᵥ v = ∑ k, (∑ j, X k j * v j) • (Pi.single k (1 : ℂ) : ι → ℂ) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  rw [hx, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_anti {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0)
    (A : (ι → ℂ) →ₗ⋆[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1)) = - A (X *ᵥ v) := by
  have hinv' : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hd)
  set w := X *ᵥ v with hw

  have hexp : w = ∑ j, (H *ᵥ w) j • (H⁻¹ *ᵥ Pi.single j 1) := by
    have h1 : H *ᵥ w = ∑ j, (H *ᵥ w) j • (Pi.single j (1 : ℂ) : ι → ℂ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    calc w = H⁻¹ *ᵥ (H *ᵥ w) := by rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
      _ = H⁻¹ *ᵥ ∑ j, (H *ᵥ w) j • (Pi.single j (1 : ℂ) : ι → ℂ) := by rw [← h1]
      _ = _ := by
        rw [Matrix.mulVec_sum]
        simp only [Matrix.mulVec_smul]
  have hA : A w = ∑ j, (starRingEnd ℂ) ((H *ᵥ w) j) * A (H⁻¹ *ᵥ Pi.single j 1) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smulₛₗ, smul_eq_mul]

  have hcoef : ∀ j, ∑ k, X k j * (star v ⬝ᵥ H *ᵥ Pi.single k 1) = -(starRingEnd ℂ) ((H *ᵥ w) j) := by
    intro j
    have hs : ∀ k, star v ⬝ᵥ H *ᵥ Pi.single k 1 = (star v ᵥ* H) k := by
      intro k
      rw [Matrix.dotProduct_mulVec]
      simp [dotProduct, Pi.single_apply]
    have hXH : (H * X)ᴴ = -(H * X) := by
      rw [Matrix.conjTranspose_mul, hH]
      exact eq_neg_of_add_eq_zero_left hX
    have hstar : (starRingEnd ℂ) ((H *ᵥ w) j) = (star v ᵥ* (H * X)ᴴ) j := by
      rw [hw, Matrix.mulVec_mulVec, ← Matrix.star_mulVec]
      rfl
    simp_rw [hs]
    rw [hstar, hXH, Matrix.vecMul_neg, Pi.neg_apply, neg_neg, ← Matrix.vecMul_vecMul]
    simp [vecMul, dotProduct, mul_comm]
  rw [hA, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ k, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1))
      = (∑ k, X k j * (star v ⬝ᵥ H *ᵥ Pi.single k 1)) * A (H⁻¹ *ᵥ Pi.single j 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
        rw [hcoef j]
        ring

theorem isQuadOf_normal {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0) :
    IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) (nC X) nP (nQ H) := by
  intro l v
  beta_reduce
  have hinv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hd)

  have hkj : ∀ k j, (∑ b1 : Bool, ∑ b2 : Bool, nC X (k, j, b1, b2) *
      (((star v ⬝ᵥ H *ᵥ nQ H (k, j, b1, b2)).im : ℂ) * l (nP (k, j, b1, b2)) +
        ((star v ⬝ᵥ H *ᵥ nP (k, j, b1, b2)).im : ℂ) * l (nQ H (k, j, b1, b2)))) =
      X k j * (-(1 / (4 * π))) * (I * (v j * linPart l (Pi.single k 1)) +
        (-I) * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1))) := by
    intro k j
    have ha : ((star v ⬝ᵥ H *ᵥ (H⁻¹ *ᵥ Pi.single j 1)).im : ℂ) +
        I * ((star v ⬝ᵥ H *ᵥ (I • H⁻¹ *ᵥ Pi.single j 1)).im : ℂ) = I * v j := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, im_add_I_re, Matrix.mulVec_mulVec, hinv,
        Matrix.one_mulVec, dotProduct_single, mul_one, Pi.star_apply, starRingEnd_apply, star_star]
    have hp : ((star v ⬝ᵥ H *ᵥ Pi.single k 1).im : ℂ) -
        I * ((star v ⬝ᵥ H *ᵥ (I • Pi.single k 1)).im : ℂ) = -I * (star v ⬝ᵥ H *ᵥ Pi.single k 1) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, im_sub_I_re]
    simp only [Fintype.sum_bool, nC, nP, nQ, Bool.false_eq_true, ↓reduceIte, linPart, antiPart, LinearMap.coe_mk, AddHom.coe_mk]
    linear_combination (X k j * (-(1 / (4 * π))) * (l (Pi.single k 1) - I * l (I • Pi.single k 1))) * ha +
      (X k j * (-(1 / (4 * π))) * (l (H⁻¹ *ᵥ Pi.single j 1) + I * l (I • H⁻¹ *ᵥ Pi.single j 1))) * hp
  have hsum : ∀ F : ι × ι × Bool × Bool → ℂ, ∑ i, F i = ∑ k, ∑ j, ∑ b1, ∑ b2, F (k, j, b1, b2) :=
    fun F => by simp only [Fintype.sum_prod_type]
  rw [hsum, Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hkj k j]
  have hsplit : (∑ k, ∑ j, X k j * (-(1 / (4 * π))) * (I * (v j * linPart l (Pi.single k 1)) +
      (-I) * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1)))) =
      (-(1 / (4 * π)) * I : ℂ) * ((∑ k, ∑ j, X k j * (v j * linPart l (Pi.single k 1))) -
        ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hLA : linPart l (X *ᵥ v) + antiPart l (X *ᵥ v) = 2 * l (X *ᵥ v) := by
    simp only [linPart, antiPart, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfin : ∀ z : ℂ, 2 * (π : ℂ) * I * (-(1 / (4 * (π : ℂ))) * I * (2 * z)) = z := by
    intro z
    rw [show 2 * (π : ℂ) * I * (-(1 / (4 * (π : ℂ))) * I * (2 * z)) = -(I * I) * ((π : ℂ) * (π : ℂ)⁻¹) * z by ring,
      I_mul_I, mul_inv_cancel₀ hπ]
    ring
  rw [hsplit, sum_lin, sum_anti hH hd hX, sub_neg_eq_add, hLA]
  exact hfin _

private theorem sm_add' {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {ρ : (ι → ℂ) → B →L[ℂ] B} {f g : B} (hf : Sm ρ f) (hg : Sm ρ g) : Sm ρ (f + g) := by
  unfold Sm at *
  simp only [map_add]
  exact hf.add hg

private theorem sm_smul' {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {ρ : (ι → ℂ) → B →L[ℂ] B} {f : B} (a : ℂ) (hf : Sm ρ f) : Sm ρ (a • f) := by
  unfold Sm at *
  simp only [map_smul]
  exact hf.const_smul a

theorem quad_normal (H X : Matrix ι ι ℂ) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (ρ : (ι → ℂ) → B →L[ℂ] B) (f : B) (hs : ∀ v, Sm ρ (dH ρ v f)) :
    quad ρ (nC X) nP (nQ H) f = nOp ρ H X f := by
  have hy : ∀ j : ι, Sm ρ (dH ρ (H⁻¹ *ᵥ Pi.single j 1) f) := fun j => hs _
  have hIy : ∀ j : ι, Sm ρ (dH ρ (I • H⁻¹ *ᵥ Pi.single j 1) f) := fun j => hs _

  have hexp : ∀ (u : ι → ℂ) (j : ι), dH ρ u (dOp ρ H j f) = (-(1 / (4 * π)) : ℂ) •
      (dH ρ u (dH ρ (H⁻¹ *ᵥ Pi.single j 1) f) + I • dH ρ u (dH ρ (I • H⁻¹ *ᵥ Pi.single j 1) f)) := by
    intro u j
    unfold dOp
    rw [dH_smul u _ (sm_add' (hy j) (sm_smul' I (hIy j))),
      dH_add u (hy j) (sm_smul' I (hIy j)), dH_smul u I (hIy j)]
  unfold quad nOp xOp
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [nC, nP, nQ, Bool.false_eq_true, ↓reduceIte, hexp]
  module

def omH (H : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((ι → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun x y : ι → ℂ => (star y ⬝ᵥ H *ᵥ x).im)
        (fun x x' y => by simp [mulVec_add])
        (fun r x y => by simp [mulVec_smul])
        (fun x y y' => by simp)
        (fun r x y => by simp))

theorem normal_quad : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H X : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → Xᴴ * H + H * X = 0 → ∃ (κ : Type) (_ : Fintype κ) (c : κ → ℂ) (p q : κ → ι → ℂ), IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) c p q ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ f, Sm ρ f → quad ρ c p q f = nOp ρ H X f := by
  intro ι _ _ H X hH hd hX
  refine ⟨ι × ι × Bool × Bool, inferInstance, nC X, nP, nQ H, isQuadOf_normal hH hd hX, ?_⟩
  intro B _ _ ρ hρ f hf
  exact quad_normal H X ρ f fun v => DCalc.sm_dH (om := omH H) hρ hf v

end GlobalTheory.Mem.Lift.Normal

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift.GenZero

theorem exists_hasDerivAt_char (s : ℝ → ℂ) (hs : ∀ t t', s (t + t') = s t * s t') (h0 : s 0 = 1)
    (hc : ContinuousAt s 0) : ∃ m : ℂ, HasDerivAt s m 0 := by
  have hcont : Continuous s := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have e : s = fun t => s (t - t₀) * s t₀ := funext fun t => by rw [← hs, sub_add_cancel]
    rw [e]
    refine ContinuousAt.mul ?_ continuousAt_const
    exact ContinuousAt.comp (g := s) (f := fun t => t - t₀) (by simpa using hc) (by fun_prop)
  let g : ℝ → ℂ := fun x => ∫ y in (0 : ℝ)..x, s y
  have hg : ∀ x, HasDerivAt g (s x) x := fun x => (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  obtain ⟨ε, hε⟩ : ∃ ε, g ε ≠ 0 := by
    by_contra hn
    push Not at hn
    have h1 : HasDerivAt g 0 0 := by
      rw [show g = fun _ => 0 from funext hn]
      exact hasDerivAt_const _ _
    have := (hg 0).unique h1
    rw [h0] at this
    exact one_ne_zero this
  have e : s = fun t => (g (t + ε) - g t) / g ε := by
    funext t
    rw [eq_div_iff hε]
    have h1 : g (t + ε) - g t = ∫ y in t..(t + ε), s y :=
      intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    rw [h1]
    have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := ε) s t
    rw [add_zero] at h2
    rw [← h2]
    simp only [hs, g]
    exact (intervalIntegral.integral_const_mul _ _).symm
  have h3 : HasDerivAt (fun t => g (t + ε)) (s (0 + ε)) 0 := HasDerivAt.comp_add_const 0 ε (hg _)
  exact ⟨_, ((h3.sub (hg 0)).div_const (g ε)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun e t)⟩

theorem lie_of_path {ι : Type} [Fintype ι] [DecidableEq ι] (H X : Matrix ι ι ℂ) (m : ℝ → Matrix ι ι ℂ) (h0 : m 0 = 1)
    (hm : ∀ t, (m t)ᴴ * H * m t = H) (hX : ∀ k l, HasDerivAt (fun t => m t k l) (X k l) 0) :
    Xᴴ * H + H * X = 0 := by
  ext i j
  have h1 : HasDerivAt (fun t => ∑ l, (∑ k, star (m t k i) * H k l) * m t l j)
      (∑ l, ((∑ k, star (X k i) * H k l) * m 0 l j + (∑ k, star (m 0 k i) * H k l) * X l j)) 0 :=
    HasDerivAt.fun_sum fun l _ =>
      (HasDerivAt.fun_sum fun k _ => (hX k i).star.mul_const (H k l)).mul (hX l j)
  have e : (fun t => ∑ l, (∑ k, star (m t k i) * H k l) * m t l j) = fun _ => H i j := by
    funext t
    rw [← congrFun (congrFun (hm t) i) j]
    simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [e] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  have h3 : (Xᴴ * H * m 0 + (m 0)ᴴ * H * X) i j = 0 := by
    rw [← h2]
    simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Finset.sum_add_distrib]
  rwa [h0, conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h3

open scoped Classical

set_option maxHeartbeats 1000000 in
open GlobalTheory.RealWeil in

theorem exists_generator : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∃ u : ℝ → GlobalTheory.RealWeil.BB ψ S T, (∀ t, ((u t).1 : WO S T → ℂ) = om (γ t) F.1) ∧ HasDerivAt u (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F) 0 := by
  intro D θ σ h ψ hψ S T om hw hc γ hγ hadd hinf X hX
  have hγ0 : γ 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := γ 0) (by rw [← this, mul_one])
  have hH := isHeis_rhoB (S := S) (T := T) h hψ
  have hL := lie_of_path (HM S T) X (fun t => mM θ S T (γ t)) (by simp only [hγ0, map_one])
    (fun t => mM_unitary h.inf _) hX
  obtain ⟨κ, _, c, p, q, hq, hn⟩ := GlobalTheory.Mem.Lift.Normal.normal_quad (Ix S T) (HM S T) X HM_herm HM_det hL
  obtain ⟨Ω, hΩ, -, hd⟩ := GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic (Ix S T) (HM S T) HM_herm HM_det (BB ψ S T) (rhoV hψ σ S T) hH
    (GA D S × GA D T) (mM θ S T) (mM_unitary h.inf)
  obtain ⟨lam, hlam⟩ := hd γ X hγ0 hX κ c p q hq
  have sm := sm_of_theta (S := S) (T := T) h hψ
  choose s hs1 hs using fun t => GlobalTheory.T.weakWeilRep_eq_unit_smul_oscillator_real_points D θ σ h ψ hψ S T om hw Ω hΩ (γ t).1 (hinf t).1 (γ t).2 (hinf t).2
  replace hs : ∀ t (F : BB ψ S T), IsThetaFunO ψ S T F.1 → om (γ t) F.1 = s t • ((Ω (γ t) F).1 : WO S T → ℂ) := hs
  obtain ⟨-, hsmul, hsm, hone, hmul, -⟩ := hΩ
  have cs : ∀ (a : ℂ) (G : BB ψ S T), ((a • G).1 : WO S T → ℂ) = a • (G.1 : WO S T → ℂ) := fun _ _ => rfl
  have hne : ∀ t, s t ≠ 0 := fun t e => by simpa [e] using hs1 t
  have hD : ∀ F : BB ψ S T, IsThetaFunO ψ S T F.1 →
      HasDerivAt (fun t => Ω (γ t) F) (nOp (rhoV hψ σ S T) (HM S T) X F + lam • F) 0 := fun F hF =>
    hn _ _ hH F (sm F hF) ▸ hlam F (sm F hF)
  by_cases hex : ∃ F₀ : BB ψ S T, IsThetaFunO ψ S T F₀.1 ∧ F₀ ≠ 0
  swap
  · push Not at hex
    refine ⟨lam, fun F hF => ⟨fun t => Ω (γ t) F, fun t => ?_, hD F hF⟩⟩
    have e : Ω (γ t) F = 0 := by
      have := hsmul (γ t) 0 F (sm F hF)
      rw [zero_smul, zero_smul] at this
      exact (congrArg (Ω (γ t)) (hex F hF)).trans this
    rw [hs t F hF]
    beta_reduce
    rw [e]
    exact (smul_zero _).symm
  obtain ⟨F₀, hF₀, hne₀⟩ := hex
  have hΩne : ∀ g, Ω g F₀ ≠ 0 := by
    intro g e
    have h1 := hmul g⁻¹ g F₀ (sm _ hF₀)
    have h2 := hsmul g⁻¹ 0 F₀ (sm _ hF₀)
    rw [zero_smul, zero_smul] at h2
    rw [inv_mul_cancel, hone _ (sm _ hF₀), e, h2] at h1
    exact hne₀ h1
  have hth : ∀ t, IsThetaFunO ψ S T (Ω (γ t) F₀).1 := by
    intro t
    have h1 := (thetaSub ψ S T).smul_mem (s t)⁻¹ (hw.om_pres (γ t) _ hF₀)
    rw [hs t F₀ hF₀, smul_smul, inv_mul_cancel₀ (hne t), one_smul] at h1
    exact h1
  have hms : ∀ t t', s (t + t') = s t * s t' := by
    intro t t'
    have h1 := hs (t + t') F₀ hF₀
    rw [hadd, map_mul, Module.End.mul_apply, hs t' F₀ hF₀, map_smul, hs t _ (hth t'), ← hmul _ _ _ (sm _ hF₀),
      smul_smul] at h1
    have h2 : (s t' * s t) • Ω (γ t * γ t') F₀ = s (t + t') • Ω (γ t * γ t') F₀ := QB_ext fun x => by
      rw [cs, cs, h1]
    rw [← smul_left_injective ℂ (hΩne _) h2, mul_comm]
  have hs0 : s 0 = 1 := by
    have := hms 0 0
    rw [add_zero] at this
    exact mul_left_cancel₀ (hne 0) (by rw [← this, mul_one])
  obtain ⟨w, hw₀⟩ : ∃ w, (F₀.1 : WO S T → ℂ) w ≠ 0 := by
    by_contra hn'
    push Not at hn'
    exact hne₀ (QB_ext hn')
  have hcs : ContinuousAt s 0 := by
    have h1 : ContinuousAt (fun t => ev _ _ w (Ω (γ t) F₀)) 0 :=
      (ev _ _ w).continuous.continuousAt.comp (hD F₀ hF₀).continuousAt
    have h2 : ev _ _ w (Ω (γ 0) F₀) ≠ 0 := by
      rw [hγ0, hone _ (sm _ hF₀), ev_apply]
      exact hw₀
    have h3 : ContinuousAt (fun t => om (γ t) F₀.1 w) 0 := ((hc _ hF₀ w).comp hγ).continuousAt
    refine (h3.div h1 h2).congr ?_
    filter_upwards [h1.eventually_ne h2] with t ht
    rw [Pi.div_apply, div_eq_iff ht, hs t F₀ hF₀, ev_apply]
    rfl
  obtain ⟨m, hm⟩ := exists_hasDerivAt_char s hms hs0 hcs
  refine ⟨lam + m, fun F hF => ⟨fun t => s t • Ω (γ t) F, fun t => (cs _ _).trans (hs t F hF).symm, ?_⟩⟩
  have h1 := hm.smul (hD F hF)
  rw [hs0, one_smul, hγ0, hone _ (sm _ hF)] at h1
  rw [add_smul, ← add_assoc]
  exact h1

end GlobalTheory.Mem.Lift.GenZero

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∃ u : ℝ → GlobalTheory.RealWeil.BB ψ S T, (∀ t, ((u t).1 : WO S T → ℂ) = om (γ t) F.1) ∧ HasDerivAt u (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F) 0 := by
  first | exact @GlobalTheory.Mem.Lift.GenZero.exists_generator | exact GlobalTheory.Mem.Lift.GenZero.exists_generator | (intros; apply GlobalTheory.Mem.Lift.GenZero.exists_generator <;> assumption)
end

section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergSmoothVector_derivative_calculus : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ f, Sm ρ f → (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧ (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (om w y : ℂ)) • ρ w f) ∧ (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f) ∧ ∀ u v, dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  first | exact @GlobalTheory.Mem.Lift.DCalc.dH_calculus | exact GlobalTheory.Mem.Lift.DCalc.dH_calculus | (intros; apply GlobalTheory.Mem.Lift.DCalc.dH_calculus <;> assumption)
end

section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.Ccr

theorem comm_comb {A : Type} [Ring A] [Algebra ℂ A] (p p' q q' : A) (s t c₁ c₂ c₃ c₄ : ℂ)
    (h₁ : p * q = q * p + c₁ • (1 : A)) (h₂ : p * q' = q' * p + c₂ • (1 : A))
    (h₃ : p' * q = q * p' + c₃ • (1 : A)) (h₄ : p' * q' = q' * p' + c₄ • (1 : A)) :
    (p + s • p') * (q + t • q') = (q + t • q') * (p + s • p') + (c₁ + t * c₂ + s * c₃ + s * t * c₄) • (1 : A) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h₁, h₂, h₃, h₄]
  module

theorem exists_om {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) :
    ∃ om : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ, ∀ x y, om x y = (star y ⬝ᵥ H *ᵥ x).im := by
  let b : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => (star y ⬝ᵥ H *ᵥ x).im)
    (fun x x' y => by simp [mulVec_add, dotProduct_add])
    (fun r x y => by simp [mulVec_smul, dotProduct_smul])
    (fun x y y' => by simp [add_dotProduct])
    (fun r x y => by simp [smul_dotProduct])
  exact ⟨LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ b), fun x y => rfl⟩

theorem im_self {ι : Type} [Fintype ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (x : ι → ℂ) :
    (star x ⬝ᵥ H *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ H *ᵥ x) = star x ⬝ᵥ H *ᵥ x := by
    rw [← star_dotProduct_star, star_star, star_mulVec, hH, dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h

theorem pair_inv {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (k l : ι) :
    star (H⁻¹ *ᵥ Pi.single l 1) ⬝ᵥ H *ᵥ Pi.single k 1 = if k = l then (1 : ℂ) else 0 := by
  rw [star_mulVec, conjTranspose_nonsing_inv, hH, ← dotProduct_mulVec, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), one_mulVec, dotProduct_single]
  by_cases h : k = l <;> simp [h]

end GlobalTheory.Mem.Lift.Ccr

open GlobalTheory.Mem.Lift.Ccr in

theorem GlobalTheory.Mem.Lift.exists_isCCR_xOp_dOp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∃ x d : ι → Module.End ℂ (smS ρ), (∀ k f, (x k f).1 = xOp ρ k f.1) ∧ (∀ k f, (d k f).1 = dOp ρ H k f.1) ∧ IsCCR x d := by
  intro ι _ _ H hH hd B _ _ ρ hρ
  obtain ⟨om, hom⟩ := exists_om H
  have hρ' : IsHeis (fun x y => om x y) ρ := by simpa only [hom] using hρ
  have key := GlobalTheory.T.heisenbergSmoothVector_derivative_calculus (ι → ℂ) B om ρ (fun x => by rw [hom, im_self hH]) hρ'
  let D : (ι → ℂ) → Module.End ℂ (smS ρ) := fun v =>
    { toFun := fun f => ⟨dH ρ v f.1, (key f.1 f.2).1 v⟩
      map_add' := fun f g => Subtype.ext (dH_add v f.2 g.2)
      map_smul' := fun a f => Subtype.ext (dH_smul v a f.2) }
  have hD : ∀ u v, D u * D v = D v * D u + (2 * π * I * ((star v ⬝ᵥ H *ᵥ u).im : ℂ)) • (1 : Module.End ℂ (smS ρ)) := by
    intro u v
    refine LinearMap.ext fun f => Subtype.ext ?_
    have := (key f.1 f.2).2.2.2.2 u v
    rw [hom, sub_eq_iff_eq_add'] at this
    exact this
  have hc : ∀ (u v : ι → ℂ) (s t : ℂ), (D u + s • D (I • u)) * (D v + t • D (I • v)) =
      (D v + t • D (I • v)) * (D u + s • D (I • u)) +
        (2 * π * I * ((1 + s * t) * (star v ⬝ᵥ H *ᵥ u).im + (s - t) * (star v ⬝ᵥ H *ᵥ u).re)) •
          (1 : Module.End ℂ (smS ρ)) := by
    intro u v s t
    rw [comm_comb _ _ _ _ s t _ _ _ _ (hD u v) (hD u (I • v)) (hD (I • u) v) (hD (I • u) (I • v))]
    congr 2
    simp only [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    simp
    ring
  have hII : (1 : ℂ) + I * I = 0 := by simp
  refine ⟨fun k => D (Pi.single k 1) + (-I) • D (I • Pi.single k 1),
    fun l => (-(1 / (4 * π)) : ℂ) • (D (H⁻¹ *ᵥ Pi.single l 1) + I • D (I • H⁻¹ *ᵥ Pi.single l 1)),
    fun k f => ?_, fun k f => rfl, fun k l => ?_, fun k l => ?_, fun k l => ?_⟩
  · rw [xOp, sub_eq_add_neg, ← neg_smul]
    rfl
  · beta_reduce
    rw [hc]
    simp
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hc]
    simp
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hc (Pi.single k 1), pair_inv hH hd, ← smul_sub, sub_add_cancel_left, ← neg_smul, smul_smul]
    by_cases h : k = l
    · simp only [h, if_true, one_im, one_re, ofReal_zero, ofReal_one]
      have hp : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have : (-(1 / (4 * π)) : ℂ) * -(2 * π * I * ((1 + -I * I) * 0 + (-I - I) * 1)) = 1 := by
        field_simp
        linear_combination (-4) * hII
      rw [this, one_smul]
    · simp [h]
end

section
noncomputable section

namespace GlobalTheory.Mem.Lift.ThOps

theorem exists_restrict {Θ M : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup M] [Module ℂ M] (j : Θ →ₗ[ℂ] M)
    (hj : Function.Injective j) (A : Module.End ℂ M) (hA : ∀ f, ∃ g, j g = A (j f)) :
    ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = A (j f) := by
  choose a ha using hA
  exact ⟨{ toFun := a
           map_add' := fun f g => hj (by simp only [map_add, ha])
           map_smul' := fun c f => hj (by simp only [map_smul, ha, RingHom.id_apply]) }, ha⟩

theorem isCCR_restrict {Θ M κ : Type} [DecidableEq κ] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup M] [Module ℂ M]
    (j : Θ →ₗ[ℂ] M) (hj : Function.Injective j) {x d : κ → Module.End ℂ Θ} {x₀ d₀ : κ → Module.End ℂ M}
    (hx : ∀ k f, j (x k f) = x₀ k (j f)) (hd : ∀ k f, j (d k f) = d₀ k (j f)) (h : GlobalTheory.Mem.Lift.IsCCR x₀ d₀) :
    GlobalTheory.Mem.Lift.IsCCR x d := by
  refine ⟨fun k l => LinearMap.ext fun f => hj ?_, fun k l => LinearMap.ext fun f => hj ?_,
    fun k l => LinearMap.ext fun f => hj ?_⟩
  · simpa only [Module.End.mul_apply, hx] using LinearMap.congr_fun (h.1 k l) (j f)
  · simpa only [Module.End.mul_apply, hd] using LinearMap.congr_fun (h.2.1 k l) (j f)
  · have := LinearMap.congr_fun (h.2.2 k l) (j f)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hx, hd] at this ⊢
    rw [this]
    split_ifs <;> simp

open Matrix GlobalTheory.RealWeil in

theorem exists_ops {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0)
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B)
    (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ) {Θ : Type} [AddCommGroup Θ] [Module ℂ Θ] (J : Θ →ₗ[ℂ] B)
    (hJ : Function.Injective J) (hs : ∀ f, Sm ρ (J f)) (hk : ∀ v f, ∃ g, J g = dH ρ v (J f)) :
    ∃ x d : ι → Module.End ℂ Θ, IsCCR x d ∧
      ∀ (X : Matrix ι ι ℂ) (f : Θ), J ((∑ k, ∑ l, X k l • (x k * d l)) f) = nOp ρ H X (J f) := by
  obtain ⟨x₀, d₀, hx₀, hd₀, hc⟩ := exists_isCCR_xOp_dOp ι H hH hd B ρ hρ
  let j : Θ →ₗ[ℂ] smS ρ := J.codRestrict _ hs
  have hj : Function.Injective j := fun f g e => hJ (congrArg Subtype.val e)
  have h1 : ∀ k, ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = x₀ k (j f) := fun k => exists_restrict j hj _ fun f => by
    obtain ⟨g₁, e₁⟩ := hk (Pi.single k 1) f
    obtain ⟨g₂, e₂⟩ := hk (Complex.I • Pi.single k 1) f
    refine ⟨g₁ - Complex.I • g₂, Subtype.ext ?_⟩
    rw [hx₀]
    change J _ = xOp ρ k (J f)
    rw [xOp, map_sub, map_smul, e₁, e₂]
  have h2 : ∀ k, ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = d₀ k (j f) := fun k => exists_restrict j hj _ fun f => by
    obtain ⟨g₁, e₁⟩ := hk (H⁻¹ *ᵥ Pi.single k 1) f
    obtain ⟨g₂, e₂⟩ := hk (Complex.I • H⁻¹ *ᵥ Pi.single k 1) f
    refine ⟨(-(1 / (4 * Real.pi)) : ℂ) • (g₁ + Complex.I • g₂), Subtype.ext ?_⟩
    rw [hd₀]
    change J _ = dOp ρ H k (J f)
    rw [dOp, map_smul, map_add, map_smul, e₁, e₂]
  choose x hx using h1
  choose d hd' using h2
  refine ⟨x, d, isCCR_restrict j hj hx hd' hc, fun X f => ?_⟩
  have ex : ∀ k f, J (x k f) = xOp ρ k (J f) := fun k f => (congrArg Subtype.val (hx k f)).trans (hx₀ k _)
  have ed : ∀ k f, J (d k f) = dOp ρ H k (J f) := fun k f => (congrArg Subtype.val (hd' k f)).trans (hd₀ k _)
  simp only [nOp, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul, ex, ed]

end GlobalTheory.Mem.Lift.ThOps

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

open GlobalTheory.RealWeil in

theorem GlobalTheory.Mem.Lift.exists_isCCR_theta : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D), ∃ x d : GlobalTheory.RealWeil.Ix S T → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), IsCCR x d ∧ ∀ (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (f : GlobalTheory.RealWeil.thetaSub ψ S T) (F : GlobalTheory.RealWeil.BB ψ S T), (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F).1 := by
  intro D θ σ h ψ hψ S T
  let J : thetaSub ψ S T →ₗ[ℂ] BB ψ S T :=
    { toFun := fun f => toB hψ f.1 f.2
      map_add' := fun f g => QB_ext fun x => rfl
      map_smul' := fun a f => QB_ext fun x => rfl }
  have hc : ∀ f, ((J f).1 : WO S T → ℂ) = f.1 := fun f => coe_toB hψ f.1 f.2
  have hJ : Function.Injective J := fun f g e => Subtype.ext (by rw [← hc, ← hc, e])
  have ht : ∀ f, IsThetaFunO ψ S T (J f).1 := fun f => (hc f).symm ▸ f.2
  have hs : ∀ f, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) (J f) := fun f => sm_of_theta h hψ _ (ht f)
  have hk : ∀ v f, ∃ g, J g = dH (rhoV hψ σ S T) v (J f) := by
    intro v f
    obtain ⟨F', hF', hd⟩ := exists_deriv h hψ (J f) (ht f) v
    refine ⟨⟨F'.1, hF'⟩, QB_ext fun w => ?_⟩
    rw [hc]
    exact (hd w).unique (((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v (hs f)))
  obtain ⟨x, d, hxd, hn⟩ := ThOps.exists_ops (HM S T) HM_herm HM_det (rhoV hψ σ S T) (isHeis_rhoB h hψ) J hJ hs hk
  refine ⟨x, d, hxd, fun X f F hF => ?_⟩
  have e : F = J f := QB_ext fun w => by rw [hF, hc]
  rw [e, ← hn, hc]

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ccr_operators_thetaFunctions : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D), ∃ x d : GlobalTheory.RealWeil.Ix S T → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), IsCCR x d ∧ ∀ (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (f : GlobalTheory.RealWeil.thetaSub ψ S T) (F : GlobalTheory.RealWeil.BB ψ S T), (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F).1 := by
  first | exact @GlobalTheory.Mem.Lift.exists_isCCR_theta | exact GlobalTheory.Mem.Lift.exists_isCCR_theta | (intros; apply GlobalTheory.Mem.Lift.exists_isCCR_theta <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.LiftGen

open GlobalTheory.RealWeil

theorem deriv_eq_of_norm {B H : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Φ : B →L[ℂ] H) {u v : ℝ → B} {A G A' : B} (hu : HasDerivAt u A 0) (hv : HasDerivAt v G 0)
    (hn : ∀ t : ℝ, ‖Φ (v t - v 0 - (t : ℂ) • A')‖ = ‖Φ (u t - u 0 - (t : ℂ) • A)‖) : Φ G = Φ A' := by
  have h1 : HasDerivAt (fun t => Φ (u t)) (Φ A) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  have h2 : HasDerivAt (fun t => Φ (v t)) (Φ G) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv
  refine h2.unique ?_
  rw [hasDerivAt_iff_isLittleO] at h1 ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h1 ⊢
  refine h1.congr_left fun t => ?_
  have := hn t
  rw [map_sub, map_sub, map_sub, map_sub, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul] at this
  simp only [sub_zero]
  exact this.symm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem deriv_om (hψ : IsStdChar D ψ (-1)) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : GlobalTheory.Ker.IsWeak ψ S T om) (p : GA D S × GA D T) {u v : ℝ → BB ψ S T} {A G : BB ψ S T}
    (hu : HasDerivAt u A 0) (hv : HasDerivAt v G 0) (hut : ∀ t, IsThetaFunO ψ S T (u t).1)
    (hA : IsThetaFunO ψ S T A.1) (e : ∀ t, ((v t).1 : WO S T → ℂ) = om p (u t).1) :
    (G.1 : WO S T → ℂ) = om p A.1 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  let A' : BB ψ S T := toB hψ _ (hW.om_pres p _ hA)
  have hA' : (A'.1 : WO S T → ℂ) = om p A.1 := coe_toB _ _ _
  have hk : ∀ a b : BB ψ S T, IsThetaFunO ψ S T b.1 → (a.1 : WO S T → ℂ) = om p b.1 →
      ‖toL2 _ _ (μ.restrict 𝓕) a‖ = ‖toL2 _ _ (μ.restrict 𝓕) b‖ := by
    intro a b hb hab
    rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2, hab]
    exact hW.om_unit μ 𝓕 hμ h𝓕 p _ hb
  have key : toL2 _ _ (μ.restrict 𝓕) G = toL2 _ _ (μ.restrict 𝓕) A' := by
    refine deriv_eq_of_norm _ hu hv fun t => ?_
    have e1 : ((u t - u 0 - (t : ℂ) • A).1 : WO S T → ℂ) =
        ((u t).1 : WO S T → ℂ) - ((u 0).1 : WO S T → ℂ) - (t : ℂ) • (A.1 : WO S T → ℂ) := rfl
    have e2 : ((v t - v 0 - (t : ℂ) • A').1 : WO S T → ℂ) = om p (u t - u 0 - (t : ℂ) • A).1 := by
      rw [e1, map_sub, map_sub, map_smul, ← e, ← e, ← hA']
      rfl
    have h3 : IsThetaFunO ψ S T (u t - u 0 - (t : ℂ) • A).1 := by
      rw [e1]
      exact (thetaSub ψ S T).sub_mem ((thetaSub ψ S T).sub_mem (hut t) (hut 0)) ((thetaSub ψ S T).smul_mem _ hA)
    exact hk _ _ h3 e2
  have h4 := lintegral_norm_sq_eq_toL2 (μ.restrict 𝓕) (G - A')
  rw [map_sub, key, sub_self, enorm_zero, zero_pow two_ne_zero,
    lintegral_eq_zero_iff ((G - A').1.continuous.measurable.enorm.pow_const 2)] at h4
  have h5 := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ (G - A').1.continuous
    (BB_norm_periodic hψ _) (by filter_upwards [h4] with x hx; simpa using hx)
  rw [← hA']
  exact sub_eq_zero.1 h5

theorem hasDerivAt_om : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∀ p w, HasDerivAt (fun t => om (p * γ t) F.1 w) (om p (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F).1 w) 0 := by
  intro D θ σ h ψ hψ S T om hW hc γ hγ hadd hinf X hX
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm D θ σ h ψ hψ S T om hW hc γ hγ hadd hinf X hX
  obtain ⟨x, d, -, hxd⟩ := GlobalTheory.T.exists_ccr_operators_thetaFunctions D θ σ h ψ hψ S T
  refine ⟨lam, fun F hF p w => ?_⟩
  obtain ⟨u, hu, hud⟩ := hlam F hF
  have hA : IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) X F + lam • F).1 := by
    have h1 := ((∑ k, ∑ l, X k l • (x k * d l)) ⟨F.1, hF⟩).2
    rw [hxd X ⟨F.1, hF⟩ F rfl] at h1
    exact (thetaSub ψ S T).add_mem h1 ((thetaSub ψ S T).smul_mem lam hF)
  have : IsTopologicalGroup (GA D S) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S).2.2.2.2.1
  have : IsTopologicalGroup (GA D T) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T).2.2.2.2.1
  have hn : ∀ V : HSp D, (GinfC V).Normal := fun V => MonoidHom.normal_ker _
  obtain ⟨lam', hlam'⟩ := GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm D θ σ h ψ hψ S T om hW hc (fun t => p * γ t * p⁻¹)
    ((continuous_const.mul hγ).mul continuous_const) (fun s t => by rw [hadd]; group)
    (fun t => ⟨(hn S).conj_mem _ (hinf t).1 p.1, (hn T).conj_mem _ (hinf t).2 p.2⟩)
    (mM θ S T p * X * mM θ S T p⁻¹) (fun k l => by
      simp only [map_mul, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun j _ => (HasDerivAt.fun_sum fun i _ => (hX i j).const_mul _).mul_const _)
  obtain ⟨v, hv, hvd⟩ := hlam' (toB hψ _ (hW.om_pres p _ hF)) (by rw [coe_toB]; exact hW.om_pres p _ hF)
  have e : ∀ t, ((v t).1 : WO S T → ℂ) = om (p * γ t) F.1 := fun t => by
    rw [hv, coe_toB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  have key := deriv_om hψ hW p hud hvd (fun t => by rw [hu]; exact hW.om_pres _ _ hF) hA
    (fun t => by rw [e, hu, map_mul, Module.End.mul_apply])
  rw [← key]
  have h3 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hvd
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  exact (congrFun (e t) w).symm

end GlobalTheory.Mem.LiftGen
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_weilRep_realOneParam_adelicPoint : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∀ p w, HasDerivAt (fun t => om (p * γ t) F.1 w) (om p (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F).1 w) 0 := by
  first | exact @GlobalTheory.Mem.LiftGen.hasDerivAt_om | exact GlobalTheory.Mem.LiftGen.hasDerivAt_om | (intros; apply GlobalTheory.Mem.LiftGen.hasDerivAt_om <;> assumption)
end
