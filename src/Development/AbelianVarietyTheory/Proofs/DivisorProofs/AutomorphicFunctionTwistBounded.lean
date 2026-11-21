import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneIntegralSkewHermitianTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeNilRadicalInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleRankOneRight
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSqFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementInfinitePointsStatement

section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_constant_term_parabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), IsIsoCols σ J C → ∀ (H K : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ), ratPts σ J ⊓ parFlag σ J C d ≤ H → IsAutOn σ J H K φ → IsConstTermOn σ J (unipFlag σ J C d) φ c → IsAutOn σ J (leftGrp σ J C d) K c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  first | exact @GlobalTheory.UAut.ConstAut.isAutOn_constTerm | exact GlobalTheory.UAut.ConstAut.isAutOn_constTerm | (intros; apply GlobalTheory.UAut.ConstAut.isAutOn_constTerm <;> assumption)
end

section
section
noncomputable section

open Matrix GlobalTheory.TorFin GlobalTheory.SmoothForms
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.TorFin.RightRep

variable {n : ℕ} {G : Type} [Group G]

def sig (J : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := J⁻¹ * Xᴴ * J
  map_add' X Y := by rw [conjTranspose_add, mul_add, add_mul]
  map_smul' c X := by
    change J⁻¹ * (c • X)ᴴ * J = c • (J⁻¹ * Xᴴ * J)
    rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]

abbrev skewSub (J : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J).toSubmodule

theorem sig_mul_eq_one_iff {J : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit J.det) (u : Matrix (Fin n) (Fin n) ℂ) :
    sig J u * u = 1 ↔ IsUni J u := by
  change J⁻¹ * uᴴ * J * u = 1 ↔ uᴴ * J * u = J
  constructor
  · intro h1
    have := congrArg (J * ·) h1
    simpa only [← mul_assoc, mul_nonsing_inv _ hu, one_mul, mul_one] using this
  · intro h1
    rw [mul_assoc, mul_assoc, ← mul_assoc uᴴ, h1, nonsing_inv_mul _ hu]

theorem isLieData {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hu : IsUnit J.det) {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) : IsLieData (sig J) (skewSub J).subtype s := by
  have anti : ∀ a b, sig J (a * b) = sig J b * sig J a := fun a b => by
    change _ * (a * b)ᴴ * _ = (_ * bᴴ * _) * (_ * aᴴ * _)
    rw [conjTranspose_mul]
    simp only [mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hu]
  refine ⟨anti, ?_, fun a => ?_, Subtype.val_injective, fun X => ⟨fun h => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change J⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J = 1
    rw [conjTranspose_one, mul_one, nonsing_inv_mul _ hu]
  · change _ * (_ * aᴴ * _)ᴴ * _ = a
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hu, nonsing_inv_mul _ hu, mul_one]
  · refine ⟨⟨X, ?_⟩, rfl⟩
    have h1 : J⁻¹ * Xᴴ * J = -X := h
    change Xᴴ * J + J * X = 0
    rw [← mul_nonsing_inv_cancel_left _ (Xᴴ * J) hu, ← mul_assoc J⁻¹, h1, mul_neg, neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    have h1 : Y.1ᴴ * J + J * Y.1 = 0 := Y.2
    change _ * Y.1ᴴ * _ = -Y.1
    rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ hu]
  · exact hs a b ((sig_mul_eq_one_iff hu a).1 ha) ((sig_mul_eq_one_iff hu b).1 hb)

theorem mem_smLoc_iff {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hu : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s) (φ : G → ℂ) :
    φ ∈ smLoc J s ↔ Sm (expMap (skewSub J).subtype s) φ := by
  have H := isLieData hJ hu hs
  rw [SecondKind.sm_iff H (hasLog_of_isLieData _ _ _ _ _ _ H) Set.univ (by simp), mem_smLoc]
  constructor
  · intro h k Y _ g
    exact h k (fun i => (Y i).1) (fun i => (Y i).2) g
  · intro h k Z hZ g
    exact h k (fun i => ⟨Z i, hZ i⟩) (fun _ => trivial) g

variable {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hu : IsUnit J.det) {s : Matrix (Fin n) (Fin n) ℂ → G}
  (hs : IsMulOn J s)

def derL (X : skewSub J) : Module.End ℂ (smLoc J s) where
  toFun φ := ⟨Der (expMap (skewSub J).subtype s) X φ.1, (mem_smLoc_iff hJ hu hs _).2
    ((der_smooth_and_linear _ _ _ _ _ _ (isLieData hJ hu hs)
      (hasLog_of_isLieData _ _ _ _ _ _ (isLieData hJ hu hs)) φ.1 ((mem_smLoc_iff hJ hu hs _).1 φ.2)).1 X)⟩
  map_add' φ ψ := Subtype.ext (funext fun g => deriv_add
    (Sm.differentiableAt ((mem_smLoc_iff hJ hu hs _).1 φ.2) g X)
    (Sm.differentiableAt ((mem_smLoc_iff hJ hu hs _).1 ψ.2) g X))
  map_smul' c φ := Subtype.ext (funext fun g =>
    deriv_const_smul c (Sm.differentiableAt ((mem_smLoc_iff hJ hu hs _).1 φ.2) g X))

theorem derL_apply (X : skewSub J) (φ : smLoc J s) :
    (derL hJ hu hs X φ).1 = Der (expMap (skewSub J).subtype s) X φ.1 := rfl

include hu hs in

theorem lineOf_add (Z : skewSub J) (t u : ℝ) : lineOf s Z.1 t * lineOf s Z.1 u = lineOf s Z.1 (t + u) := by
  have h1 : IsUni J (NormedSpace.exp (t • Z.1)) := exp_mem_UH hu (t • Z).2
  have h2 : IsUni J (NormedSpace.exp (u • Z.1)) := exp_mem_UH hu (u • Z).2
  unfold lineOf
  rw [← hs _ _ h1 h2, add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl Z.1).smul_left t).smul_right u)]

theorem hasDerivAt_derL (X : skewSub J) (φ : smLoc J s) (g : G) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => φ.1 (g * lineOf s X.1 τ)) ((derL hJ hu hs X φ).1 (g * lineOf s X.1 t)) t := by
  have hsm := (mem_smLoc_iff hJ hu hs _).1 φ.2
  set F : ℝ → ℂ := fun τ => φ.1 (g * lineOf s X.1 τ) with hFdef
  have hF : Differentiable ℝ F :=
    ((hsm g).comp (contDiff_id.smul contDiff_const : ContDiff ℝ ∞ fun τ : ℝ => τ • X)).differentiable (by simp)
  have key : (fun u : ℝ => φ.1 (g * lineOf s X.1 t * expMap (skewSub J).subtype s (u • X))) =
      fun u => F (t + u) := funext fun u => by
    show φ.1 (g * lineOf s X.1 t * lineOf s X.1 u) = φ.1 (g * lineOf s X.1 (t + u))
    rw [mul_assoc, lineOf_add hu hs]
  have e : (derL hJ hu hs X φ).1 (g * lineOf s X.1 t) = deriv F t := by
    rw [derL_apply]
    show deriv (fun u : ℝ => φ.1 (g * lineOf s X.1 t * expMap (skewSub J).subtype s (u • X))) 0 = _
    rw [key, deriv_comp_const_add, add_zero]
  rw [e]
  exact (hF t).hasDerivAt

end GlobalTheory.TorFin.RightRep

namespace GlobalTheory.TorFin

open RightRep in

theorem exists_rightDer_rep : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ)
    (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s →
    ∃ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsLieRep ρ ∧ IsRightDer J s ρ := by
  intro n G _ J s hJ hu hs
  have H := isLieData hJ hu hs
  have hl := hasLog_of_isLieData _ _ _ _ _ _ H
  let ρ₀ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → Module.End ℂ (smLoc J s) := fun X => derL hJ hu hs ⟨X.1, X.2⟩
  have hsm : ∀ φ : smLoc J s, Sm (expMap (skewSub J).subtype s) φ.1 := fun φ => (mem_smLoc_iff hJ hu hs _).1 φ.2
  obtain ⟨R, -, hR, hc⟩ := GlobalTheory.UnitaryLieComplexification.exists_extension hJ hu ρ₀
    (fun X Y => LinearMap.ext fun φ => Subtype.ext
      ((der_smooth_and_linear _ _ _ _ _ _ H hl φ.1 (hsm φ)).2.1 ⟨X.1, X.2⟩ ⟨Y.1, Y.2⟩))
    (fun c X => LinearMap.ext fun φ => Subtype.ext
      ((der_smooth_and_linear _ _ _ _ _ _ H hl φ.1 (hsm φ)).2.2 c ⟨X.1, X.2⟩))
    (fun X Y Z hZ => LinearMap.ext fun φ => Subtype.ext
      (Bracket.der_bracket _ _ _ _ _ _ H hl φ.1 (hsm φ) ⟨X.1, X.2⟩ ⟨Y.1, Y.2⟩ ⟨Z.1, Z.2⟩ hZ).symm)
  refine ⟨R, hc, fun Z hZ φ g t => ?_⟩
  have hRZ : R Z = derL hJ hu hs ⟨Z, hZ⟩ := hR ⟨Z, hZ⟩
  rw [hRZ]
  exact hasDerivAt_derL hJ hu hs ⟨Z, hZ⟩ φ g t

end GlobalTheory.TorFin
end
end

open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_local_lie_representation : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∃ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsLieRep ρ ∧ IsRightDer J s ρ := by
  atlas_forward_decl GlobalTheory.TorFin.exists_rightDer_rep
end

section
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin.RightTr

variable {n : ℕ} {G : Type} [Group G] {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}

theorem isUni_exp (hJ : IsUnit J.det) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsSkew J X) :
    IsUni J (NormedSpace.exp X) := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  change (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left,
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem isSkew_smul {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) : IsSkew J (t • Z) := by
  unfold IsSkew at *
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hZ, smul_zero]

theorem isUnit_det_of_isUni (hJ : IsUnit J.det) {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) : IsUnit u.det := by
  have h : (uᴴ * J * u).det = J.det := congrArg Matrix.det hu
  rw [det_mul] at h
  exact isUnit_of_mul_isUnit_right (h ▸ hJ)

theorem isSkew_conj_of {u Z W : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) (h : W * u = u * Z) :
    uᴴ * (Wᴴ * J + J * W) * u = Zᴴ * J + J * Z := by
  have h' : uᴴ * Wᴴ = Zᴴ * uᴴ := by rw [← conjTranspose_mul, h, conjTranspose_mul]
  unfold IsUni at hu
  calc uᴴ * (Wᴴ * J + J * W) * u = (uᴴ * Wᴴ) * J * u + uᴴ * J * (W * u) := by noncomm_ring
    _ = Zᴴ * (uᴴ * J * u) + (uᴴ * J * u) * Z := by rw [h, h']; noncomm_ring
    _ = _ := by rw [hu]

theorem isSkew_inv_conj (hJ : IsUnit J.det) {u Z : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) (hZ : IsSkew J Z) :
    IsSkew J (u⁻¹ * Z * u) := by
  have hd := isUnit_det_of_isUni hJ hu
  have := isSkew_conj_of (W := Z) (Z := u⁻¹ * Z * u) hu
    (by rw [mul_assoc, mul_nonsing_inv_cancel_left _ _ hd])
  unfold IsSkew at *
  rw [← this, hZ, mul_zero, zero_mul]

theorem isSkew_conj (hJ : IsUnit J.det) {u Z : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) (hZ : IsSkew J Z) :
    IsSkew J (u * Z * u⁻¹) := by
  have hd := isUnit_det_of_isUni hJ hu
  have hd' : IsUnit uᴴ.det := by rw [det_conjTranspose]; exact hd.star
  have := isSkew_conj_of (W := u * Z * u⁻¹) (Z := Z) hu
    (by rw [nonsing_inv_mul_cancel_right _ _ hd])
  unfold IsSkew at *
  rw [hZ] at this
  have h2 := congrArg (fun M => (uᴴ)⁻¹ * M * u⁻¹) this
  simp only [mul_zero, zero_mul] at h2
  rwa [mul_assoc uᴴ, nonsing_inv_mul_cancel_left _ _ hd', mul_nonsing_inv_cancel_right _ _ hd] at h2

theorem lineOf_zero (hs : IsMulOn J s) (Z : Matrix (Fin n) (Fin n) ℂ) : lineOf s Z 0 = 1 := by
  have h1 : IsUni J 1 := by simp [IsUni]
  have := hs 1 1 h1 h1
  rw [mul_one] at this
  rw [lineOf, zero_smul, NormedSpace.exp_zero]
  exact left_eq_mul.1 this

theorem lineOf_mul (hJ : IsUnit J.det) (hs : IsMulOn J s) {u : Matrix (Fin n) (Fin n) ℂ} {b : G} (hu : IsUni J u)
    (hb : ∀ v, IsUni J v → b * s v = s v * b) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) :
    lineOf s Z t * (s u * b) = (s u * b) * lineOf s (u⁻¹ * Z * u) t := by
  have hd := isUnit_det_of_isUni hJ hu
  have h1 := isUni_exp hJ (isSkew_smul hZ t)
  have h2 := isUni_exp hJ (isSkew_smul (isSkew_inv_conj hJ hu hZ) t)
  have e : t • (u⁻¹ * Z * u) = u⁻¹ * (t • Z) * u := by rw [mul_smul_comm, smul_mul_assoc]
  unfold lineOf
  rw [mul_assoc (s u), hb _ h2, ← mul_assoc, ← mul_assoc, ← hs _ _ h1 hu, ← hs _ _ hu h2, e,
    Matrix.exp_conj' _ _ ((isUnit_iff_isUnit_det u).2 hd), mul_assoc u⁻¹, mul_nonsing_inv_cancel_left _ _ hd]

theorem prod_ofFn_mul (c : G) : ∀ (k : ℕ) (x y : Fin k → G), (∀ i, x i * c = c * y i) →
    (List.ofFn x).prod * c = c * (List.ofFn y).prod := by
  intro k
  induction k with
  | zero => intro x y _; simp
  | succ k ih =>
    intro x y h
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      ih _ _ (fun i => h i.succ), ← mul_assoc, h, mul_assoc]

theorem exists_skew_add (hH : Jᴴ = J) (hJ : IsUnit J.det) (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ A B, IsSkew J A ∧ IsSkew J B ∧ Y = A + Complex.I • B := by
  have e1 : (J⁻¹ * Yᴴ * J)ᴴ * J = J * Y := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH,
      ← mul_assoc, nonsing_inv_mul_cancel_right _ _ hJ]
  have e2 : J * (J⁻¹ * Yᴴ * J) = Yᴴ * J := by
    rw [mul_assoc, mul_nonsing_inv_cancel_left _ _ hJ]
  generalize J⁻¹ * Yᴴ * J = Y' at e1 e2
  refine ⟨(1 / 2 : ℂ) • (Y - Y'), (-Complex.I / 2) • (Y + Y'), ?_, ?_, ?_⟩
  · unfold IsSkew
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [conjTranspose_smul, this, conjTranspose_sub, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, e1, e2]
    module
  · unfold IsSkew
    have : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) := by simp; ring
    rw [conjTranspose_smul, this, conjTranspose_add, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, e1, e2]
    module
  · have : Complex.I * (-Complex.I / 2) = 1 / 2 := by
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
    rw [smul_smul, this]
    module

theorem exists_rightTranslation : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (u : Matrix (Fin n) (Fin n) ℂ) (b : G), IsUni J u → (∀ v, IsUni J v → b * s v = s v * b) → ∃ r : Module.End ℂ (smLoc J s), (∀ (f : smLoc J s) (g : G), (r f).1 g = f.1 (g * (s u * b))) ∧ ∀ Y, r * ρ Y = ρ (u * Y * u⁻¹) * r := by
  intro n G _ J s hH hJ hs ρ hρ u b hu hb
  have hd := isUnit_det_of_isUni hJ hu
  let r : Module.End ℂ (smLoc J s) :=
    { toFun := fun f => ⟨fun g => f.1 (g * (s u * b)), fun k Z hZ g => by
        have h := f.2 k (fun i => u⁻¹ * Z i * u) (fun i => isSkew_inv_conj hJ hu (hZ i)) (g * (s u * b))
        convert h using 2 with t
        beta_reduce
        rw [mul_assoc g, mul_assoc g, prod_ofFn_mul _ _ _ _ fun i => lineOf_mul hJ hs hu hb (hZ i) (t i)]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have key : ∀ Z, IsSkew J Z → r * ρ Z = ρ (u * Z * u⁻¹) * r := by
    intro Z hZ
    refine LinearMap.ext fun f => Subtype.ext (funext fun g => ?_)
    have h1 := hρ Z hZ f (g * (s u * b)) 0
    have h2 := hρ _ (isSkew_conj hJ hu hZ) (r f) g 0
    rw [lineOf_zero hs, mul_one] at h1 h2
    refine h1.unique ?_
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    change f.1 (g * (s u * b) * lineOf s Z τ) = f.1 (g * lineOf s (u * Z * u⁻¹) τ * (s u * b))
    rw [mul_assoc g (lineOf _ _ _), lineOf_mul hJ hs hu hb (isSkew_conj hJ hu hZ), ← mul_assoc u⁻¹,
      nonsing_inv_mul_cancel_right _ _ hd, nonsing_inv_mul_cancel_left _ _ hd, mul_assoc g]
  refine ⟨r, fun _ _ => rfl, fun Y => ?_⟩
  obtain ⟨A, B, hA, hB, rfl⟩ := exists_skew_add hH hJ Y
  rw [mul_add u, add_mul, mul_smul_comm, smul_mul_assoc, map_add, map_add, map_smul, map_smul, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, key A hA, key B hB]

end GlobalTheory.TorFin.RightTr
end

open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translation_intertwines_lie : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (u : Matrix (Fin n) (Fin n) ℂ) (b : G), IsUni J u → (∀ v, IsUni J v → b * s v = s v * b) → ∃ r : Module.End ℂ (smLoc J s), (∀ (f : smLoc J s) (g : G), (r f).1 g = f.1 (g * (s u * b))) ∧ ∀ Y, r * ρ Y = ρ (u * Y * u⁻¹) * r := by
  atlas_forward_decl GlobalTheory.TorFin.RightTr.exists_rightTranslation
end

section
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin

theorem pow_mul_mem_of_mul_mem {A : Type} [Ring A] [Algebra ℂ A] {I : Submodule ℂ A} {H : A}
    (hH : ∀ i ∈ I, H * i ∈ I) (m : ℕ) {x : A} (hx : x ∈ I) : H ^ m * x ∈ I := by
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [pow_succ', mul_assoc]; exact hH _ ih

theorem finiteDimensional_span_pow_mul_pow :
    ∀ (A U W : Type) [Ring A] [Algebra ℂ A] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
      (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H H' : A) (κ : A →ₗ[ℂ] U) (Λ : A →ₗ[ℂ] W), Commute H H' →
      (∀ i ∈ I, H * i ∈ I) → (∀ i ∈ I, H' * i ∈ I) → (∀ i ∈ I, ∀ z ∈ Z, i * z ∈ I) → (∀ i ∈ I, Λ i = 0) →
      IsIntMod Z I H → IsIntMod Z I H' → FiniteDimensional ℂ ((Subalgebra.toSubmodule Z).map κ) →
      (∀ z ∈ Z, κ z = 0 → ∀ T, Λ (T * z) = 0) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun p : ℕ × ℕ => Λ (H ^ p.1 * H' ^ p.2))) := by
  intro A U W _ _ _ _ _ _ Z I H H' κ Λ hc hHI hH'I hIZ hΛ ⟨N, hN⟩ ⟨N', hN'⟩ hfin hker
  set K : Submodule ℂ A := Subalgebra.toSubmodule Z with hK
  let κK : K →ₗ[ℂ] U := κ ∘ₗ K.subtype
  let f : ℕ × ℕ → K →ₗ[ℂ] W := fun p => Λ ∘ₗ LinearMap.mulLeft ℂ (H ^ p.1 * H' ^ p.2) ∘ₗ K.subtype
  have hle : ∀ p, LinearMap.ker κK ≤ LinearMap.ker (f p) := by
    intro p z hz
    simp only [LinearMap.mem_ker] at hz ⊢
    exact hker z.1 z.2 hz _
  have hQ : Module.Finite ℂ (K ⧸ LinearMap.ker κK) := by
    have hr : LinearMap.range κK = K.map κ := by
      simp [κK, LinearMap.range_comp, Submodule.range_subtype]
    haveI : Module.Finite ℂ (LinearMap.range κK) := by rw [hr]; exact hfin
    exact Module.Finite.equiv (κK.quotKerEquivRange).symm
  have hfp : ∀ p, Module.Finite ℂ (LinearMap.range (f p)) := by
    intro p
    rw [← Submodule.range_liftQ _ (f p) (hle p)]
    exact Module.Finite.range _
  let V : Submodule ℂ W := ⨆ p : Fin N × Fin N', LinearMap.range (f (p.1.1, p.2.1))
  haveI : Module.Finite ℂ V := by
    haveI := fun p : Fin N × Fin N' => hfp (p.1.1, p.2.1)
    infer_instance
  have hbase : ∀ i j, i < N → j < N' → ∀ z ∈ Z, Λ (H ^ i * H' ^ j * z) ∈ V := by
    intro i j hi hj z hz
    refine Submodule.mem_iSup_of_mem (⟨i, hi⟩, ⟨j, hj⟩) ⟨⟨z, hz⟩, ?_⟩
    simp [f, mul_assoc]
  have main : ∀ n i j, i + j ≤ n → ∀ z ∈ Z, Λ (H ^ i * H' ^ j * z) ∈ V := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro i j hij z hz
    by_cases hi : N ≤ i
    · obtain ⟨ι, hι, s, hs, hsum⟩ := Submodule.mem_sup.1 hN
      have e : H ^ i * H' ^ j * z = H ^ (i - N) * (H' ^ j * (ι * z)) + H ^ (i - N) * H' ^ j * s * z := by
        rw [← pow_sub_mul_pow H hi, mul_assoc (H ^ (i - N)), (hc.pow_pow N j).eq, ← hsum]
        simp only [mul_add, add_mul, mul_assoc]
      rw [e, map_add, hΛ _ (pow_mul_mem_of_mul_mem hHI _ (pow_mul_mem_of_mul_mem hH'I _ (hIZ _ hι _ hz))), zero_add]
      clear e hsum
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, hk, zk, hzk, rfl⟩ := hx
        have e2 : H ^ (i - N) * H' ^ j * (H ^ k * zk) * z = H ^ (i - N + k) * H' ^ j * (zk * z) := by
          calc H ^ (i - N) * H' ^ j * (H ^ k * zk) * z = H ^ (i - N) * (H' ^ j * H ^ k) * (zk * z) := by
                simp only [mul_assoc]
            _ = H ^ (i - N) * (H ^ k * H' ^ j) * (zk * z) := by rw [(hc.pow_pow k j).eq]
            _ = _ := by rw [pow_add]; simp only [mul_assoc]
        rw [e2]
        exact ih (i - N + k + j) (by omega) _ _ le_rfl _ (Z.mul_mem hzk hz)
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul, map_add]; exact V.add_mem hx hy
      | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, map_smul]; exact V.smul_mem c hx
    by_cases hj : N' ≤ j
    · obtain ⟨ι, hι, s, hs, hsum⟩ := Submodule.mem_sup.1 hN'
      have e : H ^ i * H' ^ j * z = H ^ i * (H' ^ (j - N') * (ι * z)) + H ^ i * H' ^ (j - N') * s * z := by
        rw [← pow_sub_mul_pow H' hj, ← hsum]
        simp only [mul_add, add_mul, mul_assoc]
      rw [e, map_add, hΛ _ (pow_mul_mem_of_mul_mem hHI _ (pow_mul_mem_of_mul_mem hH'I _ (hIZ _ hι _ hz))), zero_add]
      clear e hsum
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, hk, zk, hzk, rfl⟩ := hx
        have e2 : H ^ i * H' ^ (j - N') * (H' ^ k * zk) * z = H ^ i * H' ^ (j - N' + k) * (zk * z) := by
          rw [pow_add]; simp only [mul_assoc]
        rw [e2]
        exact ih (i + (j - N' + k)) (by omega) _ _ le_rfl _ (Z.mul_mem hzk hz)
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul, map_add]; exact V.add_mem hx hy
      | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, map_smul]; exact V.smul_mem c hx
    exact hbase i j (by omega) (by omega) z hz
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  rw [Submodule.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  simpa using main (i + j) i j le_rfl 1 Z.one_mem

example : ∀ (A U W : Type) [Ring A] [Algebra ℂ A] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H H' : A) (κ : A →ₗ[ℂ] U) (Λ : A →ₗ[ℂ] W), Commute H H' → (∀ i ∈ I, H * i ∈ I) → (∀ i ∈ I, H' * i ∈ I) → (∀ i ∈ I, ∀ z ∈ Z, i * z ∈ I) → (∀ i ∈ I, Λ i = 0) → IsIntMod Z I H → IsIntMod Z I H' → FiniteDimensional ℂ ((Subalgebra.toSubmodule Z).map κ) → (∀ z ∈ Z, κ z = 0 → ∀ T, Λ (T * z) = 0) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun p : ℕ × ℕ => Λ (H ^ p.1 * H' ^ p.2))) :=
  finiteDimensional_span_pow_mul_pow

end GlobalTheory.TorFin
end

open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_module_finite_quotient : ∀ (A U W : Type) [Ring A] [Algebra ℂ A] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H H' : A) (κ : A →ₗ[ℂ] U) (Λ : A →ₗ[ℂ] W), Commute H H' → (∀ i ∈ I, H * i ∈ I) → (∀ i ∈ I, H' * i ∈ I) → (∀ i ∈ I, ∀ z ∈ Z, i * z ∈ I) → (∀ i ∈ I, Λ i = 0) → IsIntMod Z I H → IsIntMod Z I H' → FiniteDimensional ℂ ((Subalgebra.toSubmodule Z).map κ) → (∀ z ∈ Z, κ z = 0 → ∀ T, Λ (T * z) = 0) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun p : ℕ × ℕ => Λ (H ^ p.1 * H' ^ p.2))) := by
  atlas_forward_decl GlobalTheory.TorFin.finiteDimensional_span_pow_mul_pow
end

section
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin.WordSpan

variable {n : ℕ} {G : Type} [Group G]

theorem map_one_of_isMulOn {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) : s 1 = 1 := by
  have h1 : IsUni J (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [IsUni]
  have h := hs 1 1 h1 h1
  rw [mul_one] at h
  exact mul_left_cancel (a := s 1) (by rw [mul_one]; exact h.symm)

theorem lineOf_zero {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) (Z : Matrix (Fin n) (Fin n) ℂ) : lineOf s Z 0 = 1 := by
  simp [lineOf, map_one_of_isMulOn hs]

theorem rho_skew_apply {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)}
    (hρ : IsRightDer J s ρ) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (f : smLoc J s) :
    (ρ Z f).1 = rder (lineOf s Z) f.1 := by
  funext g
  have h := hρ Z hZ f g 0
  rw [lineOf_zero hs, mul_one] at h
  exact h.deriv.symm

theorem prod_apply {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)}
    (hρ : IsRightDer J s ρ) (L : List (Matrix (Fin n) (Fin n) ℂ)) (hL : ∀ Z ∈ L, IsSkew J Z)
    (f : smLoc J s) : ((L.map ρ).prod f).1 = (L.map (lineOf s)).foldr rder f.1 := by
  induction L with
  | nil => simp
  | cons Z L ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, Module.End.mul_apply]
    rw [rho_skew_apply hs hρ (hL Z (by simp)), ih (fun Y hY => hL Y (by simp [hY]))]

theorem skew_decomp {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hdet : IsUnit J.det)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Z₁ Z₂, IsSkew J Z₁ ∧ IsSkew J Z₂ ∧ Y = Z₁ + Complex.I • Z₂ := by
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hdet
  have hJiJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  set Ys := J⁻¹ * Yᴴ * J with hYs
  have hYsH : Ysᴴ * J = J * Y := by
    rw [hYs, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
      conjTranspose_nonsing_inv, hJ, Matrix.mul_assoc, Matrix.mul_assoc, hJiJ, Matrix.mul_one]
  have hJYs : J * Ys = Yᴴ * J := by
    rw [hYs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Y - Ys), (1 / (2 * Complex.I)) • (Y + Ys), ?_, ?_, ?_⟩
  · simp only [IsSkew, conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, hYsH, hJYs]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]; simp
  · simp only [IsSkew, conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, hYsH, hJYs]
    have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
      simp [Complex.ext_iff]
    rw [this, neg_smul, add_comm (J * Y), neg_add_cancel]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp]
    module

end GlobalTheory.TorFin.WordSpan

namespace GlobalTheory.TorFin.WordSpan

variable {n : ℕ} {G : Type} [Group G]

theorem wop_single (l : List (ℝ → G)) (f : G → ℂ) : wop (Finsupp.single l 1) f = l.foldr rder f := by
  funext g; simp [wop, Finsupp.sum_single_index]

theorem wop_zero (f : G → ℂ) : wop (0 : List (ℝ → G) →₀ ℂ) f = 0 := by
  funext g; simp [wop]

theorem wop_add (z z' : List (ℝ → G) →₀ ℂ) (f : G → ℂ) : wop (z + z') f = wop z f + wop z' f := by
  funext g
  simp only [wop, Pi.add_apply]
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

theorem wop_smul (c : ℂ) (z : List (ℝ → G) →₀ ℂ) (f : G → ℂ) : wop (c • z) f = c • wop z f := by
  funext g
  simp only [wop, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  simp [smul_eq_mul, mul_assoc]

def words (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G)
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) : Set (Module.End ℂ (smLoc J s)) :=
  {T | ∃ L : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ L, IsSkew J Z) ∧ T = (L.map ρ).prod}

theorem adjoin_le_span {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hdet : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) :
    ∀ T ∈ Algebra.adjoin ℂ (Set.range ρ), T ∈ Submodule.span ℂ (words J s ρ) := by
  have hone : (1 : Module.End ℂ (smLoc J s)) ∈ Submodule.span ℂ (words J s ρ) :=
    Submodule.subset_span ⟨[], by simp, by simp⟩
  have hmul : ∀ x y, x ∈ Submodule.span ℂ (words J s ρ) → y ∈ Submodule.span ℂ (words J s ρ) →
      x * y ∈ Submodule.span ℂ (words J s ρ) := by
    intro x y hx hy
    have hxy := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at hxy
    refine Submodule.span_le.mpr ?_ hxy
    rintro _ ⟨a, ⟨L, hL, rfl⟩, b, ⟨L', hL', rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨L ++ L', ?_, by simp [List.prod_append]⟩
    intro Z hZ
    rcases List.mem_append.mp hZ with h | h
    · exact hL Z h
    · exact hL' Z h
  let S : Subalgebra ℂ (Module.End ℂ (smLoc J s)) :=
    (Submodule.span ℂ (words J s ρ)).toSubalgebra hone hmul
  have hle : Algebra.adjoin ℂ (Set.range ρ) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨Y, rfl⟩
    obtain ⟨Z₁, Z₂, h₁, h₂, rfl⟩ := skew_decomp hJ hdet Y
    show ρ (Z₁ + Complex.I • Z₂) ∈ Submodule.span ℂ (words J s ρ)
    rw [map_add, map_smul]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨[Z₁], by simpa using h₁, by simp⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨[Z₂], by simpa using h₂, by simp⟩))
  intro T hT
  exact hle hT

theorem exists_wop_of_mem_adjoin : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ T ∈ Algebra.adjoin ℂ (Set.range ρ), ∃ z : List (ℝ → G) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, ∃ Z, IsSkew J Z ∧ γ = lineOf s Z) ∧ ∀ f : smLoc J s, (T f).1 = wop z f.1 := by
  intro n G _ J s hJ hdet hs ρ hρ T hT
  classical
  have hS := adjoin_le_span hJ hdet ρ T hT
  clear hT
  induction hS using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨L, hL, rfl⟩ := hx
    refine ⟨Finsupp.single (L.map (lineOf s)) 1, ?_, ?_⟩
    · intro l hl γ hγ
      have hl' : l = L.map (lineOf s) := by
        by_contra hne
        simp [Finsupp.single_apply, Ne.symm hne] at hl
        exact hne hl
      subst hl'
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hγ
      exact ⟨Z, hL Z hZ, rfl⟩
    · intro f
      rw [prod_apply hs hρ L hL f, wop_single]
  | zero =>
    exact ⟨0, by simp, fun f => by rw [wop_zero]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, hzf⟩ := hx
    obtain ⟨z', hz', hzf'⟩ := hy
    refine ⟨z + z', ?_, ?_⟩
    · intro l hl
      rcases Finset.mem_union.mp (Finsupp.support_add hl) with h | h
      · exact hz l h
      · exact hz' l h
    · intro f
      rw [wop_add, ← hzf, ← hzf']
      rfl
  | smul c x _ hx =>
    obtain ⟨z, hz, hzf⟩ := hx
    refine ⟨c • z, fun l hl => hz l (Finsupp.support_smul hl), ?_⟩
    intro f
    rw [wop_smul, ← hzf]
    rfl

end GlobalTheory.TorFin.WordSpan
end

open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enveloping_algebra_line_words : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ T ∈ Algebra.adjoin ℂ (Set.range ρ), ∃ z : List (ℝ → G) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, ∃ Z, IsSkew J Z ∧ γ = lineOf s Z) ∧ ∀ f : smLoc J s, (T f).1 = wop z f.1 := by
  atlas_forward_decl GlobalTheory.TorFin.WordSpan.exists_wop_of_mem_adjoin
end

section
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

noncomputable section

namespace GlobalTheory.TorFin.TorusExp

variable {n : ℕ}

theorem dot_swap {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (u v : Fin n → ℂ) :
    (star u ᵥ* J) ⬝ᵥ v = star ((star v ᵥ* J) ⬝ᵥ u) := by
  rw [← dotProduct_mulVec, star_dotProduct, star_mulVec, hJ]

theorem exp_smul_idem {p : Matrix (Fin n) (Fin n) ℂ} (hp : p * p = p) (a : ℂ) :
    NormedSpace.exp (a • p) = 1 + (Complex.exp a - 1) • p := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let f : ℂ × ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun st => st.1 • p + st.2 • (1 - p)
      map_one' := by simp
      map_mul' := fun s t => by
        simp only [Prod.fst_mul, Prod.snd_mul, add_mul, mul_add, smul_mul_smul_comm, mul_sub, sub_mul, hp,
          mul_one, one_mul, sub_self, smul_zero, add_zero, zero_add, sub_sub_cancel, sub_zero]
      map_zero' := by simp
      map_add' := fun s t => by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel }
  have hf : Continuous f := by
    show Continuous fun st : ℂ × ℂ => st.1 • p + st.2 • (1 - p)
    fun_prop
  have h1 : f (a, 0) = a • p := by simp [f]
  have h2 := NormedSpace.map_exp f hf (a, 0)
  rw [h1] at h2
  refine Eq.trans h2.symm ?_
  have e1 : (NormedSpace.exp ((a, 0) : ℂ × ℂ)).1 = Complex.exp a := by rw [Prod.fst_exp, Complex.exp_eq_exp_ℂ]
  have e2 : (NormedSpace.exp ((a, 0) : ℂ × ℂ)).2 = 1 := by rw [Prod.snd_exp]; exact NormedSpace.exp_zero
  show (NormedSpace.exp ((a, 0) : ℂ × ℂ)).1 • p + (NormedSpace.exp ((a, 0) : ℂ × ℂ)).2 • (1 - p) = _
  rw [e1, e2, one_smul, sub_smul, one_smul]
  abel

theorem exp_torus (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Jᴴ = J) (x y : Fin n → ℂ)
    (hx : (star x ᵥ* J) ⬝ᵥ x = 0) (hy : (star y ᵥ* J) ⬝ᵥ y = 0) (hxy : (star x ᵥ* J) ⬝ᵥ y = 1) (ζ : ℂ) :
    IsSkew J (ζ • projL J x y - star ζ • projL J y x) ∧
      NormedSpace.exp (ζ • projL J x y - star ζ • projL J y x) = torMat J x y (Complex.exp ζ) := by
  have hyx : (star y ᵥ* J) ⬝ᵥ x = 1 := by rw [dot_swap hJ, hxy, star_one]
  have pp : projL J x y * projL J x y = projL J x y := by
    simp only [projL, vecMulVec_mul_vecMulVec, hyx, one_smul]
  have qq : projL J y x * projL J y x = projL J y x := by
    simp only [projL, vecMulVec_mul_vecMulVec, hxy, one_smul]
  have pq : projL J x y * projL J y x = 0 := by
    simp only [projL, vecMulVec_mul_vecMulVec, hy, zero_smul]
    ext i j; simp [vecMulVec]
  have qp : projL J y x * projL J x y = 0 := by
    simp only [projL, vecMulVec_mul_vecMulVec, hx, zero_smul]
    ext i j; simp [vecMulVec]
  have hs : ∀ u v : Fin n → ℂ, (projL J u v)ᴴ * J = J * projL J v u := by
    intro u v
    simp only [projL, conjTranspose_vecMulVec, vecMulVec_mul, mul_vecMulVec, star_vecMul, hJ, star_star]
  refine ⟨?_, ?_⟩
  · unfold IsSkew
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, star_star, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.smul_mul, hs, hs, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
    abel
  · rw [sub_eq_add_neg, ← neg_smul, Matrix.exp_add_of_commute, exp_smul_idem pp, exp_smul_idem qq]
    · have he : (star (Complex.exp ζ))⁻¹ = Complex.exp (-star ζ) := by
        change (starRingEnd ℂ (Complex.exp ζ))⁻¹ = Complex.exp (-(starRingEnd ℂ ζ))
        rw [← Complex.exp_conj, Complex.exp_neg]
      rw [torMat, he, add_mul, mul_add, mul_add, mul_one, one_mul, smul_mul_smul_comm, pq, smul_zero, add_zero]
      simp only [mul_one]
      abel
    · show Commute _ _
      simp only [Commute, SemiconjBy, smul_mul_smul_comm, pq, qp, smul_zero]

end GlobalTheory.TorFin.TorusExp
end
end

open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_exponential_projection : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → ∀ x y : Fin n → ℂ, (star x ᵥ* J) ⬝ᵥ x = 0 → (star y ᵥ* J) ⬝ᵥ y = 0 → (star x ᵥ* J) ⬝ᵥ y = 1 → ∀ ζ : ℂ, IsSkew J (ζ • projL J x y - star ζ • projL J y x) ∧ NormedSpace.exp (ζ • projL J x y - star ζ • projL J y x) = torMat J x y (Complex.exp ζ) := by
  atlas_forward_decl GlobalTheory.TorFin.TorusExp.exp_torus
end

section
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TransODE

open NormedSpace

theorem linear_ode_eq_exp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (y : ℝ → E) (hy : ∀ s, HasDerivAt y (L (y s)) s) (t : ℝ) :
    y t = exp (t • L) (y 0) := by
  let z : ℝ → E := fun s => exp ((t - s) • L) (y s)
  have hd : ∀ s, HasDerivAt z 0 s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • L)) (exp ((t - s) • L) * L) (t - s) :=
      hasDerivAt_exp_smul_const L (t - s)
    have h2 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h3 := h1.scomp s h2
    have h4 := h3.clm_apply (hy s)
    convert h4 using 1
    · rfl
    · simp [Function.comp_def]
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [z] using hc

theorem mem_of_translate (G : Type) [Group G] (W : Submodule ℂ (G → ℂ)) (γ : ℝ → G)
    (hfin : FiniteDimensional ℂ W) (hγ : γ 0 = 1)
    (hder : ∀ ψ ∈ W, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ),
      HasDerivAt (fun τ : ℝ => ψ (γ τ * g)) (ψ' (γ t * g)) t) :
    ∀ ψ ∈ W, ∀ t : ℝ, (fun g => ψ (γ t * g)) ∈ W := by
  classical
  let d := Module.finrank ℂ W
  let b : Module.Basis (Fin d) ℂ W := Module.finBasis ℂ W
  have hb : ∀ i, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ),
      HasDerivAt (fun τ : ℝ => (b i : G → ℂ) (γ τ * g)) (ψ' (γ t * g)) t :=
    fun i => hder _ (b i).2
  choose D hDW hD using hb
  have hexp : ∀ (w : W) (x : G), (w : G → ℂ) x = ∑ j, b.repr w j * (b j : G → ℂ) x := by
    intro w x
    calc (w : G → ℂ) x = ((∑ j, b.repr w j • b j : W) : G → ℂ) x := by rw [b.sum_repr w]
      _ = _ := by
        rw [Submodule.coe_sum]
        simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  let M : Matrix (Fin d) (Fin d) ℂ := fun i j => b.repr ⟨D i, hDW i⟩ j
  have hM : ∀ i x, D i x = ∑ j, M i j * (b j : G → ℂ) x := fun i x => hexp ⟨D i, hDW i⟩ x
  let Lc : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
  let L : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) := Lc.restrictScalars ℝ
  have hL : ∀ v i, L v i = ∑ j, M i j * v j := by
    intro v i; simp [L, Lc, Matrix.mulVec, dotProduct]
  have hLc : ∀ (c : ℂ) v, L (c • v) = c • L v := fun c v => by simp [L]
  have hLs : ∀ (f : Fin d → (Fin d → ℂ)), L (∑ j, f j) = ∑ j, L (f j) := fun f => map_sum L f _
  have key : ∀ (g : G) (t : ℝ) i, (b i : G → ℂ) (γ t * g) =
      ∑ j, (exp (t • L) (Pi.single j 1)) i * (b j : G → ℂ) g := by
    intro g t i
    let y : ℝ → (Fin d → ℂ) := fun s k => (b k : G → ℂ) (γ s * g)
    have hy : ∀ s, HasDerivAt y (L (y s)) s := by
      intro s
      rw [hasDerivAt_pi]
      intro k
      have := hD k g s
      rw [hM] at this
      simpa [y, hL] using this
    let v : Fin d → ℂ := fun j => (b j : G → ℂ) g
    let y2 : ℝ → (Fin d → ℂ) := fun s => ∑ j, v j • exp (s • L) (Pi.single j 1)
    have hy2 : ∀ s, HasDerivAt y2 (L (y2 s)) s := by
      intro s
      have : HasDerivAt y2 (∑ j, v j • (L * exp (s • L)) (Pi.single j 1)) s := by
        have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun j s => v j • exp (s • L) (Pi.single j 1))
          (A' := fun j => v j • (L * exp (s • L)) (Pi.single j 1)) (x := s) (fun j _ =>
            (((hasDerivAt_exp_smul_const' L s).clm_apply (hasDerivAt_const s (Pi.single j (1:ℂ) : Fin d → ℂ))).const_smul (v j)).congr_deriv (by simp))
        simpa [y2] using this
      convert this using 1
      simp [y2, hLs, hLc, ContinuousLinearMap.mul_apply]
    have e1 := GlobalTheory.TransODE.linear_ode_eq_exp L y hy t
    have e2 := GlobalTheory.TransODE.linear_ode_eq_exp L y2 hy2 t
    have h0 : y 0 = y2 0 := by
      funext k
      simp [y, y2, v, hγ, Pi.single_apply]
    have := congrFun (e1.trans (h0 ▸ e2.symm)) i
    simpa [y, y2, v, mul_comm, Finset.sum_apply] using this
  intro ψ hψ t
  have hfun : (fun g => ψ (γ t * g)) = ∑ i, b.repr ⟨ψ, hψ⟩ i •
      ∑ j, (exp (t • L) (Pi.single j 1)) i • (b j : G → ℂ) := by
    funext g
    have := hexp ⟨ψ, hψ⟩ (γ t * g)
    simp only at this
    rw [this]
    simp [key, Finset.sum_apply, Finset.mul_sum]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2)

theorem main : ∀ (G : Type) [Group G] (W : Submodule ℂ (G → ℂ)) (γ : ℝ → G), FiniteDimensional ℂ W → γ 0 = 1 → (∀ ψ ∈ W, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ), HasDerivAt (fun τ : ℝ => ψ (γ τ * g)) (ψ' (γ t * g)) t) → ∀ ψ ∈ W, ∀ t : ℝ, (fun g => ψ (γ t * g)) ∈ W :=
  fun G _ W γ hfin hγ hder => mem_of_translate G W γ hfin hγ hder

end GlobalTheory.TransODE
end

open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_translation_invariant : ∀ (G : Type) [Group G] (W : Submodule ℂ (G → ℂ)) (γ : ℝ → G), FiniteDimensional ℂ W → γ 0 = 1 → (∀ ψ ∈ W, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ), HasDerivAt (fun τ : ℝ => ψ (γ τ * g)) (ψ' (γ t * g)) t) → ∀ ψ ∈ W, ∀ t : ℝ, (fun g => ψ (γ t * g)) ∈ W := by
  atlas_forward_decl GlobalTheory.TransODE.main
end

section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.TorFin
open GlobalTheory.Orb (archMat)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TorFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def extZeroArch (w : InfinitePlace F) : w.Completion ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  ((LinearMap.inl F (Ainf F) (Af F)).comp (GlobalTheory.AutFunCompare.sgW w)).rTensor E

theorem compInf_extZeroArch_self (w : InfinitePlace F) (e : w.Completion ⊗[F] E) :
    compInf F E w (extZeroArch w e) = e := by
  classical
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a x =>
    change (GlobalTheory.AutFunCompare.evW w (GlobalTheory.AutFunCompare.sgW w a)) ⊗ₜ[F] x = a ⊗ₜ[F] x
    simp only [GlobalTheory.AutFunCompare.evW, GlobalTheory.AutFunCompare.sgW]
    erw [Pi.evalAlgHom_apply, LinearMap.single_apply, Pi.single_eq_same]

theorem compInf_extZeroArch_ne {w u : InfinitePlace F} (h : u ≠ w) (e : w.Completion ⊗[F] E) :
    compInf F E u (extZeroArch w e) = 0 := by
  classical
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | tmul a x =>
    change (GlobalTheory.AutFunCompare.evW u (GlobalTheory.AutFunCompare.sgW w a)) ⊗ₜ[F] x = 0
    simp only [GlobalTheory.AutFunCompare.evW, GlobalTheory.AutFunCompare.sgW]
    erw [Pi.evalAlgHom_apply, LinearMap.single_apply, Pi.single_eq_of_ne h, TensorProduct.zero_tmul]

theorem compFin_extZeroArch (w : InfinitePlace F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (e : w.Completion ⊗[F] E) : compFin F E v (extZeroArch w e) = 0 := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | tmul a x =>
    change (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 0) ⊗ₜ[F] x = 0
    simp

theorem embArch_mem_unipRad_of_nilRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (x : Fin n → E) (w : InfinitePlace F) (τ : EmbOver E w) (y : GArch σ J w),
    archMat σ J τ y - 1 ∈ nilRad (J.map τ.1) (fun i => τ.1 (x i)) →
    embArch σ J w y ∈ unipRad σ J (Matrix.of fun i (_ : Fin 1) => x i) := by
  intro F E _ _ _ _ _ σ hσ n J _ x w τ y hY
  classical
  set g := embArch σ J w y with hg
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom (AF F) σ J g).1 with hM
  set Y := archMat σ J τ y - 1 with hYdef
  set x' : Fin n → ℂ := fun i => τ.1 (x i) with hx'
  obtain ⟨hY1, hY2, hY3⟩ := mem_nilRad.1 hY

  have hinf : ∀ u, M.map (compInf F E u) = (matHom _ σ J (projArch σ J u g)).1 := fun u =>
    (congrArg Units.val (matHom_projArch σ J u g)).symm
  have hinf_ne : ∀ u, u ≠ w → M.map (compInf F E u) = 1 := fun u hu => by
    rw [hinf u, hg, projArch_embArch_ne σ J hu, map_one]; rfl
  have hfin : ∀ v, M.map (compFin F E v) = 1 := fun v => by
    have h := matHom_proj σ J v g
    rw [hg, proj_embArch, map_one] at h
    exact (congrArg Units.val h).symm
  let Φ : AF F ⊗[F] E →+* ℂ := (infEmb τ).comp (compInf F E w)
  have hΦM : M.map Φ = archMat σ J τ y := by
    rw [GlobalTheory.Orb.archMat_apply, ← projArch_embArch_self σ J w y, ← hg, ← hinf w, Matrix.map_map]; rfl
  have hΦi : ∀ e : E, Φ (inclR (F := F) (AF F) e) = τ.1 e := fun e => by
    change infEmb τ ((1 : w.Completion) ⊗ₜ[F] e) = τ.1 e
    rw [infEmb_tmul, map_one, one_mul]

  have key : ∀ z : AF F ⊗[F] E, (∀ u, u ≠ w → compInf F E u z = 0) → (∀ v, compFin F E v z = 0) → Φ z = 0 → z = 0 :=
    fun z h1 h2 h3 => GlobalTheory.AdelicU.Supp.adTens_ext (fun u => by
      by_cases hu : u = w
      · subst hu
        rw [map_zero]
        exact (infEmb_bijective hσ τ).1 (h3.trans (map_zero _).symm)
      · rw [h1 u hu, map_zero]) fun v => by rw [h2 v, map_zero]
  set m := M - 1 with hm
  have hmap : ∀ {R : Type} [CommRing R] (ψ : AF F ⊗[F] E →+* R), m.map ψ = M.map ψ - 1 := fun ψ => by
    change ψ.mapMatrix (M - 1) = _
    rw [map_sub, map_one]; rfl
  have hm_ne : ∀ u, u ≠ w → m.map (compInf F E u) = 0 := fun u hu => by rw [hmap, hinf_ne u hu, sub_self]
  have hm_fin : ∀ v, m.map (compFin F E v) = 0 := fun v => by rw [hmap, hfin v, sub_self]
  have hmΦ : m.map Φ = Y := by rw [hmap, hΦM]
  have hCΦ : (adMat F (Matrix.of fun i (_ : Fin 1) => x i)).map Φ = Matrix.of fun i (_ : Fin 1) => x' i := by
    ext i j; exact hΦi (x i)
  have hrow : ∀ k i, (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * J).map τ.1 k i =
      (star x' ᵥ* J.map τ.1) i := fun k i => by
    simp only [Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.of_apply, map_sum,
      map_mul, Matrix.vecMul, dotProduct, Pi.star_apply, hx']
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show ((σ : E →+* E) (x l)) = σ (x l) from rfl, hσ.2.2.2]
  have hRΦ : ∀ k i, (adMat F (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * J)).map Φ k i =
      (star x' ᵥ* J.map τ.1) i := fun k i => by
    rw [← hrow k i]; exact hΦi _
  refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
  · ext i j
    refine key _ (fun u hu => ?_) (fun v => ?_) ?_
    · rw [RingHom.map_matrix_mul, hm_ne u hu, Matrix.zero_mul, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hm_fin v, Matrix.zero_mul, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hmΦ, hCΦ]
      have := congrFun hY1 i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · ext k j
    refine key _ (fun u hu => ?_) (fun v => ?_) ?_
    · rw [RingHom.map_matrix_mul, hm_ne u hu, Matrix.mul_zero, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hm_fin v, Matrix.mul_zero, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hmΦ, Matrix.mul_apply]
      simp only [hRΦ]
      have := congrFun hY2 j
      simpa [Matrix.vecMul, dotProduct] using this
  · intro v hv
    have hv' : (star x' ᵥ* J.map τ.1) ⬝ᵥ (fun i => τ.1 (v i)) = 0 := by
      have h0 := congrArg τ.1 (congrFun hv 0)
      rw [RingHom.map_mulVec, Pi.zero_apply, map_zero] at h0
      rw [← h0]
      simp only [Matrix.mulVec, dotProduct, hrow, Function.comp_apply]
    obtain ⟨c, hc⟩ := hY3 _ hv'
    obtain ⟨e, he⟩ := (infEmb_bijective hσ τ).2 c
    refine ⟨fun _ => extZeroArch w e, funext fun i => sub_eq_zero.1 (key _ (fun u hu => ?_) (fun v' => ?_) ?_)⟩
    · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hm_ne u hu, Matrix.zero_mulVec,
        show (compInf F E u ∘ fun _ : Fin 1 => extZeroArch w e) = 0 from funext fun _ => compInf_extZeroArch_ne hu e,
        Matrix.mulVec_zero, Pi.zero_apply, sub_zero]
    · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hm_fin v', Matrix.zero_mulVec,
        show (compFin F E v' ∘ fun _ : Fin 1 => extZeroArch w e) = 0 from funext fun _ => compFin_extZeroArch w v' e,
        Matrix.mulVec_zero, Pi.zero_apply, sub_zero]
    · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hmΦ, hCΦ]
      have hΦe : Φ (extZeroArch w e) = c := by
        change infEmb τ (compInf F E w (extZeroArch w e)) = c
        rw [compInf_extZeroArch_self, he]
      have h1 : (Φ ∘ fun j => inclR (F := F) (AF F) (v j)) = fun j => τ.1 (v j) := funext fun j => hΦi (v j)
      rw [h1, hc]
      simp [Matrix.mulVec, dotProduct, hΦe, mul_comm]

end GlobalTheory.TorFin
end
end

section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.TorFin
open GlobalTheory.Orb (archMat)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_unipotent_radical_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x : Fin n → E) (w : InfinitePlace F) (τ : EmbOver E w) (y : GArch σ J w), archMat σ J τ y - 1 ∈ nilRad (J.map τ.1) (fun i => τ.1 (x i)) → embArch σ J w y ∈ unipRad σ J (Matrix.of fun i (_ : Fin 1) => x i) := by
  first | exact @GlobalTheory.TorFin.embArch_mem_unipRad_of_nilRad | exact GlobalTheory.TorFin.embArch_mem_unipRad_of_nilRad | (intros; apply GlobalTheory.TorFin.embArch_mem_unipRad_of_nilRad <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

noncomputable section

namespace GlobalTheory.CtTransp

theorem setIntegral_unip_eq_constTerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ f : UA σ W.J → ℂ, ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ cc : GAd σ (c • W.J.map σ) → ℂ, IsConstTerm σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) (fun x => f ((toGAd hσ W.J hc).symm x)) cc → ∀ g : UA σ W.J, ∫ u in 𝓕, f (u.1 * g) ∂μ = cc (toGAd hσ W.J hc g) := by
  intro F E _ _ _ _ _ σ B _ d r s W hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH f μ 𝓕 hμ h𝓕 h1 cc hcc g
  set C : Matrix (Fin d) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => H'.x i with hCdef
  let e := toGAd hσ W.J hc
  have hmem := GlobalTheory.T.unipotent_mem_iff_unipotent_radical F E σ B d r s W hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH
  let e' : unip σ W H' ≃* unipRad σ (c • W.J.map σ) C :=
    { toFun := fun u => ⟨e u.1, (hmem u.1).1 u.2⟩
      invFun := fun v => ⟨e.symm v.1, (hmem _).2 (by rw [e.apply_symm_apply]; exact v.2)⟩
      left_inv := fun u => Subtype.ext (e.symm_apply_apply u.1)
      right_inv := fun v => Subtype.ext (e.apply_symm_apply v.1)
      map_mul' := fun u v => Subtype.ext (map_mul e u.1 v.1) }
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hes : Continuous e.symm := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have he' : Continuous e' := (he.comp continuous_subtype_val).subtype_mk _
  have hes' : Continuous e'.symm := (hes.comp continuous_subtype_val).subtype_mk _
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ W.J) := ⟨by
    have h : (fun p : UA σ W.J × UA σ W.J => p.1 * p.2) =
        e.symm ∘ (fun q : GAd σ (c • W.J.map σ) × GAd σ (c • W.J.map σ) => q.1 * q.2) ∘ Prod.map e e := by
      funext p
      simp
    rw [h]
    exact hes.comp (continuous_mul.comp (he.prodMap he))⟩
  haveI : ContinuousMul (unip σ W H') :=
    ⟨(continuous_mul.comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _⟩
  let t : unip σ W H' ≃ₜ unipRad σ (c • W.J.map σ) C := ⟨e'.toEquiv, he', hes'⟩
  let me := t.toMeasurableEquiv
  have hp : MeasurePreserving me μ (μ.map me) := ⟨me.measurable, rfl⟩
  have hH : (μ.map me).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e' he' hes'
  have hps : MeasurePreserving me.symm (μ.map me) μ := hp.symm
  have hmemU : ∀ γ : (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C),
      e'.symm γ.1 ∈ (ratU σ W.J).subgroupOf (unip σ W H') := fun γ => by
    obtain ⟨u, -, hu2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ.2))
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ⟨u, hu2⟩)
  have hmemP : ∀ δ : (ratU σ W.J).subgroupOf (unip σ W H'),
      e' δ.1 ∈ (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C) := fun δ => by
    obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 δ.2)
    have h2 := (e δ.1.1).2
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩))
    exact unitary_of_map_inclR σ d _ m _ (by rw [hm]; rfl) h2
  let fm : (ratU σ W.J).subgroupOf (unip σ W H') →
      (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C) := fun δ => ⟨e' δ.1, hmemP δ⟩
  have hf : Function.Bijective fm :=
    ⟨fun a b hab => Subtype.ext (e'.injective (congrArg Subtype.val hab)),
      fun γ => ⟨⟨e'.symm γ.1, hmemU γ⟩, Subtype.ext (e'.apply_symm_apply γ.1)⟩⟩
  have hfd := h𝓕.preimage_of_equiv hps.quasiMeasurePreserving hf fun δ x => by
    show e'.symm (e' δ.1 * x) = δ.1 * e'.symm x
    rw [map_mul, e'.symm_apply_apply]
  have hset : me ⁻¹' (me.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x
    simp
  have hmass : (μ.map me) (me.symm ⁻¹' 𝓕) = 1 := by
    rw [me.map_apply, hset, h1]
  have hc' := hcc (μ.map me) (me.symm ⁻¹' 𝓕) hH hfd hmass (e g)
  rw [hc', ← hp.setIntegral_preimage_emb me.measurableEmbedding, hset]
  refine integral_congr_ae (.of_forall fun u => ?_)
  show f (u.1 * g) = f (e.symm (e u.1 * e g))
  rw [← map_mul, e.symm_apply_apply]

end GlobalTheory.CtTransp
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_fundamental_domain_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ f : UA σ W.J → ℂ, ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ cc : GAd σ (c • W.J.map σ) → ℂ, IsConstTerm σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) (fun x => f ((toGAd hσ W.J hc).symm x)) cc → ∀ g : UA σ W.J, ∫ u in 𝓕, f (u.1 * g) ∂μ = cc (toGAd hσ W.J hc g) := by
  atlas_forward_decl GlobalTheory.CtTransp.setIntegral_unip_eq_constTerm
end

section
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin.Comb

theorem finiteDimensional_span_translates_prod : ∀ (G ι : Type) [Group G] (T : ι → Set G) (c : G → ℂ), (∀ i j, i ≠ j → ∀ a ∈ T i, ∀ b ∈ T j, a * b = b * a) → (∀ i, FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ a ∈ T i, f = fun g => c (a * g)})) → ∀ l : List ι, l.Nodup → FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ a : ι → G, (∀ i, a i ∈ T i) ∧ f = fun g => c ((l.map a).prod * g)}) := by
  intro G ι _ T c hcomm hfin l hl
  induction l with
  | nil =>
    apply FiniteDimensional.span_of_finite
    apply (Set.finite_singleton (fun g : G => c g)).subset
    rintro f ⟨a, -, rfl⟩
    simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hil, hl⟩ := hl
    haveI := ih hl
    let L : G → (G → ℂ) →ₗ[ℂ] (G → ℂ) := fun b => LinearMap.funLeft ℂ ℂ (fun g => b * g)
    have hL : ∀ b (h : G → ℂ), L b h = fun g => h (b * g) := fun b h => rfl
    set Si : Set (G → ℂ) := {f | ∃ a ∈ T i, f = fun g => c (a * g)} with hSi
    set Sl : Set (G → ℂ) := {f | ∃ a : ι → G, (∀ i, a i ∈ T i) ∧ f = fun g => c ((l.map a).prod * g)} with hSl
    haveI := hfin i
    have hfg : (Submodule.span ℂ Si).FG := Module.Finite.iff_fg.mp inferInstance
    obtain ⟨s, hsSi, hsspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset Si).mp hfg
    have hb : ∀ x : (s : Set (G → ℂ)), ∃ b ∈ T i, (x : G → ℂ) = fun g => c (b * g) :=
      fun x => hsSi x.2
    choose b hbT hbx using hb
    let U : Submodule ℂ (G → ℂ) := ⨆ x : (s : Set (G → ℂ)), (Submodule.span ℂ Sl).map (L (b x))
    haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_iSup _
    refine Submodule.finiteDimensional_of_le (S₂ := U) ?_
    rw [Submodule.span_le]
    rintro f ⟨a, ha, rfl⟩
    set m := (l.map a).prod with hm
    have hcm : ∀ y ∈ T i, y * m = m * y := by
      intro y hy
      have : Commute y m := by
        apply Commute.list_prod_right
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        have hji : i ≠ j := fun h => hil (h ▸ hj)
        exact hcomm i j hji y hy (a j) (ha j)
      exact this.eq
    have hmem : (fun g => c (a i * g)) ∈ Submodule.span ℂ (s : Set (G → ℂ)) := by
      rw [← hsspan]; exact Submodule.subset_span ⟨a i, ha i, rfl⟩
    have hf : (fun g => c ((List.map a (i :: l)).prod * g)) = L m (fun g => c (a i * g)) := by
      funext g; simp [hL, List.map_cons, List.prod_cons, mul_assoc, hm]
    rw [SetLike.mem_coe, hf]
    have hmap : Submodule.map (L m) (Submodule.span ℂ (s : Set (G → ℂ))) ≤ U := by
      rw [Submodule.map_span_le]
      intro x hx
      have hx' : L m x = L (b ⟨x, hx⟩) (fun g => c (m * g)) := by
        have e := hbx ⟨x, hx⟩
        have hyT := hbT ⟨x, hx⟩
        generalize b ⟨x, hx⟩ = y at e hyT ⊢
        simp only at e
        subst e
        funext g; simp only [hL]
        rw [← mul_assoc, hcm _ hyT, mul_assoc]
      rw [hx']
      apply le_iSup (fun x : (s : Set (G → ℂ)) => (Submodule.span ℂ Sl).map (L (b x))) ⟨x, hx⟩
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, ha, rfl⟩)
    exact hmap (Submodule.mem_map_of_mem hmem)

end GlobalTheory.TorFin.Comb
end

open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_product_translates : ∀ (G ι : Type) [Group G] (T : ι → Set G) (c : G → ℂ), (∀ i j, i ≠ j → ∀ a ∈ T i, ∀ b ∈ T j, a * b = b * a) → (∀ i, FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ a ∈ T i, f = fun g => c (a * g)})) → ∀ l : List ι, l.Nodup → FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ a : ι → G, (∀ i, a i ∈ T i) ∧ f = fun g => c ((l.map a).prod * g)}) := by
  atlas_forward_decl GlobalTheory.TorFin.Comb.finiteDimensional_span_translates_prod
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

noncomputable section
namespace GlobalTheory.TorFinArch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem herm_map_eq (σ : E →ₐ[F] E) (hτσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (hσ : ∀ x, σ (σ x) = x)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (p q : Fin n → E) (τ : E →+* ℂ) :
    (star (fun i => τ (p i)) ᵥ* (c • J.map σ).map τ) ⬝ᵥ (fun i => τ (q i)) = τ (c * σ (form σ J p q)) := by
  simp only [form, dotProduct, Matrix.vecMul, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Pi.star_apply, hσ, hτσ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (p q : Fin n → E) :
    form σ J p (fun i => a * q i) = σ a * form σ J p q := by
  simp only [form, dotProduct, Matrix.mulVec, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (p q : Fin n → E) :
    form σ J (fun i => a * p i) q = a * form σ J p q := by
  simp only [form, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem isotropic_dual_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ τ : E →+* ℂ, (star (fun i => τ (H'.x i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (H'.x i)) = 0 ∧ (star (fun i => τ (c⁻¹ * H'.y i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (c⁻¹ * H'.y i)) = 0 ∧ (star (fun i => τ (H'.x i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (c⁻¹ * H'.y i)) = 1 := by
  intro F E _ _ _ _ _ σ B hcm d r s W _ hσ c hc _ d₁ W₁ H' i₀ i₁ hH τ
  have hτσ := hcm.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [herm_map_eq σ hτσ hσ, hH.xx, map_zero, mul_zero, map_zero]
  · rw [herm_map_eq σ hτσ hσ, form_smul_right, form_smul_left, hH.yy, mul_zero, mul_zero, map_zero, mul_zero, map_zero]
  · rw [herm_map_eq σ hτσ hσ, form_smul_right, hH.xy, mul_one, hσ, mul_inv_cancel₀ hc, map_one]

end GlobalTheory.TorFinArch
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_norm_adapted_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ τ : E →+* ℂ, (star (fun i => τ (H'.x i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (H'.x i)) = 0 ∧ (star (fun i => τ (c⁻¹ * H'.y i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (c⁻¹ * H'.y i)) = 0 ∧ (star (fun i => τ (H'.x i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (c⁻¹ * H'.y i)) = 1 := by
  first | exact @GlobalTheory.TorFinArch.isotropic_dual_plane | exact GlobalTheory.TorFinArch.isotropic_dual_plane | (intros; apply GlobalTheory.TorFinArch.isotropic_dual_plane <;> assumption)
end

section
noncomputable section
namespace GlobalTheory.TorFin
open Matrix
open scoped ContDiff

section Mat
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {x y : Fin n → ℂ}

theorem form_swap (hJ : Jᴴ = J) (x y : Fin n → ℂ) : (star y ᵥ* J) ⬝ᵥ x = star ((star x ᵥ* J) ⬝ᵥ y) := by
  rw [← dotProduct_mulVec, star_dotProduct, star_mulVec, hJ]

theorem projL_mulVec (x y v : Fin n → ℂ) : projL J x y *ᵥ v = ((star y ᵥ* J) ⬝ᵥ v) • x := by
  rw [projL, vecMulVec_mulVec, op_smul_eq_smul]

theorem vecMul_projL (x y φ : Fin n → ℂ) : φ ᵥ* projL J x y = (φ ⬝ᵥ x) • (star y ᵥ* J) := by
  rw [projL, vecMul_vecMulVec]

theorem projL_mul (x y x' y' : Fin n → ℂ) (h : (star y ᵥ* J) ⬝ᵥ x' = 0) : projL J x y * projL J x' y' = 0 := by
  rw [projL, projL, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

theorem br_left (hxx : (star x ᵥ* J) ⬝ᵥ x = 0) (y : Fin n → ℂ) {Y : Matrix (Fin n) (Fin n) ℂ} (h : Y ∈ nilRad J x) :
    projL J x y * Y - Y * projL J x y ∈ nilRad J x := by
  have e : Y * projL J x y = 0 := by rw [projL, mul_vecMulVec, h.1, zero_vecMulVec]
  rw [e, sub_zero]
  refine ⟨by rw [← mulVec_mulVec, h.1, mulVec_zero], by rw [← vecMul_vecMul, vecMul_projL, hxx, zero_smul, zero_vecMul],
    fun v _ => ⟨_, by rw [← mulVec_mulVec, projL_mulVec]⟩⟩

theorem br_right (hxx : (star x ᵥ* J) ⬝ᵥ x = 0) (y : Fin n → ℂ) {Y : Matrix (Fin n) (Fin n) ℂ} (h : Y ∈ nilRad J x) :
    projL J y x * Y - Y * projL J y x ∈ nilRad J x := by
  have e : projL J y x * Y = 0 := by rw [projL, vecMulVec_mul, h.2.1, vecMulVec_zero]
  rw [e, zero_sub]
  refine neg_mem ⟨by rw [← mulVec_mulVec, projL_mulVec, hxx, zero_smul, mulVec_zero],
    by rw [← vecMul_vecMul, h.2.1, zero_vecMul],
    fun v hv => ⟨0, by rw [← mulVec_mulVec, projL_mulVec, hv, zero_smul, mulVec_zero, zero_smul]⟩⟩

theorem row_mem (hxx : (star x ᵥ* J) ⬝ᵥ x = 0) {ψ : Fin n → ℂ} (h : ψ ⬝ᵥ x = 0) : vecMulVec x ψ ∈ nilRad J x :=
  ⟨by rw [vecMulVec_mulVec, h, MulOpposite.op_zero, zero_smul], by rw [vecMul_vecMulVec, hxx, zero_smul],
    fun v _ => ⟨_, by rw [vecMulVec_mulVec, op_smul_eq_smul]⟩⟩

theorem col_mem (hxx : (star x ᵥ* J) ⬝ᵥ x = 0) {u : Fin n → ℂ} (h : (star x ᵥ* J) ⬝ᵥ u = 0) :
    vecMulVec u (star x ᵥ* J) ∈ nilRad J x :=
  ⟨by rw [vecMulVec_mulVec, hxx, MulOpposite.op_zero, zero_smul], by rw [vecMul_vecMulVec, h, zero_smul],
    fun v hv => ⟨0, by rw [vecMulVec_mulVec, hv, MulOpposite.op_zero, zero_smul, zero_smul]⟩⟩

theorem IsUni.isUnit (hd : IsUnit J.det) {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) : IsUnit u.det := by
  have := congrArg Matrix.det hu
  rw [det_mul, det_mul] at this
  exact isUnit_of_mul_isUnit_right (this.symm ▸ hd)

theorem IsSkew.exp (hd : IsUnit J.det) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) :
    IsUni J (NormedSpace.exp (t • Z)) := by
  refine GlobalTheory.SmoothForms.exp_mem_UH hd ?_
  have : Zᴴ * J + J * Z = 0 := hZ
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, this, smul_zero]

end Mat

section Alg
variable {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A}

theorem IsIntMod.mono {Z : Subalgebra ℂ A} {I I' : Submodule ℂ A} {H : A} (h : IsIntMod Z I H) (hI : I ≤ I') :
    IsIntMod Z I' H := let ⟨N, hN⟩ := h; ⟨N, sup_le_sup_right hI _ hN⟩

theorem leftIdl_mono {S S' : Set (Matrix (Fin n) (Fin n) ℂ)} (h : S ⊆ S') : leftIdl ρ S ≤ leftIdl ρ S' :=
  Submodule.span_mono fun _ ⟨Y, hY, e⟩ => ⟨Y, h hY, e⟩

theorem mul_mem_leftIdl (hρ : IsLieRep ρ) {S : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ Y ∈ S, X * Y - Y * X ∈ S) : ∀ i ∈ leftIdl ρ S, ρ X * i ∈ leftIdl ρ S := by
  intro i hi
  induction hi using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨Y, hY, w, hw, rfl⟩ := ha
    have e : ρ X * (ρ Y * w) = ρ (X * Y - Y * X) * w + ρ Y * (ρ X * w) := by rw [hρ]; noncomm_ring
    rw [e]
    exact add_mem (Submodule.subset_span ⟨_, hX Y hY, w, hw, rfl⟩)
      (Submodule.subset_span ⟨Y, hY, _, mul_mem (Algebra.subset_adjoin ⟨X, rfl⟩) hw, rfl⟩)
  | zero => simp
  | add a b _ _ h h' => rw [mul_add]; exact add_mem h h'
  | smul c a _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

theorem leftIdl_mul_mem {S : Set (Matrix (Fin n) (Fin n) ℂ)} : ∀ i ∈ leftIdl ρ S, ∀ z ∈ invAlg ρ, i * z ∈ leftIdl ρ S := by
  intro i hi z hz
  induction hi using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨Y, hY, w, hw, rfl⟩ := ha
    exact Submodule.subset_span ⟨Y, hY, _, mul_mem hw hz.1, mul_assoc _ _ _⟩
  | zero => simp
  | add a b _ _ h h' => rw [add_mul]; exact add_mem h h'
  | smul c a _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

end Alg

theorem local_finite {n : ℕ} {G : Type} [Group G] {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hJ : Jᴴ = J) (hd : IsUnit J.det) (hs : IsMulOn J s) {x y : Fin n → ℂ} (hxx : (star x ᵥ* J) ⬝ᵥ x = 0)
    (hyy : (star y ᵥ* J) ⬝ᵥ y = 0) (hxy : (star x ᵥ* J) ⬝ᵥ y = 1) (N : Subgroup G)
    (hN : ∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N)
    (hG : ∀ a : G, ∃ u b, IsUni J u ∧ (∀ v, IsUni J v → b * s v = s v * b) ∧ a = s u * b)
    {c : G → ℂ} (hc : c ∈ smLoc J s) (hcN : ∀ ν ∈ N, ∀ g, c (ν * g) = c g)
    (hz : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z : List (ℝ → G) →₀ ℂ,
      (∀ l ∈ z.support, ∀ γ ∈ l, ∃ Z, IsSkew J Z ∧ γ = lineOf s Z) ∧
      (∀ f ∈ smLoc J s, ∀ a g, wop z (fun x => f (x * a)) g = wop z f (g * a)) ∧ f = wop z c})) :
    FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ z : ℂ, z ≠ 0 ∧ f = fun g => c (s (torMat J x y z) * g)}) := by
  obtain ⟨ρ, hρ, hder⟩ := GlobalTheory.T.smooth_local_lie_representation n G J s hJ hd hs
  have hyx : (star y ᵥ* J) ⬝ᵥ x = 1 := by rw [form_swap hJ, hxy, star_one]
  have hRT := GlobalTheory.T.right_translation_intertwines_lie n G J s hJ hd hs ρ hder
  have hR : ∀ a : G, ∃ r : Module.End ℂ (smLoc J s), (∀ (f : smLoc J s) (g : G), (r f).1 g = f.1 (g * a)) ∧
      ∀ z ∈ invAlg ρ, r * z = z * r := fun a => by
    obtain ⟨u, b, hu, hb, rfl⟩ := hG a
    obtain ⟨r, h1, h2⟩ := hRT u b hu hb
    exact ⟨r, h1, fun z hz => (mem_invAlg.1 hz).2 r u u⁻¹ (mul_nonsing_inv _ (hu.isUnit hd)) h2⟩
  choose R hR1 hR2 using hR
  have hs1 : s 1 = 1 := by
    have h1 : IsUni J 1 := by simp [IsUni]
    have := hs 1 1 h1 h1
    rw [mul_one] at this
    exact left_eq_mul.1 this
  let c' : smLoc J s := ⟨c, hc⟩
  let Λ : Module.End ℂ (smLoc J s) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun T g => (T (R g c')).1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΛ : ∀ T g, Λ T g = (T (R g c')).1 1 := fun _ _ => rfl
  let κ : Module.End ℂ (smLoc J s) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun T => (T c').1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  set H := ρ (projL J x y) with hH
  set H' := ρ (projL J y x) with hH'
  have hpp : Commute (projL J x y) (projL J y x) := by
    change _ = _
    rw [projL_mul _ _ _ _ hyy, projL_mul _ _ _ _ hxx]
  have hHH : Commute H H' := by
    have := hρ (projL J x y) (projL J y x)
    rw [hpp.eq, sub_self, map_zero] at this
    exact sub_eq_zero.1 this.symm
  have hfin := GlobalTheory.T.integral_module_finite_quotient _ _ _ (invAlg ρ) (leftIdl ρ (nilRad J x : Set _)) H H' κ Λ hHH
    (mul_mem_leftIdl hρ fun Y hY => br_left hxx y hY) (mul_mem_leftIdl hρ fun Y hY => br_right hxx y hY) leftIdl_mul_mem
    (fun i hi => funext fun g => GlobalTheory.T.right_derivative_nil_radical_invariant n G J s hJ hd hs ρ hder x N hN (R g c')
      (fun ν hν g' => by rw [hR1, hR1, mul_assoc]; exact hcN ν hν _) i hi)
    ((GlobalTheory.T.integral_module_rank_one_right n _ ρ hρ x _ hyx).mono (leftIdl_mono fun _ ⟨ψ, h, e⟩ => e ▸ row_mem hxx h))
    ((GlobalTheory.T.integral_module_rank_one_left n _ ρ hρ y _ hxy).mono (leftIdl_mono fun _ ⟨u, h, e⟩ => e ▸ col_mem hxx h))
    (Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {f | ∃ z : List (ℝ → G) →₀ ℂ,
      (∀ l ∈ z.support, ∀ γ ∈ l, ∃ Z, IsSkew J Z ∧ γ = lineOf s Z) ∧
      (∀ f ∈ smLoc J s, ∀ a g, wop z (fun x => f (x * a)) g = wop z f (g * a)) ∧ f = wop z c}) (by
        rintro _ ⟨T, hT, rfl⟩
        obtain ⟨z, h1, h2⟩ := GlobalTheory.T.enveloping_algebra_line_words n G J s hJ hd hs ρ hder T hT.1
        refine Submodule.subset_span ⟨z, h1, fun f hf a g => ?_, h2 c'⟩
        have e : (fun x => f (x * a)) = (R a ⟨f, hf⟩).1 := funext fun g => (hR1 a ⟨f, hf⟩ g).symm
        rw [e, ← h2, ← h2 ⟨f, hf⟩, ← hR1, ← Module.End.mul_apply, ← hR2 a T hT, Module.End.mul_apply]))
    (fun z hz h0 T => funext fun g => by
      have h0' : z c' = 0 := Subtype.ext h0
      rw [hΛ, Module.End.mul_apply, ← Module.End.mul_apply z, ← hR2 g z hz, Module.End.mul_apply, h0', map_zero, map_zero]
      rfl)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun p : ℕ × ℕ => Λ (H ^ p.1 * H' ^ p.2)))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz0, rfl⟩
  obtain ⟨hZ, hexp⟩ := GlobalTheory.T.torus_exponential_projection n J hJ x y hxx hyy hxy (Complex.log z)
  rw [Complex.exp_log hz0] at hexp
  set ζ := Complex.log z
  set Z := ζ • projL J x y - star ζ • projL J y x with hZdef
  have hcomm : ∀ (t : ℝ) (p : ℕ × ℕ), R (lineOf s Z t) * (H ^ p.1 * H' ^ p.2) = (H ^ p.1 * H' ^ p.2) * R (lineOf s Z t) := by
    intro t p
    obtain ⟨r, h1, h2⟩ := hRT _ 1 (hZ.exp hd t) fun v _ => by rw [one_mul, mul_one]
    have e : R (lineOf s Z t) = r := LinearMap.ext fun f => Subtype.ext (funext fun g => by rw [hR1, h1, mul_one]; rfl)
    have key : ∀ X, Commute X Z → Commute r (ρ X) := fun X hX => by
      have : Commute (NormedSpace.exp (t • Z)) X := (hX.symm.smul_left t).exp_left
      have h3 := h2 X
      rwa [this.eq, mul_nonsing_inv_cancel_right _ _ ((hZ.exp hd t).isUnit hd)] at h3
    rw [e]
    exact (((key _ (((Commute.refl _).smul_right _).sub_right (hpp.smul_right _))).pow_right _).mul_right
      ((key _ ((hpp.symm.smul_right _).sub_right ((Commute.refl _).smul_right _))).pow_right _)).eq
  have hval : ∀ (T : Module.End ℂ (smLoc J s)) (t : ℝ) (g : G), R (lineOf s Z t) * T = T * R (lineOf s Z t) →
      Λ T (lineOf s Z t * g) = (T (R g c')).1 (1 * lineOf s Z t) := fun T t g hT => by
    have e : R (lineOf s Z t * g) c' = R (lineOf s Z t) (R g c') :=
      Subtype.ext (funext fun g' => by rw [hR1, hR1, hR1, mul_assoc])
    rw [hΛ, e, ← Module.End.mul_apply, ← hT, Module.End.mul_apply, hR1]
  have hρZ : ∀ p : ℕ × ℕ, ρ Z * (H ^ p.1 * H' ^ p.2) =
      ζ • (H ^ (p.1 + 1) * H' ^ p.2) - star ζ • (H ^ p.1 * H' ^ (p.2 + 1)) := fun p => by
    rw [hZdef, map_sub, map_smul, map_smul, ← hH, ← hH', sub_mul, smul_mul_assoc, smul_mul_assoc, ← mul_assoc, ← pow_succ',
      ← mul_assoc, (hHH.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  have h1 := GlobalTheory.T.finite_dim_translation_invariant G _ (lineOf s Z) hfin (by simp [lineOf, hs1]) (fun ψ hψ => by
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨p, rfl⟩ := hψ
      refine ⟨Λ (ρ Z * (H ^ p.1 * H' ^ p.2)), ?_, fun g t => ?_⟩
      · rw [hρZ, map_sub, map_smul, map_smul]
        exact sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(p.1 + 1, p.2), rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(p.1, p.2 + 1), rfl⟩))
      · have e : R (lineOf s Z t) * (ρ Z * (H ^ p.1 * H' ^ p.2)) = (ρ Z * (H ^ p.1 * H' ^ p.2)) * R (lineOf s Z t) := by
          rw [hρZ, mul_sub, sub_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
            hcomm t (p.1 + 1, p.2), hcomm t (p.1, p.2 + 1)]
        rw [hval _ t g e]
        simp only [fun τ => hval _ τ g (hcomm τ p)]
        exact hder Z hZ _ 1 t
    | zero => exact ⟨0, zero_mem _, fun g t => hasDerivAt_const t (0 : ℂ)⟩
    | add a b _ _ h h' =>
      obtain ⟨a', ha, e⟩ := h
      obtain ⟨b', hb, e'⟩ := h'
      exact ⟨a' + b', add_mem ha hb, fun g t => (e g t).add (e' g t)⟩
    | smul k a _ h =>
      obtain ⟨a', ha, e⟩ := h
      exact ⟨k • a', Submodule.smul_mem _ k ha, fun g t => (e g t).const_mul k⟩)
    (Λ (H ^ 0 * H' ^ 0)) (Submodule.subset_span ⟨(0, 0), rfl⟩) 1
  refine Set.mem_of_eq_of_mem (funext fun g => ?_) h1
  rw [hΛ, pow_zero, pow_zero, mul_one, Module.End.one_apply, hR1, one_mul, lineOf, one_smul, hexp]

end GlobalTheory.TorFin
end

noncomputable section
namespace GlobalTheory.TorFin
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Orb (archMat)
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem exists_section (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} (τ : EmbOver E w) :
    (J.map τ.1)ᴴ = J.map τ.1 ∧ IsUnit (J.map τ.1).det ∧ ∃ s : Matrix (Fin n) (Fin n) ℂ → GAd σ J,
      (∀ y, s (archMat σ J τ y) = embArch σ J w y) ∧ (∀ y, IsUni (J.map τ.1) (archMat σ J τ y)) ∧
        ∀ u, IsUni (J.map τ.1) u → ∃ y, archMat σ J τ y = u := by
  classical
  have inj : Function.Injective (archMat σ J τ) := fun a b e => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
    exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))
  have hd : IsUnit (J.map τ.1).det := by
    rw [show (J.map τ.1).det = τ.1 J.det from (RingHom.map_det τ.1 J).symm]
    exact ((map_ne_zero τ.1).2 hJ.2).isUnit
  refine ⟨Matrix.ext fun i j => ?_, hd, fun u => if hu : ∃ y, archMat σ J τ y = u then embArch σ J w hu.choose else 1,
    fun y => ?_, fun y => (archEquiv J h τ y).2, fun u hu => ?_⟩
  · rw [conjTranspose_apply, map_apply, map_apply, ← hJ.1 i j]
    exact (h.2.2.2 _ _).symm
  · have hu : ∃ y', archMat σ J τ y' = archMat σ J τ y := ⟨y, rfl⟩
    simp only [dif_pos hu]
    rw [inj hu.choose_spec]
  · refine ⟨(archEquiv J h τ).symm ⟨Matrix.nonsingInvUnit u (hu.isUnit hd), hu⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    rfl

theorem place_finite (h : IsCMExt F E σ) (hJ : IsHermND σ J) (x : Fin n → E) {w : InfinitePlace F} (τ : EmbOver E w)
    {y : Fin n → ℂ} (hxx : (star (fun i => τ.1 (x i)) ᵥ* J.map τ.1) ⬝ᵥ (fun i => τ.1 (x i)) = 0)
    (hyy : (star y ᵥ* J.map τ.1) ⬝ᵥ y = 0) (hxy : (star (fun i => τ.1 (x i)) ᵥ* J.map τ.1) ⬝ᵥ y = 1)
    {c : GAd σ J → ℂ} (hc : IsSm σ J c)
    (hcN : ∀ ν ∈ unipRad σ J (Matrix.of fun i (_ : Fin 1) => x i), ∀ g, c (ν * g) = c g)
    (hz : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z c})) :
    FiniteDimensional ℂ (Submodule.span ℂ {f : GAd σ J → ℂ | ∃ a ∈ {a | ∃ (b : GArch σ J w) (z : ℂ), z ≠ 0 ∧
      archMat σ J τ b = torMat (J.map τ.1) (fun i => τ.1 (x i)) y z ∧ a = embArch σ J w b}, f = fun g => c (a * g)}) := by
  obtain ⟨h1, hd, s, hs1, hs2, hs3⟩ := exists_section h hJ τ
  have hs : IsMulOn (J.map τ.1) s := fun a b ha hb => by
    obtain ⟨a, rfl⟩ := hs3 a ha
    obtain ⟨b, rfl⟩ := hs3 b hb
    rw [← map_mul, hs1, hs1, hs1, map_mul]
  have hline : ∀ Z, IsSkew (J.map τ.1) Z → IsRealLine σ J (lineOf s Z) := fun Z hZ =>
    ⟨w, τ, Z, hZ, fun t => by
      obtain ⟨b, hb⟩ := hs3 _ (hZ.exp hd t)
      exact ⟨b, by rw [lineOf, ← hb, hs1], hb⟩⟩
  have hsm : ∀ f, IsSm σ J f → f ∈ smLoc (J.map τ.1) s := fun f hf k Z hZ g =>
    hf k (fun i => lineOf s (Z i)) (fun i => hline _ (hZ i)) g
  have := local_finite h1 hd hs hxx hyy hxy (unipRad σ J (Matrix.of fun i (_ : Fin 1) => x i))
    (fun u hu hu' => by
      obtain ⟨b, rfl⟩ := hs3 u hu
      rw [hs1]
      exact GlobalTheory.T.arch_unipotent_radical_mem F E σ h n J hJ x w τ b hu')
    (fun a => ⟨archMat σ J τ (projArch σ J w a), (embArch σ J w (projArch σ J w a))⁻¹ * a, hs2 _, fun v hv => by
      obtain ⟨b, rfl⟩ := hs3 v hv
      rw [hs1]
      exact (commute_embArch σ J b (by simp)).eq.symm, by rw [hs1, mul_inv_cancel_left]⟩)
    (hsm c hc) hcN
    (Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z c})
      (Submodule.span_mono fun f ⟨z, hz1, hz2, e⟩ => ⟨z, ⟨fun l hl γ hγ => by
        obtain ⟨Z, hZ, rfl⟩ := hz1 l hl γ hγ
        exact hline Z hZ, fun f hf a _ g => hz2 f (hsm f hf) a g⟩, e⟩))
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {f : GAd σ J → ℂ | ∃ z : ℂ, z ≠ 0 ∧
    f = fun g => c (s (torMat (J.map τ.1) (fun i => τ.1 (x i)) y z) * g)}) (Submodule.span_mono ?_)
  rintro _ ⟨_, ⟨b, z, hz0, hb, rfl⟩, rfl⟩
  exact ⟨z, hz0, by rw [← hb, hs1]⟩

omit [NumberField E] in

theorem prod_embArch {m : GAd σ J} (hm : m ∈ infPts σ J) :
    (((Finset.univ : Finset (InfinitePlace F)).toList).map fun w => embArch σ J w (projArch σ J w m)).prod = m := by
  classical
  have key : ∀ (l : List (InfinitePlace F)), l.Nodup → ∀ u,
      projArch σ J u (l.map fun w => embArch σ J w (projArch σ J w m)).prod = if u ∈ l then projArch σ J u m else 1 := by
    intro l hl u
    induction l with
    | nil => simp
    | cons w l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih hl.of_cons]
      by_cases e : u = w
      · subst e
        simp [hl.notMem]
      · simp [projArch_embArch_ne σ J e, e]
  refine GAd_ext σ J (fun u => by rw [key _ (Finset.nodup_toList _), if_pos (by simp)]) fun v => ?_
  rw [mem_infPts_iff_forall.1 hm v, map_list_prod, List.map_map]
  exact List.prod_eq_one fun _ h => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 h
    simp

end GlobalTheory.TorFin
end

noncomputable section
namespace GlobalTheory.TorFin
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

theorem levi_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ}
    (hA : H'.IsAdapted σ B G.W W₁ i₀ i₁) (t s : (AE F E)ˣ) :
    leviElt σ G.W W₁ H' (t * s) = leviElt σ G.W W₁ H' t * leviElt σ G.W W₁ H' s := by
  have ex := fun t => GlobalTheory.LeviPlane.levi_exists F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA t
  obtain ⟨t1, t2, t3⟩ := isLevi_leviElt (ex t)
  obtain ⟨s1, s2, s3⟩ := isLevi_leviElt (ex s)
  have hm : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g g' : UA σ J), mat (g * g') = mat g * mat g' := fun _ _ => rfl
  refine GlobalTheory.T.levi_element_unique F E σ B _ _ _ G.W hT.geo.hW d₁ W₁ H' i₀ i₁ hA (t * s) _ _ (isLevi_leviElt (ex (t * s))) ⟨?_, ?_, ?_⟩
  · rw [hm, ← Matrix.mulVec_mulVec, s1, Matrix.mulVec_smul, t1, smul_smul, Units.val_mul, mul_comm]
  · rw [hm, ← Matrix.mulVec_mulVec, s2, Matrix.mulVec_smul, t2, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [hm, Matrix.mul_assoc, s3, ← Matrix.mul_assoc, t3, Matrix.mul_assoc, ← hm, mul_one]

theorem ctLevi_arch_finite : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ f : UA σ G.W.J → ℂ, (∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧ IsAut σ (c • G.W.J.map σ) K (fun x => f ((toGAd hσ G.W.J hc).symm x))) → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun a : idelesInf F E => fun a' : idelesInf F E => ctLevi σ G.W W₁ H' μ 𝓕 f h ((a' : (AE F E)ˣ) * a))) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH hσ c hc hcs f hf μ 𝓕 hμ h𝓕 h1 h
  obtain ⟨K, -, hA⟩ := hf
  have hcm := hT.base.cm
  have hJ := GlobalTheory.CtLeviCont.isHermND_smul σ B G.W hT.geo.hW hσ c hc hcs
  have hC := GlobalTheory.CtLeviCont.isIsoCols_plane σ B G.W W₁ H' hH hσ c
  obtain ⟨cc, hcc, -⟩ := existsUnique_isConstTerm hcm hJ hC (isAut_iff_isAutOn.1 hA).left
  have hct := GlobalTheory.T.unipotent_fundamental_domain_integral F E σ B hcm _ _ _ G.W hT.geo.hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH f μ 𝓕 hμ h𝓕 h1 cc hcc
  have haut := (GlobalTheory.T.automorphic_constant_term_parabolic F E σ hcm _ _ hJ 1 _ (fun _ => 0) hC _ K _ cc inf_le_left (isAut_iff_isAutOn.1 hA)
    (isConstTerm_iff_unipFlag.1 hcc)).1
  have hτ : ∀ w : InfinitePlace F, Nonempty (EmbOver E w) := fun w => inferInstance
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => (hτ w).some
  let T : InfinitePlace F → Set (GAd σ (c • G.W.J.map σ)) := fun w => {a | ∃ (b : GArch σ (c • G.W.J.map σ) w) (z : ℂ), z ≠ 0 ∧
      GlobalTheory.Orb.archMat σ _ (τ w) b = torMat ((c • G.W.J.map σ).map (τ w).1) (fun i => (τ w).1 (H'.x i))
        (fun i => (τ w).1 (c⁻¹ * H'.y i)) z ∧ a = embArch σ _ w b}
  have hfin := GlobalTheory.T.finite_dim_product_translates _ _ T cc
    (by
      rintro i j hij _ ⟨b, -, -, -, rfl⟩ _ ⟨b', -, -, -, rfl⟩
      exact (commute_embArch σ _ b (projArch_embArch_ne σ _ hij b')).eq)
    (fun w => by
      obtain ⟨e1, e2, e3⟩ := GlobalTheory.T.skew_hermitian_norm_adapted_pos F E σ B hcm _ _ _ G.W hT.geo.hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH (τ w).1
      exact place_finite hcm hJ H'.x (τ w) e1 e2 e3 haut.smooth
        (fun ν hν => haut.left ν (Subgroup.mem_sup_left (by rwa [unipFlag_const]))) haut.zfin)
    _ (Finset.nodup_toList Finset.univ)
  let L : (GAd σ (c • G.W.J.map σ) → ℂ) →ₗ[ℂ] (idelesInf F E → ℂ) :=
    LinearMap.funLeft ℂ ℂ fun a' => toGAd hσ G.W.J hc (leviElt σ G.W W₁ H' a' * h)
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ {f : GAd σ (c • G.W.J.map σ) → ℂ |
    ∃ a : InfinitePlace F → GAd σ (c • G.W.J.map σ), (∀ i, a i ∈ T i) ∧
      f = fun g => cc ((Finset.univ.toList.map a).prod * g)}).map L) (Submodule.span_le.2 ?_)
  rintro _ ⟨t, rfl⟩
  obtain ⟨hi, hz⟩ := GlobalTheory.T.levi_element_infinite_points F E σ B hcm _ _ _ G.W hT.geo.hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH t.1 t.2
  refine ⟨_, Submodule.subset_span ⟨fun w => embArch σ _ w (projArch σ _ w (toGAd hσ G.W.J hc (leviElt σ G.W W₁ H' t))),
    fun w => ?_, rfl⟩, funext fun t' => ?_⟩
  · obtain ⟨z, hz0, e⟩ := hz w (τ w)
    exact ⟨_, z, hz0, e, rfl⟩
  · rw [prod_embArch hi]
    change cc (_ * toGAd hσ G.W.J hc (leviElt σ G.W W₁ H' t' * h)) = ctLevi σ G.W W₁ H' μ 𝓕 f h (t'.1 * t.1)
    rw [ctLevi_apply, hct, mul_comm t'.1, levi_mul hT hH, mul_assoc, map_mul (toGAd hσ G.W.J hc) (leviElt σ G.W W₁ H' t)]

end GlobalTheory.TorFin
end
end
