import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.QuaternaryFourierEqAdelic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatMem
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatN

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv

private theorem slice_mem {F : Type} [Field F] [NumberField F] {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi F (Fin 4)) (a b : A F) :
    (fun z : Fin 2 → A F => f ![a, b, z 0, z 1]) ∈ schwartzBruhatPi F (Fin 2) := by
  let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
  let M : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix id e
  let N : Matrix (Fin 2 ⊕ Fin 2) (Fin 4) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix e id
  have hNM : N * M = 1 := by
    ext i j
    simp [M, N, Matrix.mul_apply, Matrix.one_apply]
  have hMN : M * N = 1 := by
    ext i j
    have h := Equiv.sum_comp e
      (fun k => (1 : Matrix (Fin 4) (Fin 4) F) i k * (1 : Matrix (Fin 4) (Fin 4) F) k j)
    rw [Matrix.mul_apply]
    refine h.trans ?_
    simp [Matrix.one_apply]
  have hv : ∀ x : Fin 2 ⊕ Fin 2 → A F, M.map (algebraMap F (A F)) *ᵥ x = fun i => x (e.symm i) := by
    intro x
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.submatrix_apply, id]
    rw [← Equiv.sum_comp e.symm]
    simp [Matrix.one_apply, apply_ite]
  have h1 := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hf
  have h2 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 ![a, b]
  have h3 : (fun z : Fin 2 → A F => f ![a, b, z 0, z 1]) =
      fun x : Fin 2 → A F => f (M.map (algebraMap F (A F)) *ᵥ Sum.elim ![a, b] x) := by
    funext z
    rw [hv]
    congr 1
    funext i
    fin_cases i <;> simp [e, finSumFinEquiv] <;> rfl
  rw [h3]
  exact h2

private def scaleEquiv {F : Type} [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) :
    (Fin 2 → F) ≃ (Fin 2 → F) where
  toFun ξ := ![2 * ξ 0, -2 * δ * ξ 1]
  invFun ξ := ![ξ 0 / 2, -(ξ 1) / (2 * δ)]
  left_inv ξ := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp
  right_inv ξ := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp

end UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv

open UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv in
theorem UpperTheory.ConvolutionTheory.R2.D.rowW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (r₀ r₁ : F) φ, ThRow (rt r₀) (rt r₁) (W.Om (wW F) φ).1 = ThRow (rt (-r₁)) (rt r₀) φ.1 := by
  intro F E _ _ _ _ _ _ _ D W r₀ r₁ φ
  have hδ : D.δ ≠ 0 := by
    intro h0
    have hθ : D.θ = 0 := by
      have h := D.sq
      rw [h0, map_zero] at h
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    have hb : D.b 1 = 0 := by rw [D.b1, hθ]
    exact D.b.ne_zero 1 hb
  have hS : (W.Om (wW F) φ).1 = ft4 D.δ φ.1 := funext (W.Om_w φ)
  set G : (Fin 2 → A F) → ℂ := fun z => hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] with hGdef
  have hG : G ∈ schwartzBruhatPi F (Fin 2) :=
    slice_mem (UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1 (-rt r₁) (rt r₀)
  have hR : ThRow (rt (-r₁)) (rt r₀) φ.1 = ∑' ξ : Fin 2 → F, G fun i => algebraMap F (A F) (ξ i) := by
    simp only [ThRow, hGdef, map_neg]
  rw [hR, tsum_algebraMap_eq_tsum_adelicFourierPi hG,
    ← (scaleEquiv D.δ hδ).tsum_eq (fun ξ : Fin 2 → F => adelicFourierPi F G fun i => algebraMap F (A F) (ξ i))]
  unfold ThRow
  refine tsum_congr fun ξ => ?_
  rw [hS, UpperTheory.ConvolutionTheory.R2.D.hatW F D.δ φ _ hδ]
  simp only [adelicFourierPi, Fin.sum_univ_two]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hGdef, ψ, scaleEquiv, Equiv.coe_fn_mk]
  have key : 2 * (z 0 * rt (ξ 0) - rt D.δ * (z 1 * rt (ξ 1))) =
      z 0 * algebraMap F (A F) (2 * ξ 0) + z 1 * algebraMap F (A F) (-2 * D.δ * ξ 1) := by
    simp only [rt, map_mul, map_neg, map_ofNat]
    ring
  show hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] *
      ((adelicChar F (2 * (z 0 * rt (ξ 0) - rt D.δ * (z 1 * rt (ξ 1)))) : Circle) : ℂ) =
    hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] *
      ((adelicChar F (z 0 * algebraMap F (A F) (2 * ξ 0) +
        z 1 * algebraMap F (A F) (-2 * D.δ * ξ 1)) : Circle) : ℂ)
  rw [key]
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D.SL2BruhatGenerators

section Gen

variable {F : Type} [Field F]

private def nF (b : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

variable (F) in

private def wF : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

private theorem coe_nF (b : F) : (nF b).1 = !![1, b; 0, 1] := rfl

private theorem coe_wF : (wF F).1 = !![0, 1; -1, 0] := rfl

private theorem decomp (γ : Matrix.SpecialLinearGroup (Fin 2) F) (hc : γ.1 1 0 ≠ 0) :
    γ = nF ((γ.1 0 0 - 1) / γ.1 1 0) * (wF F * nF (-(γ.1 1 0)) * (wF F * wF F * wF F)) *
      nF ((γ.1 1 1 - 1) / γ.1 1 0) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_nF, coe_wF]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination hdet | linear_combination -hdet

private theorem decomp0 (γ : Matrix.SpecialLinearGroup (Fin 2) F) :
    γ = (γ * wF F) * (wF F * wF F * wF F) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_wF]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem specialLinearGroup_two_induction_on_unipotent_weyl (P : Matrix.SpecialLinearGroup (Fin 2) F → Prop)
    (hmul : ∀ a b, P a → P b → P (a * b)) (hn : ∀ b, P (nF b)) (hw : P (wF F))
    (γ : Matrix.SpecialLinearGroup (Fin 2) F) : P γ := by
  have hw3 : P (wF F * wF F * wF F) := hmul _ _ (hmul _ _ hw hw) hw
  have key : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) F, γ.1 1 0 ≠ 0 → P γ := by
    intro γ hc
    rw [decomp γ hc]
    exact hmul _ _ (hmul _ _ (hn _) (hmul _ _ (hmul _ _ hw (hn _)) hw3)) (hn _)
  by_cases hc : γ.1 1 0 = 0
  · have hdet := γ.det_coe
    rw [Matrix.det_fin_two, hc] at hdet
    have hd : γ.1 1 1 ≠ 0 := by
      intro h
      rw [h] at hdet
      simp at hdet
    rw [decomp0 γ]
    refine hmul _ _ (key _ ?_) hw3
    have h10 : (γ * wF F).1 1 0 = -γ.1 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_wF, Matrix.mul_apply, Fin.sum_univ_two]
      simp
    rw [h10]
    exact neg_ne_zero.mpr hd
  · exact key γ hc

end Gen

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D)

private theorem ratS_coe (g : Matrix.SpecialLinearGroup (Fin 2) F) (i j : Fin 2) :
    (ratS F g).1 i j = rt (g.1 i j) := rfl

private theorem ratS_nF (b : F) : ratS F (nF b) = nU (rt b) := by
  apply Subtype.ext
  ext i j
  rw [ratS_coe, coe_nF]
  fin_cases i <;> fin_cases j <;> simp [nU]

private theorem ratS_wF : ratS F (wF F) = wW F := by
  apply Subtype.ext
  ext i j
  rw [ratS_coe, coe_wF]
  fin_cases i <;> fin_cases j <;> simp [wW]

private theorem psi_rt (x : F) : ψ (rt x) = 1 := by
  simp [ψ, adelicChar_algebraMap]

private def Good (γ : Matrix.SpecialLinearGroup (Fin 2) F) : Prop :=
  ∀ (r : Fin 2 → F) (φ : S4 F), ThRow (rt (r 0)) (rt (r 1)) (W.Om (ratS F γ) φ).1 =
    ThRow (rt ((r ᵥ* γ.1) 0)) (rt ((r ᵥ* γ.1) 1)) φ.1

private theorem good_mul (a b : Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : Good W a) (hb : Good W b) : Good W (a * b) := by
  intro r φ
  rw [map_mul, map_mul, Module.End.mul_apply, ha r, hb (r ᵥ* a.1) φ,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.vecMul_vecMul]

private theorem good_n (b : F) : Good W (nF b) := by
  intro r φ
  rw [ratS_nF]
  have h0 : (r ᵥ* (nF b).1) 0 = r 0 := by
    rw [coe_nF]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have h1 : (r ᵥ* (nF b).1) 1 = r 1 + b * r 0 := by
    rw [coe_nF]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  rw [h0, h1]
  unfold ThRow
  refine tsum_congr fun ξ => ?_
  rw [UpperTheory.ConvolutionTheory.R2.D.hatN F E D W (rt b) φ]
  have hψ : ψ (rt b * ((![rt (r 0), rt (r 1), rt (ξ 0), rt (ξ 1)] : V4 F) 2 ^ 2 -
      rt D.δ * (![rt (r 0), rt (r 1), rt (ξ 0), rt (ξ 1)] : V4 F) 3 ^ 2)) = 1 := by
    have : rt b * ((![rt (r 0), rt (r 1), rt (ξ 0), rt (ξ 1)] : V4 F) 2 ^ 2 -
        rt D.δ * (![rt (r 0), rt (r 1), rt (ξ 0), rt (ξ 1)] : V4 F) 3 ^ 2) =
        rt (b * (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2)) := by
      simp [map_mul, map_sub, map_pow]
    rw [this, psi_rt]
  rw [hψ, one_mul]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update, map_add, map_mul]

private theorem good_w : Good W (wF F) := by
  intro r φ
  rw [ratS_wF]
  have h0 : (r ᵥ* (wF F).1) 0 = -r 1 := by
    rw [coe_wF]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have h1 : (r ᵥ* (wF F).1) 1 = r 0 := by
    rw [coe_wF]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [h0, h1]
  exact UpperTheory.ConvolutionTheory.R2.D.rowW F E D W (r 0) (r 1) φ

private theorem good_all (γ : Matrix.SpecialLinearGroup (Fin 2) F) : Good W γ :=
  specialLinearGroup_two_induction_on_unipotent_weyl (Good W) (good_mul W) (good_n W) (good_w W) γ

end Main

end UpperTheory.ConvolutionTheory.R2.D.SL2BruhatGenerators

theorem UpperTheory.ConvolutionTheory.R2.D.row :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ γ (r : Fin 2 → F) φ, ThRow (rt (r 0)) (rt (r 1)) (W.Om (ratS F γ) φ).1 =
      ThRow (rt ((r ᵥ* γ.1) 0)) (rt ((r ᵥ* γ.1) 1)) φ.1 := by
  intro F E _ _ _ _ _ _ _ D W γ r φ
  exact UpperTheory.ConvolutionTheory.R2.D.SL2BruhatGenerators.good_all W γ r φ
end
