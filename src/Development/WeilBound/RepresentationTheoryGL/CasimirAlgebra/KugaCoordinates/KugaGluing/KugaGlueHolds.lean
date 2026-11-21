import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgLieOpComm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactCurveDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCompactActionDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactDerivativeSeparatingDual

section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

omit [NumberField E] in
theorem kg_star_atEmb (τ : E →+* ℂ) (z : ℂ) : star (atEmb τ z) = atEmb τ (starRingEnd ℂ z) := by
  classical
  unfold atEmb
  funext w
  simp only [Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp

theorem kg_cx_dmat_conj (Ξ : AlgRep E a)
    (hΞ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ)
    (τ : E →+* ℂ) (i j : Fin a) : (cx τ Ξ.dmat i j)ᴴ = cx τ Ξ.dmat j i := by
  have e : ∀ z, (Ξ.dmat (toL (Matrix.single i j (atEmb τ z))))ᴴ =
      Ξ.dmat (toL (Matrix.single j i (atEmb τ (starRingEnd ℂ z)))) := by
    intro z; rw [← hΞ, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, kg_star_atEmb]
  have e2 : Ξ.dmat (toL (Matrix.single j i (atEmb τ (-Complex.I)))) =
      -Ξ.dmat (toL (Matrix.single j i (atEmb τ Complex.I))) := by
    rw [← map_neg]
    congr 1
    funext k l
    show Matrix.single j i (atEmb τ (-Complex.I)) k l = -(Matrix.single j i (atEmb τ Complex.I) k l)
    rw [Matrix.single_apply, Matrix.single_apply, atEmb_eq τ (-Complex.I), atEmb_eq τ Complex.I]
    split_ifs <;> simp
  unfold cx
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, e, e, map_one,
    Complex.conj_I, e2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  module

theorem kg_cas_herm (Ξ : AlgRep E a)
    (hΞ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ) (τ : E →+* ℂ) :
    (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)ᴴ = ∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, kg_cx_dmat_conj Ξ hΞ]

omit [NumberField E] in
theorem kg_star_iM {X : Matrix (Fin a) (Fin a) (Cinf E)} (hX : star X = X) : star (iM X) = -iM X := by
  ext i j w
  have h : star (X j i) = X i j := by rw [← Matrix.star_apply, hX]
  have h' : star (X j i w) = X i j w := congrFun h w
  simp only [iM, Matrix.star_apply, Matrix.smul_apply, Matrix.neg_apply, Pi.star_apply, Pi.neg_apply, smul_eq_mul,
    Pi.mul_apply, star_mul', h', Complex.star_def, Complex.conj_I]
  ring

def kgL : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Lie E a where
  toFun := toL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NumberField E] in

def kgD (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) : Herm E a →ₗ[ℝ] Herm E a where
  toFun Y := ⟨Z * Y.1 - Y.1 * Z, by
    have hY : star Y.1 = Y.1 := Y.2
    show star (Z * Y.1 - Y.1 * Z) = Z * Y.1 - Y.1 * Z
    rw [star_sub, star_mul, star_mul, hY, hZ, mul_neg, neg_mul, sub_neg_eq_add, neg_add_eq_sub]⟩
  map_add' Y Y' := Subtype.ext (by
    show Z * (Y.1 + Y'.1) - (Y.1 + Y'.1) * Z = (Z * Y.1 - Y.1 * Z) + (Z * Y'.1 - Y'.1 * Z)
    rw [mul_add, add_mul]; abel)
  map_smul' c Y := Subtype.ext (by
    show Z * (c • Y.1) - (c • Y.1) * Z = c • (Z * Y.1 - Y.1 * Z)
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub])

omit [NumberField E] in
theorem kgD_val (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (Y : Herm E a) :
    (kgD Z hZ Y).1 = Z * Y.1 - Y.1 * Z := rfl

end
end PositivityTheory.Rg.Cz
end
end

section
noncomputable section

open scoped TensorProduct Matrix

namespace PositivityTheory.Rg.Cz

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {d : ℕ}
  (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (B : (V ⊗[ℂ] (Fin d → ℂ)) →ₗ[ℂ] (V ⊗[ℂ] (Fin d → ℂ)) →ₗ⋆[ℂ] ℂ)

theorem kg_form_rTensor (hB : ∀ φ ψ v w, B (φ ⊗ₜ v) (ψ ⊗ₜ w) = H ψ φ * (star w ⬝ᵥ v))
    (A : V →ₗ[ℂ] V) (s : ℂ) (hA : ∀ φ ψ, H (A φ) ψ + H φ (A ψ) = s * H φ ψ) (x y : V ⊗[ℂ] (Fin d → ℂ)) :
    B (A.rTensor _ x) y + B x (A.rTensor _ y) = s * B x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply]; linear_combination hx + hx'
  | tmul φ v =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add]; linear_combination hy + hy'
    | tmul ψ w =>
      simp only [LinearMap.rTensor_tmul, hB]
      linear_combination (star w ⬝ᵥ v) * hA ψ φ

theorem kg_form_lTensor (hB : ∀ φ ψ v w, B (φ ⊗ₜ v) (ψ ⊗ₜ w) = H ψ φ * (star w ⬝ᵥ v))
    (D : Matrix (Fin d) (Fin d) ℂ) (hD : Dᴴ = D) (x y : V ⊗[ℂ] (Fin d → ℂ)) :
    B ((Matrix.toLin' D).lTensor V x) y = B x ((Matrix.toLin' D).lTensor V y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul φ v =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul ψ w =>
      simp only [LinearMap.lTensor_tmul, hB, Matrix.toLin'_apply]
      rw [Matrix.star_mulVec, hD, ← Matrix.dotProduct_mulVec]

end

theorem kg_re_le {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) {ι : Type} [Fintype ι]
    (f : ι → Module.End ℂ V) (c : ι → ℝ) (h : ∀ i x, (B (f i x) x).re ≤ c i * (B x x).re) (x : V) :
    (B (((2 : ℂ) • ∑ i, (f i - (c i : ℂ) • 1)) x) x).re ≤ 0 := by
  have e : B (((2 : ℂ) • ∑ i, (f i - (c i : ℂ) • 1)) x) x = 2 * ∑ i, (B (f i x) x - (c i : ℂ) * B x x) := by
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_smul, map_sum, map_sub, smul_eq_mul]
  rw [e, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.re_sum]
  refine mul_nonpos_of_nonneg_of_nonpos (by norm_num) (Finset.sum_nonpos fun i _ => ?_)
  rw [Complex.sub_re, Complex.re_ofReal_mul]
  linarith [h i x]

theorem kg_cas_shift {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (x : ℂ) :
    ∑ i, ∑ j, (F i j + (if i = j then x else 0) • (1 : A)) * (F j i + (if j = i then x else 0) • (1 : A)) =
      ∑ i, ∑ j, F i j * F j i + (2 * x) • ∑ i, F i i + ((n : ℂ) * x ^ 2) • (1 : A) := by
  have h : ∀ i j, (F i j + (if i = j then x else 0) • (1 : A)) * (F j i + (if j = i then x else 0) • (1 : A)) =
      F i j * F j i + if i = j then (2 * x) • F i i + (x ^ 2) • (1 : A) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [if_true, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    · simp [hij, Ne.symm hij]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.smul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  abel
end Cz
end Rg
end PositivityTheory
end
end

section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a) (Ξ : AlgRep E a) (σ : ℝ)

theorem kg_casR (τ : E →+* ℂ) (t : ℝ) (htrX : ∑ i, cx τ Ξ.dmat i i = algebraMap ℂ _ (-(t : ℂ))) :
    ∑ i, ∑ j, cx τ (kgR π Ξ σ) i j * cx τ (kgR π Ξ σ) j i =
      (Matrix.toLin' (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)).lTensor π.V +
        ((2 * (σ / 2 : ℂ)) * (-(t : ℂ)) + (a : ℂ) * (σ / 2 : ℂ) ^ 2) • 1 := by
  let ΦR := (Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) π.V).comp (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin Ξ.d)).toAlgHom
  have hΦR : ∀ A : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ, (Matrix.toLin' A).lTensor π.V = ΦR A := fun A => rfl
  simp only [cx_kgR, hΦR]
  refine (kg_cas_shift (fun i j => ΦR (cx τ Ξ.dmat i j)) (σ / 2 : ℂ)).trans ?_
  simp only [← map_mul, ← map_sum, htrX, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
  module

theorem kg_casA (τ : E →+* ℂ) (c t : ℝ)
    (hcas : ∑ i, ∑ j, cx τ (lieOp π) i j * cx τ (lieOp π) j i = algebraMap ℂ _ (c : ℂ))
    (htr : ∑ i, cx τ (lieOp π) i i = algebraMap ℂ _ (t : ℂ)) :
    ∑ i, ∑ j, cx τ (kgA π Ξ σ) i j * cx τ (kgA π Ξ σ) j i =
      ((c : ℂ) + (2 * (-(σ / 2 : ℂ))) * (t : ℂ) + (a : ℂ) * (-(σ / 2 : ℂ)) ^ 2) • 1 := by
  let ΦA := Module.End.rTensorAlgHom ℂ π.V (Fin Ξ.d → ℂ)
  have hΦA : ∀ f : Module.End ℂ π.V, f.rTensor (Fin Ξ.d → ℂ) = ΦA f := fun f => rfl
  simp only [cx_kgA, hΦA]
  refine (kg_cas_shift (fun i j => ΦA (cx τ (lieOp π) i j)) (-(σ / 2) : ℂ)).trans ?_
  simp only [← map_mul, ← map_sum, hcas, htr, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
  module

theorem kg_casDiff (hC : FrameCas) (cc tt : (E →+* ℂ) → ℝ)
    (hcas : ∀ τ, ∑ i, ∑ j, cx τ (lieOp π) i j * cx τ (lieOp π) j i = algebraMap ℂ _ (cc τ : ℂ))
    (htr : ∀ τ, ∑ i, cx τ (lieOp π) i i = algebraMap ℂ _ (tt τ : ℂ))
    (htrX : ∀ τ, ∑ i, cx τ Ξ.dmat i i = algebraMap ℂ _ (-(tt τ : ℂ))) :
    ((∑ k, kgR π Ξ σ (toL (fr k).1) * kgR π Ξ σ (toL (fr k).1) -
        ∑ k, kgR π Ξ σ (toL (iM (fr k).1)) * kgR π Ξ σ (toL (iM (fr k).1))) -
      (∑ k, kgA π Ξ σ (toL (fr k).1) * kgA π Ξ σ (toL (fr k).1) -
        ∑ k, kgA π Ξ σ (toL (iM (fr k).1)) * kgA π Ξ σ (toL (iM (fr k).1))) :
        Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) =
      (2 : ℂ) • ∑ τ, ((Matrix.toLin' (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)).lTensor π.V - (cc τ : ℂ) • 1) := by
  rw [hC E a _ (kgR π Ξ σ), hC E a _ (kgA π Ξ σ)]
  refine (smul_sub (2 : ℂ) (_ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) _).symm.trans (congrArg _ ?_)
  refine (Finset.sum_sub_distrib (G := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) _ _).symm.trans
    (Finset.sum_congr rfl fun τ _ => ?_)
  rw [kg_casR π Ξ σ τ (tt τ) (htrX τ), kg_casA π Ξ σ τ (cc τ) (tt τ) (hcas τ) (htr τ)]
  module

end
end PositivityTheory.Rg.Cz
end
end

section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

set_option maxHeartbeats 800000 in
theorem kugaGlue_holds : KugaGlue := by
  intro hK hF hC _ hT hH E _ _ _ a π Ξ hU hS q₀ ω₀ hω₀ h0
  refine hH E a _ (tensorK π Ξ) (tensorLie π Ξ) (fun q ω hω => ?_) q₀ ω₀ hω₀ h0
  obtain ⟨Hf, σ, hHs, hHp, hHl⟩ := hU
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := hT π.V Ξ.d Hf hHs hHp
  obtain ⟨hspan, c, hc, hbr, hbr2⟩ := hF E a
  choose cc tt hcas htr htrX hle using hS.2
  have hZ : ∀ k, star (iM (fr (E := E) (a := a) k).1) = -iM (fr k).1 := fun k => kg_star_iM (fr k).2
  have hreal : ∀ X : Lie E a, starRingEnd ℂ (kgT X) = kgT X := fun X => kgT_star X

  have hskew : ∀ (X : Herm E a) (x y : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)),
      B ((kgA π Ξ σ).comp kgH X x) y = -B x ((kgA π Ξ σ).comp kgH X y) := by
    intro X x y
    have h1 := kg_form_rTensor Hf B hB3 (lieOp π (toL X.1)) (σ * kgT (toL X.1)) (fun φ ψ => hHl _ φ ψ) x y
    have hs := hreal (toL X.1)
    rw [LinearMap.comp_apply, show kgH X = toL X.1 from rfl, kgA_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
      LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, map_neg, Complex.conj_ofReal, map_div₀, map_ofNat, hs]
    linear_combination h1
  have hherm : ∀ (X : Herm E a) (x y : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)),
      B ((kgR π Ξ σ).comp kgH X x) y = B x ((kgR π Ξ σ).comp kgH X y) := by
    intro X x y
    have hD : (Ξ.dmat (toL X.1))ᴴ = Ξ.dmat (toL X.1) := by
      rw [← hS.1, show star X.1 = X.1 from X.2]
    have h2 := kg_form_lTensor Hf B hB3 _ hD x y
    have hs := hreal (toL X.1)
    rw [LinearMap.comp_apply, show kgH X = toL X.1 from rfl, kgR_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
      LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, map_neg, Complex.conj_ofReal, map_div₀, map_ofNat, hs]
    linear_combination h2

  have hbrA : ∀ i j, (kgA π Ξ σ).comp kgH (fr i) * (kgA π Ξ σ).comp kgH (fr j) -
      (kgA π Ξ σ).comp kgH (fr j) * (kgA π Ξ σ).comp kgH (fr i) =
      ∑ k, (c i j k : ℂ) • kgA π Ξ σ (toL (iM (fr k).1)) := by
    intro i j
    show kgA π Ξ σ (toL (fr i).1) * kgA π Ξ σ (toL (fr j).1) - kgA π Ξ σ (toL (fr j).1) * kgA π Ξ σ (toL (fr i).1) = _
    rw [kgA_comm, hbr i j, show toL (∑ k, c i j k • iM (fr k).1) = kgL (∑ k, c i j k • iM (fr k).1) from rfl,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, ← algebraMap_smul ℂ (c i j k)]
    rfl
  have hbrR : ∀ i j, (kgR π Ξ σ).comp kgH (fr i) * (kgR π Ξ σ).comp kgH (fr j) -
      (kgR π Ξ σ).comp kgH (fr j) * (kgR π Ξ σ).comp kgH (fr i) =
      ∑ k, (c i j k : ℂ) • kgR π Ξ σ (toL (iM (fr k).1)) := by
    intro i j
    show kgR π Ξ σ (toL (fr i).1) * kgR π Ξ σ (toL (fr j).1) - kgR π Ξ σ (toL (fr j).1) * kgR π Ξ σ (toL (fr i).1) = _
    rw [kgR_comm, hbr i j, show toL (∑ k, c i j k • iM (fr k).1) = kgL (∑ k, c i j k • iM (fr k).1) from rfl,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, ← algebraMap_smul ℂ (c i j k)]
    rfl
  have hDk : ∀ k j, kgD _ (hZ k) (fr j) = ∑ i, c i j k • fr i := fun k j => Subtype.ext (by
    rw [kgD_val, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    exact hbr2 k j)

  have hinv : ∀ k (Y : Fin q → Herm E a), (kgA π Ξ σ (toL (iM (fr k).1)) + kgR π Ξ σ (toL (iM (fr k).1))) (ω Y) =
      ∑ s, ω (Function.update Y s (kgD _ (hZ k) (Y s))) := by
    intro k Y
    obtain ⟨S, hS1, hS2⟩ := GlobalTheory.WigSep.exists_separating_functionals E a π Ξ
    obtain ⟨cv, hc0, hcd⟩ := GlobalTheory.WigCurve.exists_kinf_curve_tangent E a _ (hZ k)
    rw [kgA_add_kgR]
    exact GlobalTheory.CochainInv.lie_apply_eq_sum E a _ (tensorK π Ξ) (tensorLie π Ξ) S cv _ (hZ k) hc0 hcd hS1
      (hS2 cv _ hc0 hcd) q ω hω Y _ (fun s => rfl)

  have hcasI : ∀ x : π.V ⊗[ℂ] (Fin Ξ.d → ℂ),
      (B (((∑ i, (kgR π Ξ σ).comp kgH (fr i) * (kgR π Ξ σ).comp kgH (fr i) -
        ∑ k, kgR π Ξ σ (toL (iM (fr k).1)) * kgR π Ξ σ (toL (iM (fr k).1))) -
        (∑ i, (kgA π Ξ σ).comp kgH (fr i) * (kgA π Ξ σ).comp kgH (fr i) -
        ∑ k, kgA π Ξ σ (toL (iM (fr k).1)) * kgA π Ξ σ (toL (iM (fr k).1))) :
          Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) x) x).re ≤ 0 := by
    intro x
    have e := kg_casDiff π Ξ σ hC cc tt hcas htr htrX
    have h := kg_re_le B _ cc (fun τ y => hB4 _ (cc τ) (kg_cas_herm Ξ hS.1 τ) (hle τ) y) x
    rw [← e] at h
    exact h

  have key := hK (Herm E a) (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) _ _ fr B ((kgA π Ξ σ).comp kgH) ((kgR π Ξ σ).comp kgH)
    (fun k => kgA π Ξ σ (toL (iM (fr k).1))) (fun k => kgR π Ξ σ (toL (iM (fr k).1))) (fun k => kgD _ (hZ k)) c
    hspan hB1 hB2 hskew hherm (fun X Y => kgA_kgR_comm π Ξ σ _ _) (fun k => kgA_kgR_comm π Ξ σ _ _) hbrA hbrR hc hDk
    hcasI q ω hinv
  refine AlternatingMap.ext fun X => ?_
  rw [dCo_apply, AlternatingMap.zero_apply, ← key X]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, kgA_add_kgR]
  rfl

end PositivityTheory.Rg.Cz
end
end
