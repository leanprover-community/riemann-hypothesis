import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagNilradicalFinrankAndAbsDetConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptotic

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.PerpModulus

open GlobalTheory.FlagLeviGroup
open scoped ComplexOrder

variable {n : ℕ} {ε : Fin n → Bool}

def basisMat (V : Submodule ℂ (Fin n → ℂ)) : Matrix (Fin n) (Fin (Module.finrank ℂ V)) ℂ :=
  Matrix.of fun j i => (Module.finBasis ℂ V i : Fin n → ℂ) j

variable (ε) in

def pairMap (V : Submodule ℂ (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
  ((basisMat V)ᴴ * Formalism.REAL.Jm ε).mulVecLin

theorem pairMap_apply (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) (i) :
    pairMap ε V y i = star (Module.finBasis ℂ V i : Fin n → ℂ) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  simp only [pairMap, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, basisMat, Matrix.conjTranspose_apply, Matrix.of_apply,
    Pi.star_apply]

private theorem basisMat_mulVec (V : Submodule ℂ (Fin n → ℂ))
    (c : Fin (Module.finrank ℂ V) → ℂ) :
    basisMat V *ᵥ c = (((Module.finBasis ℂ V).equivFun.symm c : V) : Fin n → ℂ) := by
  funext j
  simp [basisMat, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]

theorem rank_basisMat (V : Submodule ℂ (Fin n → ℂ)) : (basisMat V).rank = Module.finrank ℂ V := by
  have hr : LinearMap.range (basisMat V).mulVecLin = V := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, basisMat_mulVec]
      exact Submodule.coe_mem _
    · intro x hx
      refine ⟨(Module.finBasis ℂ V).equivFun ⟨x, hx⟩, ?_⟩
      rw [Matrix.mulVecLin_apply, basisMat_mulVec, LinearEquiv.symm_apply_apply]
  rw [Matrix.rank, hr]

theorem pairMap_surj (V : Submodule ℂ (Fin n → ℂ)) : Function.Surjective (pairMap ε V) := by
  have hJ : IsUnit (Formalism.REAL.Jm ε).det :=
    Matrix.isUnit_det_of_right_inverse (Formalism.REAL.Jm_mul_self ε)
  have hrk : ((basisMat V)ᴴ * Formalism.REAL.Jm ε).rank = Module.finrank ℂ V := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hJ, Matrix.rank_conjTranspose, rank_basisMat]
  unfold Matrix.rank at hrk
  have htop : LinearMap.range (pairMap ε V) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrk
  exact LinearMap.range_eq_top.mp htop

theorem pair_sum (V : Submodule ℂ (Fin n → ℂ)) (x : V) (y : Fin n → ℂ) :
    star (x : Fin n → ℂ) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) =
      ∑ i, star ((Module.finBasis ℂ V).repr x i) * pairMap ε V y i := by
  have hx : (x : Fin n → ℂ) =
      ∑ i, (Module.finBasis ℂ V).repr x i • ((Module.finBasis ℂ V i : V) : Fin n → ℂ) := by
    have hs := congrArg V.subtype ((Module.finBasis ℂ V).sum_repr x)
    rw [map_sum] at hs
    simp only [map_smul, Submodule.subtype_apply] at hs
    exact hs.symm
  rw [hx, star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, smul_dotProduct, pairMap_apply, smul_eq_mul]

private theorem pairMap_eq_zero_iff (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    pairMap ε V y = 0 ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  constructor
  · intro h0 x hx
    have hs := pair_sum (ε := ε) V ⟨x, hx⟩ y
    simp only [h0, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hs
    exact hs
  · intro h0
    funext i
    rw [pairMap_apply, Pi.zero_apply]
    exact h0 _ (Module.finBasis ℂ V i).2

theorem ker_pairMap {V V' : Submodule ℂ (Fin n → ℂ)}
    (h : ∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) :
    LinearMap.ker (pairMap ε V) = V' := by
  ext y
  rw [LinearMap.mem_ker, pairMap_eq_zero_iff, h]

theorem finrank_perp {V V' : Submodule ℂ (Fin n → ℂ)}
    (h : ∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) :
    Module.finrank ℂ V' + Module.finrank ℂ V = n := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (pairMap ε V)
  rw [LinearMap.range_eq_top.mpr (pairMap_surj (ε := ε) V), finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun, ker_pairMap h] at hrn
  omega

theorem star_form (x y : Fin n → ℂ) :
    star (star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)) = star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  conv_lhs => rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, Formalism.REAL.Jm_conjTranspose,
    ← Matrix.dotProduct_mulVec]

theorem mem_ker_pairMap (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ LinearMap.ker (pairMap ε V) ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  rw [LinearMap.mem_ker]
  exact pairMap_eq_zero_iff V y

theorem perp_perp {V V' : Submodule ℂ (Fin n → ℂ)}
    (h : ∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) (x : Fin n → ℂ)
    (hx : ∀ y ∈ V', star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) : x ∈ V := by
  have hK : ∀ y, y ∈ LinearMap.ker (pairMap ε V') ↔
      ∀ z ∈ V', star z ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := fun y => mem_ker_pairMap V' y
  have h1 := finrank_perp hK
  have h2 := finrank_perp h
  have hle : V ≤ LinearMap.ker (pairMap ε V') := by
    intro v hv
    rw [mem_ker_pairMap]
    intro y hy
    rw [← star_form, (h y).1 hy v hv, star_zero]
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [heq, mem_ker_pairMap]
  exact hx

theorem norm_det (m : Formalism.REAL.UJ ε) : ‖(uMat m).det‖ = 1 := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have hJ : (Formalism.REAL.Jm ε).det ≠ 0 :=
    (Matrix.isUnit_det_of_right_inverse (Formalism.REAL.Jm_mul_self ε)).ne_zero
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at hd
  have h1 : star (uMat m).det * (uMat m).det = 1 := by
    have h0 : (star (uMat m).det * (uMat m).det - 1) * (Formalism.REAL.Jm ε).det = 0 := by
      linear_combination hd
    rcases mul_eq_zero.mp h0 with h | h
    · linear_combination h
    · exact absurd h hJ
  have h2 : ‖(uMat m).det‖ * ‖(uMat m).det‖ = 1 := by
    calc ‖(uMat m).det‖ * ‖(uMat m).det‖ = ‖star (uMat m).det * (uMat m).det‖ := by
          rw [norm_mul, norm_star]
      _ = 1 := by rw [h1, norm_one]
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exact h
  · linarith [norm_nonneg (uMat m).det]

theorem det_restrict_mul (m : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ))
    (h1 : ∀ y ∈ V, toLin' (uMat m) y ∈ V) (h2 : ∀ y ∈ V, toLin' (uMat m⁻¹) y ∈ V) :
    LinearMap.det ((toLin' (uMat m)).restrict h1) *
      LinearMap.det ((toLin' (uMat m⁻¹)).restrict h2) = 1 := by
  rw [← LinearMap.det_comp]
  have hid : ((toLin' (uMat m)).restrict h1).comp ((toLin' (uMat m⁻¹)).restrict h2) =
      LinearMap.id := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.coe_restrict_apply, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec, uMat_mul_inv, Matrix.one_mulVec, LinearMap.id_apply]
  rw [hid, LinearMap.det_id]

theorem det_of_intertwine {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ X] (π : X →ₗ[ℂ] Y) (hπ : Function.Surjective π) (e : X →ₗ[ℂ] X)
    (f : Y →ₗ[ℂ] Y) (hef : ∀ x, π (e x) = f (π x)) (W : Submodule ℂ X) (hW : LinearMap.ker π = W)
    (he : ∀ x ∈ W, e x ∈ W) :
    LinearMap.det e = LinearMap.det (e.restrict he) * LinearMap.det f := by
  classical
  have : FiniteDimensional ℂ Y := Module.Finite.of_surjective π hπ
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hπW : ∀ x ∈ W, π x = 0 := fun x hx => by
    rw [← LinearMap.mem_ker, hW]
    exact hx
  have hπp : ∀ x, π x = π (((Submodule.prodEquivOfIsCompl W C hC).symm x).2 : X) := by
    intro x
    conv_lhs => rw [← (Submodule.prodEquivOfIsCompl W C hC).apply_symm_apply x,
      Submodule.coe_prodEquivOfIsCompl']
    rw [map_add, hπW _ ((Submodule.prodEquivOfIsCompl W C hC).symm x).1.2, zero_add]
  have hinj : Function.Injective (π ∘ₗ C.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hcW : (c : X) ∈ W := by
      rw [← hW, LinearMap.mem_ker]
      exact hc
    exact Subtype.ext ((Submodule.disjoint_def.mp hC.disjoint) _ hcW c.2)
  have hsurj : Function.Surjective (π ∘ₗ C.subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨((Submodule.prodEquivOfIsCompl W C hC).symm x).2, (hπp x).symm⟩
  let ψ : C ≃ₗ[ℂ] Y := LinearEquiv.ofBijective (π ∘ₗ C.subtype) ⟨hinj, hsurj⟩
  let D : C →ₗ[ℂ] C := LinearMap.snd ℂ W C ∘ₗ
    ((Submodule.prodEquivOfIsCompl W C hC).symm : X →ₗ[ℂ] W × C) ∘ₗ e ∘ₗ C.subtype
  have hDf : D = (ψ.symm : Y →ₗ[ℂ] C) ∘ₗ f ∘ₗ (ψ : C →ₗ[ℂ] Y) := by
    apply LinearMap.ext
    intro c
    apply ψ.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    show π (((Submodule.prodEquivOfIsCompl W C hC).symm (e c)).2 : X) = f (π c)
    rw [← hπp, hef]
  have hdetD : LinearMap.det D = LinearMap.det f := by
    rw [hDf]
    exact LinearMap.det_conj f ψ.symm
  let e' : (W × C) →ₗ[ℂ] (W × C) := ((Submodule.prodEquivOfIsCompl W C hC).symm : X →ₗ[ℂ] W × C) ∘ₗ
    e ∘ₗ ((Submodule.prodEquivOfIsCompl W C hC) : W × C →ₗ[ℂ] X)
  have hdet' : LinearMap.det e' = LinearMap.det e := by
    have := LinearMap.det_conj e (Submodule.prodEquivOfIsCompl W C hC).symm
    rwa [LinearEquiv.symm_symm] at this
  have hinl : ∀ j, e' ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C) (Sum.inl j)) =
      (e.restrict he (Module.finBasis ℂ W j), 0) := by
    intro j
    simp only [e', Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
      LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_prodEquivOfIsCompl',
      ZeroMemClass.coe_zero, add_zero]
    exact Submodule.prodEquivOfIsCompl_symm_apply_left W C hC (e.restrict he (Module.finBasis ℂ W j))
  have hinr : ∀ j, (e' ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C) (Sum.inr j))).2 =
      D (Module.finBasis ℂ C j) := by
    intro j
    simp only [e', D, Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd,
      LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_prodEquivOfIsCompl',
      ZeroMemClass.coe_zero, zero_add, LinearMap.snd_apply, Submodule.subtype_apply]
  have hM : LinearMap.toMatrix ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C))
      ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C)) e' =
      Matrix.fromBlocks (LinearMap.toMatrix (Module.finBasis ℂ W) (Module.finBasis ℂ W) (e.restrict he))
        (LinearMap.toMatrix ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C))
          ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C)) e').toBlocks₁₂ 0
        (LinearMap.toMatrix (Module.finBasis ℂ C) (Module.finBasis ℂ C) D) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [Matrix.fromBlocks_apply₁₁, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hinl,
        Module.Basis.prod_repr_inl]
    · rfl
    · rw [Matrix.fromBlocks_apply₂₁, LinearMap.toMatrix_apply, hinl, Module.Basis.prod_repr_inr]
      simp
    · rw [Matrix.fromBlocks_apply₂₂, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
        Module.Basis.prod_repr_inr, hinr]
  rw [← hdet', ← LinearMap.det_toMatrix ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C)), hM,
    Matrix.det_fromBlocks_zero₂₁, LinearMap.det_toMatrix, LinearMap.det_toMatrix, hdetD]

theorem norm_det_perp {V V' : Submodule ℂ (Fin n → ℂ)}
    (h : ∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) (m : Formalism.REAL.UJ ε)
    (h1 : ∀ y ∈ V, toLin' (uMat m) y ∈ V) (h2 : ∀ y ∈ V', toLin' (uMat m⁻¹) y ∈ V') :
    ‖LinearMap.det ((toLin' (uMat m⁻¹)).restrict h2)‖ *
      ‖LinearMap.det ((toLin' (uMat m)).restrict h1)‖ = 1 := by
  classical
  have hef : ∀ y, pairMap ε V (toLin' (uMat m⁻¹) y) =
      toLin' (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V)
        ((toLin' (uMat m)).restrict h1))ᴴ (pairMap ε V y) := by
    intro y
    funext i
    rw [pairMap_apply]
    simp only [Matrix.toLin'_apply]
    rw [form_inv]
    have hx : uMat m *ᵥ ((Module.finBasis ℂ V i : V) : Fin n → ℂ) =
        (((toLin' (uMat m)).restrict h1 (Module.finBasis ℂ V i) : V) : Fin n → ℂ) := rfl
    rw [hx, pair_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, LinearMap.toMatrix_apply]
  have hdet := det_of_intertwine (pairMap ε V) (pairMap_surj V) (toLin' (uMat m⁻¹)) _ hef V'
    (ker_pairMap h) h2
  rw [LinearMap.det_toLin', LinearMap.det_toLin', Matrix.det_conjTranspose,
    LinearMap.det_toMatrix] at hdet
  have hn := congrArg norm hdet
  rw [norm_mul, norm_star, norm_det] at hn
  exact hn.symm

theorem perp_modulus : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Submodule ℂ (Fin n → ℂ)), (∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) → Module.finrank ℂ V' + Module.finrank ℂ V = n ∧ (∀ x, (∀ y ∈ V', star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) → x ∈ V) ∧ ∀ m : Formalism.REAL.UJ ε, ‖(uMat m).det‖ = 1 ∧ ((∀ y ∈ V, uMat m *ᵥ y ∈ V) → (∀ y ∈ V', uMat m *ᵥ y ∈ V') ∧ detOn (uMat m) V' = detOn (uMat m) V ∧ 0 < detOn (uMat m) V) := by
  intro n ε V V' h
  refine ⟨finrank_perp h, fun x hx => perp_perp h x hx, fun m => ⟨norm_det m, fun hV => ?_⟩⟩
  have hVinv : ∀ y ∈ V, uMat m⁻¹ *ᵥ y ∈ V := inv_keeps (uMat_inv_mul m) V hV
  have hV' : ∀ y ∈ V', uMat m *ᵥ y ∈ V' := by
    intro y hy
    rw [h]
    intro x hx
    have hf := form_inv m⁻¹ x y
    rw [inv_inv] at hf
    rw [hf]
    exact (h y).1 hy _ (hVinv x hx)
  have hV'inv : ∀ y ∈ V', uMat m⁻¹ *ᵥ y ∈ V' := inv_keeps (uMat_inv_mul m) V' hV'
  have k1 : ∀ y ∈ V, toLin' (uMat m) y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hV y hy
  have k1' : ∀ y ∈ V', toLin' (uMat m) y ∈ V' := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hV' y hy
  have k2 : ∀ y ∈ V, toLin' (uMat m⁻¹) y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hVinv y hy
  have k2' : ∀ y ∈ V', toLin' (uMat m⁻¹) y ∈ V' := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hV'inv y hy
  have e1 := norm_det_perp h m k1 k2'
  have e2 := congrArg norm (det_restrict_mul m V' k1' k2')
  rw [norm_mul, norm_one] at e2
  have e3 := congrArg norm (det_restrict_mul m V k1 k2)
  rw [norm_mul, norm_one] at e3
  refine ⟨hV', ?_, ?_⟩
  · unfold detOn
    rw [dif_pos k1', dif_pos k1]
    linear_combination ‖LinearMap.det ((toLin' (uMat m)).restrict k1)‖ * e2 -
      ‖LinearMap.det ((toLin' (uMat m)).restrict k1')‖ * e1
  · unfold detOn
    rw [dif_pos k1]
    refine lt_of_le_of_ne (norm_nonneg _) fun h0 => ?_
    rw [← h0, zero_mul] at e3
    exact zero_ne_one e3

end GlobalTheory.PerpModulus
end
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Submodule ℂ (Fin n → ℂ)), (∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) → Module.finrank ℂ V' + Module.finrank ℂ V = n ∧ (∀ x, (∀ y ∈ V', star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) → x ∈ V) ∧ ∀ m : Formalism.REAL.UJ ε, ‖(uMat m).det‖ = 1 ∧ ((∀ y ∈ V, uMat m *ᵥ y ∈ V) → (∀ y ∈ V', uMat m *ᵥ y ∈ V') ∧ detOn (uMat m) V' = detOn (uMat m) V ∧ 0 < detOn (uMat m) V) := by
  atlas_forward_decl GlobalTheory.PerpModulus.perp_modulus
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RealFormBasis

variable {n : ℕ} (ε : Fin n → Bool)

private theorem Jm_mul_self_eq_one' {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTransposeFlagMeasures {n : ℕ} (ε : Fin n → Bool) :
    (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem Jm_mul_Jm_mul' {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, Jm_mul_self_eq_one', Matrix.one_mul]

theorem inG_iff_adj (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε X ↔ Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε = -X := by
  unfold Formalism.REAL.inG
  constructor
  · intro h

    have h' := congrArg (fun M => Formalism.REAL.Jm ε * M) h
    simp only [Matrix.mul_add, Matrix.mul_zero, Jm_mul_Jm_mul'] at h'
    rw [← Matrix.mul_assoc] at h'
    exact eq_neg_of_add_eq_zero_left h'
  · intro h
    have h' := congrArg (fun M => Formalism.REAL.Jm ε * M) h
    simp only [Matrix.mul_assoc, Jm_mul_Jm_mul', Matrix.mul_neg] at h'
    rw [h', neg_add_cancel]

theorem adj_adj (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε = X := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Jm_conjTransposeFlagMeasures]
  simp only [Matrix.mul_assoc, Jm_mul_Jm_mul', Jm_mul_self_eq_one', Matrix.mul_one]

theorem finrank_and_det (n : ℕ) (ε : Fin n → Bool) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ X ∈ N, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N) (hE : LinearIndependent ℝ E)
    (hs : ∀ X, (X ∈ N ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) :
    Module.finrank ℂ N = d ∧ ∀ (φ : N →ₗ[ℂ] N) (L : Matrix (Fin d) (Fin d) ℝ),
      (∀ (k : Fin d) (h : E k ∈ N), ((φ ⟨E k, h⟩ : N) : Matrix (Fin n) (Fin n) ℂ) = ∑ i, L i k • E i) →
      LinearMap.det φ = ((L.det : ℝ) : ℂ) := by
  classical

  have hS_add : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (X + Y)ᴴ * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε := by
    intro X Y
    rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  have hS_sub : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (X - Y)ᴴ * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε - Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε := by
    intro X Y
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hS_smul : ∀ (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.Jm ε * (c • X)ᴴ * Formalism.REAL.Jm ε =
      star c • (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) := by
    intro c X
    rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hS_sum : ∀ g : Fin d → ℂ, Formalism.REAL.Jm ε * (∑ i, g i • E i)ᴴ * Formalism.REAL.Jm ε =
      ∑ i, star (g i) • (Formalism.REAL.Jm ε * (E i)ᴴ * Formalism.REAL.Jm ε) := by
    intro g
    rw [Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hS_smul (g i) (E i)

  have hEmem : ∀ k, E k ∈ N ∧ Formalism.REAL.inG ε (E k) := fun k =>
    (hs (E k)).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hEadj : ∀ k, Formalism.REAL.Jm ε * (E k)ᴴ * Formalism.REAL.Jm ε = -E k := fun k =>
    (inG_iff_adj ε (E k)).1 (hEmem k).2

  have hLI : LinearIndependent ℂ E := by
    rw [Fintype.linearIndependent_iff] at hE ⊢
    intro g hg i
    have h1 : ∑ i, star (g i) • E i = 0 := by
      have h : Formalism.REAL.Jm ε * (∑ i, g i • E i)ᴴ * Formalism.REAL.Jm ε =
          Formalism.REAL.Jm ε * (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε := by rw [hg]
      rw [hS_sum, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul] at h
      simpa only [hEadj, smul_neg, Finset.sum_neg_distrib, neg_eq_zero] using h
    have hre : ∑ i, (2 * (g i).re) • E i = 0 := by
      have h2 : ∑ i, (2 * (g i).re) • E i = (∑ i, g i • E i) + ∑ i, star (g i) • E i := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← add_smul, ← Complex.coe_smul]
        congr 1
        apply Complex.ext <;> simp <;> ring
      rw [h2, hg, h1, add_zero]
    have him : ∑ i, (2 * (g i).im) • E i = 0 := by
      have h2 : ∑ i, (2 * (g i).im) • E i =
          (-Complex.I) • ((∑ i, g i • E i) - ∑ i, star (g i) • E i) := by
        rw [← Finset.sum_sub_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul, smul_smul, ← Complex.coe_smul]
        congr 1
        apply Complex.ext <;> simp <;> ring
      rw [h2, hg, h1, sub_zero, smul_zero]
    have a := hE _ hre i
    have b := hE _ him i
    apply Complex.ext <;> simp <;> linarith

  have hspan : N = Submodule.span ℂ (Set.range E) := by
    apply le_antisymm
    · intro X hX
      have hSX : Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N := hN X hX
      have hSS := adj_adj ε X
      have hA : (1 / 2 : ℂ) • (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) ∈
          Submodule.span ℝ (Set.range E) := by
        refine (hs _).1 ⟨N.smul_mem _ (N.sub_mem hX hSX), ?_⟩
        rw [inG_iff_adj, hS_smul, hS_sub, hSS, ← smul_neg, neg_sub]
        congr 1
        simp
      have hB : (-Complex.I / 2) • (X + Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) ∈
          Submodule.span ℝ (Set.range E) := by
        refine (hs _).1 ⟨N.smul_mem _ (N.add_mem hX hSX), ?_⟩
        rw [inG_iff_adj, hS_smul, hS_add, hSS, add_comm (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) X,
          ← neg_smul]
        congr 1
        apply Complex.ext <;> simp <;> norm_num
      have hA' := Submodule.span_le_restrictScalars ℝ ℂ (Set.range E) hA
      have hB' := Submodule.span_le_restrictScalars ℝ ℂ (Set.range E) hB
      have hX_eq : X = (1 / 2 : ℂ) • (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) +
          Complex.I • ((-Complex.I / 2) • (X + Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)) := by
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hX_eq]
      exact Submodule.add_mem _ hA' (Submodule.smul_mem _ _ hB')
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact (hEmem k).1
  have hfin : Module.finrank ℂ N = d := by
    rw [hspan, finrank_span_eq_card hLI, Fintype.card_fin]
  refine ⟨hfin, ?_⟩
  intro φ L hφ

  let E' : Fin d → N := fun k => ⟨E k, (hEmem k).1⟩
  have hLI' : LinearIndependent ℂ E' := LinearIndependent.of_comp N.subtype hLI
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range E') := by
    rintro ⟨X, hX⟩ -
    have hX' : X ∈ Submodule.span ℂ (Set.range E) := by rw [← hspan]; exact hX
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hX'
    have hXc : (⟨X, hX⟩ : N) = ∑ i, c i • E' i := by
      apply Subtype.ext
      simp [E', ← hc]
    rw [hXc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b := Module.Basis.mk hLI' hsp
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b φ = L.map (fun r : ℝ => (r : ℂ)) := by
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    have hφk : φ (b k) = ∑ j, ((L j k : ℝ) : ℂ) • b j := by
      apply Subtype.ext
      have h := hφ k (hEmem k).1
      simp only [b, Module.Basis.mk_apply, E', Submodule.coe_sum, Submodule.coe_smul] at h ⊢
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.coe_smul]
    rw [hφk]
    have hc : ∑ j, ((L j k : ℝ) : ℂ) • b j = b.equivFun.symm (fun j => ((L j k : ℝ) : ℂ)) := by
      rw [Module.Basis.equivFun_symm_apply]
    rw [hc, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [hM]
  exact (RingHom.map_det Complex.ofRealHom L).symm

end GlobalTheory.RealFormBasis
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_and_det_of_real_basis_skew_part : ∀ (n : ℕ) (ε : Fin n → Bool) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ N, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N) → LinearIndependent ℝ E → (∀ X, (X ∈ N ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → Module.finrank ℂ N = d ∧ ∀ (φ : N →ₗ[ℂ] N) (L : Matrix (Fin d) (Fin d) ℝ), (∀ (k : Fin d) (h : E k ∈ N), ((φ ⟨E k, h⟩ : N) : Matrix (Fin n) (Fin n) ℂ) = ∑ i, L i k • E i) → LinearMap.det φ = ((L.det : ℝ) : ℂ) := by
  atlas_forward_decl GlobalTheory.RealFormBasis.finrank_and_det
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledFlag_sum_eq_unipotentDim_and_layerProd : ∀ (n a : ℕ) (j : Fin a → ℕ) (D : ℕ → ℝ) (ν : ℕ → ℕ), (∀ i, 1 ≤ j i) → (∀ s, 0 < D s) → D 0 = 1 → ν 0 = 0 → (∀ i : Fin a, ν (i + 1) = ν i + j i) → 2 * ν a ≤ n → (∀ s, s ≤ a → D (2 * a + 1 - s) = D s ∧ ν (2 * a + 1 - s) + ν s = n) → ∑ s ∈ Finset.range (2 * a + 1), (ν (s + 1) - ν s) * ν s = dimN n j ∧ layerProd n 1 j (fun i : Fin a => (D (i + 1) / D i) ^ (-(1 : ℝ) / j i)) id = (∏ s ∈ Finset.range (2 * a + 1), D s ^ ν (s + 1) / D (s + 1) ^ ν s)⁻¹ := by
  first | exact @GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq | exact GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq | (intros; apply GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq <;> assumption)
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

noncomputable def matrixEntriesEuclideanReal (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] PiLp 2 (fun _ : Fin n × Fin n => ℂ) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun v := Matrix.of fun i j => v.ofLp (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem inner_matrixEntriesEuclideanReal (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    inner ℝ (matrixEntriesEuclideanReal n Y) (matrixEntriesEuclideanReal n X)
      = ((X * Yᴴ).trace).re := by
  change inner ℝ (WithLp.toLp 2 (fun p : Fin n × Fin n => Y p.1 p.2))
      (WithLp.toLp 2 (fun p : Fin n × Fin n => X p.1 p.2)) = _
  rw [PiLp.inner_apply]
  simp only [WithLp.ofLp_toLp, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.inner, mul_comm]

theorem exists_orthonormal_basis_re_trace_mul_conjTranspose (n : ℕ)
    (U : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ),
      (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ LinearIndependent ℝ E ∧
        U = Submodule.span ℝ (Set.range E) := by
  classical
  set e := matrixEntriesEuclideanReal n
  set V : Submodule ℝ (PiLp 2 (fun _ : Fin n × Fin n => ℂ)) := U.map e.toLinearMap
  let b := stdOrthonormalBasis ℝ V
  refine ⟨Module.finrank ℝ V, fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)), ?_, ?_, ?_⟩
  · intro i k
    have h := inner_matrixEntriesEuclideanReal n (e.symm (b i)) (e.symm (b k))
    simp only [e, LinearEquiv.apply_symm_apply] at h
    rw [← h, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal k i]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  · have hb : LinearIndependent ℝ (fun i => (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ))) :=
      b.orthonormal.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    exact hb.map' e.symm.toLinearMap e.symm.ker
  · symm
    have hrange : Set.range (fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)))
        = e.symm.toLinearMap '' (V.subtype '' Set.range b) := by
      ext x; simp [Set.mem_image, Set.mem_range]
    have hspan : Submodule.span ℝ (Set.range b) = ⊤ := by
      simpa [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
    rw [hrange, Submodule.span_image, Submodule.span_image, hspan, Submodule.map_subtype_top]
    ext x
    simp [V]

end GlobalTheory
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_basis_re_trace_mul_conjTranspose' : ∀ (n : ℕ) (U : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)), ∃ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ LinearIndependent ℝ E ∧ U = Submodule.span ℝ (Set.range E) := by
  atlas_forward_decl GlobalTheory.exists_orthonormal_basis_re_trace_mul_conjTranspose
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.UnitaryCoords

open Formalism.REAL

lemma re_trace_eq_zero {n : ℕ} (J Z Y : Matrix (Fin n) (Fin n) ℂ) (hJ : J * J = 1)
    (hZ : Zᴴ * J = J * Z) (hY : Yᴴ * J + J * Y = 0) : ((Z * Yᴴ).trace).re = 0 := by
  have hY' : Yᴴ = -(J * Y * J) := by
    have h1 : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
    calc Yᴴ = Yᴴ * J * J := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.neg_mul]
  have hZ' : Zᴴ = J * Z * J := by
    calc Zᴴ = Zᴴ * J * J := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = _ := by rw [hZ]
  have h1 : ((Z * Yᴴ).trace).re = ((Y * Zᴴ).trace).re := by
    have : Y * Zᴴ = (Z * Yᴴ)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [this, Matrix.trace_conjTranspose]
    simp
  have h2 : (Y * Zᴴ).trace = -(Z * Yᴴ).trace := by
    rw [hZ', hY', Matrix.mul_neg, Matrix.trace_neg, neg_neg]
    calc (Y * (J * Z * J)).trace = ((Y * J) * (Z * J)).trace := by simp only [Matrix.mul_assoc]
      _ = ((Z * J) * (Y * J)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h2, Complex.neg_re] at h1
  linarith

lemma uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

lemma uMat_mul_inv' {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) : uMat a * uMat a⁻¹ = 1 := by
  rw [← uMat_mul', mul_inv_cancel]; rfl

lemma conjTranspose_mul_J {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) :
    (uMat a)ᴴ * Jm ε = Jm ε * uMat a⁻¹ := by
  have h : (uMat a)ᴴ * Jm ε * uMat a = Jm ε := a.2
  calc (uMat a)ᴴ * Jm ε = (uMat a)ᴴ * Jm ε * (uMat a * uMat a⁻¹) := by
        rw [uMat_mul_inv', Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h]

lemma inv_conjTranspose_mul_J {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) :
    (uMat a⁻¹)ᴴ * Jm ε = Jm ε * uMat a := by
  simpa using conjTranspose_mul_J a⁻¹

lemma coord_eq {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : inG ε Y) :
    2 * (((uMat a - 1) * Yᴴ).trace).re = (((uMat a - uMat a⁻¹) * Yᴴ).trace).re := by
  have h := re_trace_eq_zero (Jm ε) (uMat a + uMat a⁻¹ - 1 - 1) Y (Jm_mul_self ε) (by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, conjTranspose_mul_J a,
      inv_conjTranspose_mul_J a, Matrix.one_mul, Matrix.mul_one]
    abel) hY
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re,
    Complex.add_re] at h ⊢
  linarith

lemma inG_sub_inv {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) : inG ε (uMat a - uMat a⁻¹) := by
  unfold inG
  simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, conjTranspose_mul_J a,
    inv_conjTranspose_mul_J a]
  abel

lemma coord_sum {n d : ℕ} (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (t : Fin d → ℝ) (i : Fin d) :
    (((∑ k, t k • E k) * (E i)ᴴ).trace).re = t i := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, hE]
  simp

theorem coords_conj : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ (g m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), uMat g - 1 ∈ A → uMat g⁻¹ - 1 ∈ A → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → (fun i => (((uMat (m * g * m⁻¹) - 1) * (E i)ᴴ).trace).re) = L *ᵥ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) := by
  intro n ε A d E hE hA g m L hg hg' hL
  have hEG : ∀ i, inG ε (E i) := fun i =>
    ((hA (E i)).2 (Submodule.subset_span ⟨i, rfl⟩)).2
  have hX : uMat g - uMat g⁻¹ ∈ Submodule.span ℝ (Set.range E) := by
    refine (hA _).1 ⟨?_, inG_sub_inv g⟩
    have := A.sub_mem hg hg'
    simpa using this
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  have h1 : ∀ i, 2 * (((uMat g - 1) * (E i)ᴴ).trace).re = t i := fun i => by
    rw [coord_eq g _ (hEG i), ← ht, coord_sum E hE]
  have h2 : uMat (m * g * m⁻¹) - uMat (m * g * m⁻¹)⁻¹ = ∑ i, (∑ k, L i k * t k) • E i := by
    have e : (m * g * m⁻¹)⁻¹ = m * g⁻¹ * m⁻¹ := by group
    rw [e, uMat_mul', uMat_mul', uMat_mul', uMat_mul', ← Matrix.sub_mul, ← Matrix.mul_sub, ← ht,
      Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hL, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  funext i
  have h3 := coord_eq (m * g * m⁻¹) _ (hEG i)
  rw [h2, coord_sum E hE] at h3
  simp only [Matrix.mulVec, dotProduct]
  have h4 : ∑ k, L i k * t k = 2 * ∑ k, L i k * (((uMat g - 1) * (E k)ᴴ).trace).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← h1 k]; ring
  linarith

end GlobalTheory.UnitaryCoords
end
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryJ_lieCoords_conj_linear : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ (g m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), uMat g - 1 ∈ A → uMat g⁻¹ - 1 ∈ A → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → (fun i => (((uMat (m * g * m⁻¹) - 1) * (E i)ᴴ).trace).re) = L *ᵥ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) := by
  atlas_forward_decl GlobalTheory.UnitaryCoords.coords_conj
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.ConjScalesMeasure

theorem eq_smul_map_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (M : Subgroup G) [LocallyCompactSpace M] (hM : IsClosed (M : Set G)) (μ : Measure G)
    (hμ : μ (M : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ M, μ.map (fun g => s * g) = μ) [IsFiniteMeasureOnCompacts μ] :
    ∃ c : NNReal, μ = (c : ENNReal) • (Measure.haar : Measure M).map (Subtype.val : M → G) := by
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology (M : Set G)
  have hemb : MeasurableEmbedding (Subtype.val : M → G) := MeasurableEmbedding.subtype_coe hM.measurableSet
  set ν : Measure M := μ.comap Subtype.val with hν
  have hmap : ν.map Subtype.val = μ := by
    rw [hν, hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem hμ
  have hinj : ∀ ρ : Measure M, (ρ.map (Subtype.val : M → G)).comap Subtype.val = ρ := fun ρ => hemb.comap_map ρ
  haveI : ν.IsMulLeftInvariant := by
    refine ⟨fun s => ?_⟩
    rw [← hinj (ν.map _), Measure.map_map hemb.measurable (measurable_const_mul s)]
    have : (Subtype.val : M → G) ∘ (fun g => s * g) = (fun g => (s : G) * g) ∘ Subtype.val := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmap, hinv s s.2]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [hν, hemb.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top
  have e1 := Measure.isMulLeftInvariant_eq_smul ν (Measure.haar : Measure M)
  refine ⟨Measure.haarScalarFactor ν (Measure.haar : Measure M), ?_⟩
  rw [← Measure.map_smul]
  conv_lhs => rw [← hmap, e1]
  rfl

theorem map_conj_eq_smul_of_group {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (S : Subgroup G) (μ : Measure G) (hS : IsClosed (S : Set G)) (hμ : μ (S : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ S, μ.map (fun g => s * g) = μ) (hfin : IsFiniteMeasureOnCompacts μ) (h0 : μ ≠ 0)
    (m : G) (hm : ∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) :
    ∃ c : NNReal, μ.map (fun u => m * u * m⁻¹) = (c : ENNReal) • μ := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hcm : Measurable (fun u : G => m * u * m⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  haveI : IsFiniteMeasureOnCompacts (μ.map (fun u => m * u * m⁻¹)) :=
    Measure.IsFiniteMeasureOnCompacts.map μ ((Homeomorph.mulLeft m).trans (Homeomorph.mulRight m⁻¹))
  obtain ⟨a, ha⟩ := eq_smul_map_haar S hS μ hμ hinv
  obtain ⟨b, hb⟩ := eq_smul_map_haar S hS (μ.map (fun u => m * u * m⁻¹))
    (by
      rw [Measure.map_apply hcm hS.measurableSet.compl]
      convert hμ using 2
      ext g
      exact not_congr (hm g).symm)
    (by
      intro s hs
      have hs' : m⁻¹ * s * m ∈ S := (hm _).2 (by simpa [mul_assoc] using hs)
      rw [Measure.map_map (measurable_const_mul s) hcm]
      have : (fun g => s * g) ∘ (fun u : G => m * u * m⁻¹)
          = (fun u : G => m * u * m⁻¹) ∘ (fun g => (m⁻¹ * s * m) * g) := by
        funext g
        simp [mul_assoc]
      rw [this, ← Measure.map_map hcm (measurable_const_mul _), hinv _ hs'])
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using ha)
  refine ⟨b / a, ?_⟩
  rw [hb]
  conv_rhs => rw [ha]
  rw [smul_smul, ← ENNReal.coe_mul, div_mul_cancel₀ _ ha0]

theorem map_conj_eq_smul : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → μ (S : Set (Formalism.REAL.UJ ε))ᶜ = 0 → (∀ s ∈ S, μ.map (fun g => s * g) = μ) → IsFiniteMeasureOnCompacts μ → μ ≠ 0 → ∀ m : Formalism.REAL.UJ ε, (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → ∃ c : NNReal, μ.map (fun u => m * u * m⁻¹) = (c : ENNReal) • μ :=
  fun _ _ S μ hS hμ hinv hfin h0 m hm => map_conj_eq_smul_of_group S μ hS hμ hinv hfin h0 m hm

end GlobalTheory.ConjScalesMeasure
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryJ_map_conj_eq_smul_of_normalizing : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → μ (S : Set (Formalism.REAL.UJ ε))ᶜ = 0 → (∀ s ∈ S, μ.map (fun g => s * g) = μ) → IsFiniteMeasureOnCompacts μ → μ ≠ 0 → ∀ m : Formalism.REAL.UJ ε, (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → ∃ c : NNReal, μ.map (fun u => m * u * m⁻¹) = (c : ENNReal) • μ := by
  atlas_forward_decl GlobalTheory.ConjScalesMeasure.map_conj_eq_smul
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConjScale

open Topology Filter

theorem integral_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ) :
    ∫ t, φ (L *ᵥ t) = |L.det|⁻¹ * ∫ t, φ t := by
  have hc : Continuous (Matrix.toLin' L) := LinearMap.continuous_of_finiteDimensional _
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hL
  have h2 : ∫ t, φ t ∂(Measure.map (Matrix.toLin' L) volume) = ∫ t, φ (Matrix.toLin' L t) :=
    integral_map hc.measurable.aemeasurable hφ.aestronglyMeasurable
  rw [h, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul] at h2
  simpa using h2.symm

theorem hasCompactSupport_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : HasCompactSupport φ) : HasCompactSupport (fun t => φ (L *ᵥ t)) := by
  have hu : IsUnit L.det := isUnit_iff_ne_zero.2 hL
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (Matrix.toLinearEquiv' L (Matrix.invertibleOfIsUnitDet L hu)).toContinuousLinearEquiv
  exact hφ.comp_homeomorph e.toHomeomorph

theorem scalar_eq_inv_det {X : Type} [MeasurableSpace X] (μ : Measure X) (T : X → X) (hT : Measurable T)
    (h : X → ℝ) (hh : Measurable h) {d : ℕ} (t : X → Fin d → ℝ) (ht : Measurable t)
    (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0) (c : NNReal) (hc : μ.map T = (c : ENNReal) • μ)
    (hTt : ∀ᵐ g ∂μ, t (T g) = L *ᵥ t g) (C : ℝ) (hC : 1 ≤ C) (h1 : ∀ g, h (T g) ≤ C * h g)
    (h2 : ∀ g, h g ≤ C * h (T g)) (ρ : ℝ) (hρ : 0 < ρ) (hfin : μ {g | h g < ρ} ≠ ⊤)
    (hlim : ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ ρ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | h g < r₁}, φ (fun i => t g i / r) ∂μ)
        (𝓝[>] 0) (𝓝 (∫ x, φ x))) :
    (c : ℝ) = |L.det|⁻¹ := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  let b : ContDiffBump (0 : Fin d → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : (Fin d → ℝ) → ℝ := b
  have hφc : Continuous φ := b.continuous
  have hφs : HasCompactSupport φ := b.hasCompactSupport
  have hφp : 0 < ∫ x, φ x := b.integral_pos
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => b.nonneg
  have hφ1 : ∀ x, φ x ≤ 1 := fun x => b.le_one
  let ψ : (Fin d → ℝ) → ℝ := fun x => φ (L *ᵥ x)
  have hψc : Continuous ψ := hφc.comp (continuous_const.matrix_mulVec continuous_id)
  have hψs : HasCompactSupport ψ := hasCompactSupport_comp_mulVec L hL φ hφs
  have hψi : ∫ x, ψ x = |L.det|⁻¹ * ∫ x, φ x := integral_comp_mulVec L hL φ hφc
  have hr1 : 0 < ρ / C := div_pos hρ hC0
  have hr1' : ρ / C ≤ ρ := div_le_self hρ.le hC
  have hr2 : 0 < ρ / C / C := div_pos hr1 hC0
  have hr2' : ρ / C / C ≤ ρ := (div_le_self hr1.le hC).trans hr1'
  have hB1 : MeasurableSet {g | h g < ρ / C} := measurableSet_lt hh measurable_const
  have hs1 : {g | h g < ρ / C / C} ⊆ T ⁻¹' {g | h g < ρ / C} := by
    intro g hg
    have hg : h g < ρ / C / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h1 g
    show h (T g) < ρ / C
    linarith
  have hs2 : T ⁻¹' {g | h g < ρ / C} ⊆ {g | h g < ρ} := by
    intro g hg
    have hg : h (T g) < ρ / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h2 g
    show h g < ρ
    linarith
  have hm : ∀ r : ℝ, Measurable (fun g => (fun i => t g i / r : Fin d → ℝ)) := fun r =>
    measurable_pi_lambda _ fun i => ((measurable_pi_apply i).comp ht).div_const r
  have hint : ∀ r : ℝ, IntegrableOn (fun g => ψ (fun i => t g i / r)) {g | h g < ρ} μ := by
    intro r
    refine Measure.integrableOn_of_bounded (M := 1) hfin (hψc.measurable.comp (hm r)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun g => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]
    exact hφ1 _
  have key : ∀ r : ℝ, (c : ℝ) * ∫ g in {g | h g < ρ / C}, φ (fun i => t g i / r) ∂μ
      = ∫ g in T ⁻¹' {g | h g < ρ / C}, ψ (fun i => t g i / r) ∂μ := by
    intro r
    have e1 := setIntegral_map (μ := μ) (g := T) (f := fun g => φ (fun i => t g i / r)) hB1
      (hφc.measurable.comp (hm r)).aestronglyMeasurable hT.aemeasurable
    rw [hc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul] at e1
    rw [e1]
    refine integral_congr_ae (ae_restrict_of_ae (hTt.mono fun g hg => ?_))
    have e2 : ∀ y : Fin d → ℝ, (fun i => y i / r) = r⁻¹ • y := fun y => by
      ext i; simp [div_eq_inv_mul]
    show φ (fun i => t (T g) i / r) = φ (L *ᵥ fun i => t g i / r)
    rw [e2, e2, hg, Matrix.mulVec_smul]
  have l1 := (hlim _ hr1 hr1' φ hφc hφs).const_mul (c : ℝ)
  have l2 := hlim _ hr2 hr2' ψ hψc hψs
  have l3 := hlim _ hρ le_rfl ψ hψc hψs
  have a1 : ∫ x, ψ x ≤ c * ∫ x, φ x := by
    refine le_of_tendsto_of_tendsto l2 l1 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set ((hint r).mono_set hs2) (Eventually.of_forall fun g => hφ0 _) hs1.eventuallyLE
  have a2 : c * ∫ x, φ x ≤ ∫ x, ψ x := by
    refine le_of_tendsto_of_tendsto l1 l3 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set (hint r) (Eventually.of_forall fun g => hφ0 _) hs2.eventuallyLE
  exact mul_right_cancel₀ hφp.ne' ((le_antisymm a2 a1).trans hψi)

theorem hs_conj_le {n : ℕ} {ε : Fin n → Bool} (m g : Formalism.REAL.UJ ε) :
    Formalism.REAL.hs (uMat (m * g * m⁻¹) - 1) ≤
      Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) * Formalism.REAL.hs (uMat g - 1) := by
  have a : uMat (m * g * m⁻¹) = uMat m * uMat g * uMat m⁻¹ := rfl
  have b : uMat m * uMat m⁻¹ = 1 := by
    have : uMat m * uMat m⁻¹ = uMat (m * m⁻¹) := rfl
    rw [this, mul_inv_cancel]; rfl
  have e : uMat (m * g * m⁻¹) - 1 = uMat m * (uMat g - 1) * uMat m⁻¹ := by
    rw [a, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, b]
  rw [e]
  refine (Formalism.REAL.frobenius_mul_le _ _).trans ?_
  rw [mul_right_comm]
  exact mul_le_mul_of_nonneg_right (Formalism.REAL.frobenius_mul_le _ _) (Formalism.REAL.frobenius_nonneg _)

theorem map_conj_eq_inv_det_smul (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E))
    (hS : ∀ g, g ∈ S ↔ uMat g - 1 ∈ A) (hcl : IsClosed (S : Set (Formalism.REAL.UJ ε)))
    (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ)
    (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ) (hm : ∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S)
    (hmL : ∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) (hL : L.det ≠ 0) :
    μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  have hSe : (S : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := Set.ext hS
  obtain ⟨-, hK, -, r₀, hr₀, hlim⟩ := GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hE hsp μ (hSe ▸ hμ)
  obtain ⟨h1, h2, h3⟩ := hμ
  have hp : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := Metric.measure_ball_pos _ _ one_pos
  have hf : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) < ⊤ := measure_ball_lt_top
  obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ :=
    (((h3.eventually (lt_mem_nhds hp)).and (h3.eventually (gt_mem_nhds hf))).and self_mem_nhdsWithin).exists
  have hr : 0 < r := hr
  have hcu : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((hcu.sub continuous_const).matrix_elem i j).norm).pow 2
  have hne : μ ≠ 0 := by
    rintro rfl
    simp at hr1
  have hfin : μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hr2
    exact lt_irrefl _ hr2
  obtain ⟨c, hcμ⟩ := GlobalTheory.T.unitaryJ_map_conj_eq_smul_of_normalizing n ε S μ hcl h1 h2 hK hne m hm
  have hC0 : 0 ≤ Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) :=
    mul_nonneg (Formalism.REAL.frobenius_nonneg _) (Formalism.REAL.frobenius_nonneg _)
  have hT : Continuous (fun u : Formalism.REAL.UJ ε => m * u * m⁻¹) := by fun_prop
  have ht : Continuous (fun (g : Formalism.REAL.UJ ε) (i : Fin d) => (((uMat g - 1) * (E i)ᴴ).trace).re) :=
    continuous_pi fun i => Complex.continuous_re.comp
      (((hcu.sub continuous_const).matrix_mul continuous_const).matrix_trace)
  have key := scalar_eq_inv_det μ (fun u => m * u * m⁻¹) hT.measurable _ hc.measurable _ ht.measurable L hL c hcμ
    ?_ (Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) + 1) (by linarith) ?_ ?_ (min r₀ (r ^ 2))
    (lt_min hr₀ (by positivity)) ?_ (fun r₁ a b => hlim r₁ a (b.trans (min_le_left _ _)))
  · rw [hcμ, ← key, ENNReal.ofReal_coe_nnreal]
  · have : ∀ᵐ g ∂μ, g ∈ (S : Set (Formalism.REAL.UJ ε)) := h1
    filter_upwards [this] with g hg
    exact GlobalTheory.T.unitaryJ_lieCoords_conj_linear n ε A d E hE hsp g m L ((hS g).1 hg) ((hS _).1 (S.inv_mem hg)) hmL
  · intro g
    have := hs_conj_le m g
    have := Formalism.REAL.frobenius_nonneg (uMat g - 1)
    linarith
  · intro g
    have h4 := hs_conj_le m⁻¹ (m * g * m⁻¹)
    have e : m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ = g := by group
    rw [e, inv_inv] at h4
    have := Formalism.REAL.frobenius_nonneg (uMat (m * g * m⁻¹) - 1)
    linarith
  · refine ne_top_of_le_ne_top hfin (measure_mono fun g hg => ?_)
    have hg : Formalism.REAL.hs (uMat g - 1) < min r₀ (r ^ 2) := hg
    exact Real.sqrt_le_iff.2 ⟨hr.le, (hg.trans_le (min_le_right _ _)).le⟩

end GlobalTheory.GaugeConjScale
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_conj_gaugeMeasure_eq_inv_det_smul : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε)), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → (∀ g, g ∈ S ↔ uMat g - 1 ∈ A) → IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ → ∀ (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → L.det ≠ 0 → μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  atlas_forward_decl GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagModulus

open Formalism.REAL (Jm inG UJ Jm_mul_self Jm_conjTranspose)

variable {n : ℕ} {ε : Fin n → Bool}

theorem form_adj (X : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Jm ε *ᵥ ((Jm ε * Xᴴ * Jm ε) *ᵥ y)) = star (X *ᵥ x) ⬝ᵥ (Jm ε *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul,
    ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem form_symm {x y : Fin n → ℂ} (h : star x ⬝ᵥ (Jm ε *ᵥ y) = 0) : star y ⬝ᵥ (Jm ε *ᵥ x) = 0 := by
  have h2 := congrArg star h
  rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, Jm_conjTranspose, ← Matrix.dotProduct_mulVec,
    star_zero] at h2
  exact h2

theorem inG_conj (m : UJ ε) {X : Matrix (Fin n) (Fin n) ℂ} (h : inG ε X) : inG ε (uMat m * X * uMat m⁻¹) := by
  have h0 : Xᴴ * Jm ε + Jm ε * X = 0 := h
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h0
  have hg : (uMat m)ᴴ * Jm ε * uMat m = Jm ε := m.2
  have hgi : (uMat m⁻¹)ᴴ * Jm ε * uMat m⁻¹ = Jm ε := (m⁻¹).2
  have hr : uMat m * uMat m⁻¹ = 1 := GlobalTheory.FlagLeviGroup.uMat_mul_inv m
  have hl : uMat m⁻¹ * uMat m = 1 := GlobalTheory.FlagLeviGroup.uMat_inv_mul m
  have e1 : (uMat m)ᴴ * Jm ε = Jm ε * uMat m⁻¹ := by
    calc (uMat m)ᴴ * Jm ε = (uMat m)ᴴ * Jm ε * (uMat m * uMat m⁻¹) := by rw [hr, Matrix.mul_one]
      _ = ((uMat m)ᴴ * Jm ε * uMat m) * uMat m⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Jm ε * uMat m⁻¹ := by rw [hg]
  have e2 : (uMat m⁻¹)ᴴ * Jm ε = Jm ε * uMat m := by
    calc (uMat m⁻¹)ᴴ * Jm ε = (uMat m⁻¹)ᴴ * Jm ε * (uMat m⁻¹ * uMat m) := by rw [hl, Matrix.mul_one]
      _ = ((uMat m⁻¹)ᴴ * Jm ε * uMat m⁻¹) * uMat m := by simp only [Matrix.mul_assoc]
      _ = Jm ε * uMat m := by rw [hgi]
  show (uMat m * X * uMat m⁻¹)ᴴ * Jm ε + Jm ε * (uMat m * X * uMat m⁻¹) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc (uMat m⁻¹)ᴴ * (Xᴴ * (uMat m)ᴴ) * Jm ε + Jm ε * (uMat m * X * uMat m⁻¹)
      = (uMat m⁻¹)ᴴ * Xᴴ * ((uMat m)ᴴ * Jm ε) + Jm ε * (uMat m * X * uMat m⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = (uMat m⁻¹)ᴴ * (Xᴴ * Jm ε) * uMat m⁻¹ + Jm ε * (uMat m * X * uMat m⁻¹) := by
        rw [e1]; simp only [Matrix.mul_assoc]
    _ = -((uMat m⁻¹)ᴴ * Jm ε * X * uMat m⁻¹) + Jm ε * (uMat m * X * uMat m⁻¹) := by
        rw [h1]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = 0 := by
        rw [e2]; simp only [Matrix.mul_assoc]; exact neg_add_cancel _

variable (ε) in

def perpJ (V : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {y | ∀ x ∈ V, star x ⬝ᵥ (Jm ε *ᵥ y) = 0}
  add_mem' := fun {y z} hy hz x hx => by
    rw [Matrix.mulVec_add, dotProduct_add, hy x hx, hz x hx, add_zero]
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c y hy x hx => by
    rw [Matrix.mulVec_smul, dotProduct_smul, hy x hx, smul_zero]

theorem mem_perpJ {V : Submodule ℂ (Fin n → ℂ)} {y : Fin n → ℂ} :
    y ∈ perpJ ε V ↔ ∀ x ∈ V, star x ⬝ᵥ (Jm ε *ᵥ y) = 0 := Iff.rfl

variable (ε) in

def lieSub : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | inG ε X}
  add_mem' := fun {X Y} hX hY => by
    have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
    have h2 : Yᴴ * Jm ε + Jm ε * Y = 0 := hY
    change (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, h1, h2, add_zero]
  zero_mem' := by simp [inG]
  smul_mem' := fun c X hX => by
    have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
    change (c • X)ᴴ * Jm ε + Jm ε * (c • X) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]

def lower (F : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s}
  add_mem' := fun {X Y} hX hY s hs y hy => by
    rw [Matrix.add_mulVec]; exact (F s).add_mem (hX s hs y hy) (hY s hs y hy)
  zero_mem' := fun s _ y _ => by simp
  smul_mem' := fun c X hX s hs y hy => by
    rw [Matrix.smul_mulVec]; exact (F s).smul_mem c (hX s hs y hy)

variable {a : ℕ}

def natFlag (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (s : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  W ⟨min s a, by omega⟩

variable (ε) in

def dblFlag (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (s : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  if s ≤ a then natFlag W s else perpJ ε (natFlag W (2 * a + 1 - s))

variable {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}

theorem dblFlag_le {s : ℕ} (hs : s ≤ a) : dblFlag ε W s = natFlag W s := by rw [dblFlag, if_pos hs]

theorem dblFlag_fin (i : Fin (a + 1)) : dblFlag ε W i = W i := by
  rw [dblFlag_le (Nat.lt_succ_iff.mp i.isLt)]
  exact congrArg W (Fin.ext (min_eq_left (Nat.lt_succ_iff.mp i.isLt)))

theorem dblFlag_succ (i : Fin a) : dblFlag ε W (i + 1) = W i.succ := by
  rw [← Fin.val_succ]
  exact dblFlag_fin i.succ

theorem dblFlag_castSucc (i : Fin a) : dblFlag ε W i = W i.castSucc := by
  have h := dblFlag_fin (ε := ε) (W := W) i.castSucc
  rwa [Fin.val_castSucc] at h

theorem dblFlag_last : dblFlag ε W a = W (Fin.last a) := by
  have h := dblFlag_fin (ε := ε) (W := W) (Fin.last a)
  rwa [Fin.val_last] at h

theorem dblFlag_sub {s : ℕ} (hs : s ≤ a) : dblFlag ε W (2 * a + 1 - s) = perpJ ε (dblFlag ε W s) := by
  rw [dblFlag_le hs, dblFlag, if_neg (by omega), show 2 * a + 1 - (2 * a + 1 - s) = s by omega]

theorem dblFlag_dual {s : ℕ} (hs : s ≤ 2 * a + 1) :
    dblFlag ε W (2 * a + 1 - s) = perpJ ε (dblFlag ε W s) := by
  by_cases h : s ≤ a
  · exact dblFlag_sub h
  · have ht : 2 * a + 1 - s ≤ a := by omega
    have e := dblFlag_sub (ε := ε) (W := W) ht
    rw [show 2 * a + 1 - (2 * a + 1 - s) = s by omega] at e
    rw [e]
    have h40 := GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W (2 * a + 1 - s)) (perpJ ε (dblFlag ε W (2 * a + 1 - s)))
      (fun y => mem_perpJ)
    apply le_antisymm
    · intro x hx
      rw [mem_perpJ]
      intro y hy
      rw [mem_perpJ] at hy
      exact form_symm (hy x hx)
    · intro x hx
      rw [mem_perpJ] at hx
      exact h40.2.1 x hx

theorem dblFlag_mono (hW : IsIsoFlag ε j W) : Monotone (dblFlag ε W) := by
  have nm : ∀ {s t : ℕ}, s ≤ t → natFlag W s ≤ natFlag W t := fun {s t} h =>
    hW.2.1 (show (⟨min s a, by omega⟩ : Fin (a + 1)) ≤ ⟨min t a, by omega⟩ from
      Fin.mk_le_mk.2 (min_le_min_right a h))
  have anti : ∀ {V V' : Submodule ℂ (Fin n → ℂ)}, V ≤ V' → perpJ ε V' ≤ perpJ ε V := by
    intro V V' h y hy
    rw [mem_perpJ] at hy ⊢
    exact fun x hx => hy x (h hx)
  have hl : natFlag W a = W (Fin.last a) := congrArg W (Fin.ext (min_self a))
  have iso : natFlag W a ≤ perpJ ε (natFlag W a) := by
    rw [hl]
    intro x hx
    rw [mem_perpJ]
    intro x' hx'
    exact hW.2.2.2 x' hx' x hx
  intro s t hst
  by_cases ht : t ≤ a
  · rw [dblFlag_le (hst.trans ht), dblFlag_le ht]
    exact nm hst
  · have et : dblFlag ε W t = perpJ ε (natFlag W (2 * a + 1 - t)) := by rw [dblFlag, if_neg ht]
    by_cases hs : s ≤ a
    · rw [dblFlag_le hs, et]
      exact (nm hs).trans (iso.trans (anti (nm (by omega))))
    · have es : dblFlag ε W s = perpJ ε (natFlag W (2 * a + 1 - s)) := by rw [dblFlag, if_neg hs]
      rw [es, et]
      exact anti (nm (by omega))

theorem dblFlag_zero (hW : IsIsoFlag ε j W) : dblFlag ε W 0 = ⊥ := by
  rw [dblFlag_le (Nat.zero_le a)]
  have e : (⟨min 0 a, by omega⟩ : Fin (a + 1)) = 0 := Fin.ext (by simp)
  show W ⟨min 0 a, by omega⟩ = ⊥
  rw [e]
  exact hW.1

theorem dblFlag_top (hW : IsIsoFlag ε j W) : dblFlag ε W (2 * a + 1) = ⊤ := by
  have e := dblFlag_sub (ε := ε) (W := W) (Nat.zero_le a)
  rw [Nat.sub_zero, dblFlag_zero hW] at e
  rw [e, eq_top_iff]
  intro y _
  rw [mem_perpJ]
  intro x hx
  rw [(Submodule.mem_bot ℂ).1 hx, star_zero, zero_dotProduct]

theorem dblFlag_keeps (m : UJ ε) (hm : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i) (s : ℕ) :
    ∀ y ∈ dblFlag ε W s, uMat m *ᵥ y ∈ dblFlag ε W s := by
  intro y hy
  by_cases hs : s ≤ a
  · rw [dblFlag_le hs] at hy ⊢
    exact hm _ y hy
  · have e : dblFlag ε W s = perpJ ε (natFlag W (2 * a + 1 - s)) := by rw [dblFlag, if_neg hs]
    rw [e, mem_perpJ] at hy ⊢
    intro x hx
    have h1 := GlobalTheory.FlagLeviGroup.form_inv m⁻¹ x y
    rw [inv_inv] at h1
    rw [h1]
    exact hy _ (GlobalTheory.FlagMeas.UnipRad.inv_keeps m (natFlag W (2 * a + 1 - s)) (hm _) x hx)

theorem adj_mem_lower {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lower (dblFlag ε W) (2 * a + 1)) :
    Jm ε * Xᴴ * Jm ε ∈ lower (dblFlag ε W) (2 * a + 1) := by
  have hX' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s := hX
  show ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (Jm ε * Xᴴ * Jm ε) *ᵥ y ∈ dblFlag ε W s
  intro s hs y hy
  have e1 : dblFlag ε W s = perpJ ε (dblFlag ε W (2 * a + 1 - s)) := by
    have h := dblFlag_dual (ε := ε) (W := W) (s := 2 * a + 1 - s) (by omega)
    rwa [show 2 * a + 1 - (2 * a + 1 - s) = s by omega] at h
  have e2 : dblFlag ε W (s + 1) = perpJ ε (dblFlag ε W (2 * a - s)) := by
    have h := dblFlag_dual (ε := ε) (W := W) (s := 2 * a - s) (by omega)
    rwa [show 2 * a + 1 - (2 * a - s) = s + 1 by omega] at h
  rw [e1, mem_perpJ]
  rw [e2, mem_perpJ] at hy
  intro x hx
  rw [form_adj]
  have hx' : x ∈ dblFlag ε W (2 * a - s + 1) := by rwa [show 2 * a - s + 1 = 2 * a + 1 - s by omega]
  exact hy _ (hX' (2 * a - s) (by omega) x hx')

theorem mem_lower_half {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ lower (dblFlag ε W) (a + 1) ↔
    (∀ i : Fin a, ∀ y ∈ W i.succ, X *ᵥ y ∈ W i.castSucc) ∧
      ∀ y, (∀ x ∈ W (Fin.last a), star x ⬝ᵥ (Jm ε *ᵥ y) = 0) → X *ᵥ y ∈ W (Fin.last a) := by
  have ea1 : dblFlag ε W (a + 1) = perpJ ε (W (Fin.last a)) := by
    have h := dblFlag_sub (ε := ε) (W := W) (le_refl a)
    rwa [show 2 * a + 1 - a = a + 1 by omega, dblFlag_last] at h
  constructor
  · intro hX
    have hX' : ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s := hX
    refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
    · have h := hX' i (by omega) y (by rw [dblFlag_succ]; exact hy)
      rwa [dblFlag_castSucc] at h
    · have h := hX' a (by omega) y (by rw [ea1, mem_perpJ]; exact hy)
      rwa [dblFlag_last] at h
  · rintro ⟨h1, h2⟩
    show ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s
    intro s hs y hy
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · have e1 : dblFlag ε W (s + 1) = W ⟨s + 1, by omega⟩ := dblFlag_succ (ε := ε) (W := W) ⟨s, hs⟩
      have e2 : dblFlag ε W s = W ⟨s, by omega⟩ := dblFlag_castSucc (ε := ε) (W := W) ⟨s, hs⟩
      rw [e1] at hy
      rw [e2]
      exact h1 ⟨s, hs⟩ y hy
    · rw [ea1, mem_perpJ] at hy
      rw [dblFlag_last]
      exact h2 y hy

theorem conj_mem_lower {F : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ} (m : UJ ε)
    (hm : ∀ s, ∀ y ∈ F s, uMat m *ᵥ y ∈ F s) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lower F r) :
    uMat m * X * uMat m⁻¹ ∈ lower F r := by
  have hX' : ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s := hX
  show ∀ s, s < r → ∀ y ∈ F (s + 1), (uMat m * X * uMat m⁻¹) *ᵥ y ∈ F s
  intro s hs y hy
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hm s _ (hX' s hs _ (GlobalTheory.FlagMeas.UnipRad.inv_keeps m (F (s + 1)) (hm (s + 1)) y hy))

theorem modulus : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → ∀ μ, IsGaugeSub (flagN ε W) (dimN n j) μ → ∀ m ∈ flagM ε W, μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) • μ := by
  intro n ε a j W hj hW μ hμ m hm
  obtain ⟨⟨N, hN⟩, hNc, -⟩ := GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW
  obtain ⟨⟨M, hM⟩, -, -, -, hconj⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε a W
  have hmk : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i := fun i y hy => (hm i y hy).1
  have hkeep : ∀ s, ∀ y ∈ dblFlag ε W s, uMat m *ᵥ y ∈ dblFlag ε W s := dblFlag_keeps m hmk
  have hmi : m⁻¹ ∈ flagM ε W := by
    rw [← hM]
    exact M.inv_mem (by rw [← SetLike.mem_coe, hM]; exact hm)
  have hS : ∀ g, g ∈ N ↔ m * g * m⁻¹ ∈ N := by
    intro g
    rw [← SetLike.mem_coe, ← SetLike.mem_coe, hN]
    refine ⟨hconj m hm g, fun h => ?_⟩
    have h2 := hconj m⁻¹ hmi _ h
    have e : m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ = g := by group
    rwa [e] at h2
  have hNinv : ∀ g, g ∈ flagN ε W → g⁻¹ ∈ flagN ε W := by
    intro g hg
    rw [← hN] at hg ⊢
    exact N.inv_mem hg
  have half : ∀ g : UJ ε, g ∈ flagN ε W ↔ uMat g - 1 ∈ lower (dblFlag ε W) (a + 1) := by
    intro g
    rw [mem_lower_half]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact Iff.rfl
  have hNA : ∀ g : UJ ε, g ∈ flagN ε W ↔ uMat g - 1 ∈ lower (dblFlag ε W) (2 * a + 1) := by
    intro g
    constructor
    · intro hg
      have h1 : ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s :=
        (half g).1 hg
      have h2 : ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g⁻¹ - 1) *ᵥ y ∈ dblFlag ε W s :=
        (half g⁻¹).1 (hNinv g hg)
      show ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s
      intro s hs y hy
      by_cases hsa : s < a + 1
      · exact h1 s hsa y hy
      · have e1 : dblFlag ε W s = perpJ ε (dblFlag ε W (2 * a + 1 - s)) := by
          have h := dblFlag_dual (ε := ε) (W := W) (s := 2 * a + 1 - s) (by omega)
          rwa [show 2 * a + 1 - (2 * a + 1 - s) = s by omega] at h
        have e2 : dblFlag ε W (s + 1) = perpJ ε (dblFlag ε W (2 * a - s)) := by
          have h := dblFlag_dual (ε := ε) (W := W) (s := 2 * a - s) (by omega)
          rwa [show 2 * a + 1 - (2 * a - s) = s + 1 by omega] at h
        rw [e1, mem_perpJ]
        rw [e2, mem_perpJ] at hy
        intro x hx
        have h3 := GlobalTheory.FlagLeviGroup.form_inv g⁻¹ x y
        rw [inv_inv] at h3
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, dotProduct_sub, h3, ← sub_dotProduct,
          ← star_sub]
        have e3 : uMat g⁻¹ *ᵥ x - x = (uMat g⁻¹ - 1) *ᵥ x := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        rw [e3]
        exact hy _ (h2 (2 * a - s) (by omega) x (by rwa [show 2 * a - s + 1 = 2 * a + 1 - s by omega]))
    · intro h
      apply (half g).2
      have h' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s := h
      show ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s
      exact fun s hs => h' s (by omega)
  have hAmul : ∀ X ∈ lower (dblFlag ε W) (2 * a + 1), ∀ Y ∈ lower (dblFlag ε W) (2 * a + 1),
      X * Y ∈ lower (dblFlag ε W) (2 * a + 1) := by
    intro X hX Y hY
    have hX' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s := hX
    have hY' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), Y *ᵥ y ∈ dblFlag ε W s := hY
    show ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (X * Y) *ᵥ y ∈ dblFlag ε W s
    intro s hs y hy
    rw [← Matrix.mulVec_mulVec]
    rcases s with _ | s
    · have h0 : Y *ᵥ y ∈ dblFlag ε W 0 := hY' 0 hs y hy
      rw [dblFlag_zero hW, Submodule.mem_bot] at h0
      rw [h0, Matrix.mulVec_zero]
      exact zero_mem _
    · exact dblFlag_mono hW (Nat.le_succ s) (hX' s (by omega) _ (hY' (s + 1) hs y hy))
  obtain ⟨d, E, hEo, hEli, hEspan⟩ :=
    GlobalTheory.T.exists_orthonormal_basis_re_trace_mul_conjTranspose' n ((lower (dblFlag ε W) (2 * a + 1)).restrictScalars ℝ ⊓ lieSub ε)
  have hE : ∀ X, (X ∈ lower (dblFlag ε W) (2 * a + 1) ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E) := by
    intro X
    rw [← hEspan]
    exact Iff.rfl
  have h55 := GlobalTheory.T.finrank_and_det_of_real_basis_skew_part n ε (lower (dblFlag ε W) (2 * a + 1)) d E (fun X hX => adj_mem_lower hX) hEli hE
  have hdet1 : ‖(uMat m).det‖ = 1 :=
    ((GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε ⊥ (perpJ ε ⊥) (fun y => mem_perpJ)).2.2 m).1
  have h38 := GlobalTheory.T.flagNilradical_finrank_and_abs_det_conj n (uMat m) (uMat m⁻¹) (2 * a + 1) (dblFlag ε W) (lower (dblFlag ε W) (2 * a + 1))
    (GlobalTheory.FlagLeviGroup.uMat_mul_inv m) hdet1 (dblFlag_mono hW) (dblFlag_zero hW) (dblFlag_top hW) hkeep
    (fun X => Iff.rfl)
  have hDpos : ∀ s, 0 < detOn (uMat m) (dblFlag ε W s) := fun s =>
    (((GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W s) (perpJ ε (dblFlag ε W s)) (fun y => mem_perpJ)).2.2 m).2 (hkeep s)).2.2
  have hD0 : detOn (uMat m) (dblFlag ε W 0) = 1 := by
    rw [dblFlag_zero hW]
    have hb : ∀ y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)), Matrix.toLin' (uMat m) y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := by
      intro y hy
      rw [(Submodule.mem_bot ℂ).1 hy, map_zero]
      exact zero_mem _
    unfold detOn
    rw [dif_pos hb, LinearMap.det_eq_one_of_subsingleton, norm_one]
  have hν0 : Module.finrank ℂ (dblFlag ε W 0) = 0 := by rw [dblFlag_zero hW, finrank_bot]
  have hνs : ∀ i : Fin a, Module.finrank ℂ (dblFlag ε W (i + 1)) = Module.finrank ℂ (dblFlag ε W i) + j i := by
    intro i
    rw [dblFlag_succ, dblFlag_castSucc]
    exact hW.2.2.1 i
  have h2ν : 2 * Module.finrank ℂ (dblFlag ε W a) ≤ n := by
    have h40 := (GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W a) (perpJ ε (dblFlag ε W a)) (fun y => mem_perpJ)).1
    have hle : dblFlag ε W a ≤ perpJ ε (dblFlag ε W a) := by
      rw [dblFlag_last]
      intro x hx
      rw [mem_perpJ]
      intro x' hx'
      exact hW.2.2.2 x' hx' x hx
    have h3 := Submodule.finrank_mono hle
    omega
  have hsym : ∀ s, s ≤ a → detOn (uMat m) (dblFlag ε W (2 * a + 1 - s)) = detOn (uMat m) (dblFlag ε W s) ∧
      Module.finrank ℂ (dblFlag ε W (2 * a + 1 - s)) + Module.finrank ℂ (dblFlag ε W s) = n := by
    intro s hs
    have h40 := GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W s) (perpJ ε (dblFlag ε W s)) (fun y => mem_perpJ)
    rw [dblFlag_sub hs]
    exact ⟨((h40.2.2 m).2 (hkeep s)).2.1, h40.1⟩
  have h56 := GlobalTheory.T.doubledFlag_sum_eq_unipotentDim_and_layerProd n a j (fun s => detOn (uMat m) (dblFlag ε W s))
    (fun s => Module.finrank ℂ (dblFlag ε W s)) hj hDpos hD0 hν0 hνs h2ν hsym
  have hconjE : ∀ k, uMat m * E k * uMat m⁻¹ ∈ Submodule.span ℝ (Set.range E) := by
    intro k
    have hk := (hE (E k)).2 (Submodule.subset_span ⟨k, rfl⟩)
    exact (hE _).1 ⟨conj_mem_lower m hkeep hk.1, inG_conj m hk.2⟩
  choose z hz using fun k => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hconjE k)
  let L : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i k => z k i
  have hL : ∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i := fun k => (hz k).symm
  let φ : lower (dblFlag ε W) (2 * a + 1) →ₗ[ℂ] lower (dblFlag ε W) (2 * a + 1) :=
    { toFun := fun X => ⟨uMat m * X * uMat m⁻¹, conj_mem_lower m hkeep X.2⟩
      map_add' := fun X Y => by
        ext1
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        ext1
        simp }
  have hφ : ∀ X : lower (dblFlag ε W) (2 * a + 1),
      ((φ X : lower (dblFlag ε W) (2 * a + 1)) : Matrix (Fin n) (Fin n) ℂ) = uMat m * X * uMat m⁻¹ :=
    fun X => rfl
  have hdetφ : LinearMap.det φ = ((L.det : ℝ) : ℂ) := h55.2 φ L (fun k _ => hL k)
  have hnorm := h38.2 φ hφ
  have habs : |L.det| = ∏ s ∈ Finset.range (2 * a + 1), detOn (uMat m) (dblFlag ε W s) ^
      Module.finrank ℂ (dblFlag ε W (s + 1)) / detOn (uMat m) (dblFlag ε W (s + 1)) ^
      Module.finrank ℂ (dblFlag ε W s) := by
    rw [← hnorm, hdetφ, Complex.norm_real, Real.norm_eq_abs]
  have hP : 0 < ∏ s ∈ Finset.range (2 * a + 1), detOn (uMat m) (dblFlag ε W s) ^
      Module.finrank ℂ (dblFlag ε W (s + 1)) / detOn (uMat m) (dblFlag ε W (s + 1)) ^
      Module.finrank ℂ (dblFlag ε W s) :=
    Finset.prod_pos fun s _ => div_pos (pow_pos (hDpos s) _) (pow_pos (hDpos (s + 1)) _)
  have hLne : L.det ≠ 0 := abs_pos.1 (by rw [habs]; exact hP)
  have hd : d = dimN n j := by
    rw [← h55.1, h38.1]
    exact h56.1
  have hNA' : ∀ g, g ∈ N ↔ uMat g - 1 ∈ (lower (dblFlag ε W) (2 * a + 1)).restrictScalars ℝ := by
    intro g
    rw [← SetLike.mem_coe, hN]
    exact hNA g
  have h28 := GlobalTheory.T.map_conj_gaugeMeasure_eq_inv_det_smul n ε ((lower (dblFlag ε W) (2 * a + 1)).restrictScalars ℝ) d E N hAmul hEo hE hNA'
    (by rw [hN]; exact hNc) μ (by rw [hN, hd]; exact hμ) m L hS hL hLne
  have hloc : locSize j W (uMat m) = fun i : Fin a =>
      (detOn (uMat m) (dblFlag ε W (i + 1)) / detOn (uMat m) (dblFlag ε W i)) ^ (-(1 : ℝ) / j i) := by
    funext i
    rw [dblFlag_succ, dblFlag_castSucc]
    rfl
  have hfin : layerProd n 1 j (locSize j W (uMat m)) id = |L.det|⁻¹ := by
    rw [hloc, habs]
    exact h56.2
  rw [h28, hfin]

end GlobalTheory.FlagModulus
end
end
