import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaZeroDivisorJetBound

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice

open scoped Matrix

noncomputable def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun y w => (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm y w).im)
    (fun a b w => by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct])
    (fun c a w => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul,
        Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (y w : Fin g → ℂ) :
    imForm Hm y w = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm y w).im := rfl

theorem imForm_smul_I {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    imForm Hm z (Complex.I • z) = -(ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re := by
  simp [imForm_apply, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul,
    dotProduct_smul, Matrix.mulVec_neg, dotProduct_neg]

theorem imForm_injective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) :
    Function.Injective (imForm Hm) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra h0
  have h1 := imForm_smul_I Hm z
  rw [hz] at h1
  have := hpos z h0
  simp at h1
  linarith

theorem imForm_surjective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) :
    Function.Surjective (imForm Hm) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := Fin g → ℂ)).symm).1 (imForm_injective Hm hpos)

theorem exists_symplectic_basis : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ l l' : Λ, ∃ k : ℤ, (hermForm Hm (l : Fin g → ℂ) (l' : Fin g → ℂ)).im = k) →
    (∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hermForm Hm w (l : Fin g → ℂ)).im = k) → w ∈ Λ) →
    ∃ bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, ∀ α β,
      (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β := by
  intro g Λ Hm hdisc hspan hH hpos hint hdual
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ (fun x y => k x y)
    (fun x x' y => by
      apply Int.cast_injective (α := ℝ); push_cast; simp only [← hk, ← imForm_apply]
      simp)
    (fun c x y => by
      apply Int.cast_injective (α := ℝ); simp only [smul_eq_mul]; push_cast
      simp only [← hk, ← imForm_apply]
      simp [← Int.cast_smul_eq_zsmul ℝ c])
    (fun x y y' => by
      apply Int.cast_injective (α := ℝ); push_cast; simp only [← hk, ← imForm_apply]
      simp)
    (fun c x y => by
      apply Int.cast_injective (α := ℝ); simp only [smul_eq_mul]; push_cast
      simp only [← hk, ← imForm_apply]
      simp [← Int.cast_smul_eq_zsmul ℝ c])
  have hE : ∀ l m : Λ, (Ef l m : ℝ) = imForm Hm (l : Fin g → ℂ) (m : Fin g → ℂ) :=
    fun l m => (hk l m).symm
  have hanti : ∀ l m : Λ, Ef m l = - Ef l m := fun l m => by
    apply Int.cast_injective (α := ℝ)
    have h1 := congrArg Complex.im (GlobalTheory.SiegelNormalForm.form_conj hH (l : Fin g → ℂ) m)
    simp only [Complex.star_def, Complex.conj_im] at h1
    push_cast
    rw [hE, hE, imForm_apply, imForm_apply]
    exact h1.symm
  have halt : Ef.IsAlt := fun l => by
    have := hanti l l
    omega
  have hinj : Function.Injective Ef := by
    rw [injective_iff_map_eq_zero]
    intro l hl
    have hle : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤
        LinearMap.ker (imForm Hm (l : Fin g → ℂ)) := by
      rw [Submodule.span_le]
      intro m hm
      have := hE l ⟨m, hm⟩
      rw [hl] at this
      simpa using this.symm
    rw [hspan] at hle
    have h0 : imForm Hm (l : Fin g → ℂ) = 0 := LinearMap.ext fun y => hle (Submodule.mem_top)
    exact Subtype.ext ((injective_iff_map_eq_zero _).1 (imForm_injective Hm hpos) _ h0)
  have hsurj : Function.Surjective Ef := by
    intro φ
    let b := Module.finBasis ℤ Λ
    let bR := b.ofZLatticeBasis ℝ Λ
    let ψ : (Fin g → ℂ) →ₗ[ℝ] ℝ := bR.constr ℝ fun i => (φ (b i) : ℝ)
    have hψ : ∀ y : Λ, ψ (y : Fin g → ℂ) = (φ y : ℝ) := by
      intro y
      have hb : ∀ i, ψ (b i : Fin g → ℂ) = (φ (b i) : ℝ) := fun i => by
        have h := bR.constr_basis ℝ (fun i => (φ (b i) : ℝ)) i
        rwa [show bR i = (b i : Fin g → ℂ) by simp [bR]] at h
      conv_lhs => rw [← b.sum_repr y]
      conv_rhs => rw [← b.sum_repr y]
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, map_sum, map_zsmul, hb]
      simp
    obtain ⟨w, hw⟩ := imForm_surjective Hm hpos ψ
    have hwy : ∀ y : Λ, imForm Hm w (y : Fin g → ℂ) = (φ y : ℝ) := fun y => by rw [hw, hψ]
    have hwΛ : w ∈ Λ := hdual w fun l => ⟨φ l, hwy l⟩
    refine ⟨⟨w, hwΛ⟩, LinearMap.ext fun y => ?_⟩
    apply Int.cast_injective (α := ℝ)
    rw [hE, hwy]
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  obtain ⟨bs, hbs⟩ := GlobalTheory.exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg
    (GlobalTheory.bijective_neg_bilinForm ⟨hinj, hsurj⟩) hrank
  have hval : ∀ α β, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (bs α : Fin g → ℂ)
      (bs β : Fin g → ℂ)).im = (Ef (bs α) (bs β) : ℝ) := fun α β => (hE _ _).symm
  refine ⟨bs, ?_⟩
  have hee : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inl j)) = 0 := fun i j => by
    have := hbs.left_left i j
    simpa using this
  have hff : ∀ i j, Ef (bs (Sum.inr i)) (bs (Sum.inr j)) = 0 := fun i j => by
    have := hbs.right_right i j
    simpa using this
  have hef : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inr j)) = if i = j then -1 else 0 := fun i j => by
    have := hbs.left_right i j
    simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this
    rw [this]; split_ifs <;> simp
  rintro (i | i) (j | j)
  · rw [hval, hee]; simp [Matrix.J]
  · rw [hval, hef]
    by_cases h : i = j <;> simp [Matrix.J, h, Matrix.one_apply]
  · rw [hval, hanti, hef]
    by_cases h : i = j
    · subst h; simp [Matrix.J]
    · simp [Matrix.J, h, Ne.symm h, Matrix.one_apply]
  · rw [hval, hff]; simp [Matrix.J]

end GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_basis_principal_polarization : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ l l' : Λ, ∃ k : ℤ, (hermForm Hm (l : Fin g → ℂ) (l' : Fin g → ℂ)).im = k) →
    (∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hermForm Hm w (l : Fin g → ℂ)).im = k) → w ∈ Λ) →
    ∃ bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, ∀ α β,
      (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice.exists_symplectic_basis
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.NForm

open Matrix

private theorem hermForm_cols {g : ℕ} (N P Q : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    hermForm N (P *ᵥ Pi.single i 1) (Q *ᵥ Pi.single j 1) =
      (Pᵀ * N * Q.map (starRingEnd ℂ)) i j := by
  simp only [mulVec_single_one, hermForm]
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc, col_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem re_of_real_add {g : ℕ} (B C : Matrix (Fin g) (Fin g) ℝ) (i j : Fin g) :
    ((B.map (fun x : ℝ => (x : ℂ)) + Complex.I • C.map (fun x : ℝ => (x : ℂ))) i j).re = B i j := by
  simp

private theorem imInv_periodMatrix {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    GlobalTheory.CanTh.imInv (periodMatrix X Y) = Y⁻¹.map (fun x : ℝ => (x : ℂ)) := by
  have : (periodMatrix X Y).map Complex.im = Y := by ext i j; simp [periodMatrix]
  rw [GlobalTheory.CanTh.imInv, this]

private theorem map_ofReal_mul {g : ℕ} (B C : Matrix (Fin g) (Fin g) ℝ) :
    (B * C).map (fun x : ℝ => (x : ℂ)) =
      B.map (fun x : ℝ => (x : ℂ)) * C.map (fun x : ℝ => (x : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

theorem gram_eq_siegelGram {g : ℕ} {X Y : Matrix (Fin g) (Fin g) ℝ} (hX : X.IsSymm) (hY : Y.PosDef) :
    (Matrix.of fun α β : Fin g ⊕ Fin g =>
      (hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y))
        (Sum.elim (fun i => (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pi.single i 1)
          (fun i => periodMatrix X Y *ᵥ Pi.single i 1) α)
        (Sum.elim (fun i => (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pi.single i 1)
          (fun i => periodMatrix X Y *ᵥ Pi.single i 1) β)).re) = siegelGram X Y := by
  have hYs : Yᵀ = Y := by
    ext i j
    simpa using hY.isHermitian.apply i j
  have hXs : Xᵀ = X := hX
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit
  have hYY : Y * Y⁻¹ * Y = Y := by rw [mul_nonsing_inv _ hu, Matrix.one_mul]
  set c : Matrix (Fin g) (Fin g) ℝ → Matrix (Fin g) (Fin g) ℂ := fun B => B.map (fun x : ℝ => (x : ℂ)) with hc
  have hτ : periodMatrix X Y = c X + Complex.I • c Y := rfl
  have hτt : (periodMatrix X Y)ᵀ = c X + Complex.I • c Y := by
    rw [hτ, transpose_add, transpose_smul]
    have : ∀ B : Matrix (Fin g) (Fin g) ℝ, Bᵀ = B → (c B)ᵀ = c B := fun B hB => by
      rw [hc]; simp only; rw [← transpose_map, hB]
    rw [this X hXs, this Y hYs]
  have hτc : (periodMatrix X Y).map (starRingEnd ℂ) = c X - Complex.I • c Y := by
    ext i j; simp [periodMatrix, hc, Complex.ext_iff]
  have h1c : (1 : Matrix (Fin g) (Fin g) ℂ).map (starRingEnd ℂ) = 1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have mm : ∀ B C, c (B * C) = c B * c C := map_ofReal_mul
  ext α β
  rcases α with i | i <;> rcases β with j | j <;>
    simp only [of_apply, Sum.elim_inl, Sum.elim_inr, hermForm_cols, imInv_periodMatrix, siegelGram,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_one, h1c, hτt, hτc,
      Matrix.one_mul, Matrix.mul_one]
  · simp
  · have : (Y⁻¹.map (fun x : ℝ => (x : ℂ))) * (c X - Complex.I • c Y) =
        c (Y⁻¹ * X) + Complex.I • c (-(Y⁻¹ * Y)) := by
      have hneg : ∀ B, c (-B) = -c B := fun B => by ext i j; simp [hc]
      change c Y⁻¹ * _ = _
      rw [hneg, mm, mm, Matrix.mul_sub, Matrix.mul_smul, smul_neg, sub_eq_add_neg]
    rw [this]; exact re_of_real_add _ _ i j
  · have : (c X + Complex.I • c Y) * (Y⁻¹.map (fun x : ℝ => (x : ℂ))) =
        c (X * Y⁻¹) + Complex.I • c (Y * Y⁻¹) := by
      simp [hc, Matrix.add_mul, map_ofReal_mul]
    rw [this]; exact re_of_real_add _ _ i j
  · have : (c X + Complex.I • c Y) * (Y⁻¹.map (fun x : ℝ => (x : ℂ))) * (c X - Complex.I • c Y) =
        c (Y + X * Y⁻¹ * X) + Complex.I • c (Y * Y⁻¹ * X - X * Y⁻¹ * Y) := by
      have e1 : c (Y + X * Y⁻¹ * X) = c (Y * Y⁻¹ * Y) + c (X * Y⁻¹ * X) := by
        rw [hYY]; ext i j; simp [hc]
      have e2 : c (Y * Y⁻¹ * X - X * Y⁻¹ * Y) = c (Y * Y⁻¹ * X) - c (X * Y⁻¹ * Y) := by
        ext i j; simp [hc]
      rw [e1, e2]
      simp only [mm]
      change _ = _ + _
      have hI : ∀ N : Matrix (Fin g) (Fin g) ℂ, Complex.I • (Complex.I • N) = -N := fun N => by
        rw [smul_smul, Complex.I_mul_I]; simp
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_add, hI]
      abel
    rw [this]
    have := re_of_real_add (Y + X * Y⁻¹ * X) (Y * Y⁻¹ * X - X * Y⁻¹ * Y) i j
    simpa [hc] using this

theorem normal_form_gram : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (v : Fin g ⊕ Fin g → Fin g → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (v α) (v β)).im = Matrix.J (Fin g) ℝ α β) →
    ∃ (h : Matrix (Fin g) (Fin g) ℂ) (X Y : Matrix (Fin g) (Fin g) ℝ),
      IsUnit h.det ∧ X.IsSymm ∧ Y.PosDef ∧
      (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) ∧
      (∀ i, h.mulVec (v (Sum.inl i)) = Pi.single i 1) ∧
      (∀ i, h.mulVec (v (Sum.inr i)) = (periodMatrix X Y).mulVec (Pi.single i 1)) ∧
      (Matrix.of fun α β => (hermForm Hm (v α) (v β)).re) = siegelGram X Y := by
  intro g Hm v hH hpos hJ
  set A : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => v (Sum.inl j) i with hA
  set F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => v (Sum.inr j) i with hF
  set τ : Matrix (Fin g) (Fin g) ℂ := A⁻¹ * F with hτ
  obtain ⟨hu, hs, hp, hform⟩ := GlobalTheory.HolTheta.normal_form Hm (fun j => v (Sum.inl j)) (fun j => v (Sum.inr j)) hH hpos
    (fun j k => by simpa [Matrix.J] using hJ (Sum.inl j) (Sum.inl k))
    (fun j k => by simpa [Matrix.J] using hJ (Sum.inr j) (Sum.inr k))
    (fun j k => by simpa [Matrix.J] using hJ (Sum.inl j) (Sum.inr k)) hA hτ
  have hPer : periodMatrix (τ.map Complex.re) (τ.map Complex.im) = τ := by
    ext i j; apply Complex.ext <;> simp [periodMatrix]
  have hXs : (τ.map Complex.re).IsSymm := by
    ext i j; simpa using congrArg Complex.re (hs.apply i j)
  have he : ∀ i, A⁻¹ *ᵥ v (Sum.inl i) = (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pi.single i 1 := fun i => by
    have : v (Sum.inl i) = A *ᵥ Pi.single i 1 := by ext k; simp [hA]
    rw [this, mulVec_mulVec, nonsing_inv_mul A hu]
  have hf : ∀ i, A⁻¹ *ᵥ v (Sum.inr i) = τ *ᵥ Pi.single i 1 := fun i => by
    have : v (Sum.inr i) = F *ᵥ Pi.single i 1 := by ext k; simp [hF]
    rw [this, mulVec_mulVec]
  refine ⟨A⁻¹, τ.map Complex.re, τ.map Complex.im, Matrix.isUnit_nonsing_inv_det A hu, hXs, hp, ?_, ?_, ?_, ?_⟩
  · intro z w; rw [hPer]; exact hform z w
  · intro i; rw [he, one_mulVec]
  · intro i; rw [hPer]; exact hf i
  · rw [← gram_eq_siegelGram hXs hp]
    ext α β
    rw [hPer]
    simp only [of_apply]
    rw [hform]
    rcases α with i | i <;> rcases β with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, he, hf]

end GlobalTheory.CompanionTheory.NForm
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_period_matrix_normal_form : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (v : Fin g ⊕ Fin g → Fin g → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (v α) (v β)).im = Matrix.J (Fin g) ℝ α β) →
    ∃ (h : Matrix (Fin g) (Fin g) ℂ) (X Y : Matrix (Fin g) (Fin g) ℝ),
      IsUnit h.det ∧ X.IsSymm ∧ Y.PosDef ∧
      (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) ∧
      (∀ i, h.mulVec (v (Sum.inl i)) = Pi.single i 1) ∧
      (∀ i, h.mulVec (v (Sum.inr i)) = (periodMatrix X Y).mulVec (Pi.single i 1)) ∧
      (Matrix.of fun α β => (hermForm Hm (v α) (v β)).re) = siegelGram X Y := by
  atlas_forward_decl GlobalTheory.CompanionTheory.NForm.normal_form_gram
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.NformRed

open scoped Matrix

variable {g : ℕ}

theorem hermForm_sum_left {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (a : κ → ℤ)
    (x : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i, a i • x i) w = ∑ i, (a i : ℂ) * hermForm Hm (x i) w := by
  simp only [hermForm, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_dotProduct, zsmul_eq_mul]

theorem hermForm_sum_right {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (b : κ → ℤ)
    (y : κ → Fin g → ℂ) (z : Fin g → ℂ) :
    hermForm Hm z (∑ j, b j • y j) = ∑ j, (b j : ℂ) * hermForm Hm z (y j) := by
  have hs : star (∑ j, b j • y j) = ∑ j, b j • star (y j) := by
    simp [star_sum, star_smul]
  simp only [hermForm]
  rw [hs, Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, zsmul_eq_mul]

theorem hermForm_sum_sum {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : κ → ℤ)
    (x : κ → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • x i) (∑ j, b j • x j) =
      ∑ i, ∑ j, (a i : ℂ) * (b j : ℂ) * hermForm Hm (x i) (x j) := by
  rw [hermForm_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermForm_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem re_int_mul (m n : ℤ) (c : ℂ) :
    ((m : ℂ) * (n : ℂ) * c).re = (m : ℝ) * (n : ℝ) * c.re := by
  simp [Complex.mul_re]

theorem im_int_mul (m n : ℤ) (c : ℂ) :
    ((m : ℂ) * (n : ℂ) * c).im = (m : ℝ) * (n : ℝ) * c.im := by
  simp [Complex.mul_im]

theorem congr_apply {κ : Type*} [Fintype κ] (P : Matrix κ κ ℤ) (M : Matrix κ κ ℝ) (α δ : κ) :
    (P.map (Int.cast : ℤ → ℝ) * M * (P.map (Int.cast : ℤ → ℝ))ᵀ) α δ =
      ∑ β, ∑ ε, (P α β : ℝ) * (P δ ε : ℝ) * M β ε := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun ε _ => ?_
  ring

theorem J_map_int : (Matrix.J (Fin g) ℤ).map (Int.cast : ℤ → ℝ) = Matrix.J (Fin g) ℝ :=
  Matrix.map_J (Fin g) (Int.castRingHom ℝ)

theorem cast_symplectic {P : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hP : P ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    P.map (Int.cast : ℤ → ℝ) * Matrix.J (Fin g) ℝ * (P.map (Int.cast : ℤ → ℝ))ᵀ =
      Matrix.J (Fin g) ℝ := by
  have h := SymplecticGroup.mem_iff.1 hP
  have h2 := congrArg (fun M => M.map (Int.castRingHom ℝ)) h
  simp only [Matrix.map_mul] at h2
  have e : (Int.castRingHom ℝ : ℤ → ℝ) = (Int.cast : ℤ → ℝ) := rfl
  rw [e, J_map_int, Matrix.transpose_map] at h2
  exact h2

theorem left_inv_transpose {P : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hP : P ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    (-(Matrix.J (Fin g) ℤ * P * Matrix.J (Fin g) ℤ)) * Pᵀ = 1 := by
  have h := SymplecticGroup.mem_iff.1 hP
  have : Matrix.J (Fin g) ℤ * P * Matrix.J (Fin g) ℤ * Pᵀ =
      Matrix.J (Fin g) ℤ * (P * Matrix.J (Fin g) ℤ * Pᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.neg_mul, this, h, Matrix.J_squared, neg_neg]

noncomputable def twist {κ M : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    (b : Module.Basis κ ℤ M) (P Q : Matrix κ κ ℤ) (h : Q * Pᵀ = 1) : Module.Basis κ ℤ M :=
  b.map (b.equivFun.trans ((Matrix.toLinearEquiv' Pᵀ ⟨Q, h, mul_eq_one_comm.1 h⟩).trans
    b.equivFun.symm))

theorem twist_apply {κ M : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    (b : Module.Basis κ ℤ M) (P Q : Matrix κ κ ℤ) (h : Q * Pᵀ = 1) (α : κ) :
    twist b P Q h α = ∑ β, P α β • b β := by
  have h1 : b.equivFun (b α) = Pi.single α 1 := by
    ext j
    simp [Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  simp only [twist, Module.Basis.map_apply, LinearEquiv.trans_apply, h1,
    Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  change (Pᵀ *ᵥ Pi.single α 1) β • b β = _
  rw [Matrix.mulVec_single_one]
  rfl

theorem coe_sum_smul {n : ℕ} {κ : Type*} [Fintype κ] (Λ : Submodule ℤ (Fin n → ℂ)) (v : κ → ℤ)
    (x : κ → Λ) : ((∑ α, v α • x α : Λ) : Fin n → ℂ) = ∑ α, v α • (x α : Fin n → ℂ) := by
  simp [Submodule.coe_sum]

theorem symplectic_reduction_basis :
    ∀ (g : ℕ) [NeZero g] (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re) ∈ Matrix.symplecticGroup (Fin g) ℝ →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re).PosDef →
    ∃ (bs' : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (ρ : ℝ),
      0 < ρ ∧ ρ ^ 2 ≤ 2 * g ∧
      (∀ α β, (hermForm Hm (bs' α : Fin g → ℂ) (bs' β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) ∧
      (hermForm Hm (bs' (Sum.inl 0) : Fin g → ℂ) (bs' (Sum.inl 0) : Fin g → ℂ)).re = ρ ^ 2 ∧
      (∀ l : Λ, l ≠ 0 → ρ ^ 2 ≤ (hermForm Hm (l : Fin g → ℂ) (l : Fin g → ℂ)).re) ∧
      (Matrix.of fun i j : Fin g => (hermForm Hm (bs' (Sum.inl i) : Fin g → ℂ) (bs' (Sum.inl j) : Fin g → ℂ)).re).det ≤
        ρ ^ 2 * (2 * g) ^ (g - 1) := by
  intro g _ Λ Hm bs hHm hpos him hsymp hposdef
  set G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
    Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re with hG
  obtain ⟨ρsq, hleast, hle, P, hP, hfirst, hdet⟩ := SymplecticReduction.full g G hsymp hposdef
  have hqf : ∀ v : Fin g ⊕ Fin g → ℤ, qf G (intVec v) =
      (hermForm Hm (∑ α, v α • (bs α : Fin g → ℂ)) (∑ α, v α • (bs α : Fin g → ℂ))).re := by
    intro v
    rw [hermForm_sum_sum, Complex.re_sum]
    simp only [Complex.re_sum, re_int_mul, qf, intVec, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hG, Matrix.of_apply]
    ring
  have hne : ∀ v : Fin g ⊕ Fin g → ℤ, v ≠ 0 → ∑ α, v α • (bs α : Fin g → ℂ) ≠ 0 := by
    intro v hv h0
    apply hv
    have h1 : (∑ α, v α • bs α : Λ) = 0 := by
      apply Subtype.ext
      rw [coe_sum_smul]
      exact h0
    funext α
    exact Fintype.linearIndependent_iff.1 bs.linearIndependent v h1 α
  have hρpos : 0 < ρsq := by
    obtain ⟨v, hv, hval⟩ := hleast.1
    rw [hval, hqf]
    exact hpos _ (hne v hv)
  have hb' : ∀ α, ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ) =
      ∑ β, P α β • (bs β : Fin g → ℂ) := by
    intro α
    rw [twist_apply, coe_sum_smul]
  have hre : ∀ α δ, (hermForm Hm ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ)
      ((twist bs P _ (left_inv_transpose hP) δ : Λ) : Fin g → ℂ)).re =
      (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ) α δ := by
    intro α δ
    rw [hb', hb', hermForm_sum_sum, congr_apply]
    simp only [Complex.re_sum, re_int_mul, hG, Matrix.of_apply]
  have him' : ∀ α δ, (hermForm Hm ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ)
      ((twist bs P _ (left_inv_transpose hP) δ : Λ) : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α δ := by
    intro α δ
    rw [hb', hb', hermForm_sum_sum, ← cast_symplectic hP, congr_apply]
    simp only [Complex.im_sum, im_int_mul, him]
  refine ⟨twist bs P _ (left_inv_transpose hP), Real.sqrt ρsq, Real.sqrt_pos.2 hρpos, ?_, him', ?_,
    ?_, ?_⟩
  · rw [Real.sq_sqrt hρpos.le]
    exact hle
  · rw [Real.sq_sqrt hρpos.le, hre]
    exact hfirst
  · intro l hl
    rw [Real.sq_sqrt hρpos.le]
    have hv : (fun α => bs.repr l α) ≠ 0 := by
      intro h0
      apply hl
      have : bs.repr l = 0 := by
        ext α
        exact congrFun h0 α
      simpa using this
    have hsum : (l : Fin g → ℂ) = ∑ α, bs.repr l α • (bs α : Fin g → ℂ) := by
      rw [← coe_sum_smul, bs.sum_repr]
    rw [hsum, ← hqf (fun α => bs.repr l α)]
    exact hleast.2 ⟨_, hv, rfl⟩
  · rw [Real.sq_sqrt hρpos.le]
    have : (Matrix.of fun i j : Fin g =>
        (hermForm Hm ((twist bs P _ (left_inv_transpose hP) (Sum.inl i) : Λ) : Fin g → ℂ)
          ((twist bs P _ (left_inv_transpose hP) (Sum.inl j) : Λ) : Fin g → ℂ)).re) =
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ).toBlocks₁₁ := by
      ext i j
      simp only [Matrix.of_apply, hre, Matrix.toBlocks₁₁]
    rw [this]
    exact hdet

end GlobalTheory.CompanionTheory.Ar.NformRed
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_part_gram_in_symplectic_group : ∀ (g : ℕ) [NeZero g] (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re) ∈ Matrix.symplecticGroup (Fin g) ℝ →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re).PosDef →
    ∃ (bs' : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (ρ : ℝ),
      0 < ρ ∧ ρ ^ 2 ≤ 2 * g ∧
      (∀ α β, (hermForm Hm (bs' α : Fin g → ℂ) (bs' β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) ∧
      (hermForm Hm (bs' (Sum.inl 0) : Fin g → ℂ) (bs' (Sum.inl 0) : Fin g → ℂ)).re = ρ ^ 2 ∧
      (∀ l : Λ, l ≠ 0 → ρ ^ 2 ≤ (hermForm Hm (l : Fin g → ℂ) (l : Fin g → ℂ)).re) ∧
      (Matrix.of fun i j : Fin g => (hermForm Hm (bs' (Sum.inl i) : Fin g → ℂ) (bs' (Sum.inl j) : Fin g → ℂ)).re).det ≤
        ρ ^ 2 * (2 * g) ^ (g - 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.NformRed.symplectic_reduction_basis
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Nform

theorem exists_half_canMult : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (χ : Λ → ℂ),
    (∀ l l' : Λ, χ (l + l') = χ l * χ l' * Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) - bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ))) →
    (∀ l, χ l ^ 2 = 1) →
    ∃ a c : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, c i = 0 ∨ c i = 1 / 2) ∧
      ∀ x, χ x = GlobalTheory.CanTh.canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  intro g Λ bs χ hχ hsq
  classical
  have hpm : ∀ l, χ l = 1 ∨ χ l = -1 := fun l =>
    mul_self_eq_one_iff.mp (by rw [← sq]; exact hsq l)
  have hexp : ∀ k : ℤ, Complex.exp (↑Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (-1) ^ k := by
    intro k
    rw [Complex.ofReal_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hhalf : Complex.exp (2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = ↑Real.pi * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
  have hhalf' : Complex.exp (-(2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [Complex.exp_neg, hhalf]
    norm_num
  have hsame : ∀ j k : Fin g ⊕ Fin g, bs.repr (bs j) k = if j = k then 1 else 0 := by
    intro j k
    rw [Module.Basis.repr_self, Finsupp.single_apply]
  have hsingle : ∀ i : Fin g, (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k)) = Pi.single i 1 ∧
      (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) = Pi.single i 1 := by
    intro i
    refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
      by_cases hk : k = i
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
  have hdot : ∀ (a : Fin g → ℝ) (i : Fin g),
      (a ⬝ᵥ fun k => (((Pi.single i 1 : Fin g → ℤ) k : ℤ) : ℝ)) = a i := by
    intro a i
    simp [dotProduct, Pi.single_apply]
  have hdot0 : ∀ a : Fin g → ℝ, (a ⬝ᵥ fun k => (((0 : Fin g → ℤ) k : ℤ) : ℝ)) = 0 := by
    intro a
    simp [dotProduct]
  have hC_inl : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) =
        Complex.exp (2 * ↑Real.pi * Complex.I * ((a i : ℝ) : ℂ)) := by
    intro a c i
    obtain ⟨h1, h2, -, -⟩ := hsingle i
    rw [h1, h2]
    simp only [GlobalTheory.CanTh.canMult, dotProduct_zero, hdot, hdot0]
    congr 1
    push_cast
    ring
  have hC_inr : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) =
        Complex.exp (-(2 * ↑Real.pi * Complex.I * ((c i : ℝ) : ℂ))) := by
    intro a c i
    obtain ⟨-, -, h3, h4⟩ := hsingle i
    rw [h3, h4]
    simp only [GlobalTheory.CanTh.canMult, zero_dotProduct, hdot, hdot0]
    congr 1
    push_cast
    ring
  obtain ⟨a, ha⟩ : ∃ a : Fin g → ℝ, a = fun i => if χ (bs (Sum.inl i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin g → ℝ, c = fun i => if χ (bs (Sum.inr i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  refine ⟨a, c, fun i => ?_, fun i => ?_, ?_⟩
  · simp only [ha]
    split_ifs <;> norm_num
  · simp only [hc]
    split_ifs <;> norm_num
  have hχ0 : ∀ l, χ l ≠ 0 := by
    intro l h
    have h' := hsq l
    rw [h] at h'
    norm_num at h'
  have hψ0 : ∀ l : Λ, GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)) ≠ 0 := by
    intro l
    simp only [GlobalTheory.CanTh.canMult]
    exact Complex.exp_ne_zero _
  have hψ : ∀ l l' : Λ,
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (l + l') (Sum.inl i))
                   (fun i => bs.repr (l + l') (Sum.inr i)) =
        GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
                     (fun i => bs.repr l (Sum.inr i)) *
          GlobalTheory.CanTh.canMult a c (fun i => bs.repr l' (Sum.inl i))
            (fun i => bs.repr l' (Sum.inr i)) *
          Complex.exp (Real.pi * Complex.I *
            (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
              bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)) := by
    intro l l'
    have hm : (fun i => bs.repr (l + l') (Sum.inl i)) =
        (fun i => bs.repr l (Sum.inl i)) + (fun i => bs.repr l' (Sum.inl i)) := by
      funext i
      simp [map_add]
    have hn : (fun i => bs.repr (l + l') (Sum.inr i)) =
        (fun i => bs.repr l (Sum.inr i)) + (fun i => bs.repr l' (Sum.inr i)) := by
      funext i
      simp [map_add]
    rw [hm, hn, GlobalTheory.HolTheta.canMult_add, hexp, Finset.sum_sub_distrib]
    rfl
  have hbasis : ∀ j : Fin g ⊕ Fin g, χ (bs j) =
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (bs j) (Sum.inl i))
        (fun i => bs.repr (bs j) (Sum.inr i)) := by
    rintro (i | i)
    · rw [hC_inl]
      rcases hpm (bs (Sum.inl i)) with h | h
      · simp [ha, h]
      · have h' : χ (bs (Sum.inl i)) ≠ 1 := by rw [h]; norm_num
        simp only [ha, h', if_false]
        rw [h, hhalf]
    · rw [hC_inr]
      rcases hpm (bs (Sum.inr i)) with h | h
      · simp [hc, h]
      · have h' : χ (bs (Sum.inr i)) ≠ 1 := by rw [h]; norm_num
        simp only [hc, h', if_false]
        rw [h, hhalf']
  exact GlobalTheory.HolTheta.eq_of_cocycle bs
    (fun l l' => Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
        bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)))
    (ψ := fun l => GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)))
    (fun _ _ => Complex.exp_ne_zero _) hχ0 hψ0 hχ hψ hbasis

end GlobalTheory.CompanionTheory.Ar.Nform
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semicharacter_theta_characteristic : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (χ : Λ → ℂ),
    (∀ l l' : Λ, χ (l + l') = χ l * χ l' * Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) - bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ))) →
    (∀ l, χ l ^ 2 = 1) →
    ∃ a c : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, c i = 0 ∨ c i = 1 / 2) ∧
      ∀ x, χ x = GlobalTheory.CanTh.canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Nform.exists_half_canMult
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.CanThLine

section Law

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem gaussian_mul_factor {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (a c : Fin g → ℝ) (m n : Fin g → ℤ) {l : Fin g → ℂ}
    (hl : l = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) (ζ : Fin g → ℂ) :
    cexp (-(π / 2 * ((ζ + l) ⬝ᵥ imInv τ *ᵥ (ζ + l)))) *
        (canMult a c m n *
          cexp (π * hermForm (imInv τ) ζ l + π / 2 * hermForm (imInv τ) l l)) =
      eC (((1 : ℕ) : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec c ⬝ᵥ ofIntVec n)) *
        eC (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ ζ)) *
        cexp (-(π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))) := by
  have hl' : l = (fun i => (((m i : ℝ)) : ℂ)) + τ *ᵥ fun i => (((n i : ℝ)) : ℂ) := by
    simpa using hl
  have h1 := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) ζ
  have h2 := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) l
  rw [← hl'] at h1 h2
  have h3 := dot_mulVec_symm (isSymm_imInv hs) ζ l
  have e0 : (fun i => (((n i : ℝ)) : ℂ)) = ofIntVec n := by
    funext i; simp [ofIntVec]
  have h5 : (l ⬝ᵥ ofIntVec n) = ((m ⬝ᵥ n : ℤ) : ℂ) + ofIntVec n ⬝ᵥ τ *ᵥ ofIntVec n := by
    rw [hl, add_dotProduct, dotProduct_comm (τ *ᵥ _)]
    congr 1
    simp [dotProduct, ofIntVec]
  have e1 : ((a ⬝ᵥ (fun i => (m i : ℝ)) : ℝ) : ℂ) = ofRealVec a ⬝ᵥ ofIntVec m := by
    simp [dotProduct, ofRealVec, ofIntVec]
  have e2 : ((c ⬝ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) = ofRealVec c ⬝ᵥ ofIntVec n := by
    simp [dotProduct, ofRealVec, ofIntVec]
  rw [e0] at h1 h2
  rw [canMult, e1, e2]
  simp only [eC, ← Complex.exp_add]
  congr 1
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, h3, h1, h2, h5,
    dotProduct_comm (ofIntVec n) ζ]
  push_cast
  ring

end Law

section Main

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem gaussian_mul_mem_thetaLevelChar {τ h Hm : Matrix (Fin g) (Fin g) ℂ} {a c : Fin g → ℝ}
    {θ : (Fin g → ℂ) → ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det)
    (hH : ∀ z w, hermForm Hm z w = hermForm (imInv τ) (h *ᵥ z) (h *ᵥ w))
    (hθ : Differentiable ℂ θ)
    (hlaw : ∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ),
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = canMult a c m n *
        cexp (π * hermForm Hm z lam + π / 2 * hermForm Hm lam lam) * θ z) :
    (fun ζ => cexp (-(π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))) * θ (h⁻¹ *ᵥ ζ)) ∈
      GlobalTheory.thetaLevelChar a c 1 τ := by
  have hhi : h * h⁻¹ = 1 := mul_nonsing_inv _ hh
  have hback : ∀ v : Fin g → ℂ, h *ᵥ (h⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hhi, one_mulVec]
  have hd : Differentiable ℂ (fun ζ : Fin g → ℂ => h⁻¹ *ᵥ ζ) :=
    differentiable_pi.2 fun i => by
      simp only [mulVec, dotProduct]
      fun_prop
  refine GlobalTheory.mem_thetaLevelChar.2 ⟨?_, fun n n' z => ?_⟩
  · refine Differentiable.mul ?_ (hθ.comp hd)
    simp only [dotProduct, mulVec]
    fun_prop
  · set l : Fin g → ℂ := (fun i => (n' i : ℂ)) + τ *ᵥ fun i => (n i : ℂ) with hl
    have e : z + τ *ᵥ ofIntVec n + ofIntVec n' = z + l := by
      rw [hl, add_assoc, add_comm (τ *ᵥ _)]
      rfl
    have hL := hlaw n' n (h⁻¹ *ᵥ l) (hback l) (h⁻¹ *ᵥ z)
    rw [hH, hH, hback, hback] at hL
    have hG := gaussian_mul_factor hs hp a c n' n hl z
    simp only [e]
    rw [show h⁻¹ *ᵥ (z + l) = h⁻¹ *ᵥ z + h⁻¹ *ᵥ l from mulVec_add _ _ _, hL]
    linear_combination θ (h⁻¹ *ᵥ z) * hG

theorem eq_const_mul_canTh {τ h Hm : Matrix (Fin g) (Fin g) ℂ} {a c : Fin g → ℝ}
    {θ : (Fin g → ℂ) → ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det)
    (hH : ∀ z w, hermForm Hm z w = hermForm (imInv τ) (h *ᵥ z) (h *ᵥ w))
    (hθ : Differentiable ℂ θ)
    (hlaw : ∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ),
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = canMult a c m n *
        cexp (π * hermForm Hm z lam + π / 2 * hermForm Hm lam lam) * θ z) :
    ∃ κ : ℂ, ∀ z, θ z = κ * canTh τ a c (h *ᵥ z) := by
  have hmem := gaussian_mul_mem_thetaLevelChar hs hp hh hH hθ hlaw
  rw [GlobalTheory.thetaLevelChar_one (a := a) (b := c) (τ := τ) ⟨hs, hp⟩, Submodule.mem_span_singleton] at hmem
  obtain ⟨κ, hκ⟩ := hmem
  refine ⟨κ, fun z => ?_⟩
  have hback : h⁻¹ *ᵥ (h *ᵥ z) = z := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec]
  have hz := congrFun hκ (h *ᵥ z)
  simp only [Pi.smul_apply, smul_eq_mul] at hz
  rw [hback] at hz
  rw [canTh, thetaChar_eq_theta, mul_left_comm, hz, ← _root_.mul_assoc, ← Complex.exp_add]
  simp

end Main

theorem level_one_line : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (θ : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    Differentiable ℂ θ →
    (∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ), h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = GlobalTheory.CanTh.canMult a c m n *
        Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) * θ z) →
    ∃ κ : ℂ, ∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z) := by
  intro g τ h Hm a c θ hs hp hh hH hθ hlaw
  exact eq_const_mul_canTh hs hp hh hH hθ hlaw

end GlobalTheory.CompanionTheory.CanThLine
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_canonical_multiplier : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (θ : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    Differentiable ℂ θ →
    (∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ), h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = GlobalTheory.CanTh.canMult a c m n *
        Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) * θ z) →
    ∃ κ : ℂ, ∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CanThLine.level_one_line
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

open Complex Matrix

namespace GlobalTheory.CompanionTheory.Metric

theorem mean_sq_fixes_norm_const :
    ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (Λ : Submodule ℤ (Fin g → ℂ))
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ) (b : ℝ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, c i = 0 ∨ c i = 1 / 2) →
    (∀ lam, lam ∈ Λ ↔ ∃ m n : Fin g → ℤ, h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z)) →
    (∀ l ∈ Λ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z, θ (z + l) = ε *
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z) →
    0 < b →
    (∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
      b ^ 2 = (∫ w in Fd, (‖θ w‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm w w).re)) ^ 2) / (volume Fd).toReal) →
    b ^ 2 = ‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  intro g τ h Hm a c Λ θ κ b hs hp hh ha hc hΛ hH hθ hper hb hmean
  have h₁ : ∀ i, (fun i => (a i : ℂ)) i = 0 ∨ (fun i => (a i : ℂ)) i = 1 / 2 := fun i => by
    rcases ha i with e | e <;> simp [e]
  have h₂ : ∀ i, (fun i => (c i : ℂ)) i = 0 ∨ (fun i => (c i : ℂ)) i = 1 / 2 := fun i => by
    rcases hc i with e | e <;> simp [e]
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  obtain ⟨Fd, hFd, -⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g τ h
    (fun i => (a i : ℂ)) (fun i => (c i : ℂ)) Λ.toAddSubgroup hs hp hh h₁ h₂ hΛ
  have hFdΛ : IsAddFundamentalDomain Λ Fd volume := hFd
  have hb2 := hmean Fd hFdΛ
  have hsq := GlobalTheory.Dict.VacNorm.norm_sq_of_mean (τ := τ) (h := h) (A := Λ.toAddSubgroup)
    (H := hermForm Hm) (θ := fun z => θ z / b) (a := κ / b) ⟨hs, hp⟩ hh h₁ h₂ hΛ
    (fun z w => by
      rw [hH]
      rfl)
    (fun z => by
      simp only [hθ, GlobalTheory.CanTh.canTh, GlobalTheory.CanTh.imInv]
      ring)
    (fun p hp' => by
      obtain ⟨ε, hε, hz⟩ := hper p hp'
      have hε0 : ε ≠ 0 := by
        intro e
        simp [e] at hε
      refine ⟨ε⁻¹, by simp [hε], fun z => ?_⟩
      have e2 : hermForm Hm (z + (1 / 2 : ℂ) • p) p = hermForm Hm z p + 1 / 2 * hermForm Hm p p := by
        simp only [hermForm, add_dotProduct, smul_dotProduct, smul_eq_mul]
      simp only [hz, e2]
      have e3 : Complex.exp (-(((1 : ℕ) : ℂ) * Real.pi * (hermForm Hm z p + 1 / 2 * hermForm Hm p p))) *
          Complex.exp (Real.pi * hermForm Hm z p + Real.pi / 2 * hermForm Hm p p) = 1 := by
        rw [← Complex.exp_add]
        simp only [Nat.cast_one]
        ring_nf
        simp
      have e1 : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε0
      linear_combination (θ z / b * Complex.exp (-(((1 : ℕ) : ℂ) * Real.pi * (hermForm Hm z p + 1 / 2 * hermForm Hm p p))) *
        Complex.exp (Real.pi * hermForm Hm z p + Real.pi / 2 * hermForm Hm p p)) * e1 + (θ z / b) * e3)
    hFd
    (by
      have hint : ∀ z, ‖θ z / (b : ℂ)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) = (b ^ 2)⁻¹ *
          (‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re)) ^ 2 := by
        intro z
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, mul_pow, div_pow,
          ← Real.exp_nat_mul]
        have : ((2 : ℕ) : ℝ) * (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) =
            -Real.pi * (hermForm Hm z z).re := by
          push_cast
          ring
        rw [this]
        ring
      simp only [hint]
      rw [MeasureTheory.integral_const_mul, mul_div_assoc, ← hb2]
      exact inv_mul_cancel₀ (pow_ne_zero _ hb.ne'))
  have hD : 0 < Real.sqrt (2 ^ g * (τ.map Complex.im).det) :=
    Real.sqrt_pos.2 (mul_pos (by positivity) hp.det_pos)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, div_pow,
    div_eq_iff (pow_ne_zero _ hb.ne')] at hsq
  rw [hsq]
  field_simp

end GlobalTheory.CompanionTheory.Metric
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_canonical_form : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (Λ : Submodule ℤ (Fin g → ℂ))
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ) (b : ℝ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, c i = 0 ∨ c i = 1 / 2) →
    (∀ lam, lam ∈ Λ ↔ ∃ m n : Fin g → ℤ, h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z)) →
    (∀ l ∈ Λ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z, θ (z + l) = ε *
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z) →
    0 < b →
    (∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
      b ^ 2 = (∫ w in Fd, (‖θ w‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm w w).re)) ^ 2) / (volume Fd).toReal) →
    b ^ 2 = ‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Metric.mean_sq_fixes_norm_const
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Nform

theorem re_dot_sub_re_hermForm {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (ζ : Fin g → ℂ) :
    (ζ ⬝ᵥ (B.map fun x : ℝ => (x : ℂ)).mulVec ζ).re - (hermForm (B.map fun x : ℝ => (x : ℂ)) ζ ζ).re =
      -2 * ((fun i => (ζ i).im) ⬝ᵥ B.mulVec fun i => (ζ i).im) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum,
    Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem periodMatrix_map_im {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    (GroundTheory.Heights₂.Heights.periodMatrix X Y).map Complex.im = Y := by
  ext i j
  simp [GroundTheory.Heights₂.Heights.periodMatrix]

theorem im_period_point {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (u₁ u₂ : Fin g → ℝ) :
    (fun i => (((GroundTheory.Heights₂.Heights.periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) +
      (fun i => (u₂ i : ℂ))) i).im) = Y.mulVec u₁ := by
  funext i
  simp [GroundTheory.Heights₂.Heights.periodMatrix, Matrix.mulVec, dotProduct, Complex.im_sum]

theorem thetaChar_eq {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (ζ : Fin g → ℂ) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (GroundTheory.Heights₂.Heights.periodMatrix X Y)
        (fun i => (a i : ℂ)) (fun i => (c i : ℂ)) ζ =
      GroundTheory.Heights₂.Heights.thetaChar X Y a c ζ := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar GroundTheory.Heights₂.Heights.thetaChar
  refine tsum_congr fun k => ?_
  have e : ((fun i => (k i : ℂ)) + fun i => (a i : ℂ)) =
      fun i => ((intVec k i + a i : ℝ) : ℂ) := by
    funext i
    simp [intVec]
  rw [e]

theorem norm_mul_canTh : ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (h Hm : Matrix (Fin g) (Fin g) ℂ)
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ),
    X.IsSymm → Y.PosDef →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh (periodMatrix X Y) a c (h.mulVec z)) →
    ∀ (u₁ u₂ : Fin g → ℝ) (z : Fin g → ℂ),
      h.mulVec z = (periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) + (fun i => (u₂ i : ℂ)) →
      ‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) = ‖κ‖ * thetaNorm X Y a c u₁ u₂ := by
  intro g X Y a c h Hm θ κ _ hY hH hθ u₁ u₂ z hz
  have him := periodMatrix_map_im X Y
  have hinv : GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y) =
      Y⁻¹.map fun x : ℝ => (x : ℂ) := by
    rw [GlobalTheory.CanTh.imInv, him]
  have hq : (fun i => ((h.mulVec z) i).im) = Y.mulVec u₁ := by
    rw [hz]
    exact im_period_point X Y u₁ u₂
  have hdiff := re_dot_sub_re_hermForm Y⁻¹ (h.mulVec z)
  have hcancel : Y⁻¹.mulVec (Y.mulVec u₁) = u₁ := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hY.det_pos.ne'.isUnit, Matrix.one_mulVec]
  rw [hq, hcancel, dotProduct_comm (Y.mulVec u₁) u₁, ← hinv] at hdiff
  have hqf : u₁ ⬝ᵥ Y.mulVec u₁ = qf Y u₁ := rfl
  rw [hqf] at hdiff
  rw [hθ z, hH z z, norm_mul, GlobalTheory.CanTh.canTh, norm_mul, Complex.norm_exp, thetaChar_eq, thetaNorm,
    ← hz]
  have hre : ((Real.pi / 2 : ℂ) * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z))).re =
      Real.pi / 2 * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re := by
    have : ((Real.pi / 2 : ℂ)) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.re_ofReal_mul]
  rw [hre]
  have hexp : Real.exp (Real.pi / 2 * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re) *
      Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) *
        (hermForm (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y))
          (h.mulVec z) (h.mulVec z)).re) = Real.exp (-Real.pi * qf Y u₁) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    linear_combination (Real.pi / 2) * hdiff
  calc _ = ‖κ‖ * (‖GroundTheory.Heights₂.Heights.thetaChar X Y a c (h.mulVec z)‖ *
        (Real.exp (Real.pi / 2 * (h.mulVec z ⬝ᵥ
          (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re) *
        Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) *
          (hermForm (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y))
            (h.mulVec z) (h.mulVec z)).re))) := by ring
    _ = _ := by rw [hexp]

end GlobalTheory.CompanionTheory.Ar.Nform
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_norm_in_period_coordinates : ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (h Hm : Matrix (Fin g) (Fin g) ℂ)
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ),
    X.IsSymm → Y.PosDef →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh (periodMatrix X Y) a c (h.mulVec z)) →
    ∀ (u₁ u₂ : Fin g → ℝ) (z : Fin g → ℂ),
      h.mulVec z = (periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) + (fun i => (u₂ i : ℂ)) →
      ‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) = ‖κ‖ * thetaNorm X Y a c u₁ u₂ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Nform.norm_mul_canTh
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.NForm

open Matrix in
theorem periodMatrix_im {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) : (periodMatrix X Y).map Complex.im = Y := by
  ext i j; simp [periodMatrix]

open Matrix in
theorem periodMatrix_isSymm {g : ℕ} {X Y : Matrix (Fin g) (Fin g) ℝ} (hX : X.IsSymm) (hY : Y.IsSymm) :
    (periodMatrix X Y).IsSymm := by
  ext i j
  have h1 := congrFun (congrFun hX i) j
  have h2 := congrFun (congrFun hY i) j
  simp only [Matrix.transpose_apply] at h1 h2
  simp [periodMatrix, h1, h2]

theorem hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (x y w : Fin g → ℂ) :
    hermForm Hm (x + y) w = hermForm Hm x w + hermForm Hm y w := by
  simp [hermForm, add_dotProduct]

theorem hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w x y : Fin g → ℂ) :
    hermForm Hm w (x + y) = hermForm Hm w x + hermForm Hm w y := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_zsmul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℤ) (x w : Fin g → ℂ) :
    hermForm Hm (k • x) w = k * hermForm Hm x w := by
  rw [← Int.cast_smul_eq_zsmul ℂ k x]
  simp [hermForm, smul_dotProduct]

theorem hermForm_zsmul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℤ) (w x : Fin g → ℂ) :
    hermForm Hm w (k • x) = k * hermForm Hm w x := by
  rw [← Int.cast_smul_eq_zsmul ℂ k x]
  have h : star ((k : ℂ) • x) = (k : ℂ) • star x := by
    ext i; simp
  simp [hermForm, h, Matrix.mulVec_smul, dotProduct_smul]

theorem hermForm_sum_left {g : ℕ} {J : Type} (Hm : Matrix (Fin g) (Fin g) ℂ) (s : Finset J)
    (f : J → Fin g → ℂ) (w : Fin g → ℂ) : hermForm Hm (∑ α ∈ s, f α) w = ∑ α ∈ s, hermForm Hm (f α) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermForm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermForm_add_left, ih]

theorem hermForm_sum_right {g : ℕ} {J : Type} (Hm : Matrix (Fin g) (Fin g) ℂ) (s : Finset J)
    (f : J → Fin g → ℂ) (w : Fin g → ℂ) : hermForm Hm w (∑ α ∈ s, f α) = ∑ α ∈ s, hermForm Hm w (f α) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermForm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermForm_add_right, ih]

theorem hermForm_sum {g : ℕ} {J : Type} [Fintype J] (Hm : Matrix (Fin g) (Fin g) ℂ) (v : J → Fin g → ℂ)
    (m n : J → ℤ) :
    hermForm Hm (∑ α, m α • v α) (∑ β, n β • v β) =
      ∑ α, ∑ β, ((m α * n β : ℤ) : ℂ) * hermForm Hm (v α) (v β) := by
  rw [hermForm_sum_left]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hermForm_sum_right]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [hermForm_zsmul_left, hermForm_zsmul_right]
  push_cast
  ring

theorem mulVec_zsum {g : ℕ} {J : Type} [Fintype J] (h : Matrix (Fin g) (Fin g) ℂ) (v : J → Fin g → ℂ)
    (m : J → ℤ) : h.mulVec (∑ α, m α • v α) = ∑ α, m α • h.mulVec (v α) := by
  calc h.mulVec (∑ α, m α • v α) = Matrix.mulVecLin h (∑ α, m α • v α) := rfl
    _ = ∑ α, Matrix.mulVecLin h (m α • v α) := map_sum _ _ _
    _ = ∑ α, m α • h.mulVec (v α) := Finset.sum_congr rfl fun α _ => by rw [map_zsmul]; rfl

theorem zsum_single {g : ℕ} (m : Fin g → ℤ) :
    (∑ i, m i • (Pi.single i 1 : Fin g → ℂ)) = fun i => (m i : ℂ) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem exists_reduced (g : ℕ) [NeZero g] (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hd : DiscreteTopology Λ) (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hint : ∀ l l' : Λ, ∃ k : ℤ, (hermForm Hm (l : Fin g → ℂ) (l' : Fin g → ℂ)).im = k)
    (hdual : ∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hermForm Hm w (l : Fin g → ℂ)).im = k) → w ∈ Λ) :
    ∃ (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (h : Matrix (Fin g) (Fin g) ℂ)
      (X Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ),
      IsUnit h.det ∧ X.IsSymm ∧ Y.PosDef ∧ IsReducedImaginaryPart Y ρ ∧
      (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) ∧
      (∀ x : Λ, h.mulVec (x : Fin g → ℂ) = (fun i => ((bs.repr x (Sum.inl i) : ℤ) : ℂ)) +
        (periodMatrix X Y).mulVec fun i => ((bs.repr x (Sum.inr i) : ℤ) : ℂ)) ∧
      (∀ x y : Λ, (hermForm Hm (x : Fin g → ℂ) (y : Fin g → ℂ)).im =
        ((∑ i, (bs.repr x (Sum.inr i) * bs.repr y (Sum.inl i) -
          bs.repr x (Sum.inl i) * bs.repr y (Sum.inr i)) : ℤ) : ℝ)) := by
  obtain ⟨bs0, hJ0⟩ := GlobalTheory.T.exists_symplectic_basis_principal_polarization g Λ Hm hd hs hH hpos hint hdual
  obtain ⟨h0, X0, Y0, -, hX0, hY0, -, -, -, hG0⟩ := GlobalTheory.T.hermitian_form_period_matrix_normal_form g Hm (fun α => (bs0 α : Fin g → ℂ)) hH hpos hJ0
  have hS := (SiegelCoordinates.intersectionNumber_baseChange g).1 X0 Y0 hX0 hY0
  obtain ⟨bs, ρ, hρ, hρ2, hJ, hfirst, hmin, hdet⟩ :=
    GlobalTheory.T.real_part_gram_in_symplectic_group g Λ Hm bs0 hH hpos hJ0 (by rw [hG0]; exact hS.1) (by rw [hG0]; exact hS.2)
  obtain ⟨h, X, Y, hh, hX, hY, hHh, hin, hinr, -⟩ := GlobalTheory.T.hermitian_form_period_matrix_normal_form g Hm (fun α => (bs α : Fin g → ℂ)) hH hpos hJ
  have hτim : (periodMatrix X Y).map Complex.im = Y := periodMatrix_im X Y
  have hexp : ∀ x : Λ, (x : Fin g → ℂ) = ∑ α, (bs.repr x α) • (bs α : Fin g → ℂ) := fun x => by
    have := congrArg Subtype.val (bs.sum_repr x)
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at this
    exact this.symm
  have hYe : ∀ i j, Y⁻¹ i j = (hermForm Hm (bs (Sum.inl i) : Fin g → ℂ) (bs (Sum.inl j) : Fin g → ℂ)).re := by
    intro i j
    rw [hHh, hin, hin, hermForm, GlobalTheory.SiegelNormalForm.form_single, GlobalTheory.CanTh.imInv, hτim]
    simp
  have hred : IsReducedImaginaryPart Y ρ := by
    refine ⟨hρ, hρ2, by rw [hYe]; exact hfirst, fun l hl => ?_, ?_⟩
    · let x : Λ := ∑ i, l i • bs (Sum.inl i)
      have hxc : (x : Fin g → ℂ) = ∑ i, l i • (bs (Sum.inl i) : Fin g → ℂ) := by simp [x]
      have hhx : h.mulVec (x : Fin g → ℂ) = fun i => (l i : ℂ) := by
        rw [hxc, mulVec_zsum]
        simp only [hin]
        exact zsum_single l
      have hx0 : x ≠ 0 := by
        intro e
        rw [e] at hhx
        apply hl
        funext i
        have := congrFun hhx i
        simpa using this.symm
      have := hmin x hx0
      rw [hHh, hhx, hermForm, GlobalTheory.CanTh.imInv, hτim] at this
      convert this using 1
      have hst : star (fun i => (l i : ℂ)) = fun i : Fin g => (l i : ℂ) := by
        ext i; simp
      rw [hst]
      simp only [qf, intVec, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp
    · have : Y⁻¹ = Matrix.of fun i j : Fin g => (hermForm Hm (bs (Sum.inl i) : Fin g → ℂ) (bs (Sum.inl j) : Fin g → ℂ)).re := by
        ext i j; simp [hYe]
      rw [this]
      simpa using hdet
  refine ⟨bs, h, X, Y, ρ, hh, hX, hY, hred, hHh, fun x => ?_, fun x y => ?_⟩
  · rw [hexp x, mulVec_zsum, Fintype.sum_sum_type]
    simp only [hin, hinr]
    rw [zsum_single (fun i => bs.repr x (Sum.inl i))]
    congr 1
    have e : (fun i => ((bs.repr x (Sum.inr i) : ℤ) : ℂ)) = ∑ i, bs.repr x (Sum.inr i) • (Pi.single i 1 : Fin g → ℂ) :=
      (zsum_single (fun i => bs.repr x (Sum.inr i))).symm
    rw [e, mulVec_zsum]
  · rw [hexp x, hexp y, hermForm_sum, Complex.im_sum]
    simp only [Complex.im_sum]
    have hc : ∀ (k : ℤ) (c : ℂ), ((k : ℂ) * c).im = (k : ℝ) * c.im := fun k c => by simp
    simp only [hc, hJ, Fintype.sum_sum_type, Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply]
    simp only [mul_zero, Finset.sum_const_zero, zero_add, add_zero, mul_neg, mul_ite, _root_.mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_neg_distrib]
    push_cast
    rw [Finset.sum_sub_distrib]
    ring

theorem nform : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), 1 ≤ g → (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → (∀ l : a.u.Λ, a.χ l ^ 2 = 1) → ∀ (θ : (Fin g → ℂ) → ℂ) (b : ℝ), a.IsTheta 1 θ → a.IsThetaMeanSquareNorm θ b → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ √(2 * g) ∧ (∀ w, a.nrm 1 θ w ≤ b * Real.exp (g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g))) ∧ ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ), (∀ i, (m : ℂ) • r i ∈ a.u.Λ ∧ θ (r i) ≠ 0) → (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ a.u.Λ → θ w ≠ 0 → ∃! i, w - r i ∈ a.u.Λ) → Nonempty Ix ∧ (Fintype.card Ix : ℝ) * (Real.pi / 96 * (ρ ^ 2)⁻¹ - (g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g))) ≤ ∑ i, -Real.log (a.nrm 1 θ (r i) / b) := by
  obtain ⟨C, hC, hB⟩ := ThetaBound.full
  refine ⟨C, hC.le, ?_⟩
  intro S G _ _ P z g a hg hint hdual hsc hsq θ b hθ hL2
  haveI : NeZero g := ⟨by omega⟩
  obtain ⟨hH, hpos, hχn, -⟩ := a.ah
  obtain ⟨bs, h, X, Y, ρ, hh, hX, hY, hR, hHh, hcoord, him⟩ :=
    exists_reduced g a.u.Λ a.Hm a.u.discrete a.u.full hH hpos hint hdual
  have hτim : (periodMatrix X Y).map Complex.im = Y := periodMatrix_im X Y
  have hYs : Y.IsSymm := by
    have := hY.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hτs : (periodMatrix X Y).IsSymm := periodMatrix_isSymm hX hYs
  have hτp : ((periodMatrix X Y).map Complex.im).PosDef := by rw [hτim]; exact hY
  have hhu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hh
  have hhi : Function.Injective h.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hhu
  have hxy : ∀ m n : Fin g → ℤ, ∃ x : a.u.Λ,
      h.mulVec (x : Fin g → ℂ) = (fun i => (m i : ℂ)) + (periodMatrix X Y).mulVec (fun i => (n i : ℂ)) ∧
      (∀ i, bs.repr x (Sum.inl i) = m i) ∧ (∀ i, bs.repr x (Sum.inr i) = n i) := by
    intro m n
    have hr : ∀ α, bs.repr (bs.equivFun.symm (Sum.elim m n)) α = Sum.elim m n α := fun α => by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    refine ⟨bs.equivFun.symm (Sum.elim m n), ?_, fun i => hr _, fun i => hr _⟩
    rw [hcoord]
    simp only [hr, Sum.elim_inl, Sum.elim_inr]
  have hmem : ∀ lam, lam ∈ a.u.Λ ↔ ∃ m n : Fin g → ℤ,
      h.mulVec lam = (fun i => (m i : ℂ)) + (periodMatrix X Y).mulVec (fun i => (n i : ℂ)) := by
    intro lam
    constructor
    · intro hl
      exact ⟨_, _, hcoord ⟨lam, hl⟩⟩
    · rintro ⟨m, n, e⟩
      obtain ⟨x, hx, -, -⟩ := hxy m n
      have : lam = x := hhi (e.trans hx.symm)
      rw [this]
      exact x.2
  obtain ⟨a₀, c₀, ha₀, hc₀, hχ⟩ := GlobalTheory.T.semicharacter_theta_characteristic g a.u.Λ bs a.χ (fun l l' => by
    have := hsc l l'
    rw [show (a.herm l l').im = _ from him l l'] at this
    exact this) hsq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.theta_function_canonical_multiplier g (periodMatrix X Y) h a.Hm a₀ c₀ θ hτs hτp hh hHh hθ.1 (fun m n lam hlam w => by
    obtain ⟨x, hx, hxm, hxn⟩ := hxy m n
    obtain rfl : lam = x := hhi (hlam.trans hx.symm)
    have := hθ.2 x w
    rw [pow_one, hχ x] at this
    have e1 : (fun i => bs.repr x (Sum.inl i)) = m := funext hxm
    have e2 : (fun i => bs.repr x (Sum.inr i)) = n := funext hxn
    rw [e1, e2] at this
    exact this)
  have hb2 := GlobalTheory.T.theta_function_canonical_form g (periodMatrix X Y) h a.Hm a₀ c₀ a.u.Λ θ κ b hτs hτp hh ha₀ hc₀ hmem hHh hκ
    (fun l hl => ⟨a.χ ⟨l, hl⟩, hχn _, fun w => by
      have := hθ.2 ⟨l, hl⟩ w
      rw [pow_one] at this
      exact this⟩) hL2.1 hL2.2
  rw [hτim] at hb2
  have hbpos := hL2.1
  have hDpos : (0 : ℝ) < 2 ^ g * Y.det := mul_pos (by positivity) hY.det_pos
  set β : ℝ := ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) with hβ
  have hβpos : 0 < β := Real.rpow_pos_of_pos hDpos _
  have hβ2 : β ^ 2 = (Real.sqrt (2 ^ g * Y.det))⁻¹ := by
    rw [hβ, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hDpos.le, ← Real.rpow_neg hDpos.le]
    norm_num
  have hbκ : b = ‖κ‖ * β := by
    have : b ^ 2 = (‖κ‖ * β) ^ 2 := by rw [mul_pow, hβ2]; exact hb2
    exact (sq_eq_sq₀ hbpos.le (by positivity)).1 this
  have hκpos : 0 < ‖κ‖ := by
    rcases (norm_nonneg κ).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hbκ
      exact absurd hbκ hbpos.ne'
    · exact h0
  have hκ0 : κ ≠ 0 := norm_pos_iff.1 hκpos

  let Hq : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet h hh)).restrictScalars ℝ
  have hHq (w : Fin g → ℂ) : Hq w = h.mulVec w := rfl
  let L : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    (LinearEquiv.ofBijective (GlobalTheory.ThetaMean.periodMap (periodMatrix X Y))
      (GlobalTheory.ThetaMean.periodMap_bijective hτp)).trans Hq.symm
  have hLap (p) : h.mulVec (L p) = GlobalTheory.ThetaMean.periodMap (periodMatrix X Y) p := by
    rw [← hHq]
    exact Hq.apply_symm_apply _
  have hcoordL : ∀ w, h.mulVec w = (periodMatrix X Y).mulVec (fun i => (L.symm w (Sum.inr i) : ℂ)) +
      (fun i => (L.symm w (Sum.inl i) : ℂ)) := by
    intro w
    have := hLap (L.symm w)
    rw [L.apply_symm_apply, GlobalTheory.ThetaMean.periodMap_apply, add_comm] at this
    exact this
  have hE := GlobalTheory.T.theta_norm_in_period_coordinates g X Y a₀ c₀ h a.Hm θ κ hX hY hHh hκ
  set E : ℝ := g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g) with hEdef
  have hhalf : ∀ (t : Fin g → ℝ), (∀ i, t i = 0 ∨ t i = 1 / 2) → ∀ i, ∃ m : ℤ, t i = m / 2 := by
    intro t ht i
    rcases ht i with e | e
    · exact ⟨0, by simp [e]⟩
    · exact ⟨1, by simp [e]⟩
  have hbd := (hB g X Y ρ a₀ c₀ hX hY hR (hhalf a₀ ha₀) (hhalf c₀ hc₀)).2
  let d : (Fin g → ℂ) → ℝ := fun w =>
    Metric.infDist (L.symm w (Sum.inr 0) + a₀ 0) (Set.range ((↑) : ℤ → ℝ))
  have hρ : 0 < ρ := hR.pos
  have hnb : ∀ w, a.nrm 1 θ w ≤ b * Real.exp (-(Real.pi / (2 * ρ ^ 2)) * d w ^ 2 + E) := by
    intro w
    have h1 := hE (fun i => L.symm w (Sum.inr i)) (fun i => L.symm w (Sum.inl i)) w (hcoordL w)
    have h2 := hbd (fun i => L.symm w (Sum.inr i)) (fun i => L.symm w (Sum.inl i))
    have h3 : a.nrm 1 θ w = ‖κ‖ * thetaNorm X Y a₀ c₀ (fun i => L.symm w (Sum.inr i))
        (fun i => L.symm w (Sum.inl i)) := h1
    rw [h3, hbκ, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hκpos.le
  refine ⟨ρ, hρ, Real.le_sqrt_of_sq_le hR.sq_le, fun w => ?_, ?_⟩
  · refine (hnb w).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hbpos.le)
    have : 0 ≤ Real.pi / (2 * ρ ^ 2) * d w ^ 2 := by positivity
    linarith
  have hnz : ∃ w, θ w ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := Function.ne_iff.1 (GlobalTheory.CanTh.canTh_ne_zero (a := a₀) (b := c₀) hτs hτp)
    obtain ⟨w, rfl⟩ := (Matrix.mulVec_surjective_iff_isUnit.2 hhu) ζ
    exact ⟨w, by rw [hκ]; exact mul_ne_zero hκ0 hζ⟩
  have hLint : ∀ p, L p ∈ a.u.Λ ↔ ∃ k : Fin g ⊕ Fin g → ℤ, p = fun α => (k α : ℝ) := by
    intro p
    rw [hmem, hLap]
    constructor
    · rintro ⟨m, n, e⟩
      refine ⟨Sum.elim m n, (GlobalTheory.ThetaMean.periodMap_bijective hτp).1 ?_⟩
      rw [e, GlobalTheory.ThetaMean.periodMap_apply]
      simp
    · rintro ⟨k, rfl⟩
      refine ⟨fun i => k (Sum.inl i), fun i => k (Sum.inr i), ?_⟩
      rw [GlobalTheory.ThetaMean.periodMap_apply]
      simp
  have hinv : ∀ l ∈ a.u.Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0 := by
    intro l hl w
    have := hθ.2 ⟨l, hl⟩ w
    rw [pow_one] at this
    have hne : a.χ ⟨l, hl⟩ ≠ 0 := fun e => by
      have := hχn ⟨l, hl⟩
      rw [e] at this
      simp at this
    change θ (w + l) = _ at this
    rw [this]
    simp [hne, Complex.exp_ne_zero]
  filter_upwards [GlobalTheory.T.theta_zero_divisor_jet_bound g a.u.Λ θ L (Sum.inr 0) (a₀ 0) hθ.1 hnz hLint hinv (hhalf a₀ ha₀ 0)] with m hm
  intro Ix _ r hr hu
  obtain ⟨hne, hcard⟩ := hm Ix r hr hu
  refine ⟨hne, ?_⟩
  classical
  have hper : ∀ i, Real.pi / (2 * ρ ^ 2) * d (r i) ^ 2 - E ≤ -Real.log (a.nrm 1 θ (r i) / b) := by
    intro i
    have hn0 : 0 < a.nrm 1 θ (r i) := by
      unfold ArchFrame.nrm
      exact mul_pos (norm_pos_iff.2 (hr i).2) (Real.exp_pos _)
    have h1 : a.nrm 1 θ (r i) / b ≤ Real.exp (-(Real.pi / (2 * ρ ^ 2)) * d (r i) ^ 2 + E) := by
      rw [div_le_iff₀ hbpos, mul_comm]
      exact hnb _
    have h2 := (Real.log_le_iff_le_exp (div_pos hn0 hbpos)).2 h1
    linarith
  let A : Finset Ix := Finset.univ.filter fun i => (1 / 4 : ℝ) ≤ d (r i)
  have hA : {i | (1 / 4 : ℝ) ≤ Metric.infDist (L.symm (r i) (Sum.inr 0) + a₀ 0) (Set.range ((↑) : ℤ → ℝ))}.ncard = A.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [A, d]
  rw [hA] at hcard
  have hsum : (A.card : ℝ) / 16 ≤ ∑ i, d (r i) ^ 2 := by
    calc (A.card : ℝ) / 16 = ∑ i ∈ A, (1 / 16 : ℝ) := by simp; ring
      _ ≤ ∑ i ∈ A, d (r i) ^ 2 := Finset.sum_le_sum fun i hi => by
          have : (1 / 4 : ℝ) ≤ d (r i) := (Finset.mem_filter.1 hi).2
          nlinarith
      _ ≤ ∑ i, d (r i) ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun i _ _ => sq_nonneg _
  have hcard' : (Fintype.card Ix : ℝ) ≤ 3 * A.card := by exact_mod_cast hcard
  have hq : 0 < Real.pi / (2 * ρ ^ 2) := by positivity
  calc (Fintype.card Ix : ℝ) * (Real.pi / 96 * (ρ ^ 2)⁻¹ - E)
      = Real.pi / (2 * ρ ^ 2) * ((Fintype.card Ix : ℝ) / 48) - Fintype.card Ix * E := by
        field_simp
        ring
    _ ≤ Real.pi / (2 * ρ ^ 2) * (∑ i, d (r i) ^ 2) - Fintype.card Ix * E := by
        have : (Fintype.card Ix : ℝ) / 48 ≤ ∑ i, d (r i) ^ 2 := by linarith
        nlinarith
    _ = ∑ i, (Real.pi / (2 * ρ ^ 2) * d (r i) ^ 2 - E) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
        simp
    _ ≤ ∑ i, -Real.log (a.nrm 1 θ (r i) / b) := Finset.sum_le_sum fun i _ => hper i

end GlobalTheory.CompanionTheory.Ar.NForm
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_even_bound : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), 1 ≤ g → (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → (∀ l : a.u.Λ, a.χ l ^ 2 = 1) → ∀ (θ : (Fin g → ℂ) → ℂ) (b : ℝ), a.IsTheta 1 θ → a.IsThetaMeanSquareNorm θ b → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ √(2 * g) ∧ (∀ w, a.nrm 1 θ w ≤ b * Real.exp (g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g))) ∧ ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ), (∀ i, (m : ℂ) • r i ∈ a.u.Λ ∧ θ (r i) ≠ 0) → (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ a.u.Λ → θ w ≠ 0 → ∃! i, w - r i ∈ a.u.Λ) → Nonempty Ix ∧ (Fintype.card Ix : ℝ) * (Real.pi / 96 * (ρ ^ 2)⁻¹ - (g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g))) ≤ ∑ i, -Real.log (a.nrm 1 θ (r i) / b) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.NForm.nform
end
