import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyUniformizationExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismDescendsToAlgebraicModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyPeriodNormalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodRatioAlgebraic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeDifferentialsAlgebraic

section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_preserving_map_gives_endomorphism : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (M : LB X.A.left) (g : ℕ)
    (u : HolUnif X.A M g) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w ∈ u.Λ, T w ∈ u.Λ) →
      ∃ α : X.A ⟶ X.A, IsMonHom α ∧ ∀ w, u.ex (T w) = u.ex w ≫ α := by
  first | exact @GlobalTheory.RealMult.Obj.exists_isMonHom_of_map_lattice | exact GlobalTheory.RealMult.Obj.exists_isMonHom_of_map_lattice | (intros; apply GlobalTheory.RealMult.Obj.exists_isMonHom_of_map_lattice <;> assumption)
end

section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_descends_to_algebraic_model : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X₀ : Obj F 𝔠 (Sp Qb)) (X : Obj F 𝔠 (Sp ℂ))
    (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
      ∀ (α : X.A ⟶ X.A) [IsMonHom α], ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left := by
  first | exact @GlobalTheory.RealMult.Obj.exists_end_descend_algebraic | exact GlobalTheory.RealMult.Obj.exists_end_descend_algebraic | (intros; apply GlobalTheory.RealMult.Obj.exists_end_descend_algebraic <;> assumption)
end

section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_abelian_variety_period_normalization : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
      ∃ (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p := by
  first | exact @GlobalTheory.CMModel.exists_model | exact GlobalTheory.CMModel.exists_model | (intros; apply GlobalTheory.CMModel.exists_model <;> assumption)
end

section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_period_ratio_algebraic : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf io 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X) (X₀ : Obj (FR E) 𝔠 (Sp Qb))
        (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
      ∃ (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
        ∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧
          a i ≠ 0 ∧ IsAlgebraic ℚ (a i * Ω₀) := by
  first | exact @GlobalTheory.CMLiePeriod.exists_lie_frame | exact GlobalTheory.CMLiePeriod.exists_lie_frame | (intros; apply GlobalTheory.CMLiePeriod.exists_lie_frame <;> assumption)
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CMModel

theorem exists_model_of_lattice : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf io 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∃ (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
        (U : Unif φ (lattice c y) 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
        X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p ∧
        (∀ i, U.h i ≠ 0 ∧ IsAlgebraic ℚ ((U.h i : ℂ) * (Real.sqrt d : ℝ))) ∧
        (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧
          a i ≠ 0 ∧ IsAlgebraic ℚ (a i * Ω₀)) ∧
        (∀ b : E, (∀ x ∈ lattice c y, b * x ∈ lattice c y) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
          ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) ∧
        ∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
          ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left := by
  intro hPC hDR hDC K _ _ d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ hφ hio c y hc
  obtain ⟨𝔠, X, U, hU⟩ := GlobalTheory.T.cm_abelian_variety_uniformization_exists K d δ io hK hd hδ E I φ hφ hio c y hc
  obtain ⟨X₀, p, hp⟩ := GlobalTheory.T.cm_abelian_variety_period_normalization hPC hDR hDC K d δ io hK hd hδ E I φ hφ hio c y hc 𝔠 X U
  obtain ⟨v₀, v, a, hv⟩ := GlobalTheory.T.cm_period_ratio_algebraic hPC hDR hDC K d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E I φ hφ hio c y hc 𝔠 X U X₀ p hp
  refine ⟨𝔠, X₀, X, p, U, v₀, v, a, hp, hU, hv, ?_, ?_⟩
  · intro b hb
    let T : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      { toFun := fun w j ↦ φ (U.e j) b * w j
        map_add' := fun w w' ↦ by funext j; simp [mul_add]
        map_smul' := fun r w ↦ by funext j; simp; ring }
    obtain ⟨α, hα, hex⟩ := GlobalTheory.T.lattice_preserving_map_gives_endomorphism (FR E) 𝔠 X _ _ U.u T (by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := (U.lat w).1 hw
      refine (U.lat _).2 ⟨b * x, hb x hx, ?_⟩
      funext j
      simp [T, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord])
    exact ⟨α, hα, fun w' ↦ hex w'⟩
  · intro b α _ _
    exact GlobalTheory.T.endomorphism_descends_to_algebraic_model (FR E) 𝔠 X₀ X p hp α

end GlobalTheory.CMModel
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_period_from_elliptic_lattice : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf io 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∃ (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
        (U : Unif φ (lattice c y) 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
        X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p ∧
        (∀ i, U.h i ≠ 0 ∧ IsAlgebraic ℚ ((U.h i : ℂ) * (Real.sqrt d : ℝ))) ∧
        (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧
          a i ≠ 0 ∧ IsAlgebraic ℚ (a i * Ω₀)) ∧
        (∀ b : E, (∀ x ∈ lattice c y, b * x ∈ lattice c y) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
          ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) ∧
        ∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
          ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left := by
  atlas_forward_decl GlobalTheory.CMModel.exists_model_of_lattice
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem Obj.exists_detGen_holUnif : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (κ : ℂ), κ ≠ 0 →
    ∃ δ : X.DetGen, ∀ (v : Fin (Module.finrank ℚ F) → X.Lie)
      (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ i, u.IsDiff (W i) (v i).hom) → δ.1 v = κ * W.det := by
  intro F _ _ 𝔠 X L u κ hκ
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  obtain ⟨d, hdi, hd⟩ := GlobalTheory.DiagCoord.exists_diff_linear u X.rm h₁ h₂
  have hds : Function.Surjective d := fun w => by
    obtain ⟨v, hv, hw⟩ := (h₂ w).exists
    refine ⟨GlobalTheory.Serre.Lie.mk X.rm v hv, ?_⟩
    exact (h₁ _ hv).unique (hd _) hw
  let e : X.Lie ≃ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ) := LinearEquiv.ofBijective d ⟨hdi, hds⟩
  let b : Module.Basis (Fin (Module.finrank ℚ F)) ℂ X.Lie := (Pi.basisFun ℂ _).map e.symm
  refine ⟨⟨κ • b.det, ?_⟩, fun v W hW => ?_⟩
  · rw [show κ • b.det = (Units.mk0 κ hκ : ℂˣ) • b.det from rfl, Submodule.span_singleton_group_smul_eq]
    exact (Obj.DetGen.ofBasis X b).2
  · have hv : ∀ i, d (v i) = W i := fun i => (h₁ _ (v i).isTangent).unique (hd _) (hW i)
    have hm : b.toMatrix v = W.transpose := by
      ext i j
      rw [Module.Basis.toMatrix_apply, Matrix.transpose_apply]
      rw [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, Pi.basisFun_repr]
      exact congrFun (hv j) i
    rw [AlternatingMap.smul_apply, Module.Basis.det_apply, hm, Matrix.det_transpose, smul_eq_mul]

end GlobalTheory.RealMult
end
end

section
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

theorem exists_detGen_coeff_algebraic : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E) (𝔠 : FracId (FR E))
    (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left) (U : Unif φ L 0 X)
    (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom) →
    ∃ (δ₀ : X₀.DetGen) (δ : X.DetGen) (C : ℂ), Obj.DetCorr (algebraMap Qb ℂ) p δ₀.1 δ.1 ∧ U.IsDet δ.1 C ∧
      IsAlgebraic ℚ (C * ∏ i, a i) := by
  intro E _ _ I _ φ L 𝔠 X₀ X p U v₀ v a hpb hv
  haveI := Obj.invertible_detOmega X₀
  obtain ⟨d, -, hd⟩ := finrank_eq_one_iff'.1 (Module.Invertible.finrank_eq_one Qb X₀.DetOmega)
  let δ₀ : X₀.DetGen := ⟨d, eq_top_iff.2 fun w _ ↦ Submodule.mem_span_singleton.2 (hd w)⟩
  obtain ⟨δ, hδ, -⟩ := hpb.existsUnique_detGen (algebraMap Qb ℂ) δ₀
  obtain ⟨δ₁, hδ₁⟩ := Obj.exists_detGen_holUnif (FR E) 𝔠 X _ U.u 1 one_ne_zero
  have hmem : δ.1 ∈ Submodule.span ℂ {δ₁.1} := by rw [δ₁.2]; exact Submodule.mem_top
  obtain ⟨C, hC⟩ := Submodule.mem_span_singleton.1 hmem
  have hdet : U.IsDet δ.1 C := fun w W hW ↦ by
    rw [← hC, AlternatingMap.smul_apply, hδ₁ w W hW, smul_eq_mul, _root_.one_mul]
  refine ⟨δ₀, δ, C, hδ, hdet, ?_⟩
  have hW : ∀ j, U.u.IsDiff ((Matrix.diagonal fun j ↦ a (U.e j)) j) (v (U.e j)).hom := fun j ↦ by
    have h := (hv (U.e j)).2
    rw [Equiv.symm_apply_apply] at h
    convert h using 1
    ext k
    simp [Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  have h1 := hdet (fun j ↦ v (U.e j)) _ hW
  have h2 := hδ (fun j ↦ v₀ (U.e j)) (fun j ↦ v (U.e j)) fun j ↦ (hv (U.e j)).1
  rw [Matrix.det_diagonal, Equiv.prod_comp U.e a] at h1
  rw [← h1, h2]
  exact (mem_algebraicClosure_iff.1 (δ₀.1 fun j ↦ v₀ (U.e j)).2)

end GlobalTheory.LatJet
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_correspondence_differentials : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E) (𝔠 : FracId (FR E))
    (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left) (U : Unif φ L 0 X)
    (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom) →
    ∃ (δ₀ : X₀.DetGen) (δ : X.DetGen) (C : ℂ), Obj.DetCorr (algebraMap Qb ℂ) p δ₀.1 δ.1 ∧ U.IsDet δ.1 C ∧
      IsAlgebraic ℚ (C * ∏ i, a i) := by
  atlas_forward_decl GlobalTheory.LatJet.exists_detGen_coeff_algebraic
end

section
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ModelAlgProof

theorem modelAlg : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ModelAlg := by
  intro hPC hDR hDC K _ _ d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ hφ hio c y hc
  obtain ⟨𝔠, X₀, X, p, U, v₀, v, a, hp, hh, hv, hex, hdesc⟩ :=
    GlobalTheory.T.cm_period_from_elliptic_lattice hPC hDR hDC K d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E I φ hφ hio c y hc
  obtain ⟨δ₀, δX, C, hDCr, hdet, hCa⟩ :=
    GlobalTheory.T.lie_correspondence_differentials E I φ _ 𝔠 X₀ X p U v₀ v a hp fun i ↦ ⟨(hv i).1, (hv i).2.1⟩
  obtain ⟨N, m, ψ, yv, w, hpol, hAdm, hvec⟩ := GlobalTheory.T.cm_type_differentials_algebraic hPC hDR hDC E I φ _ 𝔠 X₀ X p U v₀ v a hφ hp
    (fun i ↦ ⟨(hv i).1, (hv i).2.1, (hv i).2.2.1⟩) hex hdesc

  have hσ : ∀ x : Qb, IsAlgebraic ℚ (algebraMap Qb ℂ x) := fun x ↦ by
    have := x.2
    rwa [mem_algebraicClosure_iff] at this
  have toQ : ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ (algebraicClosure ℚ ℂ) := fun z hz ↦ by
    rwa [mem_algebraicClosure_iff]
  have ofQ : ∀ z : ℂ, z ∈ (algebraicClosure ℚ ℂ) → IsAlgebraic ℚ z := fun z hz ↦ by
    rwa [mem_algebraicClosure_iff] at hz
  let T : CxPt 𝔠 φ (lattice c y) :=
    { X := X, U := U, δ := δX, C := C, det := hdet, ψ := ψ, pol := hpol, y := yv, w := w, s := fun _ ↦ 1,
      cm := fun i ↦ (hvec i).1 }
  have ha0 : ∀ i, a i ≠ 0 := fun i ↦ (hv i).2.2.1
  refine ⟨𝔠, X₀, δ₀, N, T, hAdm, ⟨p, m, hp, hDCr, fun i x₀ x hx ↦ ?_⟩, ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · have := (hvec i).2.2.2 x₀ x hx
    simpa [T, CxPt.low] using this
  · have hprod : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ ha0 i
    have e : C / Ω₀ ^ Fintype.card I = (C * ∏ i, a i) / ∏ i, (a i * Ω₀) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_comm (∏ x, a x) _,
        mul_div_mul_right _ _ hprod]
    change IsAlgebraic ℚ (C / Ω₀ ^ Fintype.card I)
    rw [e]
    apply ofQ
    exact div_mem (toQ _ hCa) (prod_mem fun i _ ↦ toQ _ (hv i).2.2.2)
  · have hw := (hvec i).2.1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    change (Real.pi : ℂ) * (U.h i : ℂ) * 1 * w i ^ 2 ≠ 0
    have := (hh i).1
    simp only [_root_.mul_one]
    exact mul_ne_zero (mul_ne_zero hpi (Complex.ofReal_ne_zero.2 this)) (pow_ne_zero _ hw)
  · have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have e : T.A i * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi) =
        ((U.h i : ℂ) * (Real.sqrt d : ℝ)) * (w i / a i) ^ 2 * (a i * Ω₀) ^ 2 / 2 := by
      change (Real.pi : ℂ) * (U.h i : ℂ) * 1 * w i ^ 2 * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi) = _
      field_simp [ha0 i]
    rw [e]
    apply ofQ
    refine div_mem (mul_mem (mul_mem (toQ _ (hh i).2) (pow_mem (toQ _ (hvec i).2.2.1) _))
      (pow_mem (toQ _ (hv i).2.2.2) _)) ?_
    simpa using (algebraicClosure ℚ ℂ).algebraMap_mem (2 : ℚ)

end GlobalTheory.ModelAlgProof
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_model_of_de_rham : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ModelAlg := by
  atlas_forward_decl GlobalTheory.ModelAlgProof.modelAlg
end
