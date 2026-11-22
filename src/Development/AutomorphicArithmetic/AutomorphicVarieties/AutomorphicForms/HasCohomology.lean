module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep
open scoped TensorProduct

namespace UpperTheory.V.TR

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

section Complex

omit [NumberField E]

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)

end Complex

variable [IsTotallyReal E]

end UpperTheory.V.TR

namespace UpperTheory.V.Af

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def levelRep (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ ↥Γ ((GL (Fin a) (Af E) ⧸ U) → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f x => ξ γ *ᵥ f ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1)⁻¹ • x)
      map_add' := fun f g => funext fun x => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun x => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f x; simp
  map_mul' γ δ := by ext f x; simp [mul_smul]

def cohDim (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) : Cardinal :=
  Cardinal.sum fun q : ℕ => Module.rank ℂ (groupCohomology (Rep.of (levelRep Γ U ξ)) q)

variable [_root_.NumberField.IsTotallyComplex E]

def ratC (Ξ : GlobalTheory.GKCoh.AlgRep E a) : GL (Fin a) E →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  Ξ.mat.comp ((GeneralLinearGroup.map (pInf E)).comp (ratGL E a))

omit [_root_.NumberField.IsTotallyComplex E] in
def AlgInfChar (Ξ : GlobalTheory.GKCoh.AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun i j => (1 / 2 : ℂ) • (Ξ.dmat (toL (Matrix.single i j (atEmb τ 1))) -
      Complex.I • Ξ.dmat (toL (Matrix.single i j (atEmb τ Complex.I))))) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def IsFinComp (π : CuspSub E a) (σ : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.finPart g (f v)

omit [_root_.NumberField.IsTotallyComplex E] in
def IsConjBy (σ : ℂ ≃+* ℂ) (τ τ' : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ T : τ.V ≃+ τ'.V, (∀ (c : ℂ) v, T (c • v) = σ c • T v) ∧ ∀ g v, T (τ.ρ g v) = τ'.ρ g (T v)

end UpperTheory.V.Af
