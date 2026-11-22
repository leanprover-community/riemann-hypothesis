module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WitApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GfResZpow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.MatIrrOpenGd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.WeightZeroAlgebraLeEntryAlgebra
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base

namespace UpperTheory.GalN.V

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}

theorem attC_iso [_root_.NumberField.IsTotallyComplex F] {π : CuspSub F n} (h : RepIso r r') (H : AttC ι r π) : AttC ι r' π := by
  refine ⟨?_, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩
  obtain ⟨g, hg⟩ := h
  let e : (Fin n → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) :=
    Matrix.toLin'OfInv (M := (g : Matrix (Fin n) (Fin n) (Qbar l)))
      (M' := ((g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)))
      (Units.mul_inv g) (Units.inv_mul g)
  have he (v : Fin n → Qbar l) :
      e v = ((g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := rfl
  have intertwine (s : G F Ω) (v : Fin n → Qbar l) :
      e ((r' s : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) =
        (r s : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (e v) := by
    rw [he, he, hg s, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  intro W hW
  obtain ⟨W', hW', hc⟩ := H.1 (W.map e.toLinearMap) (by
    rintro s _ ⟨v, hv, rfl⟩
    exact ⟨_, hW s v hv, intertwine s v⟩)
  refine ⟨W'.comap e.toLinearMap, fun s v hv => ?_, ?_⟩
  · show e _ ∈ W'
    rw [intertwine]
    exact hW' s (e v) hv
  · have hcompl : IsCompl ((W.map e.toLinearMap).comap e.toLinearMap) (W'.comap e.toLinearMap) :=
      (Submodule.orderIsoMapComap e).symm.isCompl hc
    rwa [Submodule.comap_map_eq_of_injective e.injective] at hcompl

end

def NewformAut0 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (j : ℤ), f.Att ι (tw W (cycBar ℚ Ω l ^ j)) → IsAutomorphicOverImagQuad ι W

end UpperTheory.GalN.V
