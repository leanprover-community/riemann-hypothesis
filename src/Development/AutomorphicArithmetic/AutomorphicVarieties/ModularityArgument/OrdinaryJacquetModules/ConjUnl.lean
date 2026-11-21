import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistedDualFrobeniusCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.ExConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.IsPairingOfIsAutCsd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
open scoped Matrix
open scoped Pointwise

namespace UpperTheory.V.Z.Ord.CU

section Abs

variable {H H' k : Type} [Group H] [Group H'] [Field k] {n : ℕ}






private def revM (n : ℕ) (k : Type) [Field k] : Matrix (Fin n) (Fin n) k := (1 : Matrix (Fin n) (Fin n) k).submatrix Fin.rev id

private theorem revM_mul (X : Matrix (Fin n) (Fin n) k) (i j : Fin n) : (revM n k * X) i j = X (Fin.rev i) j := by
  simp [revM, Matrix.mul_apply, Matrix.one_apply]


private theorem revM_sq : revM n k * revM n k = 1 := by
  ext i j
  rw [revM_mul]
  simp [revM, Matrix.one_apply]

private def revG (n : ℕ) (k : Type) [Field k] : GL (Fin n) k := ⟨revM n k, revM n k, revM_sq, revM_sq⟩

private def trG (g : GL (Fin n) k) : GL (Fin n) k :=
  ⟨(g : Matrix (Fin n) (Fin n) k)ᵀ, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]⟩


private theorem aux₁ {C : Type} [CommGroup C] {a b e μ : C} {m : ℕ} (h : a ^ m = (b * e) ^ m) :
    (b⁻¹ * μ) ^ m = (a⁻¹ * μ * e) ^ m := by
  simp only [mul_pow, inv_pow] at h ⊢
  rw [h, mul_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [mul_left_comm (e ^ m), mul_left_comm (e ^ m), mul_inv_cancel, mul_one]

private theorem aux₂ {C : Type} [CommGroup C] {x y e μ : C} {m : ℕ} (h : (x⁻¹ * μ) ^ m = (y⁻¹ * μ * e) ^ m) :
    y ^ m = (x * e) ^ m := by
  simp only [mul_pow, inv_pow] at h ⊢
  have h' : (x ^ m)⁻¹ = (y ^ m)⁻¹ * e ^ m := by
    have := mul_right_cancel (b := μ ^ m) (a := (x ^ m)⁻¹) (c := (y ^ m)⁻¹ * e ^ m) (by rw [h]; simp [mul_comm, mul_left_comm, mul_assoc])
    exact this
  have h2 : x ^ m = y ^ m * (e ^ m)⁻¹ := by
    have := congrArg (·⁻¹) h'
    simpa [mul_comm] using this
  rw [h2]
  simp

private def Rel (r₁ : H →* GL (Fin n) k) (r₂ : H' →* GL (Fin n) k) (f : H' →* H) : Prop :=
  (∃ N : GL (Fin n) k, ∀ t, r₂ t = N * r₁ (f t) * N⁻¹) ∨
    ∃ (N : GL (Fin n) k) (μ : H' →* kˣ), ∀ t, (r₂ t : Matrix (Fin n) (Fin n) k) =
      (μ t : k) • ((N * GlobalTheory.MonoConj.dualRep r₁ (f t) * N⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)


end Abs

end UpperTheory.V.Z.Ord.CU

namespace UpperTheory.V.Z.Ord.CU

open UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu GlobalTheory.MonoConj

section Conc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}


private def decMap {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) :
    Dec (F := E) A' →* Dec (F := E) A :=
  ((conjGal h).comp (Dec (F := E) A').subtype).codRestrict _ fun t => conjGal_mem_Dec h hA t.2





end Conc

end UpperTheory.V.Z.Ord.CU

namespace UpperTheory.V.Z.Ord.CU

open UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu GlobalTheory.MonoConj

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}




end UpperTheory.V.Z.Ord.CU
