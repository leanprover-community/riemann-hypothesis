import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.TemperedDerivatives.StepsD
open Ad3.K.LC

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementGaussK

abbrev CIdx : Type := Fin 2 × Fin 3 ⊕ Fin 2

abbrev RIdx : Type := CIdx × Bool

def cz : CIdx → (M23 × (Fin 2 → ℂ)) →ₗ[ℝ] ℂ
  | .inl (r, c) => (LinearMap.proj c) ∘ₗ (LinearMap.proj r) ∘ₗ (LinearMap.fst ℝ M23 (Fin 2 → ℂ))
  | .inr a => (LinearMap.proj a) ∘ₗ (LinearMap.snd ℝ M23 (Fin 2 → ℂ))

def rc : Bool → ℂ →ₗ[ℝ] ℝ
  | false => Complex.reLm
  | true => Complex.imLm

def toEuc : (M23 × (Fin 2 → ℂ)) →ₗ[ℝ] EuclideanSpace ℝ RIdx :=
  (WithLp.linearEquiv 2 ℝ (RIdx → ℝ)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i => Real.sqrt 2 • (rc i.2 ∘ₗ cz i.1)

theorem toEuc_apply (p : M23 × (Fin 2 → ℂ)) (i : RIdx) :
    toEuc p i = Real.sqrt 2 * rc i.2 (cz i.1 p) := by
  simp [toEuc]

theorem toEuc_injective : Function.Injective toEuc := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have key : ∀ i : CIdx, cz i p = 0 := by
    intro i
    have h0 := toEuc_apply p (i, false)
    have h1 := toEuc_apply p (i, true)
    rw [hp] at h0 h1
    simp only [PiLp.zero_apply] at h0 h1
    apply Complex.ext
    · have := (mul_eq_zero.1 h0.symm).resolve_left hs
      simpa [rc] using this
    · have := (mul_eq_zero.1 h1.symm).resolve_left hs
      simpa [rc] using this
  refine Prod.ext ?_ ?_
  · funext r c
    simpa [cz] using key (.inl (r, c))
  · funext a
    simpa [cz] using key (.inr a)

theorem finrank_eq :
    Module.finrank ℝ (M23 × (Fin 2 → ℂ)) = Module.finrank ℝ (EuclideanSpace ℝ RIdx) := by
  simp [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex]

def euc : (M23 × (Fin 2 → ℂ)) ≃L[ℝ] EuclideanSpace ℝ RIdx :=
  (LinearMap.linearEquivOfInjective toEuc toEuc_injective finrank_eq).toContinuousLinearEquiv



def gaussK : Sw :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euc
    (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ RIdx))


def polyK (k : ℕ) (p : M23 × (Fin 2 → ℂ)) : ℂ :=
  (crd 0 0 p * crd 1 1 p - crd 0 1 p * crd 1 0 p) ^ (2 * k - 2) *
    (crqc 0 p * crdc 0 0 p + crqc 1 p * crdc 1 0 p) ^ (4 * k - 4)



end GlobalTheory.CompanionTheory.GodementGaussK
