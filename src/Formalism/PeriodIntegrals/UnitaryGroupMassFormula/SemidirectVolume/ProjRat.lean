import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjStep

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField
open scoped TensorProduct Matrix

section E

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def datE : PG.Dat E (Fin M) r where
  σA := (σ : E →+* E)
  JA := J
  e := P.e
  f := P.f
  z := P.z
  tz := (algebraMap F E (-T))⁻¹

variable {σ J P T}


variable (R : Type) [CommRing R] [Algebra F R]


theorem ratV_add' (x y : Fin M → E) :
    ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
  funext i; simp [ratV]






theorem ratV_mulVec' (Q : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    ratV (F := F) R (Q *ᵥ x) = (Q.map (inclR (F := F) R)) *ᵥ ratV (F := F) R x := by
  funext i
  exact RingHom.map_mulVec (inclR (F := F) R) Q x i

theorem lin_rat (g : HA R σ J) (γ : GL (Fin M) E)
    (hγ : Formalism.UG.bc (inclR (F := F) R) γ = (g : HR R σ J).1) (x : Fin M → E) :
    lin R σ J g (ratV (F := F) R x) = ratV (F := F) R ((γ : Matrix (Fin M) (Fin M) E) *ᵥ x) := by
  rw [ratV_mulVec']
  show (((g : HR R σ J).1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ _ = _
  rw [← hγ]
  rfl



end E

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}


end Main


end PI.VolSemiDirect.W
