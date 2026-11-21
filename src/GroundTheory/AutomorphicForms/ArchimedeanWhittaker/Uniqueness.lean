import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.HasDerivAtCompLog

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

theorem det_eps : (((eps : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by
  simp [Matrix.det_fin_two_of]



end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

def IsWhit (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (ψ : ℝ → ℂ) (l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w

omit [CompleteSpace H] in
theorem eq_zero_of_mem_bot {V : Submodule ℂ H} (hV : V = ⊥) {u : H} (hu : u ∈ V) : u = 0 := by
  rw [hV, Submodule.mem_bot] at hu; exact hu



end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

noncomputable def whitSpace (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (ψ : ℝ → ℂ) :
    Submodule ℂ (hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) where
  carrier := {l | ∀ (x : ℝ) (w : hGL2.SmoothFrechet (πσ σ)),
    l (hGL2.smoothOp (πσ σ) (nMat x) w) = ψ x * l w}
  add_mem' {a b} ha hb := fun x w => by
    show a _ + b _ = ψ x * (a w + b w)
    rw [ha x w, hb x w]; ring
  zero_mem' := fun x w => by
    show (0 : ℂ) = ψ x * 0
    ring
  smul_mem' c a ha := fun x w => by
    show c * a _ = ψ x * (c * a w)
    rw [ha x w]; ring

noncomputable def toLin (l : hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ where
  toFun w := l w
  map_add' a b := l.map_add a b
  map_smul' c a := l.map_smul c a

theorem toLin_apply (l : hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) (w : hGL2.smoothVectors (πσ σ)) :
    toLin l w = l w := rfl








end GroundTheory.Automorphic.ArchWhittaker
