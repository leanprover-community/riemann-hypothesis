module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem lift_rep_of_entries_in_image : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  intro k L Γ _ _ _ f b τ h
  choose pre hpre using h
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin b) (Fin b) k →+* Matrix (Fin b) (Fin b) L) :=
    Matrix.map_injective f.injective
  have key : ∀ g, f.mapMatrix (Matrix.of (pre g)) = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
    intro g; ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, hpre]
  let m : Γ →* Matrix (Fin b) (Fin b) k :=
    { toFun := fun g => Matrix.of (pre g)
      map_one' := hinj (by rw [key, map_one, map_one]; rfl)
      map_mul' := fun x y => hinj (by rw [map_mul, key, key, key, map_mul]; rfl) }
  refine ⟨MonoidHom.toHomUnits m, ?_⟩
  ext g i j
  simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  rw [MonoidHom.coe_toHomUnits]
  exact congrFun (congrFun (key g) i) j

end GlobalTheory
