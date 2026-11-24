module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.continuous_units_inv_of_continuous_coe_finite_Qp_algebra :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] {X : Type} [TopologicalSpace X] (f : X → Bˣ), Continuous (fun x => (f x : B)) → Continuous fun x => (((f x)⁻¹ : Bˣ) : B) := by
  intro l _ B _ _ _ _ _ _ X _ f hf
  classical
  let b := Module.finBasis ℚ_[l] B
  let M := Algebra.leftMulMatrix b
  let E : (Fin (Module.finrank ℚ_[l] B) → ℚ_[l]) →ₗ[ℚ_[l]] B := b.equivFun.symm.toLinearMap
  have key : ∀ u : Bˣ, ((u⁻¹ : Bˣ) : B) = E (Matrix.mulVec (M (u : B))⁻¹ (b.repr 1)) := by
    intro u
    have hinv : (M (u : B))⁻¹ = M ((u⁻¹ : Bˣ) : B) := by
      apply Matrix.inv_eq_left_inv
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hinv, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    simp [E]
  have hM : Continuous fun y : B => M y :=
    IsModuleTopology.continuous_of_linearMap M.toLinearMap
  have hE : Continuous E := LinearMap.continuous_on_pi E
  have hcomp : Continuous fun x => E (Matrix.mulVec (M (f x : B))⁻¹ (b.repr 1)) := by
    refine hE.comp ?_
    refine Continuous.matrix_mulVec ?_ continuous_const
    rw [continuous_iff_continuousAt]
    intro x
    refine ContinuousAt.comp (f := fun x => M (f x : B)) (g := Inv.inv) ?_ (hM.comp hf).continuousAt
    apply continuousAt_matrix_inv
    have hdet : IsUnit (M (f x : B)).det := by
      have : IsUnit (M (f x : B)) := (f x).isUnit.map M
      exact (Matrix.isUnit_iff_isUnit_det _).1 this
    obtain ⟨d, hd⟩ := hdet
    rw [← hd]
    exact NormedRing.inverse_continuousAt d
  simpa only [← key] using hcomp
