module

public import Mathlib.Algebra.Module.Equiv.Defs
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
import Mathlib.NumberTheory.Padics.PadicNumbers
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc UpperTheory.V.U3

section Gen

variable {Q A V V' : Type} [Field Q] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V]
  [IsScalarTower Q A V] [AddCommGroup V'] [Module A V'] [Module Q V'] [IsScalarTower Q A V']

private noncomputable def tr (B : Type) [AddCommGroup B] [Module Q B] (e : V ≃ₗ[A] V') :
    V ⊗[Q] B ≃ₗ[A] V' ⊗[Q] B := AlgebraTensorModule.congr e (LinearEquiv.refl Q B)

variable {B B' : Type} [AddCommGroup B] [Module Q B] [AddCommGroup B'] [Module Q B'] (e : V ≃ₗ[A] V')

private theorem tr_map {f : V →ₗ[A] V} {f' : V' →ₗ[A] V'} (h : ∀ x, e (f x) = f' (e x)) (b : B →ₗ[Q] B')
    (x : V ⊗[Q] B) :
    tr B' e (AlgebraTensorModule.map f b x) = AlgebraTensorModule.map f' b (tr B e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [tr, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem tr_smul {K : Type} [AddCommGroup K] [Module Q K] (s : K →ₗ[Q] Module.End Q B) (c : A ⊗[Q] K)
    (x : V ⊗[Q] B) :
    tr B e (((TensorProduct.homTensorHomMap (RingHom.id Q) V B V B).comp
      (TensorProduct.map (Algebra.lsmul Q Q V : A →ₐ[Q] Module.End Q V).toLinearMap s)) c x) =
    ((TensorProduct.homTensorHomMap (RingHom.id Q) V' B V' B).comp
      (TensorProduct.map (Algebra.lsmul Q Q V' : A →ₐ[Q] Module.End Q V').toLinearMap s)) c (tr B e x) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c d hc hd => simp only [map_add (f := _), LinearMap.add_apply, hc, hd]
  | tmul a k =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [tr]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Gen

section Per

variable {l : ℕ} [Fact l.Prime] {A V V' : Type} [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V']
  [IsScalarTower ℚ_[l] A V'] (e : V ≃ₗ[A] V')

end Per
