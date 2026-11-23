module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detCo_of :
    CoFacts := by
  intro F L B _ _ _ _ _ a
  refine ⟨fun x y => ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    simp [co, map_add (f := _)]
  · intro c x
    funext i
    show AlgebraTensorModule.map (LinearMap.proj i) LinearMap.id (c • x) =
      (c ⊗ₜ[F] (1 : B)) * AlgebraTensorModule.map (LinearMap.proj i) LinearMap.id x
    rw [map_smul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  · intro b x
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp [co]
    | tmul m n => simp [co, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp_all [co, mul_add]
  · intro T A hT s x
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp [co, Matrix.mulVec, dotProduct]
    | tmul m n =>
      simp [co, onR, hT, Matrix.mulVec, dotProduct, TensorProduct.sum_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _), Pi.add_apply] at hx hy ⊢
      simp_all [co, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  · convert (AlgebraTensorModule.congr (LinearEquiv.funUnique (Fin 1) L L)
      (LinearEquiv.refl F B)).bijective using 1
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp [co]
    | tmul m n => simp [co]
    | add x y hx hy => simp_all [co]
