module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgBcC.Cxb

open PositivityTheory.RgBcC

variable {n : ℕ}

theorem map_comp' {M N P : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] [AddCommGroup P]
    [Module ℂ P] (f : N →ₗ[ℂ] P) (g : M →ₗ[ℂ] N) :
    ExteriorAlgebra.map (f ∘ₗ g) = (ExteriorAlgebra.map f).comp (ExteriorAlgebra.map g) := by
  ext m
  simp

theorem creL_eq (v : Md n → ℂ) : creL n v = matL n (LinearMap.mul ℂ (abelian₂ n) (ExteriorAlgebra.ι ℂ v)) := rfl

theorem annL_eq (w : Md n → ℂ) :
    annL n w = matL n (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf w)) := rfl

theorem gamM_eq (g : Matrix (Md n) (Md n) ℂ) : gamM g = matL n (ExteriorAlgebra.map (Matrix.toLin' g)).toLinearMap := rfl

theorem matL_mul (f h : abelian₂ n →ₗ[ℂ] abelian₂ n) : matL n (f * h) = matL n f * matL n h := LinearMap.toMatrix_mul _ _ _

theorem matL_one : matL n (1 : abelian₂ n →ₗ[ℂ] abelian₂ n) = 1 := LinearMap.toMatrix_one _

theorem contractLeft_map (f : (Md n → ℂ) →ₗ[ℂ] (Md n → ℂ)) (d : Module.Dual ℂ (Md n → ℂ)) (y : abelian₂ n) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) d (ExteriorAlgebra.map f y) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (d ∘ₗ f) y) := by
  induction y using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  | ι_mul x m hx =>
    have e : ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) m * x) =
        CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) (f m) * ExteriorAlgebra.map f x := by
      rw [map_mul]
      exact congrArg (· * _) (ExteriorAlgebra.map_apply_ι f m)
    rw [e, CliffordAlgebra.contractLeft_ι_mul, hx, CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul]
    rw [show ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) m) =
      CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) (f m) from ExteriorAlgebra.map_apply_ι f m]
    rfl

end PositivityTheory.RgBcC.Cxb

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.Cxb

theorem gamMul : GamMul := by
  intro n
  refine ⟨?_, fun g h => ?_⟩
  · rw [gamM_eq, Matrix.toLin'_one, ExteriorAlgebra.map_id]
    exact LinearMap.toMatrix_id _
  · rw [gamM_eq, gamM_eq, gamM_eq, Matrix.toLin'_mul, map_comp', AlgHom.comp_toLinearMap, ← matL_mul]
    rfl

theorem car : Car := by
  intro n v w
  rw [annL_eq, creL_eq, ← matL_mul, ← matL_mul, ← map_add (f := _), ← matL_one, ← map_smul]
  congr 1
  apply LinearMap.ext
  intro y
  rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.mul_apply', LinearMap.mul_apply', CliffordAlgebra.contractLeft_ι_mul]
  show (w ⬝ᵥ v) • y - _ + _ = _
  abel

theorem gamCre : GamCre := by
  intro n g v w
  refine ⟨?_, ?_⟩
  · rw [gamM_eq, creL_eq, creL_eq, ← matL_mul, ← matL_mul]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply, LinearMap.mul_apply', map_mul, ExteriorAlgebra.map_apply_ι,
      Matrix.toLin'_apply]
  · rw [gamM_eq, annL_eq, annL_eq, ← matL_mul, ← matL_mul]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply]
    have hd : dualOf w ∘ₗ Matrix.toLin' g = dualOf (gᵀ *ᵥ w) := by
      refine LinearMap.ext fun u => ?_
      simp only [LinearMap.comp_apply, dualOf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.toLin'_apply]
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    rw [contractLeft_map, hd]

end PositivityTheory.RgBcC
