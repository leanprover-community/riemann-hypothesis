module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem span_image_inf_of_linearIndependent {K V W ι : Type} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W)
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun k => j (b k)))
    (U U' : Submodule K V) :
    Submodule.span ℂ (j '' (U : Set V)) ⊓ Submodule.span ℂ (j '' (U' : Set V)) =
      Submodule.span ℂ (j '' ((U ⊓ U' : Submodule K V) : Set V)) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := Fintype.ofFinite ι
  let B := Algebra.TensorProduct.basis ℂ b
  let J : ℂ ⊗[K] V →ₗ[ℂ] W := B.constr ℂ (fun k => j (b k))
  have hJb : ∀ k, J (1 ⊗ₜ b k) = j (b k) := fun k => by
    have := B.constr_basis ℂ (fun k => j (b k)) k
    rwa [Algebra.TensorProduct.basis_apply] at this
  have hJ : ∀ v, J (1 ⊗ₜ v) = j v := fun v => by

    rw [← b.sum_repr v, TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, map_smulₛₗ j, ← hJb, ← map_smul,
      ← algebraMap_smul ℂ (b.repr v k)]
    rfl
  have hinj : Function.Injective J := by
    apply Module.Basis.injective_constr_of_linearIndependent
    exact hb
  have key : ∀ A : Submodule K V,
      Submodule.span ℂ (j '' (A : Set V)) = (A.baseChange ℂ).map J := fun A => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => (hJ v).symm
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ hinj]

end GlobalTheory
