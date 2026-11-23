module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Defs

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

namespace PeterssonComplement

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)

variable {ι}

theorem aeval_mem {T : Module.End ℂ V} {Z : Submodule ℂ V} (hZ : ∀ z ∈ Z, T z ∈ Z) (q : ℂ[X]) :
    ∀ z ∈ Z, aeval T q z ∈ Z := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro z hz
    rw [aeval_C, Module.algebraMap_end_apply]
    exact Z.smul_mem a hz
  | add p q hp hq =>
    intro z hz
    rw [map_add (f := _), LinearMap.add_apply]
    exact Z.add_mem (hp z hz) (hq z hz)
  | monomial k a ih =>
    intro z hz
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (hZ z hz)

theorem apply_aeval_comm (T : Module.End ℂ V) (q : ℂ[X]) (z : V) : T (aeval T q z) = aeval T q (T z) := by
  have h := (Commute.all (X : ℂ[X]) q).map (aeval T)
  rw [aeval_X] at h
  exact congrArg (fun L : Module.End ℂ V => L z) h.eq

end PeterssonComplement

end GroundTheory.Automorphic
