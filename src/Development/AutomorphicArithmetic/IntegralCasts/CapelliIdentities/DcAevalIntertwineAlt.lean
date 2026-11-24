module

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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p
  have hpow : ∀ (n : ℕ) (y : Y), ψ ((A ^ n) y) = (B ^ n) (ψ y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | monomial n a =>
    intro y
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
