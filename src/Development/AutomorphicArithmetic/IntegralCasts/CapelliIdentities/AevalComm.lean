module

public import Mathlib.Algebra.Polynomial.AlgebraMap
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

theorem UpperTheory.Reformulated.B.Qk66.aeval_comm :
    ∀ {L M N : Type} [inst : Field L]
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module L M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module L N]
    (φ : M →ₗ[L] N) (A : Module.End L M) (A' : Module.End L N),
    (∀ (y : M), (φ : M → N) ((A : M → M) y) = (A' : N → N) ((φ : M → N) y)) →
      ∀ (Q : Polynomial L) (y : M),
        (φ : M → N) (((Polynomial.aeval A : Polynomial L → Module.End L M) Q : M → M) y) =
          ((Polynomial.aeval A' : Polynomial L → Module.End L N) Q : N → N) ((φ : M → N) y) := by
  intro L M N _ _ _ _ _ φ A A' h Q
  induction Q using Polynomial.induction_on with
  | C a =>
    intro y
    simp [Module.algebraMap_end_apply]
  | add p q hp hq =>
    intro y
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a ih =>
    intro y
    rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval A), map_mul (Polynomial.aeval A'),
      Polynomial.aeval_X, Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]
