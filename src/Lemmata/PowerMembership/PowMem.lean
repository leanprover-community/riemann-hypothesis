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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u_1 u_2

namespace Bl.PowerMembership

private lemma powMem {R : Type u_1} {M : Type u_2} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) (f : Module.End R M) (hf : ∀ v : M, v ∈ S → f v ∈ S) (n : ℕ) :
    ∀ {v : M}, v ∈ S → (f ^ n) v ∈ S := by
  induction n with
  | zero => intro v hv; simpa using hv
  | succ n ih => intro v hv; rw [pow_succ']; exact hf _ (ih hv)

theorem goal1 :
  ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing.{u_1} R] [inst_1 : AddCommGroup.{u_2} M]
  [inst_2 : Module.{u_1, u_2} R M] (S : Submodule.{u_1, u_2} R M) (f : Module.End.{u_1, u_2} R M),
  (∀ (v : M),
      Membership.mem.{u_2, u_2} S v → Membership.mem.{u_2, u_2} S (DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1} f v)) →
    ∀ (P : Polynomial.{u_1} R) {v : M},
      Membership.mem.{u_2, u_2} S v →
        Membership.mem.{u_2, u_2} S
          (DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1}
            (DFunLike.coe.{max (u_2 + 1) (u_1 + 1), u_1 + 1, u_2 + 1} (Polynomial.aeval.{u_1, u_2} f) P) v) := by
  intro R M _ _ _ S f hf P v hv
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), LinearMap.add_apply]; exact S.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact S.smul_mem a (powMem S f hf n hv)

end Bl.PowerMembership
