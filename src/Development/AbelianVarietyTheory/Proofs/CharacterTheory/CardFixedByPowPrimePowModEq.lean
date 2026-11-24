module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.Perm.Cycle.Type

@[expose] public section

namespace GlobalTheory

theorem card_fixedBy_pow_prime_pow_modEq (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X]
    (x : G) (p k : ℕ) (hp : p.Prime) :
    Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End (MulAction.fixedBy X (x ^ p ^ k)) := fun y => ⟨x • (y : X), by
    have hy : (x ^ p ^ k) • (y : X) = y := y.2
    show (x ^ p ^ k) • x • (y : X) = x • (y : X)
    rw [← mul_smul, ← pow_succ, pow_succ', mul_smul, hy]⟩
  have hf : ∀ (n : ℕ) (y : MulAction.fixedBy X (x ^ p ^ k)), (((f ^ n) y : MulAction.fixedBy X (x ^ p ^ k)) : X) = x ^ n • (y : X) := by
    intro n
    induction n with
    | zero => intro y; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ', mul_smul, ← ih y]
      rfl
  have h1 : f ^ p ^ k = 1 := by
    funext y
    apply Subtype.ext
    rw [hf]
    exact y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := k) h1
  have e : (Function.fixedPoints f) ≃ MulAction.fixedBy X x :=
    { toFun := fun y => ⟨(y.1 : X), congrArg Subtype.val y.2⟩
      invFun := fun y => ⟨⟨y.1, MulAction.fixedBy_subset_fixedBy_zpow X x ((p ^ k : ℕ) : ℤ) y.2 |> fun h => by
          rwa [zpow_natCast] at h⟩, Subtype.ext y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h2

end GlobalTheory
