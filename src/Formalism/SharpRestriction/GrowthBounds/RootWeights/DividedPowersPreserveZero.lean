module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Nat.Factorial.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section good

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

def DividedPowersPreserve (Q : V → Prop) (D : Module.End K V) : Prop :=
  ∀ (k : ℕ) (x : V), Q x → Q (((k.factorial : K)⁻¹) • (D ^ k) x)

theorem predicate_finset_sum_mem (Q : V → Prop) (h0 : Q 0) (hadd : ∀ x y, Q x → Q y → Q (x + y)) {α : Type*}
    (s : Finset α) (f : α → V) (h : ∀ i ∈ s, Q (f i)) : Q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hadd _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem divided_powers_preserve_add (Q : V → Prop) (h0 : Q 0) (hadd : ∀ x y, Q x → Q y → Q (x + y))
    (D D' : Module.End K V) (hc : Commute D D') (hD : DividedPowersPreserve Q D) (hD' : DividedPowersPreserve Q D') :
    DividedPowersPreserve Q (D + D') := by
  intro k x hx
  rw [hc.add_pow, LinearMap.sum_apply, Finset.smul_sum]
  refine predicate_finset_sum_mem Q h0 hadd _ _ fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have h1 := hD m _ (hD' (k - m) x hx)
  have h2 : ((k.factorial : K)⁻¹) • (D ^ m * D' ^ (k - m) * ((k.choose m : ℕ) : Module.End K V)) x =
      ((m.factorial : K)⁻¹) • (D ^ m) ((((k - m).factorial : K)⁻¹) • (D' ^ (k - m)) x) := by
    have h3 : ((k.choose m : ℕ) : Module.End K V) x = ((k.choose m : ℕ) : K) • x := by
      rw [Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    simp only [Module.End.mul_apply, h3, map_smul, smul_smul]
    congr 1
    have h4 : ((k.choose m : ℕ) : K) = (k.factorial : K) / ((m.factorial : K) * ((k - m).factorial : K)) :=
      Nat.cast_choose K hmk
    have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hm' : (m.factorial : K) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hkm : ((k - m).factorial : K) ≠ 0 := by exact_mod_cast (k - m).factorial_ne_zero
    rw [h4]
    field_simp
  rw [h2]
  exact h1

end good

end Formalism.MainNotions.G.GLWeightTheory
