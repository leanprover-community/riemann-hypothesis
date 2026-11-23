module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.Galois.Notation
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace GroundTheory.Variant₂.N1

theorem exists_pow_apply_eq_self_of_aeval_eq_zero {K : Type*} [Field K] {Ω : Type*} [Field Ω]
    [Algebra K Ω] (σ : Gal(Ω/K)) {p : Polynomial K} (hp : p ≠ 0) {x : Ω}
    (hx : Polynomial.aeval x p = 0) : ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x := by
  have hmem : ∀ n : ℕ, (σ ^ n) x ∈ p.rootSet Ω := fun n => by
    rw [Polynomial.mem_rootSet_of_ne hp, Polynomial.aeval_algHom_apply, hx, map_zero]
  have : Finite (p.rootSet Ω) := (Polynomial.rootSet_finite p Ω).to_subtype
  let f : ℕ → p.rootSet Ω := fun n => ⟨(σ ^ n) x, hmem n⟩
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : (σ ^ i) x = (σ ^ j) x := congrArg Subtype.val hij
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨j - i, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ i).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]
  · refine ⟨i - j, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ j).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]

end GroundTheory.Variant₂.N1
