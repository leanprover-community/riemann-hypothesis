module

public import Formalism.CyclotomicNorms.StatementT
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open Polynomial

namespace GlobalTheory.RangeOfPowerFixed

theorem mem_range_of_pow_eq_self {g : ℕ} [Fact (Nat.Prime g)] {K : Type*} [Field K] [Algebra (ZMod g) K]
    (z : K) (hz : z ^ g = z) : ∃ c : ZMod g, algebraMap (ZMod g) K c = z := by
  classical
  by_contra hne
  simp only [not_exists] at hne
  have hg : 1 < g := (Fact.out : Nat.Prime g).one_lt
  set P : K[X] := X ^ g - X with hPeq
  have hP0 : P ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hg
  have hdeg : P.natDegree = g := Polynomial.natDegree_X_pow_sub_X (R := K) hg

  have hroot : ∀ x : K, x ^ g = x → x ∈ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hP0, hPeq]
    simp [hx]

  set S : Finset K := insert z (Finset.univ.image (algebraMap (ZMod g) K)) with hSeq
  have hzS : z ∉ Finset.univ.image (algebraMap (ZMod g) K) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hne
  have hcard : S.card = g + 1 := by
    rw [hSeq, Finset.card_insert_of_notMem hzS,
      Finset.card_image_of_injective _ (algebraMap (ZMod g) K).injective, Finset.card_univ, ZMod.card]
  have hsub : S ⊆ P.roots.toFinset := by
    intro x hx
    rw [hSeq, Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨c, -, rfl⟩
    · exact hroot _ hz
    · exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  have := (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans (card_roots' P))
  omega

theorem main : ∀ {g : ℕ} [inst : Fact (Nat.Prime g)] (z : Formalism.CyclotomicNorms.Fbar g), z ^ g = z →
    ∃ (c : ZMod g), (Algebra.algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) : ZMod g → Formalism.CyclotomicNorms.Fbar g) c = z := by
  intro g _ z hz
  exact mem_range_of_pow_eq_self z hz

end GlobalTheory.RangeOfPowerFixed
