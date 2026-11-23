module

public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

namespace GlobalTheory

theorem endo_indecomposable_finite_length_nilpotent_or_bijective :
    ∀ (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
      (∀ A B : Submodule R P, IsCompl A B → A = ⊥ ∨ B = ⊥) →
      ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f := by
  intro R P _ _ _ _ _ hind f
  obtain ⟨n, hn⟩ := (LinearMap.eventually_isCompl_ker_pow_range_pow f).exists_forall_of_atTop
  have hc := hn (n + 1) (Nat.le_succ n)
  rcases hind _ _ hc with hk | hr
  · right
    have hk1 : LinearMap.ker f = ⊥ := by
      rw [eq_bot_iff, ← hk]
      intro x hx
      have hx' : f x = 0 := hx
      rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hx', map_zero]
    have hr1 : LinearMap.range (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hk, bot_sup_eq] at this
    have hs : LinearMap.range f = ⊤ := by
      rw [eq_top_iff, ← hr1]
      rintro _ ⟨x, rfl⟩
      rw [pow_succ', Module.End.mul_apply]
      exact ⟨_, rfl⟩
    exact ⟨LinearMap.ker_eq_bot.mp hk1, LinearMap.range_eq_top.mp hs⟩
  · left
    refine ⟨n + 1, ?_⟩
    have hk1 : LinearMap.ker (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hr, sup_bot_eq] at this
    exact LinearMap.ker_eq_top.mp hk1

end GlobalTheory
