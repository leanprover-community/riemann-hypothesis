module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre

theorem summable_comp_of_bounded_fibres :
    ∀ (A B : Type) (π : A → B) (k : ℕ), (∀ b, Finite {a // π a = b} ∧ Nat.card {a // π a = b} ≤ k) → ∀ (g : B → ℝ), (∀ b, 0 ≤ g b) → Summable g → Summable (fun a => g (π a)) ∧ ∑' a, g (π a) ≤ k * ∑' b, g b := by
  intro A B π k h g hg hs
  classical
  have hcard : ∀ (u : Finset A) (b : B), (u.filter (fun a => π a = b)).card ≤ k := by
    intro u b
    have hf : ({a | π a = b} : Set A).Finite := Set.finite_coe_iff.mp (h b).1
    calc (u.filter (fun a => π a = b)).card
        = ((u.filter (fun a => π a = b) : Finset A) : Set A).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ ({a | π a = b} : Set A).ncard := by
          apply Set.ncard_le_ncard _ hf
          intro a ha
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
          exact ha.2
      _ = Nat.card {a // π a = b} := (Nat.card_coe_set_eq _).symm
      _ ≤ k := (h b).2
  have hbound : ∀ u : Finset A, ∑ a ∈ u, g (π a) ≤ k * ∑' b, g b := by
    intro u
    rw [Finset.sum_comp]
    calc ∑ b ∈ u.image π, (u.filter (fun a => π a = b)).card • g b
        ≤ ∑ b ∈ u.image π, (k : ℝ) * g b := by
          apply Finset.sum_le_sum
          intro b _
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard u b) (hg b)
      _ = k * ∑ b ∈ u.image π, g b := by rw [Finset.mul_sum]
      _ ≤ k * ∑' b, g b :=
          mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun b _ => hg b)) (Nat.cast_nonneg k)
  have hsum : Summable (fun a => g (π a)) := summable_of_sum_le (fun a => hg (π a)) hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre
