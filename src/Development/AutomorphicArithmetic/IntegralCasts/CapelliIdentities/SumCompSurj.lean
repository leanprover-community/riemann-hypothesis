module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Card
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.Index

@[expose] public section

theorem UpperTheory.Reformulated.B.Rd1.sum_comp_surj :
    ∀ {A B : Type} [inst : AddCommGroup A] [inst_1 : AddCommGroup B]
    [inst_2 : Fintype A] [inst_3 : Fintype B] (π : A →+ B),
    Function.Surjective (⇑π : A → B) →
      ∀ (G : B → ℂ), (↑(Fintype.card B) : ℂ) * ∑ a : A, G ((π : A → B) a) = (↑(Fintype.card A) : ℂ) * ∑ b : B, G b := by
  intro A B _ _ _ _ π hπ G
  classical
  have hfib : ∀ b : B, (Finset.univ.filter (fun a : A => π a = b)).card
      = (Finset.univ.filter (fun a : A => π a = 0)).card := fun b =>
    AddMonoidHom.card_fiber_eq_of_mem_range π (hπ b) (hπ 0)
  set k : ℕ := (Finset.univ.filter (fun a : A => π a = 0)).card with hk
  have key : ∀ H : B → ℂ, ∑ a : A, H (π a) = (k : ℂ) * ∑ b : B, H b := by
    intro H
    rw [← Finset.sum_fiberwise' Finset.univ (fun a : A => π a) H, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_const, hfib b, nsmul_eq_mul]
  have h1 : (Fintype.card A : ℂ) = (k : ℂ) * (Fintype.card B : ℂ) := by
    simpa using key (fun _ => 1)
  rw [key G, h1]
  ring
