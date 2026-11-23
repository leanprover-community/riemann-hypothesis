module

public import Mathlib.NumberTheory.Padics.Complex
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

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yza4.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.Yza4.Cg :
    {l : ℕ} → [inst : Fact (Nat.Prime l)] → ℕ → UpperTheory.Reformulated.B.Yza4.Qbar l → UpperTheory.Reformulated.B.Yza4.Qbar l → Prop :=
    fun {l : ℕ} [Fact (Nat.Prime l)] (n : ℕ) (a b : UpperTheory.Reformulated.B.Yza4.Qbar l) ↦
      ‖a - b‖ ≤ ‖(↑l : UpperTheory.Reformulated.B.Yza4.Qbar l) ^ n‖

theorem UpperTheory.Reformulated.B.Yza4.congruence_mul_of_unit_factor :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {n : ℕ} {P h un D : UpperTheory.Reformulated.B.Yza4.Qbar l},
      UpperTheory.Reformulated.B.Yza4.Cg n (P * h) (0 : UpperTheory.Reformulated.B.Yza4.Qbar l) →
        UpperTheory.Reformulated.B.Yza4.Cg n P (un * D) →
          ‖un‖ = (1 : ℝ) → ‖h‖ ≤ (1 : ℝ) → UpperTheory.Reformulated.B.Yza4.Cg n (D * h) (0 : UpperTheory.Reformulated.B.Yza4.Qbar l) := by
  intro l _ n P h un D h1 h2 hu hh
  unfold UpperTheory.Reformulated.B.Yza4.Cg at *
  rw [sub_zero] at h1 ⊢
  set c : ℝ := ‖(↑l : PadicAlgCl l) ^ n‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have hmul : ∀ a b : PadicAlgCl l, ‖a * b‖ = ‖a‖ * ‖b‖ := fun a b => norm_mul a b
  have key : un * (D * h) = P * h + (un * D - P) * h := by ring
  have h3 : ‖(un * D - P) * h‖ ≤ c := by
    rw [hmul, norm_sub_rev]
    calc ‖P - un * D‖ * ‖h‖ ≤ c * 1 := mul_le_mul h2 hh (norm_nonneg _) hc0
      _ = c := mul_one c
  have h4 : ‖un * (D * h)‖ ≤ c := by
    rw [key]
    exact (PadicAlgCl.isNonarchimedean l _ _).trans (max_le h1 h3)
  rw [hmul, hu, one_mul] at h4
  exact h4
