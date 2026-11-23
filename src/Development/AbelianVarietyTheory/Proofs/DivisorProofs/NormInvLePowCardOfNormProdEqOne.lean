module

public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Analysis.Normed.Field.Basic

@[expose] public section

namespace GlobalTheory

theorem norm_inv_le_pow_card_of_norm_prod_eq_one :
    ∀ (B : Multiset ℂˣ) (M : ℝ), 1 ≤ M → (∀ b ∈ B, ‖(b : ℂ)‖ ≤ M) →
      ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 → ∀ b ∈ B, ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ M ^ B.card := by
  intro B M hM hB hprod b hb
  have aux : ∀ C : Multiset ℂˣ, (∀ c ∈ C, ‖(c : ℂ)‖ ≤ M) →
      ‖(C.map fun c : ℂˣ => (c : ℂ)).prod‖ ≤ M ^ C.card := by
    intro C
    induction C using Multiset.induction_on with
    | empty => intro _; simp
    | cons a C ih =>
      intro hC
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, norm_mul,
        mul_comm (M ^ _)]
      exact mul_le_mul (hC a (Multiset.mem_cons_self a C))
        (ih fun c hc => hC c (Multiset.mem_cons_of_mem hc)) (norm_nonneg _) (by linarith)
  obtain ⟨C, rfl⟩ := Multiset.exists_cons_of_mem hb
  have hC : ∀ c ∈ C, ‖(c : ℂ)‖ ≤ M := fun c hc => hB c (Multiset.mem_cons_of_mem hc)
  rw [Multiset.map_cons, Multiset.prod_cons, norm_mul] at hprod
  have hinv : ‖((b⁻¹ : ℂˣ) : ℂ)‖ = ‖(C.map fun c : ℂˣ => (c : ℂ)).prod‖ := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact (eq_inv_of_mul_eq_one_right hprod).symm
  rw [hinv, Multiset.card_cons]
  exact (aux C hC).trans (pow_le_pow_right₀ hM (Nat.le_succ _))

end GlobalTheory
