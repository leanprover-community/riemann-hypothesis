module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_eq_const_mul_prod_inner_of_positionwise (ι : Type) [Fintype ι] [DecidableEq ι]
    (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
    (B : (∀ i, Hs i) → (∀ i, Hs i) → ℂ)
    (h : ∀ i v v', ∃ c : ℂ, ∀ w w' : Hs i,
      B (Function.update v i w) (Function.update v' i w') = c * ⟪w, w'⟫_ℂ) :
    ∃ c : ℂ, ∀ v v', B v v' = c * ∏ i, ⟪v i, v' i⟫_ℂ := by
  by_cases h0 : ∃ i, ∀ w : Hs i, w = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, fun v v' => ?_⟩
    obtain ⟨c, hc⟩ := h i v v'
    have h1 := hc (v i) (v' i)
    rw [Function.update_eq_self, Function.update_eq_self, hi (v i)] at h1
    simpa using h1
  · have h1 : ∀ i, ∃ e : Hs i, ⟪e, e⟫_ℂ = 1 := by
      intro i
      have : ∃ w : Hs i, w ≠ 0 := by
        by_contra hn
        exact h0 ⟨i, fun w => by_contra fun hw => hn ⟨w, hw⟩⟩
      obtain ⟨w, hw⟩ := this
      refine ⟨((‖w‖ : ℂ))⁻¹ • w, ?_⟩
      have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
      rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
      simp only [map_inv₀, Complex.conj_ofReal]
      change ((‖w‖ : ℂ))⁻¹ * (((‖w‖ : ℂ))⁻¹ * (‖w‖ : ℂ) ^ 2) = 1
      field_simp
    choose e he using h1
    have step : ∀ i v v', B v v' =
        B (Function.update v i (e i)) (Function.update v' i (e i)) * ⟪v i, v' i⟫_ℂ := by
      intro i v v'
      obtain ⟨c, hc⟩ := h i v v'
      have h2 := hc (v i) (v' i)
      rw [Function.update_eq_self, Function.update_eq_self] at h2
      rw [h2, hc, he, mul_one]
    have key : ∀ (s : Finset ι) v v', B v v' =
        B (s.piecewise e v) (s.piecewise e v') * ∏ i ∈ s, ⟪v i, v' i⟫_ℂ := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro v v'; simp
      | insert a s ha ih =>
        intro v v'
        rw [ih v v', step a (s.piecewise e v) (s.piecewise e v'), Finset.prod_insert ha,
          Finset.piecewise_insert, Finset.piecewise_insert,
          Finset.piecewise_eq_of_notMem _ _ _ ha, Finset.piecewise_eq_of_notMem _ _ _ ha,
          mul_assoc]
    refine ⟨B e e, fun v v' => ?_⟩
    have := key Finset.univ v v'
    rwa [Finset.piecewise_univ, Finset.piecewise_univ] at this

end GlobalTheory
