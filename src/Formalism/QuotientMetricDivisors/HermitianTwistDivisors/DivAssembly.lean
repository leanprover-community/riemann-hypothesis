module

public import Formalism.QuotientMetricDivisors.StatementJ
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.DivisionValues

theorem divisor_inequality_assembly : DivAssembly := by
  intro J Pl _ _ TT _ muC mu0 Lpass logκ Fo Eb hu hP mlam e6 eP logOm logT kk hK eK pq a w phν nν fa
    eE δ h1 h2 h3 h4 h5 h6 h7 h8
  have hpt : ∀ j ρ, pq j * w j ρ * logOm + phν j ρ - fa j ρ - nν j ρ * logOm ≤
      (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (a ρ) - a ρ * logOm else 0) + eE j ρ +
        |pq j - kk| * |w j ρ| * |logOm| + |δ j ρ| * |logOm| := by
    intro j ρ
    have e7 := h7 j ρ
    rw [h8 j ρ]
    have hA : (pq j - kk) * w j ρ * logOm ≤ |pq j - kk| * |w j ρ| * |logOm| := by
      calc _ ≤ |(pq j - kk) * w j ρ * logOm| := le_abs_self _
        _ = _ := by rw [abs_mul, abs_mul]
    have hB : -(δ j ρ * logOm) ≤ |δ j ρ| * |logOm| := by rw [← abs_mul]; exact neg_le_abs _
    split_ifs at e7 ⊢ with hρ <;> linarith
  have hsum : ∑ j, ∑ ρ, (pq j * w j ρ * logOm + phν j ρ - fa j ρ - nν j ρ * logOm) ≤
      ∑ j, ∑ ρ, ((if ρ ∈ TT then Formalism.LatticeIndexTer.ph (a ρ) - a ρ * logOm else 0) + eE j ρ +
        |pq j - kk| * |w j ρ| * |logOm| + |δ j ρ| * |logOm|) :=
    sum_le_sum fun j _ => sum_le_sum fun ρ _ => hpt j ρ
  have hite : (∑ ρ : Pl, (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (a ρ) - a ρ * logOm else 0)) =
      ∑ t ∈ TT, (Formalism.LatticeIndexTer.ph (a t) - a t * logOm) := by
    rw [← sum_filter]
    congr 1
    ext x; simp
  have hK' : ∑ j, hK j ≤ ∑ j, ((∑ ρ, (phν j ρ - nν j ρ * logOm)) + eK j) :=
    sum_le_sum fun j _ => h4 j
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum hK'
  rw [hite] at hsum
  have hTT : ∑ t ∈ TT, ((Fintype.card J : ℝ) * (Formalism.LatticeIndexTer.ph (a t) - a t * logOm) - a t * logT) =
      (Fintype.card J : ℝ) * ∑ t ∈ TT, (Formalism.LatticeIndexTer.ph (a t) - a t * logOm) - ∑ t ∈ TT, a t * logT := by
    rw [sum_sub_distrib, mul_sum]
  rw [hTT]
  linarith

end Formalism.DivisionValues
