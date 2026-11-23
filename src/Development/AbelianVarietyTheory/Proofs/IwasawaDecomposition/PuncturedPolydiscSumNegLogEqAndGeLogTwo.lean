module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
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

open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo

theorem tlog_sum_eq_and_log_two_le : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (∑ i : Fin a, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp (Fin.castLE ha i)) = (∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) / (2 * Real.pi)) ∧ (0 < a → Real.log 2 ≤ ∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) := by
  intro n a ha ρ hρ v hv
  have hpos : ∀ i : Fin a, 0 < ‖v.ofLp (Fin.castLE ha i)‖ := fun i => norm_pos_iff.2 (hv.2 i)
  have hlt : ∀ i : Fin a, ‖v.ofLp (Fin.castLE ha i)‖ < 1 / 2 := fun i =>
    lt_of_lt_of_le (hv.1 (Fin.castLE ha i)) hρ
  have hneg : ∀ i : Fin a, Real.log ‖v.ofLp (Fin.castLE ha i)‖ < 0 := fun i =>
    Real.log_neg (hpos i) (by linarith [hlt i])
  refine ⟨?_, fun h0 => ?_⟩
  · rw [Finset.sum_map, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.castLEEmb_apply, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]
    rw [abs_of_neg (hneg i)]
  · rw [Finset.sum_map]
    have hs := Finset.single_le_sum (f := fun i : Fin a => |Real.log ‖v (Fin.castLEEmb ha i)‖|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ (⟨0, h0⟩ : Fin a))
    refine le_trans ?_ hs
    have e : |Real.log ‖v (Fin.castLEEmb ha ⟨0, h0⟩)‖| = -Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ :=
      abs_of_neg (hneg _)
    simp only [] at e ⊢
    rw [e]
    have hl : Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ ≤ Real.log (1 / 2) :=
      Real.log_le_log (hpos _) (hlt _).le
    have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    linarith

end GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo
