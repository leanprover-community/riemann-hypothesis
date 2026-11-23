module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchConcatAlternantZero.proof : SchConcatAlternantZero.Statement := by
  intro r a lam hanti hnot
  have hex : ∃ i, lam i < a := by
    by_contra h
    exact hnot fun i => not_lt.mp fun hi => h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let k : Fin r := ⟨r - 1, by omega⟩
  have hkv : (k : ℕ) = r - 1 := rfl
  have hik : i ≤ k := by
    rw [Fin.le_def, hkv]; omega
  have hka : lam k < a := lt_of_le_of_lt (hanti hik) hi
  let j : Fin a := ⟨a - 1 - lam k, by omega⟩
  have hjv : (j : ℕ) = a - 1 - lam k := rfl
  have hexp : lam k + (r - 1 - (k : ℕ)) = a - 1 - (j : ℕ) := by
    rw [hkv, hjv]; omega
  unfold alternant
  apply Matrix.det_zero_of_column_eq (i := Sum.inl k) (j := Sum.inr j) Sum.inl_ne_inr
  intro p
  simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  rw [hexp]

end

end GroundTheory.Heights₂.Heights.RestTerms
