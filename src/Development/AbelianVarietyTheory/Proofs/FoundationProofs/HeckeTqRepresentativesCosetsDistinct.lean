module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory

theorem tqFam_cosets_distinct : ∀ (q : ℕ) (σ g : SL(2, ℤ)) (i i' : Fin (q + 1)), q.Prime →
    tqFam q σ i = mat g * tqFam q σ i' → i = i' := by
  intro q σ g i i' hq h
  have hq1 : (1 : ℤ) < q := by exact_mod_cast hq.one_lt
  have hdet : (mat g).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrArg (· 0 0) h
  have e01 := congrArg (· 0 1) h
  have e10 := congrArg (· 1 0) h
  have e11 := congrArg (· 1 1) h
  simp only [tqFam] at e00 e01 e10 e11
  have hi := i.isLt
  have hi' := i'.isLt
  by_cases h1 : (i : ℕ) < q <;> by_cases h2 : (i' : ℕ) < q <;>
    simp only [h1, h2, if_true, if_false, dg, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at e00 e01 e10 e11
  ·
    apply Fin.ext
    have hg00 : (mat g) 0 0 = 1 := by linarith
    rw [hg00] at e01
    have hii : (0:ℤ) ≤ (i : ℕ) := by positivity
    have hii' : (0:ℤ) ≤ (i' : ℕ) := by positivity
    have hlt : ((i : ℕ) : ℤ) < q := by exact_mod_cast h1
    have hlt' : ((i' : ℕ) : ℤ) < q := by exact_mod_cast h2
    rcases lt_trichotomy ((mat g) 0 1) 0 with hn | hz | hp
    · exfalso; nlinarith
    · rw [hz] at e01; exact_mod_cast (by linarith : ((i : ℕ) : ℤ) = (i' : ℕ))
    · exfalso; nlinarith
  · exfalso
    have hd : (q : ℤ) ∣ 1 := ⟨mat g 0 0 * mat σ 0 0 + mat g 0 1 * mat σ 1 0, by linear_combination e00⟩
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · exfalso
    have hd : (q : ℤ) ∣ 1 := by
      rw [← hdet]
      exact Dvd.dvd.sub (Dvd.dvd.mul_right ⟨mat σ 0 0, by linear_combination -e00⟩ _)
        (Dvd.dvd.mul_left ⟨mat σ 1 0, by linear_combination -e10⟩ _)
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · apply Fin.ext; omega

end GlobalTheory
