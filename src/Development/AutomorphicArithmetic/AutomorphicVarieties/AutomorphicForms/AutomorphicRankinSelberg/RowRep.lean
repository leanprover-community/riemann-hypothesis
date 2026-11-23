module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped MatrixGroups

theorem UpperTheory.V.Af.Rs.rowRep :
    UpperTheory.V.Af.Rs.RowRep := by
  intro x
  set g := (x 0).gcd (x 1) with hg
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · obtain ⟨h0', h1'⟩ := Int.gcd_eq_zero_iff.mp h0
    refine ⟨0, 1, ?_⟩
    funext i
    fin_cases i <;> simp [h0', h1']
  · have hc : IsCoprime (x 0 / (g : ℤ)) (x 1 / (g : ℤ)) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
    obtain ⟨γ, -, hγ⟩ := ModularGroup.bottom_row_surj (R := ℤ)
      (show ![x 0 / (g : ℤ), x 1 / (g : ℤ)] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} by simpa using hc)
    refine ⟨g, γ, ?_⟩
    funext i
    have hi := congrFun hγ i
    simp only [UpperTheory.V.Af.Rs.row, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hi]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left (x 0) (x 1))).symm
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right (x 0) (x 1))).symm
