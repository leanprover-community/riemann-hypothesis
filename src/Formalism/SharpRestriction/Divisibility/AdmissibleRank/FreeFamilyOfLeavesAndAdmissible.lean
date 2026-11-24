module

public import Formalism.LocalRingCardinality.DataKap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions MeasureTheory Matrix ComplexConjugate

end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hkSigPar_lt (D : D7) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.sigPar D τ (i + 1) < DV.sigPar D τ i := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  unfold DV.sigPar
  by_cases h1 : i + 1 < D.R.k - 1
  · have h0 : i < D.R.k - 1 := by omega
    rw [dite_eq_left h1, dite_eq_left h0]
    have a := (D.hc τ).u_gt_v ⟨i + 1, h1⟩
    have b := (D.hc τ).v_gt_u ⟨i, h0⟩
    exact a.trans b
  · by_cases h0 : i < D.R.k - 1
    · have hb : i + 1 - (D.R.k - 1) < D.R.m := by omega
      rw [dite_eq_right h1, dite_eq_left hb, dite_eq_left h0]
      have a := (D.hc τ).u_last_gt (by omega) (by omega)
      have b := (D.hc τ).v_gt_u ⟨i, h0⟩
      have e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, by omega⟩ := by
        rw [Fin.mk.injEq]
        omega
      have e2 : (⟨i + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := by
        rw [Fin.mk.injEq]
        omega
      rw [e1]
      have b' : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨i, h0⟩ := by
        rw [← e2]
        exact b
      exact a.trans b'
    · have hb0 : i - (D.R.k - 1) < D.R.m := by omega
      have hb1 : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hb2 : i - (D.R.k - 1) + 1 < D.R.m := by omega
      rw [dite_eq_right h1, dite_eq_left hb1, dite_eq_right h0, dite_eq_left hb0]
      have a := (D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩
      have b := (D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ hb2
      have e1 : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, hb2⟩ := by
        rw [Fin.mk.injEq]
        omega
      rw [e1]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith

theorem aPlusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ (i + 1) ≤ DV.aPlusQ D j τ i := by
  obtain ⟨a, ha⟩ := DV.sigPar_int D τ i
  obtain ⟨b, hb⟩ := DV.sigPar_int D τ (i + 1)
  have h := hkSigPar_lt D τ i hi
  rw [ha, hb] at h
  have h' : b < a := by exact_mod_cast h
  have h'' : (b : ℚ) + 1 ≤ a := by exact_mod_cast h'
  rw [DV.aPlusQ_eq, DV.aPlusQ_eq, ha, hb]
  push_cast
  linarith

theorem aMinusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) (hc : j + c + 1 < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ (c + 1) := by
  have h0 : j + c < D.R.m := by omega
  have h1 : j + (c + 1) < D.R.m := by omega
  unfold DV.aMinusQ
  rw [dite_eq_left h0, dite_eq_left h1]
  have a := (D.hc τ).gap_be ⟨j + c, h0⟩
  have b := (D.hc τ).gap_eb ⟨j + c, h0⟩ hc
  have e1 : (⟨j + (c + 1), h1⟩ : Fin D.R.m) = ⟨j + c + 1, hc⟩ := by
    rw [Fin.mk.injEq]
    omega
  rw [e1]
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  push_cast
  linarith

theorem aMinusQ_mono (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c c' : ℕ) (h : c ≤ c') (hc' : j + c' < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ c' := by
  induction c', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (ih (by omega)).trans (aMinusQ_step D j τ n (by omega))


variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)


end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.DV

section Proved

open Formalism.BasicNotions.TH

end Proved


set_option linter.unusedVariables false

open Formalism.BasicNotions Formalism.BasicNotions.TH

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)


end Formalism.MainNotions.DIV

end
