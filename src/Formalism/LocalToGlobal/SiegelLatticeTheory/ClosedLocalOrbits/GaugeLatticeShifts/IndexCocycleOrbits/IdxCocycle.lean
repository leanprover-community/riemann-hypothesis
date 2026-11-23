module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.OrbStabZ
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.SG.Pf.IndexCocycleOrbits

theorem index_ratio_identity (m n aB aC cA : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (key : aB * n = m * aC) :
    ((m * cA : ℕ) : ℝ) / (aB : ℝ) = (n : ℝ) * ((cA : ℝ) / (aC : ℝ)) := by
  have keyR : (aB : ℝ) * n = m * aC := by exact_mod_cast key
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  by_cases haC : (aC : ℝ) = 0
  · have haB : (aB : ℝ) = 0 := by
      have h0 : (aB : ℝ) * n = 0 := by rw [keyR, haC, mul_zero]
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hnR
    rw [haB, haC]
    simp
  · have haB : (aB : ℝ) ≠ 0 := by
      intro h
      have h0 : (m : ℝ) * aC = 0 := by rw [← keyR, h, zero_mul]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact hmR h'
      · exact haC h'
    rw [eq_comm, mul_div_assoc', div_eq_div_iff haC haB]
    linear_combination (cA : ℝ) * keyR

theorem idxCocycle : IdxCocycle := by
  intro G _ A B C hBC hn
  have hBinf : B ⊓ C = B := inf_eq_left.mpr hBC
  have e1 : B.relIndex (C ⊓ A) * C.relIndex A = B.relIndex A := by
    have h := Subgroup.relIndex_inf_mul_relIndex B C A
    rwa [hBinf] at h
  have e2 : A.relIndex (B ⊓ C) * B.relIndex C = (A ⊓ B).relIndex C :=
    Subgroup.relIndex_inf_mul_relIndex A B C
  rw [hBinf] at e2
  have e3 : B.relIndex (A ⊓ C) * A.relIndex C = (B ⊓ A).relIndex C :=
    Subgroup.relIndex_inf_mul_relIndex B A C
  rw [inf_comm B A, inf_comm A C] at e3
  have hm : B.relIndex (C ⊓ A) ≠ 0 := fun h =>
    hn (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  have key : A.relIndex B * B.relIndex C = B.relIndex (C ⊓ A) * A.relIndex C := by rw [e2, e3]
  unfold IdxRatio
  rw [← e1]
  exact index_ratio_identity _ _ _ _ _ hm hn key

end Formalism.L2.SG.Pf.IndexCocycleOrbits
