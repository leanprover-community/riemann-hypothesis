module

public import Formalism.LocalRingCardinality.DataKernels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem unitChain_num_sub_half (R : Ranks) (q : ℚ) (hq : ∃ z : ℤ, q = z) (j : ℕ) :
    (((q - (R.N j : ℚ) / 2).num : ℤ) : ℚ) = q - (R.N j : ℚ) / 2 := by
  obtain ⟨z, rfl⟩ := hq
  have hN : Even (R.N j) := by
    unfold Ranks.N
    exact R.k_even.add ((R.t_odd.add_one).mul_left j)
  obtain ⟨a, ha⟩ := hN
  have h : (z : ℚ) - (R.N j : ℚ) / 2 = ((z - a : ℤ) : ℚ) := by
    rw [ha]; push_cast; ring
  rw [h, Rat.num_intCast]

def unitColumnChain (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) :
    ColumnChain R ι hc where
  cls _ := Unit
  stab _ _ := PUnit
  DGam := 1
  DGam_pos := Nat.one_pos
  dvd_DGam _ _ _ := by simp
  Y _ := Unit
  de _ _ _ := 1
  de_ne _ _ _ := one_ne_zero
  rhoDet _ _ := 1
  rhoDet' _ _ := 1
  rho_norm _ _ _ := norm_one
  rho'_norm _ _ _ := norm_one
  unf _ _ _ := LinearMap.id
  sSharp i τ := if h : i < R.m then (sExp' R ((hc τ).e ⟨i, h⟩) (i + 1)).num else 0
  sSharp_eq i h τ := by
    rw [dite_eq_left h]
    exact unitChain_num_sub_half R _ ((hc τ).e_int _) _
  sDiv i τ := if h : i < R.m then (sExp R ((hc τ).e ⟨i, h⟩) (i + 1)).num else 0
  sDiv_eq i h τ := by
    rw [dite_eq_left h]
    exact unitChain_num_sub_half R _ ((hc τ).e_int _) _

end GlobalTheory
