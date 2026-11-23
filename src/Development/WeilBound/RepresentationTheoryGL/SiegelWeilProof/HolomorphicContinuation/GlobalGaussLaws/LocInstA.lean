module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

variable {σ : Type}

def reP (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (AddMonoidAlgebra.coeff p m).re

def imaginary (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (AddMonoidAlgebra.coeff p m).im

theorem coeff_reP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (reP p) m = (AddMonoidAlgebra.coeff p m).re := by
  classical
  unfold reP
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : AddMonoidAlgebra.coeff p m = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem coeff_imP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (imaginary p) m = (AddMonoidAlgebra.coeff p m).im := by
  classical
  unfold imaginary
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : AddMonoidAlgebra.coeff p m = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem eq_map_re_add_im (p : MvPolynomial σ ℂ) :
    p = map (algebraMap ℝ ℂ) (reP p) + C Complex.I * map (algebraMap ℝ ℂ) (imaginary p) := by
  ext m
  rw [MvPolynomial.coeff_add, coeff_C_mul, coeff_map, coeff_map, coeff_reP, coeff_imP]
  apply Complex.ext <;> simp

theorem eq_zero_of_eval_real (p : MvPolynomial σ ℂ) (h : ∀ y : σ → ℝ, eval (fun i => (y i : ℂ)) p = 0) : p = 0 := by
  apply GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_real <;> assumption

end PositivityTheory.Rg.Sw.Glob.LocInstH
