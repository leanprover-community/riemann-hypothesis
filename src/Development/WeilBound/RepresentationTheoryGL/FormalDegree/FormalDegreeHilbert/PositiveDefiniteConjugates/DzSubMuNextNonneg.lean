module

public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FiPmatEqFiOneSmulPmat

@[expose] public section

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem exists_pmat {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    ∃ z : PCoord ε → ℂ, pmat z = X := by
  refine ⟨fun ab => X ab.1.1 ab.1.2, ?_⟩
  have hH := ReciprocityTheory.ChartRestriction.DS.S7.isHermitian_of_mem_noncompactPart' hX
  ext a b
  show (if h : b < a ∧ ε a ≠ ε b then X a b else if h' : a < b ∧ ε b ≠ ε a then star (X b a) else 0) = X a b
  split_ifs with h1 h2
  · rfl
  · have h3 := congrFun (congrFun hH a) b
    simpa [Matrix.conjTranspose_apply] using h3
  · symm
    apply _root_.ReciprocityTheory.ChartRestriction.DS.inP_apply_eq_zero hX
    by_contra hne
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact h2 ⟨hlt, fun e => hne e.symm⟩
    · exact hne (by rw [heq])
    · exact h1 ⟨hgt, hne⟩

theorem one_le_lead_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (i : ℕ) (hi : i ≤ n) :
    1 ≤ (lead i (NormedSpace.exp X)).re := by
  obtain ⟨z, hz⟩ := exists_pmat hX
  have h0 := ReciprocityTheory.ChartRestriction.DS.fi_nonneg z i
  rw [hz] at h0
  have hpos : 0 < (lead i (NormedSpace.exp X)).re := by
    have hsub := (ReciprocityTheory.ChartRestriction.DS.S7.exp_noncompactPart_posDef hX).submatrix (Fin.castLE_injective hi)
    show 0 < (if h : i ≤ n then ((NormedSpace.exp X).submatrix (Fin.castLE h) (Fin.castLE h)).det else 0).re
    rw [dite_eq_left hi]
    exact (Complex.pos_iff.1 hsub.det_pos).1
  exact (Real.log_nonneg_iff hpos).1 h0

end PositivityTheory.RgFd
