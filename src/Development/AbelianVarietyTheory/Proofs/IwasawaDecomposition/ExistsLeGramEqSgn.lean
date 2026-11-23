module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField

namespace GlobalTheory.HermSignature

theorem exists_le_gram_eq_sgn : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → ∀ τ : E →+* ℂ, ∃ p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧ ReciprocityTheory.ChartRestriction.G.FD.gram τ G P = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  intro E _ _ _ r G hG hd τ
  obtain ⟨p, Q, hQ, h⟩ := GlobalTheory.Published.LandherrSt.exists_gram_eq_sgn hG hd τ
  refine ⟨min p r, min_le_right _ _, Q, hQ, ?_⟩
  rw [h]
  congr 1
  funext a
  have ha := a.2
  simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, lt_min_iff, ha, and_true]

end GlobalTheory.HermSignature
