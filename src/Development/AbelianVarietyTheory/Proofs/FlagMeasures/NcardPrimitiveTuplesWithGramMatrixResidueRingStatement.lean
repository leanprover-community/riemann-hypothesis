module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Basic.Real.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimitiveTuplesWithGramMatrixResidueRing
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

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.ncard_primitiveTuplesWithGramMatrix_residueRing : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (m n : ℕ), 2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) → (q : ℝ) ^ (2 * n * m - m ^ 2) ≤ 2 * (Set.ncard (sols c n G) : ℝ) ∧ (Set.ncard (sols c n G) : ℝ) ≤ 2 * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  first | exact @GlobalTheory.GramCount.ncard_sols_residue | exact GlobalTheory.GramCount.ncard_sols_residue | (intros; apply GlobalTheory.GramCount.ncard_sols_residue <;> assumption)
