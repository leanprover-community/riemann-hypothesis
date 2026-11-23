module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGrassmannianRelationIdealSupMonomialSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


theorem _root_.GlobalTheory.T.mem_grassmannianRelationIdeal_sup_monomialSpan : ∀ (p q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ), h ∈ (GlobalTheory.GrassTop.J p q).restrictScalars ℝ ⊔ Submodule.span ℝ (GlobalTheory.GrassTop.basis p q) := by
  first | exact @GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top | exact GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top | (intros; apply GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top <;> assumption)
