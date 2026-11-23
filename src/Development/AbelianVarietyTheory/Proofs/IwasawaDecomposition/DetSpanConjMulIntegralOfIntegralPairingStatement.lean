module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetSpanConjMulIntegralOfIntegralPairing
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem _root_.GlobalTheory.T.detSpan_conj_mul_integral_of_integral_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M M' : Submodule (𝓞 E) (Fin n → E)), (∀ v ∈ M, ∀ w ∈ M', ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range) → ∀ x ∈ GlobalTheory.BetaEx.detSpan M, ∀ y ∈ GlobalTheory.BetaEx.detSpan M', IsCMField.complexConj E x * y ∈ (algebraMap (𝓞 E) E).range := by
  first | exact @GlobalTheory.detSpan_conj_mul_mem_range | exact GlobalTheory.detSpan_conj_mul_mem_range | (intros; apply GlobalTheory.detSpan_conj_mul_mem_range <;> assumption)
