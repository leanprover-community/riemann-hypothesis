module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardPrimitiveTuplesHermitianGramModUniformizer
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

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.card_primitive_tuples_hermitian_gram_mod_uniformizer : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (n m j : ℕ), 2 * m + 3 ≤ n → 1 ≤ j → ∀ (Gm : Matrix (Fin m) (Fin m) E), IsHerm L Gm → IsIntM L Gm → ∀ (R : Finset E), (∀ u ∈ R, u ∈ L.O) → (∀ u ∈ L.O, ∃! w, w ∈ R ∧ ∃ c ∈ L.O, u - w = algebraMap F E ((ϖ : F) ^ j) * c) → ∀ N : ℕ, N = Set.ncard {x : Fin m → Fin n → E | (∀ a i, x a i ∈ R) ∧ (∃ y : Fin m → Fin n → E, (∀ a i, y a i ∈ L.O) ∧ ∀ a b, hf L 1 (x a) (y b) = if a = b then 1 else 0) ∧ ∀ a b, ∃ c ∈ L.O, hf L 1 (x b) (x a) - Gm a b = algebraMap F E ((ϖ : F) ^ j) * c} → (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) ≤ 2 * N ∧ (N : ℝ) ≤ 2 * (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) := by
  first | exact @GlobalTheory.GramCount.primitive_gram_count | exact GlobalTheory.GramCount.primitive_gram_count | (intros; apply GlobalTheory.GramCount.primitive_gram_count <;> assumption)
