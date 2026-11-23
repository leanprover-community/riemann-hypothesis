module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebra
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

open GlobalTheory.AlmostEt

theorem _root_.GlobalTheory.T.kaehler_relation_of_derivation_on_large_subalgebra : ∀ (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (n : ℕ) (x y : Fin n → S), ∑ i, x i • KaehlerDifferential.D A S (y i) = 0 → ∃ T : Finset S, ∀ C : Subalgebra A S, (↑T : Set S) ⊆ C → (∀ i, y i ∈ C) → ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D → ∑ i, x i • D (y i) = 0 := by
  first | exact @GlobalTheory.AlmostEt.kaehler_rel_local | exact GlobalTheory.AlmostEt.kaehler_rel_local | (intros; apply GlobalTheory.AlmostEt.kaehler_rel_local <;> assumption)
